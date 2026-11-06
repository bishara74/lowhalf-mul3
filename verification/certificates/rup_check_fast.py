"""Compiled (numba) forward DRUP checker. Same semantics as rup_check.py:
every added lemma must be RUP w.r.t. the live database; deletions are applied lazily
(sound: every clause in the database is implied by the CNF); success = empty clause or
top-level conflict. Watch lists are linked lists of watch entries e = 2*cid + slot.
"""
import sys, time, array
import numpy as np
from numba import njit


def parse(cnf_path, proof_path):
    lits = array.array('i')
    starts = array.array('q')
    lens = array.array('i')
    nv = 0
    n_orig = 0
    cur = []
    with open(cnf_path) as f:
        for line in f:
            if not line or line[0] in 'c%':
                continue
            if line[0] == 'p':
                nv = int(line.split()[2])
                continue
            for tok in line.split():
                x = int(tok)
                if x == 0:
                    cl = list(dict.fromkeys(cur))        # drop repeated literals, keep order
                    starts.append(len(lits)); lens.append(len(cl)); lits.extend(cl); cur = []
                else:
                    cur.append(x)
    n_orig = len(lens)
    ops = array.array('q')            # >=0: add clause id ; <0: delete clause id (-(id+1))
    table = {}                        # hash(sorted lits) -> list of live ids
    for cid in range(n_orig):
        s = starts[cid]
        key = hash(tuple(sorted(lits[s:s + lens[cid]])))
        table.setdefault(key, []).append(cid)
    with open(proof_path) as f:
        for line in f:
            t = line.split()
            if not t:
                continue
            if t[-1] != '0':
                raise ValueError('unterminated proof line')
            if t[0] == 'd':
                sl = sorted(set(int(x) for x in t[1:-1]))
                ids = table.get(hash(tuple(sl)))
                if ids:
                    # confirm the literal sets match (hash collisions)
                    for k in range(len(ids) - 1, -1, -1):
                        c = ids[k]
                        s = starts[c]
                        if sorted(lits[s:s + lens[c]]) == sl:
                            ids.pop(k)
                            ops.append(-(c + 1))
                            break
                continue
            cl = list(dict.fromkeys(int(x) for x in t[:-1]))
            cid = len(lens)
            starts.append(len(lits)); lens.append(len(cl)); lits.extend(cl)
            table.setdefault(hash(tuple(sorted(cl))), []).append(cid)
            ops.append(cid)
    return (nv, n_orig, np.frombuffer(lits, dtype=np.int32).copy(),
            np.frombuffer(starts, dtype=np.int64).copy(), np.frombuffer(lens, dtype=np.int32).copy(),
            np.frombuffer(ops, dtype=np.int64).copy())


@njit(cache=False)
def _li(l):
    return 2 * l if l > 0 else -2 * l + 1


@njit(cache=False)
def _value(val, l):
    v = val[l if l > 0 else -l]
    return v if l > 0 else -v


def check(cnf_path, proof_path):
    t0 = time.time()
    nv, n_orig, lits, starts, lens, ops = parse(cnf_path, proof_path)
    t1 = time.time()
    ok, reason, nadd = core(nv, n_orig, lits, starts, lens, ops)
    return {'ok': bool(ok), 'reason': ['proof ended without empty clause', 'empty clause derived',
                                       'top-level conflict', 'lemma not RUP', 'empty clause in CNF'][reason],
            'lemmas_checked': int(nadd), 'parse_s': round(t1 - t0, 1), 'check_s': round(time.time() - t1, 1)}


@njit(cache=False)
def core(nv, n_orig, lits, starts, lens, ops):
    ncls = lens.shape[0]
    val = np.zeros(nv + 1, dtype=np.int8)
    alive = np.ones(ncls, dtype=np.bool_)
    head = -np.ones(2 * nv + 2, dtype=np.int64)
    nxt = -np.ones(2 * ncls, dtype=np.int64)
    trail = np.zeros(nv + 2, dtype=np.int32)
    tl = 0
    top = 0                      # trail length of permanent (top-level) assignments
    conflict = False

    # attach watches for all original clauses with length >= 2
    for c in range(n_orig):
        if lens[c] == 0:
            return True, 4, 0
        if lens[c] >= 2:
            s = starts[c]
            for slot in range(2):
                l = lits[s + slot]
                li = 2 * l if l > 0 else -2 * l + 1
                e = 2 * c + slot
                nxt[e] = head[li]
                head[li] = e

    # top-level scan of original clauses
    for c in range(n_orig):
        res, tl = topscan(c, lits, starts, lens, val, alive, head, nxt, trail, tl)
        if res:
            return True, 2, 0
    top = tl

    nadd = 0
    for k in range(ops.shape[0]):
        op = ops[k]
        if op < 0:
            alive[-op - 1] = False
            continue
        c = op
        s = starts[c]
        n = lens[c]
        # RUP check
        start = tl
        confl = False
        for i in range(n):
            l = lits[s + i]
            v = val[l if l > 0 else -l]
            v = v if l > 0 else -v
            if v == 1:
                confl = True
                break
            if v == 0:
                x = -l
                val[x if x > 0 else -x] = 1 if x > 0 else -1
                trail[tl] = x
                tl += 1
        if not confl:
            confl, tl = propagate(start, lits, starts, lens, val, alive, head, nxt, trail, tl)
        for i in range(start, tl):
            x = trail[i]
            val[x if x > 0 else -x] = 0
        tl = start
        if not confl:
            return False, 3, nadd
        nadd += 1
        if n == 0:
            return True, 1, nadd
        if n >= 2:
            for slot in range(2):
                l = lits[s + slot]
                li = 2 * l if l > 0 else -2 * l + 1
                e = 2 * c + slot
                nxt[e] = head[li]
                head[li] = e
        res, tl = topscan(c, lits, starts, lens, val, alive, head, nxt, trail, tl)
        if res:
            return True, 2, nadd
    return False, 0, nadd


@njit(cache=False)
def propagate(start, lits, starts, lens, val, alive, head, nxt, trail, tl):
    i = start
    while i < tl:
        p = trail[i]
        i += 1
        fl = -p
        li = 2 * fl if fl > 0 else -2 * fl + 1
        e = head[li]
        head[li] = -1
        prev_keep = -1          # we rebuild the list of entries that stay on fl
        while e != -1:
            enext = nxt[e]
            c = e >> 1
            if not alive[c]:
                e = enext
                continue
            s = starts[c]
            # ensure the false literal fl is at position 1 (entries do not encode positions)
            if lits[s] == fl:
                lits[s] = lits[s + 1]
                lits[s + 1] = fl
            other = lits[s]
            vo = val[other if other > 0 else -other]
            vo = vo if other > 0 else -vo
            e1 = e                  # relink exactly the entry being processed
            if vo == 1:
                # keep on fl's list
                nxt[e1] = head[li]
                head[li] = e1
                e = enext
                continue
            found = False
            n = lens[c]
            for k in range(2, n):
                lk = lits[s + k]
                vk = val[lk if lk > 0 else -lk]
                vk = vk if lk > 0 else -vk
                if vk != -1:
                    lits[s + 1] = lk
                    lits[s + k] = fl
                    lj = 2 * lk if lk > 0 else -2 * lk + 1
                    nxt[e1] = head[lj]
                    head[lj] = e1
                    found = True
                    break
            if found:
                e = enext
                continue
            nxt[e1] = head[li]
            head[li] = e1
            if vo == -1:
                # conflict: re-attach the remaining entries
                e = enext
                while e != -1:
                    en2 = nxt[e]
                    nxt[e] = head[li]
                    head[li] = e
                    e = en2
                return True, tl
            val[other if other > 0 else -other] = 1 if other > 0 else -1
            trail[tl] = other
            tl += 1
            e = enext
    return False, tl


@njit(cache=False)
def topscan(c, lits, starts, lens, val, alive, head, nxt, trail, tl):
    s = starts[c]
    n = lens[c]
    nun = 0
    last = 0
    for i in range(n):
        l = lits[s + i]
        v = val[l if l > 0 else -l]
        v = v if l > 0 else -v
        if v == 1:
            return False, tl
        if v == 0:
            nun += 1
            last = l
    if nun == 0:
        return True, tl
    if nun == 1:
        start = tl
        val[last if last > 0 else -last] = 1 if last > 0 else -1
        trail[tl] = last
        tl += 1
        confl, tl = propagate(start, lits, starts, lens, val, alive, head, nxt, trail, tl)
        return confl, tl
    # >= 2 unassigned: make sure both watched positions are unassigned
    v0 = val[abs(lits[s])]
    v1 = val[abs(lits[s + 1])]
    if v0 != 0 or v1 != 0:
        # detach the clause's two entries (whichever ids they carry) from the two lists
        for slot in range(2):
            l = lits[s + slot]
            li = 2 * l if l > 0 else -2 * l + 1
            cur = head[li]
            prev = -1
            while cur != -1:
                if (cur >> 1) == c:
                    if prev == -1:
                        head[li] = nxt[cur]
                    else:
                        nxt[prev] = nxt[cur]
                    break
                prev = cur
                cur = nxt[cur]
        # move two unassigned literals to the front
        pos = 0
        for i in range(n):
            l = lits[s + i]
            if val[abs(l)] == 0:
                tmp = lits[s + pos]
                lits[s + pos] = l
                lits[s + i] = tmp
                pos += 1
                if pos == 2:
                    break
        for slot in range(2):
            l = lits[s + slot]
            li = 2 * l if l > 0 else -2 * l + 1
            e = 2 * c + slot
            nxt[e] = head[li]
            head[li] = e
    return False, tl


if __name__ == '__main__':
    print(check(sys.argv[1], sys.argv[2]))
