"""Minimal forward DRUP checker (reverse unit propagation), written for this project.

check(cnf_path, proof_path) -> dict(ok=bool, reason=str, lemmas=int, ...)
A proof is accepted iff every added lemma is RUP w.r.t. the current clause database
(original clauses + previously accepted lemmas, minus deleted ones) and the empty clause
(or a top-level conflict) is derived. Deleting clauses can only weaken the database and
every clause in it is implied by the CNF, so top-level assignments are kept on deletion.
Independent of the SAT solvers: it shares no code with PySAT.
"""
import sys, time


def read_cnf(path):
    clauses = []
    nv = 0
    cur = []
    with open(path) as f:
        for line in f:
            if not line or line[0] in 'cp%':
                if line.startswith('p cnf'):
                    nv = int(line.split()[2])
                continue
            for tok in line.split():
                x = int(tok)
                if x == 0:
                    clauses.append(cur)
                    cur = []
                else:
                    cur.append(x)
    return nv, clauses


class Checker:
    def __init__(self, nv):
        self.nv = nv
        self.val = [0] * (nv + 1)          # 0 unassigned, 1 true, -1 false (for the variable)
        self.watch = {}                    # literal -> list of clause ids watching it
        self.cls = []                      # clause literal lists
        self.alive = []
        self.index = {}                    # sorted tuple -> list of ids (for deletion)
        self.trail = []
        self.conflict = False

    def value(self, l):
        v = self.val[l if l > 0 else -l]
        return v if l > 0 else -v

    def assign(self, l):
        self.val[l if l > 0 else -l] = 1 if l > 0 else -1
        self.trail.append(l)

    def add_clause(self, lits):
        lits = list(dict.fromkeys(lits))
        cid = len(self.cls)
        self.cls.append(lits)
        self.alive.append(True)
        self.index.setdefault(tuple(sorted(lits)), []).append(cid)
        if len(lits) >= 2:
            self.watch.setdefault(lits[0], []).append(cid)
            self.watch.setdefault(lits[1], []).append(cid)
        return cid

    def propagate(self, start):
        """unit propagation from trail[start:]; returns True on conflict"""
        i = start
        cls, alive, watch, val = self.cls, self.alive, self.watch, self.val
        while i < len(self.trail):
            p = self.trail[i]
            i += 1
            falsel = -p
            wl = watch.get(falsel)
            if not wl:
                continue
            j = 0
            keep = []
            n = len(wl)
            while j < n:
                cid = wl[j]
                j += 1
                if not alive[cid]:
                    continue
                c = cls[cid]
                if c[0] == falsel:
                    c[0], c[1] = c[1], c[0]
                # c[1] is the false watched literal
                other = c[0]
                vo = val[other if other > 0 else -other]
                if (vo if other > 0 else -vo) == 1:
                    keep.append(cid)
                    continue
                found = False
                for k in range(2, len(c)):
                    lk = c[k]
                    vk = val[lk if lk > 0 else -lk]
                    if (vk if lk > 0 else -vk) != -1:
                        c[1], c[k] = c[k], c[1]
                        watch.setdefault(c[1], []).append(cid)
                        found = True
                        break
                if found:
                    continue
                keep.append(cid)
                if (vo if other > 0 else -vo) == -1:
                    keep.extend(x for x in wl[j:] if alive[x])
                    watch[falsel] = keep
                    return True
                self.assign(other)
            watch[falsel] = keep
        return False

    def top_unit_scan(self, cid):
        """after adding clause cid at top level: assign if unit, detect conflict"""
        c = self.cls[cid]
        unassigned = [l for l in c if self.value(l) == 0]
        if any(self.value(l) == 1 for l in c):
            return
        if not unassigned:
            self.conflict = True
            return
        if len(unassigned) == 1:
            start = len(self.trail)
            self.assign(unassigned[0])
            if self.propagate(start):
                self.conflict = True
        elif len(c) >= 2 and (self.value(c[0]) != 0 or self.value(c[1]) != 0):
            # >= 2 unassigned literals but a watch sits on a false literal: rebuild watches
            for w in (c[0], c[1]):
                wl = self.watch.get(w)
                if wl:
                    while cid in wl:
                        wl.remove(cid)
            una = [l for l in c if self.value(l) == 0]
            rest = [l for l in c if self.value(l) != 0]
            c[:] = una + rest
            self.watch.setdefault(c[0], []).append(cid)
            self.watch.setdefault(c[1], []).append(cid)

    def rup(self, lemma):
        if self.conflict:
            return True
        start = len(self.trail)
        conflict = False
        for l in lemma:
            v = self.value(l)
            if v == 1:
                conflict = True          # lemma satisfied at top level: trivially implied
                break
            if v == 0:
                self.assign(-l)
        if not conflict:
            conflict = self.propagate(start)
        for l in self.trail[start:]:
            self.val[l if l > 0 else -l] = 0
        del self.trail[start:]
        return conflict


def check(cnf_path, proof_path, progress=0):
    t0 = time.time()
    nv, clauses = read_cnf(cnf_path)
    ck = Checker(nv)
    # grow variable array if the proof introduces no new vars (DRUP never does)
    for c in clauses:
        if len(c) == 0:
            return {'ok': True, 'reason': 'empty clause in CNF'}
        cid = ck.add_clause(c)
    for cid in range(len(ck.cls)):
        ck.top_unit_scan(cid)
        if ck.conflict:
            break
    n_add = n_del = 0
    with open(proof_path) as f:
        for line in f:
            s = line.split()
            if not s:
                continue
            if s[-1] != '0':
                return {'ok': False, 'reason': 'unterminated proof line', 'lemmas': n_add}
            if s[0] == 'd':
                lits = tuple(sorted(int(x) for x in s[1:-1]))
                ids = ck.index.get(lits)
                if ids:
                    ck.alive[ids.pop()] = False
                    n_del += 1
                continue
            lemma = [int(x) for x in s[:-1]]
            if any(abs(l) > nv for l in lemma):
                return {'ok': False, 'reason': 'unknown variable in lemma', 'lemmas': n_add}
            if not ck.rup(lemma):
                return {'ok': False, 'reason': 'lemma %d is not RUP' % (n_add + 1), 'lemmas': n_add}
            n_add += 1
            if progress and n_add % progress == 0:
                print('  %d lemmas, %.0fs' % (n_add, time.time() - t0), flush=True)
            if len(lemma) == 0 or ck.conflict:
                return {'ok': True, 'reason': 'empty clause derived', 'lemmas': n_add,
                        'deletions': n_del, 'seconds': round(time.time() - t0, 1)}
            cid = ck.add_clause(lemma)
            ck.top_unit_scan(cid)
            if ck.conflict:
                return {'ok': True, 'reason': 'top-level conflict', 'lemmas': n_add,
                        'deletions': n_del, 'seconds': round(time.time() - t0, 1)}
    return {'ok': False, 'reason': 'proof ended without empty clause', 'lemmas': n_add}


if __name__ == '__main__':
    print(check(sys.argv[1], sys.argv[2], progress=50000))
