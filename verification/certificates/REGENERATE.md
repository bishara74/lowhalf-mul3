# Regenerate and check the low-half multiplier LRAT proofs

The compact archive `mc3mod8_certificate_small.tar.zst` supplies the six CNF
and trimmed text LRAT pairs `k0` through `k4` and `cover5`. It also includes
the encoder, `cubes.txt`, `manifest.tsv`, `generation_log.tsv` and
`check_all.log`. The manifest and logs record 657 jobs. The 651 `k5_L_M`
proofs and their CNFs are absent from the archive. The five-gate exclusion
requires the coverage proof and a checked UNSAT proof for each cube. See
[CERTIFICATE_INVENTORY.md](CERTIFICATE_INVENTORY.md) for the separate earlier
lambda-case searches and the availability of their files.

## Setup

Run the following Bash blocks in sequence from the Lean repository root on
x86-64 Linux with Python 3, Git, GCC, GNU Make, GNU tar, coreutils and the
`zstd` CLI. The commands keep all generated files in a fresh directory.

```bash
set -euo pipefail
archive="$PWD/verification/certificates/mc3mod8_certificate_small.tar.zst"
printf '%s  %s\n' \
  72edad8e2072270b13a5fa659c20f80e1eb49cbf6847fbabf8a964ce164f2edd \
  "$archive" | sha256sum -c -
work=$(mktemp -d)
tar --zstd -xf "$archive" -C "$work"
cd "$work"

fetch() {
  local dir=$1 url=$2 rev=$3
  git init -q "$dir"
  git -C "$dir" fetch --depth=1 "$url" "$rev"
  git -C "$dir" checkout -q --detach FETCH_HEAD
}
fetch cadical https://github.com/arminbiere/cadical.git \
  c60730422e758ef1cebe7aeddf2dda31c996bf04
fetch lrat-trim https://github.com/arminbiere/lrat-trim.git \
  b30f400f4ee5c32b77ee566a7c006081b521534f
fetch cake_lpr https://github.com/tanyongkiam/cake_lpr.git \
  a36874a8b750b43fe4b385b8ddbf5b033e46a3fa
(cd cadical && ./configure && make -j2)
(cd lrat-trim && ./configure && make)
make -C cake_lpr

solver="$work/cadical/build/cadical"
trimmer="$work/lrat-trim/lrat-trim"
cake="$work/cake_lpr/cake_lpr"
"$solver" --version  # 3.0.1
cd "$work/mc3mod8_certificate"
python3 audit_structure.py
```

`mc_encode.py` generates the base, cube and coverage CNFs. Each cube appends
12 units to `base 5`. The coverage CNF uses 85 gate-zero clauses and one
blocking clause per cube. `original_mcS2.py` is the earlier encoder supplied
for reference. The archive supplies `cubes.txt` directly. This enumeration
recovers the same set. Use the archived order for the coverage CNF hash.

```bash
python3 - <<'PY'
from pathlib import Path

archived = [tuple(map(int, row.split()))
            for row in Path("cubes.txt").read_text().splitlines()]
generated = {(left, right)
             for left in range(1, 64) for right in range(1, 64)
             if (left & -left) < (right & -right)
             and not (left & (right & -right))}
assert len(archived) == 651 == len(generated)
assert set(archived) == generated
PY
```

## Replay the six archived proofs

The archived `check_all.sh` expects all 657 proofs. Run the following against
the compact archive. Expect six `s VERIFIED UNSAT` verdicts. The structure
audit reports `A1 ok`, `A2 ok` and `A3 ok` for the CNF construction and
manifest coverage.

```bash
replay="$work/archived-replay"
mkdir -p "$replay"

manifest_hash() {
  awk -F '\t' -v name="$1" -v col="$2" '$1 == name {print $col}' manifest.tsv
}
check_hash() {
  printf '%s  %s\n' "$1" "$2" | sha256sum -c -
}
verify_lrat() {
  "$cake" --CML_HEAP_SIZE=2500 --CML_STACK_SIZE=500 "$1" "$2" |
    grep -Fx 's VERIFIED UNSAT'
}

for name in k0 k1 k2 k3 k4 cover5; do
  if [[ "$name" = cover5 ]]; then
    args=(cover 5 cubes.txt)
  else
    args=(base "${name#k}")
  fi
  cnf="$replay/$name.cnf"
  proof="$replay/$name.lrat"
  python3 mc_encode.py "${args[@]}" > "$cnf"
  zstd -dc "cnf/$name.cnf.zst" | cmp "$cnf" -
  zstd -dc "proofs/$name.lrat.zst" > "$proof"
  check_hash "$(manifest_hash "$name" 3)" "$cnf"
  check_hash "$(manifest_hash "$name" 4)" "$proof"
  verify_lrat "$cnf" "$proof"
done
```

## Regenerate and check all 657 jobs

This reproduces the pipeline from `run_job.sh` with working-directory paths
and an enforced checker verdict. Allow several hours and scratch space. The
historical trimmed proofs total about 14.3 GB before compression. To
regenerate only the six archived cases, stop before the `while` loop.

```bash
out="$work/regenerated"
mkdir -p "$out"
printf 'job\tcnf_sha256\tproof_sha256\tverdict\n' > "$out/results.tsv"

regenerate() {
  local name=$1 cnf raw proof rc
  shift
  cnf="$out/$name.cnf"
  raw="$out/$name.raw.lrat"
  proof="$out/$name.lrat"
  python3 mc_encode.py "$@" > "$cnf"
  check_hash "$(manifest_hash "$name" 3)" "$cnf"

  rc=0
  env -i PATH="$PATH" LC_ALL=C "$solver" -q --seed=0 --lrat=true --binary=false \
    "$cnf" "$raw" > "$out/$name.solver.log" || rc=$?
  if [[ "$rc" != 20 ]]; then
    printf '%s solver exit %s, expected 20\n' "$name" "$rc" >&2
    return 1
  fi
  grep -Fx 's UNSATISFIABLE' "$out/$name.solver.log"

  rc=0
  "$trimmer" -q --ascii "$cnf" "$raw" "$proof" || rc=$?
  if [[ "$rc" != 20 ]]; then
    printf '%s trimmer exit %s, expected 20\n' "$name" "$rc" >&2
    return 1
  fi
  verify_lrat "$cnf" "$proof"
  printf '%s\t%s\t%s\t%s\n' "$name" "$(sha256sum < "$cnf" | cut -d' ' -f1)" \
    "$(sha256sum < "$proof" | cut -d' ' -f1)" 's VERIFIED UNSAT' >> "$out/results.tsv"
  zstd -q --force -9 "$proof" -o "$proof.zst"
  rm "$raw" "$proof"
}

for k in 0 1 2 3 4; do
  regenerate "k$k" base "$k"
done
regenerate cover5 cover 5 cubes.txt

while read -r left right; do
  regenerate "k5_${left}_${right}" cube 5 "$left" "$right"
done < cubes.txt

test "$(awk -F '\t' '$4 == "s VERIFIED UNSAT" {print $1}' "$out/results.tsv" |
  sort -u | wc -l)" -eq 657
```

Expect one CNF, solver log and compressed trimmed text LRAT per job, and
657 checked rows in `results.tsv`. The proof digest is computed on the
uncompressed trimmed LRAT. To recheck a generated proof later, decompress
its `.lrat.zst` and pass the CNF and the proof to `verify_lrat`.

The encoder and its iteration order are deterministic. The original
`run_job.sh` uses single-process CaDiCaL 3.0.1 with
`--lrat=true --binary=false`. It relies on the pinned source's default seed
of zero. The original environment is unrecorded. The replay above makes
the seed explicit with `--seed=0` and clears `CADICAL_*` environment
overrides. Proof bytes can depend on the binary build and options. The
historical CNF hashes must match. A regenerated proof is accepted when
`cake_lpr` verifies it against its matching CNF.
