#!/usr/bin/env bash
# Print the axioms the main theorems depend on and fail on anything outside the
# allowed set: Lean's three classical axioms plus the uninterpreted platform
# functions that the Sail RISC-V extraction declares as `axiom`
# (LeanRV64D/RiscvExtras.lean: floating point, reservations, ...).
set -euo pipefail
cd "$(dirname "$0")/.."
f=$(mktemp --suffix=.lean -p .)
trap 'rm -f "$f"' EXIT
cat > "$f" <<'LEAN'
import FlapjackRiscvCheck
#print axioms FlapjackRiscvCheck.exec_sim
#print axioms FlapjackRiscvCheck.sail_decode_sim
#print axioms FlapjackRiscvCheck.step_sim
#print axioms FlapjackRiscvCheck.run_sim
#print axioms FlapjackRiscvCheck.Witness.run_sim_nonvacuous
LEAN
lake lean "$f" > "$f.out" 2>&1 || true
python3 - "$f.out" <<'PY'
import re, sys, glob
out = open(sys.argv[1]).read()
sail = set()
for p in glob.glob(".lake/packages/Lean_RV64D/LeanRV64D/RiscvExtras*.lean"):
    sail |= set(re.findall(r"^axiom (\S+)", open(p).read(), re.M))
allowed = {"propext", "Classical.choice", "Quot.sound"} | sail
ok = True
for name, body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out):
    used = {a.strip() for a in body.replace("\n", " ").split(",") if a.strip()}
    extra = used - allowed
    print(f"{name}: {len(used & {'propext','Classical.choice','Quot.sound'})} core + "
          f"{len(used & sail)} Sail platform axioms" + (f"; UNEXPECTED: {sorted(extra)}" if extra else ""))
    ok &= not extra
if "error" in out and "depends on axioms" not in out:
    print(out[-2000:]); ok = False
print("OK: only Lean's classical axioms and Sail's declared platform functions" if ok else "FAILED")
sys.exit(0 if ok else 1)
PY
rm -f "$f.out"
