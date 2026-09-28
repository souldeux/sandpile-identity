#!/usr/bin/env bash
# Re-runs every machine check behind the proof of (U) (even grid). Needs Python 3 with numpy and
# z3-solver. Each z3 stage prints "checked 1500 (profile, target) pairs; failures: 0" on success.
set -e
cd "$(dirname "$0")"
export VFORM=ky            # vertical-step family V(y,x) <= 2(k - y)
echo "== induction step, every window profile, symbolic k >= 8 ==";  python check_invariants.py
echo "== hypotheses satisfiable in every window (no vacuous proofs) =="; VACUITY=1 python check_invariants.py
echo "== encoding matches real avalanches (concrete states substituted) =="; ENCODE_TEST=1 python check_invariants.py
echo "== E(d) in the diagonal windows ==";                          python recheck_minimal.py
