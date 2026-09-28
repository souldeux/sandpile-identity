# Odd/even identity theorem: proof notes

**Claim.** For every k ≥ 1, the identity of the (2k+1)-grid with its middle row and column removed
equals the identity of the 2k-grid. Verified directly for every k ≤ 128.

**Status (2026-09-28).** The claim is equivalent to two one-sided statements, (U) and (M).
**(U) is proven for every k** (computer-assisted: an inductive invariant verified symbolically
by z3 for all k ≥ 8, plus direct computation for k < 8). Given (U), the rest reduces to an
even-grid statement **(L)** (every seam value ≥ 1), which follows from one two-round invariant,
**LA**. LA holds on all data but is **not yet proven**; see "What remains".

Notation: m = 2k, n = 2k+1. L is the reduced Laplacian (4 on the diagonal, −1 per neighbour; the sink
is outside the grid). "Stable" means every value ≤ 3. v_j = (k−1, j) is the quarter cell beside
the cross, and σ_j = (k, j) is the cross cell below it (arm cells j = 0..k−1; centre (k, k)).

## The reduction (proven by hand)

1. **Le Borgne–Rossin start pile.** With depth d = distance to the border + 1 and
   W = 2kd − d² + d, the pile D_m = L_m W is 2 off the corner diagonals and 4(k − d) on the
   diagonal cell (d, d). It differs from the empty pile only by topplings and is ≥ 2, so
   stab(D_m) = e_m.
2. **Odd start pile.** c_n = (D_m in the four quarters, 2 on the cross, 0 at the centre)
   = L_n ext(W), where ext copies each row-(k−1) value onto the cross (checked at the arm ends and
   the centre too). c_n dominates "2 everywhere, 0 at the centre", which has no forbidden
   subconfiguration (the extreme cells of any finite set have ≤ 2 neighbours inside it), so
   stab(c_n) = e_n.
3. **Least action principle, both directions.** Let a be the odometer of D_m and b of c_n.
   - (U) If the second differences of a along row k−1 are ≤ 1, then g := c_n − L_n ext(a) is
     stable (quarters e_m, arms 2 + Δ_x a, centre 0), so b ≤ ext(a).
   - (M) If b(σ_j) ≥ b(v_j) for all j, then D_m − L_m b|quarters is e_n minus nonnegative terms on
     the cells beside the cross, so it is stable, so b|quarters ≥ a.
   - Together b = ext(a), so e_n = g: the claim. Conversely the claim implies (U) and (M).
4. **(U) from monotonicity.** On row k−1 (j ≤ k−2), u(k−1,j) − u(k−2,j) = a(k−2,j) − a(k−1,j)
   because W agrees on those rows, and s = e − δ ≤ 3 needs δ ≥ 0. At j = k−1, δ = 2 − E(k−1)
   with E(d) = a(d,d) − a(d,d−1). So (U) follows from **a(y−1, x) ≥ a(y, x) below the diagonal**
   and **E(k−1) ≤ 1**.

## Proof of (U): an inductive invariant for the avalanche

Parallel rounds from T = 0: T′(p) = ⌊(D(p) + Σ_{q∼p} T(q)) / 4⌋. They increase to the odometer a.
On the triangle 0 ≤ x < y ≤ k−1 (the rest follows by symmetry), with T(y, −1) = 0:

| Family | Statement |
|---|---|
| H0 | T(y, x+1) − T(y, x) ≥ 0 |
| H1 | T(y, x+1) − T(y, x) ≤ 2(k − x) − 3, for −1 ≤ x ≤ y−1 (so T(y,0) ≤ 2k−1, and E(d) ≤ 2(k−d)−1) |
| V0 | T(y−1, x) − T(y, x) ≥ 0 |
| V1′ | T(y−1, x) − T(y, x) ≤ 2(k − y) |
| C≥0 | every cell holds ≥ 0 grains: D + Σ_{nbrs} T − 4T ≥ 0 |

- **Base.** All hold at T = 0.
- **C≥0 is inductive** by monotonicity: it says T ≤ F(T) for the monotone round map F.
- **The others** are inductive by `tools/check_invariants.py` (with VFORM=ky): for each target
  family and each of 1,500 window profiles (distance of the cell to the top, left edge, diagonal
  and midline, each either exact or "≥ n"), z3 finds no integer state satisfying every family
  instance inside the window whose next round violates the target. k is symbolic (k ≥ 8), so each
  UNSAT covers every grid. The floor is encoded exactly (4n ≤ S ≤ 4n + 3, n integer).
- **Sanity checks, all passing:** the hypotheses are satisfiable in every window (VACUITY=1), and
  real avalanche states from simulations satisfy every window constraint and goal at many rounds
  (ENCODE_TEST=1). The families also hold at every round for every even m from 4 to 140.
- **Conclusion.** At the odometer, V0 gives the monotonicity and H1 at the diagonal gives
  E(k−1) ≤ 1, so (U) holds for all k ≥ 8. Smaller k are covered by the direct verification.

To re-run everything: `tools/prove_U.sh`.

**How V1′ was found.** The first vertical bound, 2k − x − y − 1, holds but is not inductive near
the diagonal. Measuring its slack showed it is loose by exactly 1 per step away from the diagonal,
which collapses to 2(k − y). Earlier attempts (Houdini over thousands of mined templates, and a
core-guided closure) kept rebuilding pieces of this bound from diagonal-drop couplings.

## What remains: (L), an even-grid statement (replaces (M))

With (U) proven, (M) is not needed. (U) makes g stable, and g is recurrent as soon as every seam
value s(j) = 2 + Δa(j) is ≥ 1 (the forbidden-subconfiguration argument above). So the theorem
follows from

> **(L)** at the end of the even-grid avalanche, Δa(j) = a(k−1,j−1) − 2a(k−1,j) + a(k−1,j+1) ≥ −1
> for 0 ≤ j ≤ k−1 (a(k−1,−1) = 0, a(k−1,k) = a(k−1,k−1)).

(L) is not a round-by-round invariant (mid-avalanche Δ reaches −2), but this two-round one is,
and at the end it is exactly (L):

> **LA** Δ_t(j) + [T_t(k−1,j) − T_{t−1}(k−1,j)] ≥ −1: the midline row can bend more sharply than
> −1 only at a cell that toppled in the last round.

Supporting two-round facts, found from z3 counterexamples, all holding at every round for
k = 2..80 and all tight:

- **VA** T_{t−1}(k−2, j) ≤ T_t(k−1, j) + 1 (the row above, one round ago, is at most one topple
  ahead of the midline row now). **Proven inductive given VD.**
- **VD** 2·T(k−2, j) ≤ T(k−1, j−1) + T(k−1, j+1) + 4.

`tools/even_check2.py` (two-round induction, even grid) proves every earlier family plus VA and
LA at the centre corner, and 436 goals in total. LA and VD still fail along the midline row.
Their counterexamples are frozen states: a bend of −2 on the midline row with every nearby cell
holding ≤ 3 grains, so the bend would survive to the end. Real avalanches never do this, but no
single linear fact found so far rules it out. A core-guided closure over ~6,000 mined midline facts
(`tools/mid_closure.py`) found no genuine counterexample to LA or VD, but stalled on solver
timeouts once 20+ supporting facts were in play.

## (M): superseded by (L), kept for the record

Odd-grid avalanche from c_n. At the end, (M) follows from **M\***:
T(σ_{j−1}) + T(σ_{j+1}) + 2 ≥ 2 T(v_j), because the cross update then gives b(σ_j) ≥ b(v_j).
Families checked at every round for every odd n from 5 to 141: the quarter families above
(V1′ included), C0 σ_j ≤ v_j, C1 v_j − σ_j ≤ 1, M\*, centre ≤ σ_{k−1}, and C≥0.
What is established so far (`tools/odd_check2.py`, a **two-round** induction: families at rounds
t−1 and t plus the exact parallel step between them imply the families at t+1; base rounds 0 and 1
checked by hand, since round 1 is explicit: diagonal cell (d, d) has k − d topples, all else 0):

- 548 family goals are proven across the 135 odd-grid window profiles, including **M\* in every
  cross window** and CU2 below.
- New families found by measuring slack, both holding at every round for k up to 80 on both grids:
  **H2: H(y, x) ≤ 2k − x − y − 2** (equal to k − x − 1 on the midline row; the horizontal
  counterpart of V1′) and **CU2: T(k−2, x) − σ_x ≤ 2** (the drop from two rows up down to the
  cross; on the even grid this is V1′ at the midline).
- The partner bound Vd is restricted to d ≤ k − 2 on the odd grid (at d = k − 1 the cell below the
  diagonal is a cross cell, covered by C1).

Still failing, all next to the cross: C0 (σ_x ≤ v_x) in most cross windows, V1′ in the row just
above the cross, and H2 in two windows. The counterexamples are avalanche fronts that are far
steeper along the row above the cross than real ones (steps of about k − x near the border,
where real steps are about k/2). The linear step bounds are tight next to the diagonal but loose
near the border, and the cross region needs that gap closed. Two approaches tried and shelved:
Houdini over mined templates (too slow with 135 windows) and a parallel core-guided closure
(`tools/odd_closure.py`; it banned the targets on solver timeouts, and C0 has a genuine
counterexample from the mined pool alone).

## Dead ends worth remembering

- Round-by-round, row-(k−1) second differences reach ±2 mid-avalanche, so invariants about the
  final shape alone don't induct.
- The rule fails on rectangles taller than ≈1.4× their width, so any proof must use the square.
- Houdini with timeouts silently drops true facts; the fix was to drop only on real
  counterexamples, or to follow unsat cores.
