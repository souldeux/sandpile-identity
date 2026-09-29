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

**Pile-free form of (L) (2026-09-28, late).** Let u = L⁻¹e be the potential of the even identity
(u = 0 on the sink, e = L·u; u is the odometer of stabilizing e + e). Since D_m = L·W,
e = L·(W − a), so u = W − a. Along row k−1 the depth is min(j+1, m−j, k) and W(d) = 2kd − d² + d
has second difference exactly −2 at every cell of that row (including the centre, where
W(k) − W(k−1) = 2). Hence

> **(L) ⇔ −Δ_x u(k−1, j) ≥ 1 for every j**: the identity's potential is strictly concave along
> the row next to the midline.

Checked equivalent for k = 2..40; in fact −Δ_x u ∈ {1, 2} there.

The theorem itself has the same shape in potentials: **u_{2k+1} is u_{2k} with its middle row and
column duplicated into the cross** (checked k = 6, 10 by computing both potentials; this is just
the README's partial-proof construction V, seen from the potential side). Applying L to
the duplicated potential gives e_{2k} off the cross, 0 at the centre and −Δ_x u(k−1, j) on the
cross (the vertical second difference vanishes because the cross equals its neighbours). So the
whole theorem is: **1 ≤ −Δ_x u_{2k}(k−1, j) ≤ 3 along the row next to the midline**. The upper
bound is what (U) delivers (g stable); the lower bound is (L).

With δ_u = u(k−1,j) − u(k−2,j) (which is 0 or 1) and the mirror row, e(k−1, j) = −Δ_x u + δ_u, so (L) says a midline cell holds
more grains than its vertical potential step. The data show the geometry behind it: on the
midline row the grains are 2 inside the central square (δ_u = 1, bend 1) and mostly 3 outside it
(δ_u = 1, bend 2), with isolated 2s among the 3s and a few δ_u = 0 cells near the border. Any
start pile with the same identity gives the same u; for the border pile N·β (β = L·1, N large)
the odometer is N − u, and its midline row stays convex (second difference ≥ 0 with the sink at N)
at every round for m ≤ 32, but it only becomes ≥ 1 at the end.

(L) is not a round-by-round invariant (mid-avalanche Δ reaches −2), but this two-round one is,
and at the end it is exactly (L):

> **LA** Δ_t(j) + [T_t(k−1,j) − T_{t−1}(k−1,j)] ≥ −1: the midline row can bend more sharply than
> −1 only at a cell that toppled in the last round.

Supporting two-round facts, found from z3 counterexamples, all holding at every round for
k = 2..80 and all tight:

- **VA** T_{t−1}(k−2, j) ≤ T_t(k−1, j) + 1 (the row above, one round ago, is at most one topple
  ahead of the midline row now). **Proven inductive given VD.**
- **VD** 2·T(k−2, j) ≤ T(k−1, j−1) + T(k−1, j+1) + 4.

**The mechanism behind LA (from data).** On the midline row, with z = grains and δ = step into
the row, z_j = 2 + δ_j + Δ_j at every round (the cell below is the mirror). So LA ⇔ z + A ≥ δ + 1,
and LA carries to the next round unless the cell holds ≤ min(3, δ) grains and neither row
neighbour topples. In every simulated round (k ≤ 60) the tight states are exactly
(z, δ, A) = (1, 1, 1), and every one of them has a row neighbour with δ = 2 and ≥ 4 grains,
which topples next round and rescues it. Only nine (z, δ) pairs ever occur on the midline row:
(1,0), (2,0), (1,1), (2,1), (3,1), (4,1), (4,2), (5,2), (6,2). Linear facts extracted from this,
all holding at every round for k ≤ 70:

- **P1** δ = 2 ⇒ z ≥ 4: 3u − v − v_l − v_r ≤ 6
- **P2** z ≥ 1: 3v − u − v_l − v_r ≤ 1
- **P3** z ≤ 2 + 2δ: v_l + v_r − v − u ≤ 0
- **P5** a tight cell has a neighbour with δ = 2: 6v − 2v_l − 2v_r − u_l − u_r ≤ 3 (j ≤ k−3)
- **VA_y** (generalizes VA to every row) T_{t−1}(y−1, x) − T_t(y, x) ≤ 2(k − y) − 1: a vertical
  step is at its maximum only right after the cell above toppled. Tight on the midline row.

Also from recurrence alone: at the end VA gives δ ∈ {0, 1}, and a midline cell with 0 grains would
form a forbidden pair with its mirror, so (L) holds automatically wherever δ = 0.

`tools/even_check2.py` (two-round induction, even grid) proves every earlier family plus VA and
LA at the centre corner, and 436 goals in total. With P1–P5 added, LA has no counterexample in
any window (proven in some, solver timeouts in others), but the P-families and VD are not yet
inductive, and VA_y fails two cells from the diagonal. Each round of counterexamples has exposed
another true fact that is missing: the reachable states near the midline are a thin set that
linear inequalities describe poorly, and the rescue rule is itself a disjunction.

**Table invariants (2026-09-28, evening).** Replacing linear facts by exact tables of the (z, δ, A)
combinations seen in simulations (grains, step into the cell, last-round topples, all bounded
near the midline; horizontal steps are never needed) works for LA:

- With two small midline tables, TA = (δ_{j−1}, z_j, δ_j, A_j, δ_{j+1}) (37 interior tuples) and
  TC = (z_j, δ_j, A_j, A_up) (17 tuples), **LA is proven in every midline window**
  (`tools/table_check.py`, minutes of solver time).
- The tables themselves are not yet inductive: their next-round values depend on the rows above,
  and the counterexamples use steep vertical steps two or three rows up that real avalanches never
  have near the midline (measured: V(y, x) − 2(k − y) is 0 on the midline row but ≤ −1 one row up
  and ≤ −2 two rows up away from the diagonal; a class-indexed version of that envelope is true
  but not self-inductive either).
- `tools/table_cegar.py` automates the repair: a library of 680 table shapes over (z, δ, A) within
  one cell of anchors on the four rows nearest the midline, mined up to k = 34; each z3
  counterexample is blocked by a mined table at any anchor of its window. One iteration blocked all
  123 counterexamples (125 tables), but the next iteration took hours with the larger table set,
  so it was stopped. State is saved (`cegar_shapes.json`, `cegar_proven.json`, `lib_tabs.json`) and
  the script resumes; with the proof cache, later iterations only recheck failures.
- Localizing the hypotheses (tables assumed only within Chebyshev radius 2 of the window centre,
  `HYP_R=2`) made an iteration cheaper (97 min on 15 cores) but much weaker: 66 of 77 windows
  failed with 884 counterexamples, 180 of them excluded only by tables already in the set at
  anchors that were no longer assumed. LA itself had no counterexample. Back to full hypotheses;
  proofs cached under fewer hypotheses remain valid.
- With full hypotheses the resumed iteration (71 min) was just as bad: 66 windows failing, 891
  counterexamples, LA still never failing. Blocking added 543 tables (125 → 668) and left 348
  counterexamples that no library table excludes, almost all on rows 1–3 above the midline
  (classes (1..3, 2, 3)). **The band-table CEGAR is diverging, so it was stopped.** Reading: each
  row's table needs a model of the row above, the library only reaches row 3, and the proven linear
  bounds from (U) get looser, not tighter, with distance from the midline, so nothing closes the
  chain from above. A finite band invariant would need an exact far-field description (how the
  avalanche from the diagonal stacks arrives at the band), not more local patterns.

**Possible next approach: a finite pattern invariant.** Local midline patterns (grains, step and
recent topples on rows k−1 and k−2, three columns wide) appear to saturate: 376 distinct at
k = 10, 648 at 22, 705 at 40, 731 at 70. If the set is finite, it could serve as an exact,
non-linear invariant near the midline, combined with the linear families elsewhere. The open
issue is that row k−2 depends on row k−3, so the pattern region needs a model of its input
from above. LA and VD still fail along the midline row.
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
- **Static route to (L) (2026-09-28, late).** `tools/static_L.py` asks whether the final state
  alone forces seams ≥ 1: final odometer on a midline window at a generic arm position, with
  stability, the proven (U) bounds, mirror symmetry and recurrence (every forbidden subset of the
  window blocked lazily), optionally plus δ ≤ 1 and s ≥ 1 already established at the columns
  nearer the border (induction along the row). z3 finds windows with seam 0 in every variant
  (R = 3, C = 4), and δ ≤ 1 is not forced either. This matches the rectangle experiment: tall
  rectangles have genuine identities with seam 0, so local facts about one final state cannot
  suffice; the size information has to come from the avalanche dynamics.
- **Far-field probe (2026-09-28, late).** Can the input to a midline band be described exactly?
  `tools/farfield_probe.py` compares the square's LBR avalanche with a long rectangle's (same width,
  height 2k + 2t, identical start pile on rows 0..k−1; Le Borgne–Rossin showed the long rectangle's
  avalanche never reaches its middle). They differ on every row from round 3 on (the difference
  moves up one row per round), and at the end by up to 1084 at k = 64 (≈ k²/4), falling off
  roughly linearly with distance from the midline. The difference field is smooth at large scale
  but its steps jitter by ±1–2, so it is not an explicit function either. The midline influences
  the whole quarter almost at once; there is no bounded band with known input. This closes the
  band-invariant route.
