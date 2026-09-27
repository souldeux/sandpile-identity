# Odd/even identity theorem: proof notes

**Claim.** For every k ≥ 1, the identity of the (2k+1)-grid with its middle row and column removed
equals the identity of the 2k-grid. Verified for every k ≤ 128.

Notation: m = 2k, n = 2k+1. L is the reduced Laplacian (4 on the diagonal, −1 per neighbour; the sink
is outside the grid). "Stable" means every value ≤ 3. v_j = (k−1, j) is the quarter cell beside
the cross, and σ_j = (k, j) is the cross cell below it (arm cells j = 0..k−1; centre (k, k)).

## Proven

1. **Le Borgne–Rossin start pile.** With depth d = distance to the border + 1 and
   W = 2kd − d² + d, the pile D_m = L_m W is 2 off the corner diagonals and 4(k − d_cell + 1) on
   them. It differs from the empty pile only by topplings and is ≥ 2, so stab(D_m) = e_m.
2. **Odd start pile.** c_n = (D_m in the four quarters, 2 on the cross, 0 at the centre)
   = L_n ext(W), where ext copies each row-(k−1) value onto the cross. c_n dominates
   "2 everywhere, 0 at the centre", which has no forbidden subconfiguration (the extreme cells of
   any finite set have ≤ 2 neighbours inside it), so stab(c_n) = e_n.
3. **Reduction (least action principle, both directions).** Let a be the odometer of D_m and b
   the odometer of c_n.
   - (U) If the second differences of a along row k−1 are ≤ 1, then g := c_n − L_n ext(a) is
     stable (quarters e_m, arms 2 + Δ_x a, centre 0), so b ≤ ext(a).
   - (M) If b(σ_j) ≥ b(v_j) for all j, then D_m − L_m b|quarters equals e_n minus nonnegative
     terms on the cells beside the cross, so it is stable, so b|quarters ≥ a.
   - Together: b = ext(a), so e_n = g and the claim holds. Conversely the claim implies (U) and
     (M). **Claim ⇔ (U) ∧ (M).** No recurrence argument is needed on this route.
4. **(U) from monotonicity.** On row k−1 (j ≤ k−2) the step δ_j = u(k−1,j) − u(k−2,j) equals
   a(k−2,j) − a(k−1,j) because W agrees on those rows. So (U) follows from
   (a) a(y−1, x) ≥ a(y, x) below the diagonal. The corner cell j = k−1 has
   δ = 2 − E(k−1) with E as below, so it follows from E(k−1) ≤ 1.
5. **Inductive step for (a), parallel rounds** T_{t+1}(p) = ⌊(D(p) + Σ_{q∼p} T_t(q)) / 4⌋:
   for cells with x ≤ y−2 the Le Borgne–Rossin neighbour matching works (four pairs, the midline
   pair being an equality by mirror symmetry). For x = y−1 it needs the diagonal inequality
   (b) E(y−1) + E(y) ≤ D(y−1, y−1) − 2, where E(d) := T(d,d) − T(d,d−1).
   (b) follows from **E(d) ≤ 2(k − d) − 1**.
6. **(M) from a lagged invariant.** T_{t+1}(σ_j) ≥ T_t(v_j) for all t implies (M). One induction
   step reduces it to (S): T_{t−1}(v_{j−1}) + T_{t−1}(v_{j+1}) + 2 ≥ 2 T_t(v_j). The centre obeys
   T_{t+1}(centre) = T_t(σ_{k−1}) exactly; the j = k−1 case needs that lag worked in (not yet done).

## Verified numerically at every round, not yet proven

| Statement | Checked on | Tightness |
|---|---|---|
| (a) monotone toward the midline below the diagonal | m = 16, 32, 64, 96 | — |
| (b) diagonal inequality | m = 16, 32, 64, 96 | min slack 3 |
| E(d) ≤ 2(k − d) − 1 | every m ≡ 0 mod 4, 8..100 | min slack 0 (tight) |
| lagged (M) and (S) | n = 17, 33, 49, 65, 97 | — |
| final (U): second differences of a on row k−1 ∈ {−1, 0} | every even m, 4..128 | — |

## Where it is stuck

- Proving E(d) ≤ 2(k − d) − 1 inductively reduces, after the floor algebra, to
  (a − q) + (a − r) ≤ 2(k − d) − 4 with a = T(d,d−1), q = T(d+1,d−1), r = T(d,d−2):
  a bound on the vertical plus horizontal steps beside the diagonal. Those need their own
  inductive bounds; whether the chain closes is unknown.
- (S) needs a lower bound on the row-(k−1) second differences at intermediate rounds, but those
  reach −2 mid-avalanche (only the final state has {−1, 0}), so (S) must get its slack from the
  lag between σ and v. No closed invariant found yet.
- Not true on rectangles taller than ≈1.4× their width, so any proof must use the square shape;
  in this framework that enters through the diagonal stacks meeting at the centre.
