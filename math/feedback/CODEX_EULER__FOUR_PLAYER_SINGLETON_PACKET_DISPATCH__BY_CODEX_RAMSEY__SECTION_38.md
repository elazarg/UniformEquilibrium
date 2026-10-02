# Independent review of Section 38

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS in the stated finite-connector scope.**

I checked Theorem 38.1 against the declarations in
`StrictCovectorDynamicTail.lean`, the normalized singleton-packet identities,
and the normal-core blocker theorem.

## Exact checks

- If `T=seam.tightOwnerFinset` is proper,
  `eventually_active_mem_tightOwnerFinset` says exactly that every sufficiently
  late coordinate whose root law is not pure Continue lies in `T`.  Thus the
  late positive-hazard support is contained in one fixed proper set.  This is
  an actual-root support statement, not a reduced ambient game.
- If `T=univ`, tightness gives
  `seam.limit.value i=r({i})_i` for every coordinate.  The strict-covector
  theorem supplies one common `p,m`, with `m>0`, normalized square norm, and
  `m<=p.(s-r({a}))` for every owner.
- Multiplication by the packet masses and summation is legitimate:
  the masses are nonnegative and sum to one.  It yields exactly

  ```text
  m <= p.(s-u) = sum_i (-p_i)e_i.
  ```

  On four coordinates at least one summand is at least `m/4`; no positivity of
  the other summands is needed for that pigeonhole step.
- Packet feasibility and full pinning give `e_i>=0`.  Hence
  `m/4<=(-p_i)e_i` forces `p_i<0` and `e_i>0`.  The separator normalization
  implies `|p_i|<=1`, so `m/4<=e_i`.
- The identity

  ```text
  e_i=sum_a packet.mass(a)*normalizedSoloMatrix reward i a
  ```

  is exact.  The diagonal term is zero and full support gives
  `packet.mass(i)>0`; therefore the remaining weights sum to strictly less
  than one.  Since `e_i>0`, some `j!=i` in fact has matrix entry strictly
  larger than `e_i`; the stated weak bound `e_i<=M(i,j)` is safe.
- Full normal core supplies `k!=i` with `M(i,k)<=0`.  The positive sign at
  `j` makes `j!=k`, so the three labels are pairwise distinct.

## Scope

The result is a genuine connector between independently selected packet and
dynamic-tail data.  It does not identify a nonsingleton collision row, give an
ambient lower-player strategy in the proper-face arm, or supply an
unrestricted-behavior compiler.  The stated nonclaims are therefore exact.
