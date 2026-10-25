# Independent review: the signed Fin4 table

Reviewer: CODEX_COLLAR_ADVERSARY. **Mathematical verdict: PASS.**
Internal stationary and exact finite-calendar exclusions; no UE, counterexample,
export, or Lean claim.

Complete reviewed
[note](../notes/CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_TABLE.md):
SHA256 `1f3815857c0df1aab93a929234e15663955f53e2293bcde0589f930c3d0f0584`.
Complete reviewed
[checker](../experiments/CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_STATIONARY_CHECK.py):
SHA256 `0c3dd850b01c1e3fe2caf7ca5b47ea07df492ea2f5943f5a691d025659ab3431`.
I read the whole proof and implementation without consulting another review.

## Mathematical scope and table

The original own-singleton-one game has strictly positive observer-margin
capacities for all four pivots, but a strictly positive terminal regret floor
over every fixed stationary hazard vector. Complete behavioral deviations,
including Never, are included. It also has no Nash root with a sure quitter
against any actual continuation caps, hence no absorbing exact finite-calendar
Nash profile. Unrestricted nonstationary approximate-equilibrium existence
remains open; no approximate finite-calendar exclusion is asserted.

I independently parsed all sixty rational rewards from the printed table and
compared them with the checker. All agree. The singleton matrix is exactly
the reference matrix printed in the existing diffuse-flow exports. Independent
exact computation verifies determinant25, the positive inverse pivot column,
and all six size-two and four size-three principal determinants. The R0
argument is complete: every support of size at least two has an invertible
principal matrix, and a singleton support violates a negative outsider entry.

I recomputed all A and C rows and evaluated every possible endpoint or pairwise
intersection of their affine lines. The four maxima and maximizing arguments
are exactly those printed: `1,1/5,3/29,1/7`. The three specified negative pair
joining gaps also follow directly from the raw rewards. Row shifts cancel in
these differences, without shifting live play or AllNever.

## Full-response stationary adapter

With at least two positive stationary hazards, every deviator has a proper
opponent. Every original response therefore equals one plus its native value.
Against stationary opponents, a deadline offer is

    Never + H^t (Quit0 - Never).

The complete cap is the maximum of these two endpoints. For an interior own
hazard the prescribed value is a strict convex combination of the endpoints;
the boundary cases select the appropriate one. This gives precisely the
equality and weak-sign conditions on `(1-H)Q-P` used by the checker.

The four solo cases are valid independent exclusions: the selected observer
has respective Quit0 gains `1+q0, 2, 1, 1+3q3` over its prescribed Never.
Each faces a proper opponent, so these comparisons retain the original row
shift. AllNever separately has an original profitable singleton deviation.
No undefined Never quotient or discontinuous own-cap substitution is used.

## Polynomial construction and exact finite certificate

I reconstructed all four Q, P and H polynomials directly from the printed
table using independent symbolic algebra. Every coefficient of all four
resulting gains agrees with the checker's sparse polynomials. Their coordinate
degrees are at most two, as required by its tensor Bernstein representation.

I inspected each certificate step:

* The 80 nonzero fixed-zero/fixed-one/interior patterns exhaust the relevant
  hazard vectors. Pure cases check scalar signs exactly. The four solo
  interiors have a negative passive entry and a nonnegative joining reward,
  which gives the strict gain required throughout their open interval.
* Substituting fixed coordinates preserves the printed polynomial. Interior
  rows require equality; other rows retain their correct weak signs. Adding
  an inverse-principal-matrix combination of equality rows is always valid,
  including patterns with a sure coordinate.
* The power-to-Bernstein formula is the tensor product of the degree-two
  monomial conversion. Its coefficients bound the polynomial by the
  nonnegative Bernstein partition of unity. A common positive denominator
  is removed exactly; no numerical approximation occurs.
* I independently verified both printed dyadic de Casteljau identities as
  symbolic polynomials. Every descendant coefficient is scaled by a positive
  common factor. The two closed children cover the whole parent interval.
* A box is discarded only by a strict inconsistent sign interval or the
  separately justified origin exclusion. Depth/node limits raise failure;
  they never certify an unresolved box.

For the origin exclusion, the code checks zero constants and linear part
`-Gamma_SS q` before forming the remainder bound. On a unit cube with
`t=max q`, every monomial of total degree at least two is bounded by `t^2`.
Thus `t<=K t^2` excludes every nonzero point with `t<1/K`. The integer box
test is exactly the condition that every coordinate upper endpoint is at
most `2^-E`, chosen strictly below `1/K`. Excluding the zero point along with
that cube causes no loss: the original pattern requires a nonzero profile,
and the original AllNever profile was handled separately.

Independent recomputation gives full-support `K=159656/25`; `2^-13<1/K`.
The checker reproduced `898` total nodes and `213` for the full interior.
Its output was `EXACT RATIONAL PASS: all 80 nonzero supports excluded; 898 nodes`.

## Sure roots over arbitrary actual continuations

I independently enumerated the passive native values and verified the floor
`(-12,-8,-10,-12)`. Original Never payoff minus one is an expectation of these
passive native values and `-1` on AllNever. Thus the actual translated full
cap is at least the claimed floor, even for improper or nonoptimal tails.

The original root gap is exactly `Q-P-H(B-1)`. With a sure owner p, every
other row has `H_i=0`. Lowering the continuation cap therefore changes only
the sure owner's gap, increasing it and preserving its required nonnegative
sign. With multiple sure owners nothing changes. This justifies the necessary
fixed-floor polynomial test without incorrectly applying monotonicity to an
inactive player's opposite inequality.

I reconstructed all four fixed-floor root polynomials independently from the
printed table and verified their equality with ROOT. They are multiaffine,
so the degree-two Bernstein machinery remains valid. Its 65 tested patterns
are exactly those containing a fixed sure coordinate. No solo shortcut or
origin pruning is invoked in this mode. Exact execution reproduced the second
line: `EXACT RATIONAL PASS: all 65 sure-root patterns excluded; 325 nodes`.

An absorbing finite-calendar profile has a first reached sure root. Exact
full-response Nash passes to every reached conditional tail. At that root,
the sure owner's Continue deviation uses actual opponent continuation laws;
its own irrelevant off-path continuation can be completed arbitrarily. The
remaining root rows have zero continuation coefficient. Hence the proven
cap floor applies even to off-path punishments, giving the contradiction.
In fact the argument only requires one bounded proper prescribed clock;
the other laws may have unbounded off-path support. This exact conclusion
supplies no regret floor for approximate finite-calendar profiles.

## Positive regret floor and semantic limits

The compactness argument is valid. At a limit with at least two active owners,
all opponent absorption denominators remain positive, so endpoint offers and
prescribed values are continuous. Vanishing regret would give an excluded
exact stationary Nash profile. At a solo limit, the corresponding observer's
strict positive gap persists; continuity of the sole owner's Never cap is
unnecessary.

At a zero-hazard limit, normalize by total hazard. The first-order absorption
numerator gives original value `1+Gamma alpha`, while Quit0 tends to one.
Thus `Gamma alpha>=0`. For `alpha_i<1`, the Never denominator remains
proportional to `1-alpha_i`, yielding complementarity. For `alpha_i=1`, the
zero diagonal gives it directly. The normalized nonzero alpha then violates
R0. These cases exhaust the compact hazard cube and prove a positive floor.
Fixed profitable terminal deviations persist at sufficiently long finite
horizons, so stationary profiles cannot provide arbitrarily accurate UE.

I statically inspected both cited Lean declarations in their named files:
the conjecture is a proposition definition; the terminal-all-errors equivalence
quantifies unrestricted behavioral profiles. Neither was used to strengthen
this stationary result, and no Lean build was run. Documentation and whitespace
checks passed. No mathematical objection remains at the reviewed hashes.
