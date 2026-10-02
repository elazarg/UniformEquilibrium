# Review of Proposition 6BM and Corollaries/Theorems 6BM.1--3

Reviewer: `CODEX_EULER`

Verdict: **PASS** as ordinary mathematics in the stated timing-specific
architecture scope.  The one-point topology, finite-truncation continuity,
uniform sentinel tails, Fan--Glicksberg hypotheses, selector contrapositive,
late-or-Never constant, two-identity refinement, completeness consumer, and
stopping-law compactification boundary all check.  No repair is required.

## Proper sentinel and joint continuity

Give `Omega=Nat union {infinity}` its one-point compactification topology.
It is compact metrizable, and `P(Omega)` is compact convex metrizable in the
weak topology.  Every such probability law has the ordinary behavioral hazard
representation, including Never mass and arbitrary actions after zero reach.

For a finite proper net `F_s`, every member has zero mass at infinity and a
vanishing finite tail.  Finiteness gives, uniformly over its convex hull,

```text
sup_(nu in conv(F_s)) nu(T_s>H) -> 0.
```

On `{T_s<=H}`, absorption occurs no later than `H`.  The first coalition is
then determined by the finitely many cells

```text
{0},...,{H},{H+1,H+2,...,infinity}
```

of every clock.  Each cell is clopen in the one-point compactification, so its
probability is weakly continuous.  The truncated payoff is a finite
multilinear polynomial in these probabilities.  Removing the event
`T_s>H` changes a payoff bounded by `M` by at most `M*Pr(T_s>H)`, uniformly in
every other law.  Therefore the true payoff is a uniform limit of jointly
continuous functions on

```text
conv(F_s) x product_(i!=s) P(Omega).
```

This proves the joint weak continuity that fails on the unrestricted product
when every clock can escape together.

The strategy sets are nonempty compact convex subsets of locally convex
spaces, and payoff is continuous and affine, hence quasiconcave, in each own
law.  Fan--Glicksberg therefore supplies an auxiliary Nash profile.  Every
non-sentinel player has the full law space and hence an exact unrestricted
best-response inequality.  The sentinel's Nash inequalities on `F_s` transfer
to all `D_s` with loss `epsilon` through the global pseudometric.  This proves
Theorem 6BM.1, including the empty-family convention.

## Selector and tail contrapositives

At the profile from 6BM.1, a fixed-gap selector choosing the sentinel is
controlled within `epsilon<g`; choosing any other player is controlled
exactly.  Hence no selected range `D_s` can be properly strategically
approximable.  Since the empty range is approximable, every player identity
must occur somewhere in any such selector.

Proper finite approximation in total variation is equivalent to

```text
forall eta>0, exists H,
  sup_(mu in D_s) mu(T_s>H)<eta,
```

where the tail includes infinity.  A finite proper TV net has one common
finite tail cutoff.  Conversely, move the common tail mass to a fixed finite
time and net the resulting finite-dimensional simplex; all centers are
proper.  Since `d_s<=2M*TV`, uniform finite-time tightness would imply proper
strategic approximation.  Its failure therefore yields `eta_s>0` with tail
supremum at least `eta_s` for every `H`.  Taking
`kappa_s=eta_s/2` avoids any supremum-attainment assumption and gives the
claimed late-or-Never mass.

The refinement using reviewed algebra of 6BL is exact: at least two distinct
selector ranges must be strategically nonprecompact, and strategic
nonprecompactness forces failure of TV total boundedness, hence fixed mass at
arbitrarily late **finite** times.  Thus every identity has late-or-Never mass
and at least two identities have genuinely late finite mass.  The theorem
correctly does not make the two witnesses simultaneous at one candidate
profile.

## Complete sentinel class

If the properly approximable sentinel range is complete for unrestricted best
responses against every behavioral opponent profile, take the supremum of its
6BM.1 inequality over `D_s` and use completeness.  Every other player already
has its unrestricted inequality.  This produces terminal
`epsilon`-Nash profiles for every positive error.  The checked all-errors
equivalence then yields a uniform-equilibrium payoff.  No compactness or
completeness assumption is made on any other reply class.

## Scope and source boundary

The construction uses the special clock topology rather than a generic Nash
theorem for discontinuous games.  A uniformly proper sentinel removes the
joint all-Never seam; without it, common finite quit times can converge to all
Never while retaining collision/tie payoffs, exactly as recorded in
`CODEX_CEDAR__STOPPING_TIME_COMPACT_GAME.md`.

Finite finite-time menus and uniformly finite-time-tight classes fall within
the theorem.  Never or unbounded pure-time families may remain strategically
separated from every proper finite net and are deliberately left open.  The
result does not construct a reward table, force simultaneous two-clock
exposure, derive the target pair atoms, or control leftover mass.  If promoted
as an unrestricted strategy-class theorem, it requires a separate packet gate
and the mandatory second independent falsification review.
