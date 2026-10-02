# Positive-minimum response compactification ends at a paid Never face

Author: `CODEX_SPINOZA`

Status: **proved ordinary compactness, strategy-entry, tail-implementation,
and coherent-projective dichotomies.  A coherent exact repair chronology has
summable entrant mass; if its censor seams are also summable it compactifies
to an exact unrestricted terminal Nash profile.  The surviving output is a
macroscopic old-law reshuffling edge carrying a paid-Never cylinder.  Section
22 audits the stronger source-dependent strategy-entry operator: its graph is
compact semialgebraic at every fixed menu, but Browder continuation is not
anchored at an arbitrary input equilibrium, and its growing-clock closure has
a quantitative paid Late/Never discontinuity.  Section 24 gives an exact
quitting-timing regression to continuous equilibrium selection: a single
penalized strategy entry produces two unique branches joined only through a
vertical Nash fibre.  Thus even the smallest quitting-specific entry problem
has no continuous parameter section.  This is a route reduction, not a
conjecture solution.**

The attained minimum source is not enough to make the complete-law payoff
game continuous.  If a compact response enclosure were uniformly
opponent-tight, Debreu--Fan--Glicksberg would produce an actual unrestricted
terminal approximate Nash profile.  Under a positive global debt minimum,
such an enclosure must instead meet a boundary on which three opponents have
a positive common Never cylinder.  Finite-menu Nash profiles exhibit the
sharper quantitative version: a player with positive singleton self-reward
has an opponent-Never cylinder bounded below by the global gap divided by
that reward.

The remaining obstruction is therefore not the zero-debt all-Never profile.
It is a positive-`D_*`, moving late-Quit response whose entire gain is released
from a macroscopic opponent-Never cylinder.  Minimum-fibre isolation does not
attach that cylinder or its moving response to the attained minimum source.

## 1. Exact question and notation

Fix a four-player quitting reward table.  Let

\[
 T=\mathbb N\cup\{\infty\}
\]

be the one-point compactification of the pure quitting clocks, and let
`Delta(T)` be the compact convex space of probability laws on `T`.  Independent
laws are behaviorally realized through their hazard strategies.  Write

\[
 U_i(\mu),\qquad
 B_i(\mu)=\sup_{\lambda_i\in\Delta(T)}
 U_i(\lambda_i,\mu_{-i}),qquad
 d_i(\mu)=B_i(\mu)-U_i(\mu).
\]

Assume that an actual source `sigma_*` attains the positive global minimum

\[
 D_* = \min_\sigma \sum_i d_i(\sigma)>0.                 \tag{1.1}
\]

The question is whether one may put the complete response laws generated
from `sigma_*` in a compact convex product, take a fixed point, and use the
strict minimum-fibre/unique-all-Continue neighborhood to exclude the only
payoff discontinuity at joint infinity.

The answer is no without one further tightness invariant.  The exact
positive result and its forced failure are below.

## 2. Uniformly opponent-tight response enclosures

Let `K_i` be nonempty compact convex subsets of `Delta(T)` and put
`K=prod_i K_i`.  Call `K` **uniformly opponent-tight** if, for every player
`i` and every `epsilon>0`, there is `H` such that

\[
 \sup_{\mu\in K}
 \prod_{j\ne i}\mu_j(\{H+1,H+2,\ldots,\infty\})<\epsilon.       \tag{2.1}
\]

Call it **`zeta`-response-complete** if

\[
 B_i(\mu)\le
 \sup_{\lambda_i\in K_i}U_i(\lambda_i,\mu_{-i})+\zeta
 \quad(\mu\in K,\ i=1,\ldots,4).                    \tag{2.2}
\]

The enclosure may be required to contain the stopping laws of the attained
minimum source.  That extra requirement does not affect the theorem.

### Theorem 2.1 (tight compact response enclosure gives an actual profile)

If `K` satisfies (2.1) and (2.2), there is an actual behavioral profile
`sigma` such that

\[
 B_i(\sigma)-U_i(\sigma)\le\zeta\qquad(i=1,\ldots,4).            \tag{2.3}
\]

In particular, under (1.1), no such enclosure exists when
`4 zeta < D_*`.

#### Proof

Take any convergent sequence in `K`.  Condition (2.1) makes its complete-law
sequence opponent-tight for every owner.  The checked opponent-tight
realization theorems therefore give continuity of every prescribed terminal
payoff on `K`; they also give continuity of every fixed pure-time response
payoff, including Never.  The payoff is affine in each player's own stopping
law.  Debreu--Fan--Glicksberg applied to the four compact convex sets `K_i`
gives a Nash point `mu` for the game restricted to `K`.

At that point restricted Nash optimality and (2.2) give

\[
 B_i(\mu)\le U_i(\mu)+\zeta.
\]

Canonical hazard reconstruction turns `mu` into a literal behavioral
profile with the same prescribed payoff and unrestricted cap.  This proves
(2.3).  Its total semantic debt is at most `4 zeta`, contradicting (1.1) if
`4 zeta<D_*`.  \(\square\)

This is a genuine actual-profile conclusion, not a stationary or
finite-menu conclusion.  The unrestricted cap is covered by (2.2), and the
canonical laws include randomized, arbitrarily late, and Never clocks.

## 3. Exact boundary forced by failure of tightness

The failure in Theorem 2.1 has a concrete compact limit.

### Proposition 3.1 (a three-opponent Never face)

If the compact product `K` is not uniformly opponent-tight, then there are a
player `i`, a number `beta>0`, profiles `mu^n in K`, and a limit `mu^infty in
K` such that

\[
 \prod_{j\ne i}\mu_j^n(\{n+1,n+2,\ldots,\infty\})\ge\beta,
 \qquad
 \prod_{j\ne i}\mu_j^\infty(\{\infty\})\ge\beta.       \tag{3.1}
\]

#### Proof

Negating (2.1) gives fixed `i,beta` and one `mu^n` for every horizon `n`.
Compactness supplies a convergent subsequence.  For each fixed `H`, the
late-or-Never set after `H` is clopen in `T`, so its marginal masses and their
finite product converge.  Monotonicity of tails gives the lower bound `beta`
at every fixed `H` in the limit.  Letting `H` tend to infinity and using
continuity from above gives the Never product in (3.1).  \(\square\)

Canonical reconstruction makes `mu^infty` an actual profile.  By (1.1), at
least one payer `p` satisfies

\[
 d_p(\mu^\infty)\ge D_*/4.                             \tag{3.2}
\]

Pure-time extremality then gives, for every `eta>0`, a deterministic finite
clock or Never response with gain at least `D_*/4-eta`.  Thus failure of
tightness is not a ghost boundary: it carries an actual paid response.  What
is not forced is `p=i`, preservation of the Never cylinder after the
response, or a return to the attained minimum source.

### Corollary 3.2 (positive-gap compactification dichotomy)

Let `K` be a compact convex product containing the complete laws of the
attained minimum source and satisfying (2.2) with `4 zeta<D_*`.  Then `K`
contains a profile satisfying (3.1), and its canonical behavioral
realization has a payer satisfying (3.2).

This is the sharp obstruction to the proposed Glicksberg route.  Positive
minimum does not remove the all-infinity discontinuity; response
completeness forces the closure to encounter it.

## 4. The stronger finite-menu obstruction

For each deadline `n`, let

\[
 A_n=\{0,1,\ldots,n,\infty\}
\]

and choose a mixed Nash equilibrium `mu^n` of the finite clock game.  Its
hazard realization is an actual `QuittingFiniteDeadlineNashProfile`.
Finite-menu Nash controls every time in `A_n`.  Against opponents supported
on `A_n`, all finite times later than `n` have the same value, and late Quit
differs from Never only on the event that all three opponents selected
Never.

Let `s_i=r_i({i})`.  At every such profile, (1.1) and the checked deadline
escape-charge estimate force a player `i_n` with

\[
 s_{i_n}>0,
 \qquad
 s_{i_n}\prod_{j\ne i_n}\mu_j^n(\{\infty\})
 \ge D_*/4.                                           \tag{4.1}
\]

After stabilizing the mover label,

\[
 \prod_{j\ne i}\mu_j^n(\{\infty\})
 \ge {D_*\over 4s_i}.                                \tag{4.2}
\]

The improving clock is `n+1`; every fixed finite clock is eventually in the
Nash menu and has nonpositive gain.  Consequently weak compactness cannot
turn this sequence into an actual terminal approximate Nash profile.  The
missing response escapes to infinity while (4.2) keeps its payment
macroscopic.

This quantitative conclusion is stronger than Proposition 3.1 and is already
represented by checked declarations:

* `QuittingFiniteDeadlineNashProfile.semanticDebt_le_escapeCharge`;
* `TerminalSemanticGlobalDebtBarrierCertificate.Certificate.floor_le_sum_finiteDeadlineEscapeCharge`;
* `TerminalSemanticGlobalDebtBarrierCertificate.Certificate.exists_floor_div_sumPositiveSingleton_le_deadlineSurvival`.

The last declaration uses the total positive-singleton bill as denominator;
the playerwise `D_*/4` form (4.1) follows directly in Fin4 by selecting a
maximum-debt player and using the exact late-Quit/Never identity.

## 5. Why minimum-fibre isolation does not close the boundary

The strict minimum-fibre theorem controls one-stage Bellman roots for payoff
tails near the minimum envelope, and makes all Continue the unique exact root
in its robust tube.  It does not impose (2.1) on complete stopping laws in a
response closure.  In particular:

1. a finite-menu Nash law need not remain in the minimum fibre or preserve
   the original source law;
2. three players may carry the uniform Never product (4.2) while the terminal
   semantic pair lies outside the isolated tube;
3. the paid response `n+1` varies with the menu, so no fixed response passes
   to the weak limit; and
4. applying the paid response may erase one factor of the Never cylinder and
   supplies no source re-entry.

Thus the attained source cannot be inserted into the compactification merely
as a distinguished point.  A successful fixed-point proof needs a new global
invariant: a response-complete compact enclosure that is opponent-tight, or a
source-attached rule which consumes the paid Never cylinder before it is
destroyed.  Theorem 2.1 shows that the former would already settle the
terminal problem; (4.1) shows exactly why the ordinary finite-menu closure
cannot provide it under `D_*>0`.

## 6. Nonclaims

This note does not prove `D_*>0` is realizable, does not produce a uniform
equilibrium, and does not turn (4.1) into a renewable paid packet.  It does
not identify the late-boundary owner with the payer for an arbitrary compact
response enclosure.  No static label, local root, or S.3 compiler is used.

## 7. Sources inspected

* `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`:
  `quittingTerminalPayoff_compactStoppingLawProfile_tendsto_of_jointTight`,
  `quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_tendsto`,
  `quittingTerminalPayoff_update_compactStoppingLawProfile_finiteTime_tendsto`,
  `quittingContinuationBestResponseValue_compactStoppingLawProfile_tendsto`,
  and `QuittingOpponentTightLawSequence.of_twoProperLimits`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`:
  `QuittingFiniteDeadlineNashProfile`, its escape-charge bounds, and the
  global-floor survival theorem;
* `UniformEquilibrium/Quitting/Terminal/StoppingLawCanonicalization.lean`;
* `notes/CODEX_FERMAT__FINITE_DEADLINE_NASH_HORIZON_ESCAPE.md`;
* `notes/CODEX_SNELL__AGGREGATE_PAID_ORIENTATION_FINITE_ATOM_AND_NORMALIZED_PASSPORT.md`,
  Section 7.14 (the already existing stronger ordinary-mathematics
  formulation of the finite-menu boundary); and
* `notes/CODEX_SPINOZA__NEAR_MINIMUM_MOVING_ROW_LINEAR_SEAM_CERTIFICATE.md`,
  Sections 13--16.

## 8. Precise next question

Can the paid late-Quit response in (4.1) be applied while retaining a fixed
positive fraction of the same three-opponent Never cylinder and returning to
an actual minimum-fibre source?  Neither complete-law compactness nor
minimum-fibre isolation supplies that source-preserving consumption rule.

## 9. Exact attachment regression: the paid bubble is a semantic plateau

The positive cylinder supports a stronger exact calculation.  It explains
why neither weak-law compactness nor equality of successive terminal semantic
pairs attaches the paid response to a renewable spine.

Fix one deadline-`n` mixed clock Nash law `mu`, and select the player `i`
from (4.1).  Put

\[
 c=\prod_{j\ne i}\mu_j(\{\infty\}),
 \qquad s_i=r_i(\{i\}),
 \qquad u_i=U_i(\mu).
\]

For every finite `L>n`, let `rho^L` be the actual profile obtained by replacing
only player `i`'s clock by deterministic Quit at `L`.  Let `rho^infty` use
Never instead.

### Proposition 9.1 (paid late-clock plateau and discontinuous endpoint)

With the preceding data:

1. every `rho^L`, `L>n`, gives player `i` its unrestricted cap against
   `mu_{-i}`;
2. the gain over the finite-menu source and the late-versus-Never jump obey

   \[
   g:=U_i(\rho^L)-u_i\ge D_*/4,
   \qquad
   U_i(\rho^L)-U_i(\rho^\infty)=c s_i\ge g;           \tag{9.1}
   \]

3. the **full terminal semantic pair** of `rho^L` is independent of `L` for
   every `L>=n+2`; but
4. `rho^L` converges coordinatewise in compact stopping laws to
   `rho^infty`, while its prescribed `i` payoff drops by `c s_i>=D_*/4` and
   its `i` debt jumps from zero to `c s_i` at that endpoint.

#### Proof

Every clock in `A_n` has payoff at most `u_i` by finite-game Nash.  Against
opponents supported on `A_n`, all finite clocks later than `n` have one common
value.  Pure-time extremality says that the unrestricted cap is the maximum
of the finite-menu values and this one late value.  The positive debt choice
of `i` makes the late value the cap and gives the first inequality in (9.1).

Late Quit and Never differ only when all opponents selected Never.  That
event has probability `c`; its outcome changes from no terminal coalition to
the singleton `{i}`.  Hence

\[
 U_i(\rho^L)-U_i(\rho^\infty)=c s_i.
\]

Never belongs to `A_n`, so its payoff is at most `u_i`.  Therefore

\[
 c s_i
 =\bigl(U_i(\rho^L)-u_i\bigr)
  +\bigl(u_i-U_i(\rho^\infty)\bigr)
 \ge g,
\]

proving (9.1).

It remains to check the full semantic plateau.  The prescribed terminal law
is independent of `L>n`: if an opponent has a finite clock, the first
coalition occurs by `n`; otherwise `{i}` quits alone at `L`.  Player `i`'s
cap depends only on the unchanged opponents.

For another owner `k`, classify a deterministic deviation clock relative to
`n<L`:

* a clock at most `n`;
* a clock strictly between `n` and `L`;
* the clock exactly `L`;
* a clock after `L`, including Never.

In these four cases, conditional on no earlier opponent clock, the new
terminal coalition is respectively determined before the old deadline,
`{k}`, `{i,k}`, or `{i}`.  The associated expected values do not depend on
the numerical value of `L`.  When `L>=n+2`, every category is represented.
Pure-time extremality makes `k`'s cap the supremum of this same finite list,
so every cap coordinate is independent of `L`.  This proves the full
semantic-pair assertion.

Finally, deterministic clocks `L` converge weakly to Never in the one-point
compactification.  At `rho^L`, player `i` plays its cap, hence has zero debt.
At `rho^infty` its opponents, and therefore its cap, are unchanged, while
its prescribed payoff has fallen by `c s_i`.  Its debt is exactly `c s_i`.
\(\square\)

### Corollary 9.2 (no compact endpoint with subcharge semantic seam)

The finite profiles `rho^L` have pairwise zero terminal-semantic seam for
`L>=n+2`, and their stopping laws converge in the compact law space.  Yet the
canonical profile at the compact endpoint has semantic seam at least
`D_*/4` in the payer coordinate.  Consequently no argument which merely
closes the paid late-clock family in weak stopping-law topology can return an
endpoint with seam `o(g)`.

This is not a generic zero-minimum all-Never example.  The source `mu` is a
literal finite-menu Nash profile inside the hypothetical positive global
gap, the response has gain `g>=D_*/4`, and the lost endpoint mass is the
same quantitative cylinder `c s_i` which pays that response.

## 10. Why the plateau is not a one-persistent spine

The sequence

\[
 \rho^{n+2},\rho^{n+3},\rho^{n+4},\ldots
\]

may look stronger than an approximate spine: its semantic residual is
exactly zero.  It nevertheless fails chronology in two separate exact ways.

First, these are alternative complete profiles from the same source, not
successive tail continuations.  In each `rho^L`, player `i` surely quits at
`L` if nobody has quit earlier.  Thus the profile is terminal by `L`; there
is no live successor on which `rho^{L+1}` can begin.  Declaring the weak-law
endpoint to be that successor deletes precisely the charge in (9.1).

Second, player `i` has zero debt at every finite endpoint.  The global floor
only says that some other player is paid there.  It neither preserves the
finite-menu Nash inequalities nor the same opponent-Never cylinder when that
new response is applied.  Hence payer stabilization at the original source
does not give a persistent active-clock rank.

This leaves an exact three-way verdict for the requested continuation:

* **one-persistent spine:** not produced, because the finite paid endpoints
  are terminal alternatives and the limiting endpoint restores debt by a
  discontinuous loss;
* **summable paid first-disagreement block:** not produced, because the only
  compact retraction has seam at least the full paid gain, not `o(g)`; and
* **regression:** Propositions 9.1--9.2 show exactly that the macroscopic
  opponent-Never cylinder pays the late response and simultaneously prevents
  its weak-law attachment.

The next possible strengthening must use more than the cylinder and its
payer: it must transfer the new debt at a finite `rho^L` to another player
while keeping a literal live suffix, or provide a source re-entry before the
sure quitting clock.  Moving the clock farther out cannot do either.

## 11. The second payer has a finite exact response alphabet

Return to one finite endpoint `rho^L`, with `L>=n+2`.  Player `i` has zero
debt there.  Since every actual carrier point has total debt at least `D_*`,
some other player `p` satisfies the sharper bound

\[
 d_p(\rho^L)\ge D_*/3.                               \tag{11.1}
\]

Against `p`, player `i` is the sure clock `L`, while the two remaining
opponents have laws supported on `A_n`.  Hence an exact pure-time cap response
of `p` has a representative in

\[
 \{0,1,\ldots,n,n+1,L,\infty\}.                     \tag{11.2}
\]

Indeed clocks at most `n` are kept individually; every clock strictly
between `n` and `L` has the same value as `n+1`; `L` is the collision clock;
and every clock after `L` has the same value as Never because `i` has already
quit surely.  Thus the second exact paid edge never needs a date beyond `L`.

If the selected response is before `L`, its target terminates surely by that
strictly earlier date.  This is a literal source-attached deadline descent of
gain at least `D_*/3`.  The two residual choices are exactly the simultaneous
`{i,p}` clock at `L` and withdrawal to Never.  The adjacent-deadline
operational-effect theorem does not consume either as chronology; it gives a
same-tail paid behavioral port, not an exact Nash--Bellman successor.

## 12. Outer-anchor descent or a single-stage paid toggle cycle

There is nevertheless a finite exact classification of repeated responses
before any earlier clock is installed.  It uses the special separation

\[
 n+1<L.                                               \tag{12.1}
\]

For each player, retain three possible roles:

* `O`: that player's original law from `mu`, supported on `A_n`, when that
  law is not already literal Never;
* `A`: the pure anchor clock `L`;
* `N`: Never.

Initially `i` has role `A`, and every other player has role `O` or `N`
according as its original law is non-Never or Never.  At every
state choose, with fixed tie rules, a maximum-debt player and a pure-time
exact best response.  Every chosen edge has gain at least

\[
 D_*/4.                                               \tag{12.2}
\]

Use the following canonical representatives: choose `n+1` for the common
value of a clock strictly between `n` and `L`, and choose Never for any clock
after `L` when an opponent anchor exists.

### Theorem 12.1 (finite outer-anchor trichotomy)

Starting at `rho^L`, the canonical response recursion reaches one of the
following in finitely many steps:

1. a paid response at a date at most `n+1`, hence a strict sure-deadline
   descent below `L`;
2. a literal directed cycle of paid responses among `O/A/N` profiles, with
   at least one `A` at every vertex; or
3. temporary erasure of the last `A`, followed after at most four further
   paid responses by arm 1.

In arm 2 the set of `O` players is constant around the repeated segment and
every edge toggles one other player between `A` and `N`.

#### Proof

As long as some anchor is present, a mover having an anchor opponent never
needs a clock after `L`: such clocks equal Never.  If its cap is attained
strictly before `L`, the representative is at most `n+1` or at one of the
old dates at most `n`, and arm 1 occurs.  Otherwise a nonanchor moves only to
`A` or `N`; an anchor can only move to `N`, because choosing its prescribed
clock `L` has zero gain.

The only mover without an anchor opponent is the unique remaining anchor.
Its opponents then have roles `O` or `N`, so all their finite clocks are at
most `n`.  Every finite clock of the mover after `n` has one common value and
is represented by `n+1<L`.  Therefore this mover either gives arm 1 or erases
the last anchor by choosing Never.

Suppose the last anchor is erased.  The resulting profile has only `O` and
`N` coordinates.  Since `i` began as `A`, it is now `N`.  If

\[
 c=\prod_{j\ne i}\mu_j(\{\infty\}),
\]

then its full joint Never probability is

\[
 \prod_j \nu_j(\{\infty\})\ge c>0:                  \tag{12.3}
\]

every original factor is retained, while replacing an original law by
Never only changes its factor to one.  At an `O/N` state every cap has a
representative in

\[
 \{0,1,\ldots,n,n+1,\infty\}.                       \tag{12.4}
\]

A positive-gain Never response must move an `O` player, and permanently
reduces the number of `O` coordinates.  Such a reduction can occur at most
four times.  Once it cannot occur, the positive global floor forces a finite
response in (12.4), which is arm 1.  This proves arm 3.

If neither arm 1 nor erasure of the last anchor occurs, the recursion stays
in the finite set of `O/A/N` profiles with nonempty anchor set.  A state
repeats.  On the repeated segment an `O` coordinate cannot change, because
it can never return to `O`; hence the `O` set is fixed.  Every remaining paid
edge is exactly `A -> N` or `N -> A`.  This proves arm 2.  \(\square\)

The quantitative cylinder is genuinely used in arm 3: (12.3) shows that
last-anchor erasure restores, rather than spends, the original Never waist.
The finite `O` rank then forces an earlier sure clock.

## 13. The cycle has a quitting-specific table projection

Arm 2 is more structured than an arbitrary best-response cycle with mixed
backgrounds.  Let `O` be its fixed set of original-law players and put

\[
 a=\prod_{j\in O}\mu_j(\{\infty\})>0.                \tag{13.1}
\]

At a cycle vertex, let `S` be the nonempty set of `A` players.  Any `O`
player who quits does so by date `n`, before the toggles at `L`.  On that
event an `A/N` toggle is irrelevant.  Conditional on every `O` player
selecting Never, the terminal coalition at `L` is exactly `S`.

Consequently, if `x,x'` are successive cycle vertices with anchor sets
\(S,S'=S\mathbin\triangle\{p\}\), an edge with mover `p` has the exact gain
identity

\[
 U_p(x')-U_p(x)
 =a\bigl(r_p(S')-r_p(S)\bigr)
 \ge D_*/4.                                          \tag{13.2}
\]

Both endpoint coalitions are nonempty, because arm 2 never erases the last
anchor.  After extracting a simple subcycle, arm 2 therefore supplies a
literal nonempty strict-toggle cycle in the Fin4 reward table, with every raw
edge margin at least `D_*/4`.

This factorization is the special quitting-game fact absent from generic
finite best-response dynamics.  It also removes the usual mixed-background
objection: the background affects every toggle edge only through the same
positive scalar `a`, rather than averaging several coalition comparisons.

### 13.1 Exact checked-dispatch mismatch

The checked four-player semantic dispatch does **not** directly accept this
cycle.  Its input is

```text
QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle
```

whose every edge is the particular `strictToggleSuccessor` selected by
`Classical.choose` from the terminal witness.  The response recursion above
selects a maximum-debt player in a changing complete-profile context.  Even
after (13.2) projects its edge to a raw table inequality, there is no reason
that this mover equals the witness's fixed chosen toggle player at that
coalition.  The reviewed dispatch packet explicitly records: “This does not
compile an arbitrary strict-toggle cycle.”

For reference, the exact checked dispatch is
`hasQuittingStrictToggleSemanticDispatch` in
`StrictToggleSemanticDispatch.lean`.  After ruling out its uniform-payoff
arm, `hasQuittingStrictToggleSemanticResidual_of_no_uniformPayoff` returns
one of **three**, not two, residual constructors:

1. persistent base of cardinality at least two, with a positive lower bound
   for `quittingPersistentLargeBaseExcess` on its whole induced Nash set;
2. singleton persistent base, with a positive lower bound for
   `quittingSingletonBaseExcess` on its whole induced Nash set; or
3. empty persistent base, with no
   `IsQuittingEmptyBaseSimplexInteriorSolution` and positive
   `quittingEmptyBaseSimplexDefect` on every compact interior rho-box.

The first two are the two persistent-base shapes often grouped as output
`A.2`; the third is output `B.2`.  The reviewed
`LARGE_PERSISTENT_BASE_FINITE_NASH_DISPATCH` further makes the first shape
finite, but retains pure paid-leave or matching-pennies deletion residuals.
It does not eliminate the shape.

### 13.2 Recent consumers do not close this cycle

The checked Fin4 monodromy impossibility has a narrower input.  Its trace
vertices are nonsingleton coalitions and its terminal predicate discards a
pair as soon as it has any mass-preserving route to a singleton, without
requiring that route to be profitable.  A general nonempty toggle cycle may
pass through singleton and pair vertices.  The reviewed note
`ATLAS_GATEKEEPER__SERIAL_NONEMPTY_TOGGLE_DISPATCH_NOT_MONODROMY.md` proves
this exact type mismatch.  Hence monodromy impossibility cannot be applied to
arm 2.

The balanced full-core consumer is also inapplicable.  It assumes the exact
twelve-coordinate identity

```text
normalizedSoloMatrix reward = fullCoreMatrix
```

and then builds a specific four-phase singleton cycle.  Equation (13.2)
imposes only the displayed membership-toggle inequalities, possibly involving
nonsingleton rewards; it does not force that normalized singleton matrix.
The full-core theorem's own scope says nothing about matrices outside that
literal fibre.

Thus (13.2) is a genuine quitting-specific projection, but the result remains
an arbitrary horizontal strict-toggle cycle.  Serializing it would repeat the
horizontal-versus-vertical category error.  An ordinary extension of the
face dispatch to arbitrary supplied cycles would still end at the same three
semantic residual shapes and would not provide chronology.

## 14. Renewable-rank verdict

The outer separation `n+1<L` makes Theorem 12.1 a one-pass deadline descent.
After arm 1 the new sure deadline is at most `n+1`, inside the support range
of the original background.  Reapplying the same argument need not decrease
it again: an exact response can move to a later existing opponent deadline.
Hence no renewable natural-valued deadline rank has been proved.

The exact outcome is:

\[
\boxed{
\begin{array}{c}
\text{positive finite-menu Never waist plus its paid late response}
\end{array}
\Longrightarrow
\begin{array}{c}
\text{a literal paid clock before the outer deadline,}\\
\text{or an arbitrary source-attached strict toggle cycle.}
\end{array}}
\tag{14.1}
\]

The first output is source-attached but not presently renewable.  The second
has the single-coalition factorization (13.2), but it is not an input to the
checked selected-cycle dispatch, the monodromy contradiction, or the balanced
full-core fibre theorem.  No new local screen remains at the outer deadline;
the exact residual is the broader source-attached horizontal cycle.

Additional source inspected:

* `formalized/STRICT_TOGGLE_CYCLE_SEMANTIC_DISPATCH.md` and
  `hasQuittingStrictToggleSemanticDispatch_of_card_four` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StrictToggleSemanticDispatch.lean`;
* `notes/CODEX_SINGLETON_SOURCE__ONE_SURE_OWNER_EXACT_RESPONSE_HANDOFF.md`,
  Propositions 9.1--9.3; and
* `notes/CODEX_DESCENDANT__FINITE_CLOCK_PAID_PORT_RESPONSE_CURL_REDUCTION.md`,
  which records why a generic finite response cycle is horizontal.

## 15. Exact finite-Nash field lost at a descending target

Suppose arm 1 of Theorem 12.1 occurs.  Let `x -> y` be its paid edge, let
`p` be the mover, and let `t<=n+1<L` be the selected pure response.  Several
useful fields survive literally:

* `y` is an actual descendant of the original finite-menu Nash source;
* every prescribed law still has finite support bounded by `L`, so the live
  roots are all Continue from `L+1` onward;
* `p` Quits surely at `t`, so prescribed play terminates by `t`; and
* `p` plays an exact unrestricted best response and has zero debt at `y`.

The field needed to restart the finite-menu construction does not survive.

### Proposition 15.1 (quantitative loss of joint finite-menu Nash)

At the descending target `y`, some player `h != p` and some pure time or
Never response `q_h` in

\[
 \{0,1,\ldots,t,\infty\}\subseteq
 \{0,1,\ldots,L,\infty\}                            \tag{15.1}
\]

satisfy

\[
 U_h(q_h,y_{-h})-U_h(y)\ge D_*/3.                   \tag{15.2}
\]

Consequently `y` fails the `pureTime_le` field of a deadline-`L+1`
`QuittingFiniteDeadlineNashProfile` by at least `D_*/3`, even though its
`allContinue_from` field still holds.

#### Proof

The mover `p` has zero debt after its exact cap response.  The total debt of
the actual target is at least `D_*`, so one of the other three players has
debt at least `D_*/3`.  That player faces the sure opponent clock `p=Q_t`.
Every pure clock after `t` has the same terminal law as Never, since `p` has
already quit.  Pure-time extremality therefore attains the full cap among
the finite clocks at most `t` and Never, proving (15.1)--(15.2).  \(\square\)

This pinpoints the ancestry failure.  The original deadline Nash inequality

\[
 U_h(Q_s,\mu_{-h})\le U_h(\mu)
\]

is an opponents-dependent statement.  Replacing `i` by `Q_L`, and then the
subsequent response movers, changes those opponents.  Only the most recent
mover's cap equality is preserved; earlier solved coordinates may reactivate.
Proposition 15.1 shows that this is not merely lack of a proof or a small
error: at every descending target a permitted old-menu deviation has a fixed
macroscopic gain.

Re-solving the finite normal form at deadline `L+1` would restore
`pureTime_le`, but it supplies a newly selected Nash law with no bound on its
distance from `y`, no retained paid edge, and no source seam.  Truncating
post-`t` prescribed clocks is also insufficient: it preserves prescribed
play because `p` quits surely, but it can change `p`'s cap when `p` deviates
and thereby exposes the truncated opponents.  Thus neither support
compression nor screened prescribed-payoff equivalence recovers the lost
certificate.

The exact nonrenewal statement is therefore:

\[
\boxed{
\text{deadline descent retains ancestry and bounded support, but loses joint
finite-menu Nash by at least }D_*/3.}
\tag{15.3}
\]

## 16. Strategy entry has a macroscopic shadow-price crossing

The preceding loss suggests re-solving globally while the late clock is
introduced.  There is a clean finite-game continuation theorem, but it does
not give a small actual-Nash seam.

Fix the old clock menu

\[
 A=\{0,1,\ldots,n,\infty\}
\]

and one new pure clock `e=Q_L`, where `L>n`.  Let `G_kappa` be the finite game
on `A union {e}` in which the actual quitting payoff is used except that a
player choosing `e` pays an artificial cost `kappa>=0`.  Thus, for a mixed
profile `x`,

\[
 U_i^{\kappa}(x)=U_i(x)-\kappa x_i(e).                \tag{16.1}
\]

Assume `|r_i(S)|<=R` and choose `K>2R`.  At `kappa=K`, the new clock is
strictly dominated by Never, so the Nash set is exactly the lifted old-game
Nash set.  At `kappa=0`, this is the actual expanded timing game.

### Theorem 16.1 (entry continuation, boundary atom, and price moat)

Assume the global total terminal debt floor `D_*>0`.

1. There is a compact connected component of pairs `(kappa,x)`, with `x`
   Nash in `G_kappa`, which meets both `kappa=K` and `kappa=0`.  Since the
   graph is semialgebraic, the component contains a continuous path between
   those two parameter faces.
2. Every Nash profile `q` of the actual expanded game has

   \[
   \sum_i q_i(e)>0.                                   \tag{16.2}
   \]

   At fixed `n,L`, compactness therefore gives a number
   `beta_(n,L)>0` such that the left side of (16.2) is at least
   `beta_(n,L)` at every expanded-game Nash profile.
3. If `p` is any old-game Nash profile and `q` is any actual expanded-game
   Nash profile, then

   \[
   \sum_j \operatorname{TV}(p_j,q_j)
      \ge {D_*\over16R},                              \tag{16.3}
   \]

   where `p` is understood to give the new action zero mass.
4. Follow any spanning path from its `kappa=K` end until the new action first
   enters.  If `(kappa_0,x^0)` is that entry boundary, then

   \[
   \kappa_0\ge D_*/4.                                 \tag{16.4}
   \]

   More precisely, there are path points
   `(kappa_m,x^m)->(kappa_0,x^0)` and one stabilized player `i` such that
   `x_i^m(e)>0`, `x_i^m(e)->0`, and

   \[
   U_i(e,x^m_{-i})-U_i(x^m)
      =\kappa_m\bigl(1-x_i^m(e)\bigr)
      \longrightarrow\kappa_0\ge D_*/4.              \tag{16.5}
   \]

   The entry source `x^0` has a literal opponent-Never cylinder:

   \[
   r_i(\{i\})\prod_{j\ne i}x_j^0(\infty)
      \ge\kappa_0\ge D_*/4.                           \tag{16.6}
   \]

   Consequently, for all large `m`, the prescribed terminal event in which
   `i` chooses `e` and every opponent chooses Never has probability at least

   \[
   {D_*\over8R}\,x_i^m(e).                            \tag{16.7}
   \]

#### Proof

For part 1, use the standard Nash fixed-point map, formed by adding the
positive parts of pure-action gains to the current mixed weights and
renormalizing.  Its fixed points are exactly Nash profiles.  Browder's
continuation lemma gives a connected fixed-point component spanning the
parameter interval.  The finite Nash graph is semialgebraic, so connected
components are path connected.  Strict domination at `K` identifies its
first parameter face with old-game Nash profiles.

For the remaining parts, first note the exact old-face identity

\[
 d_i(p)=\bigl[U_i(e,p_{-i})-U_i(p)\bigr]_+             \tag{16.8}
\]

for every old-game Nash profile `p`.  Indeed, old-menu deviations are
controlled by Nash, every finite clock after `n` has the same payoff against
old-menu opponents, and `e` represents that common late value.  Therefore

\[
 \max_i\bigl(U_i(e,p_{-i})-U_i(p)\bigr)\ge D_*/4.     \tag{16.9}
\]

If an actual expanded-game Nash profile put zero mass on `e`, it would be an
old-game Nash profile and would also make every gain in (16.8) nonpositive.
It would then be an unrestricted terminal Nash profile, contrary to
`D_*>0`.  This proves (16.2); compactness proves the fixed-game positive
minimum.

For (16.3), select `i` satisfying (16.9).  The same `e`-gain is nonpositive
at `q`.  The finite total-variation coupling bound for one response gain is

\[
 |G_i(e;p)-G_i(e;q)|
 \le4R\sum_j\operatorname{TV}(p_j,q_j).
\]

Combining this with (16.9) proves (16.3).

At an entry boundary `x^0`, the new action has zero mass, so `x^0` is an
old-game Nash profile.  Penalized Nash optimality says that every actual
`e`-gain there is at most `kappa_0`.  Equation (16.9) then proves (16.4).
Choose nearby positive-entry points and stabilize a player `i` who uses `e`.
Because a used pure action attains the penalized equilibrium payoff,

\[
 U_i(e,x^m_{-i})-\kappa_m
   =U_i(x^m)-\kappa_m x_i^m(e),
\]

which is exactly (16.5).  At the old-face limit, Never is an available old
action and hence pays at most the prescribed equilibrium payoff.  Against
old-menu opponents, `e` and Never differ only when every opponent chose
Never.  Thus

\[
 r_i(\{i\})\prod_{j\ne i}x_j^0(\infty)
 =U_i(e,x^0_{-i})-U_i(\infty,x^0_{-i})
 \ge\kappa_0.
\]

This proves (16.6).  It also gives `r_i({i})>0` and, using the reward bound,
an opponent-Never product at least `D_*/(4R)`.  Continuity gives half that
bound at the nearby path points, proving (16.7).  \(\square\)

### 16.2 Exact interpretation

The theorem produces all three objects suggested by strategy-entry
continuation, but separates them sharply:

* an actual expanded-game Nash law has a positive declared new-clock atom,
  but is at least `D_*/(16R)` away from every old Nash law;
* the continuation component is source-coherent at first entry and carries a
  literal reached new-clock atom, but only in an **artificially penalized**
  game; and
* the price needed to keep that source Nash is macroscopic, at least
  `D_*/4`.  Equation (16.5) says that removing the price restores a response
  gain of that same order even while the prescribed new-clock atom vanishes.

Thus the homotopy does not repair Proposition 15.1.  It replaces the lost
joint-Nash field by a capacity/shadow-price field whose defect is fixed, not
`o` of the entering hazard.  Nor does semialgebraic curve selection give the
needed relative seam: it gives `x^m->x^0`, but no estimate

\[
 \|x^m-x^0\|=o\bigl(x_i^m(e)\bigr),                   \tag{16.10}
\]

and the support-optimality error in (16.5) remains at least `D_*/4+o(1)` in
any case.

The boundary mass in (16.2) is only a declared strategy atom.  It need not be
reached under prescribed play: an opponent may Quit earlier with probability
one.  The stronger reached atom (16.7) exists at the source-coherent entry,
but there the Nash statement belongs to `G_(kappa_m)`, not to the actual
quitting game.  This is the exact finite global re-solving obstruction.

## 17. Revised next question

Can the macroscopic entry price in (16.4)--(16.6) be represented by an
**actual retained continuation payoff** while keeping the old-face Nash
inequalities and the reached atom (16.7)?  A bare strategy-entry homotopy
cannot do this: actual adjacent Nash laws are separated by (16.3), while the
only source-coherent component pays with an artificial action cost.

Additional source inspected:

* `formalized/FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md`,
  especially the adjacent total-variation separation and the
  boundary-participation/reshuffling split.

## 18. Exact support equations for implementing the entry price

The artificial price can be tested directly against a retained tail.  This
gives a finite incompatibility system, not just the observation that the tax
is external to the quitting game.

Fix one penalized equilibrium `(kappa,x)` from Section 16.  Write

\[
 h_i=x_i(e),\qquad
 M=\prod_jx_j(\infty),\qquad
 m_i=\prod_{j\ne i}x_j(\infty).                       \tag{18.1}
\]

Let `u` be the payoff vector of a literal continuation placed strictly after
date `L`.  Denote hard-zero-tail pure-action payoffs by `V_i(a)`.  Grafting
the tail changes the relevant quantities exactly as follows:

\[
 \begin{array}{rcl}
 V_i^u(f)&=&V_i(f),\qquad f\le n,\\
 V_i^u(e)&=&V_i(e),\\
 V_i^u(\infty)&=&V_i(\infty)+m_i u_i,\\
 V_i^u(x)&=&V_i(x)+M u_i.
 \end{array}                                          \tag{18.2}
\]

The first two lines are the key: both an old finite Quit and `Q_L` absorb
before the retained tail and therefore forgo the same continuation.

### Proposition 18.1 (tail-implementability equations)

Suppose `h_i>0`.

1. If player `i` also gives positive mass to any old finite clock `f<=n`, no
   retained post-`L` tail can make `x_i` a best response, even support-wise.
   The two required support equations are incompatible:

   \[
   V_i^u(e)=V_i^u(f),
   \qquad
   V_i^u(e)-V_i^u(f)=\kappa.                           \tag{18.3}
   \]

2. If player `i` uses no old finite clock, then
   `x_i(infinity)=1-h_i`; exact support-wise Nash is possible only if

   \[
   m_i u_i=\kappa.                                     \tag{18.4}
   \]

   This equation is also sufficient for equality of `i`'s two supported
   actions `e` and Never and for their common payoff to equal the prescribed
   payoff.
3. If a nonentering player `j` uses both an old finite clock and Never, then
   every exact tail implementation must satisfy

   \[
   m_j u_j=0.                                          \tag{18.5}
   \]

   In the positive opponent-Never tube, this reduces to `u_j=0`.

#### Proof

Since `e` is supported at a `kappa`-penalized equilibrium, its hard payoff is
the penalized equilibrium value plus `kappa`.  Every supported old action has
hard payoff equal to the penalized equilibrium value.  Hence

\[
 V_i(e)-V_i(f)=\kappa                                  \tag{18.6}
\]

for each supported old finite `f`, and the same equality holds with Never
when Never is supported.  Equation (18.2) leaves the left side of (18.6)
unchanged for finite `f`, proving (18.3).

If no old finite clock is used, the only other supported action is Never.
Equating its tail-adjusted payoff to the unchanged `e` payoff gives (18.4).
Moreover `M=(1-h_i)m_i`, so

\[
 V_i(x)+M u_i
 =V_i(x)+(1-h_i)\kappa
 =V_i(e),
\]

where the last equality is (16.5).  This proves sufficiency on the used
support.  Finally, a nonentrant finite/Never mixer has equal hard payoffs on
those two supported actions.  Equation (18.2) preserves equality only when
`m_j u_j=0`, proving (18.5).  \(\square\)

### Corollary 18.2 (the first-entry affine tail face)

Take the first-entry sequence in Theorem 16.1 and stabilize every entering
label along a subsequence.  A post-`L` implementation has only two
possibilities.

* If some entrant's old-face law has positive mass on a finite clock, tail
  implementation is impossible by (18.3).
* Otherwise every entrant is pure Never at the old-face limit.  For each such
  entrant `i`, (18.4) tends to

  \[
  u_i=r_i(\{i\}).                                      \tag{18.7}
  \]

  Every nonentrant which mixes a finite clock and Never simultaneously
  requires `u_j=0` by (18.5).

Thus the retained payoff must lie in the explicit affine coordinate face

\[
 \boxed{
 u_i=r_i(\{i\})\ (i\in J),
 \qquad
 u_j=0\ (j\in Z),}                                    \tag{18.8}
\]

where `J` is the stabilized entrant set and `Z` is the set of old-face
finite/Never mixers.  In addition it must satisfy the unused-action Nash
inequalities for every player.  Positive `D_*` supplied the cylinder and the
price in (16.6); it does not assert that an actual continuation payoff lies
in (18.8).

To verify (18.7), an entrant pure-Never at the old face has prescribed payoff
equal to its Never payoff.  The exact late-versus-Never identity and the
limit of (16.5) give

\[
 \kappa_0
 =r_i(\{i\})m_i^0.
\]

Taking limits in `m_i u_i=kappa` gives (18.7).

## 19. A pre-`L` prefix must have macroscopic conditional absorption

A block placed between the old horizon and date `L` can distinguish `Q_L`
from an earlier supported Quit, because the former waits through the block.
But bounded rewards force such a repair to be macroscopic.

### Proposition 19.1 (price-to-absorption lower bound)

Suppose an entrant `i` in a `kappa`-penalized equilibrium also uses an old
finite clock.  Insert any finite prefix after date `n` and before date `L`,
followed on survival by the original `Q_L` outcome and an arbitrary bounded
tail.  Let `alpha_i` be the probability that this inserted prefix absorbs
when player `i` commits to `Q_L` and the opponents follow `x_{-i}`.  Let
`theta_i` be the same absorption probability conditional on the prefix being
reached, so `alpha_i<=theta_i`.  If all terminal rewards and the tail payoff
are bounded in absolute value by `R`, then correcting the support gap in
(18.6) requires

\[
 \alpha_i\ge {\kappa\over2R},
 \qquad
 \theta_i\ge {\kappa\over2R}.                         \tag{19.1}
\]

Along the first-entry sequence of Theorem 16.1,

\[
 \liminf_m\alpha_i^m,\ \liminf_m\theta_i^m
 \ge {D_*\over8R}.                                   \tag{19.2}
\]

In the prescribed mixed profile, player `i` is assigned to `Q_L` with
probability `x_i^m(e)`, independently of the opponents.  Conditional on that
assignment, `alpha_i` is exactly the preceding response experiment.
Therefore the unconditional prefix-absorption mass tagged by the entering
`Q_L` branch is at least

\[
 {D_*\over16R}\,x_i^m(e)                              \tag{19.3}
\]

for all sufficiently large `m`.

#### Proof

The old finite support action terminates before the inserted prefix and its
payoff is unchanged.  If the prefix does not absorb, the committed `Q_L`
action reaches the same date-`L` outcome as before.  Coupling the modified
and unmodified `Q_L` experiments, their payoffs differ only on prefix
absorption, and by at most `2R` there.  Erasing the support gap `kappa` in
(18.6) therefore requires `2R alpha_i>=kappa`.  Since
`theta_i>=alpha_i`, this proves (19.1).  Taking lower limits and using
(16.4) gives (19.2).  In particular both probabilities are at least
`D_*/(16R)` for all sufficiently large `m`; independence of the player's
mixed-action draw from the opponents then gives (19.3).  \(\square\)

### 19.2 Route verdict

A literal retained tail solves the entry price only on the special affine
face (18.8); otherwise the finite support equations already contradict one
another.  A prefix before `L` can repair the contradiction only by a fixed
conditional absorption whose lower limit is at least `D_*/(8R)`.  Near first
entry its unconditional absorption is therefore at least linear in the
entering hazard, not sublinear.

This does not say that the macroscopic prefix arm is impossible.  It is a
new, literal source-attached charged-block obligation: one must solve the
full cap-Nash equations of that prefix and then consume an absorption mass
of order `x_i(e)`.  Strategy-entry continuation itself provides neither
those equations nor an endpoint seam smaller than that charge.  The exact
remaining alternative is now finite:

\[
\boxed{
\begin{array}{c}
\text{an actual tail payoff in the affine face (18.8),}
\\[2mm]
\text{or a pre-`L` cap-Nash block with conditional absorption}
\text{ having lower limit }\ge D_*/(8R).
\end{array}}
\tag{19.4}
\]

## 20. Minimum-fibre separation and the bounded-capacity budget

Let `K_*` be the compact prescribed-payoff projection of the positive
minimum fibre.  The checked strict minimum-plateau theorem supplies

\[
 \delta_*:=\min_{U\in K_*,\ i}(U_i-s_i)>0.             \tag{20.1}
\]

For nonempty `J` and a disjoint set `Z`, let

\[
 F_{J,Z}=\{u:u_i=s_i\ (i\in J),\ u_j=0\ (j\in Z)\}.  \tag{20.2}
\]

This is the affine tail face forced by (18.8).  In the sup norm its exact
separation from the minimum fibre is

\[
 \begin{split}
 \operatorname{dist}_\infty(K_*,F_{J,Z})
 &=\min_{U\in K_*}
   \max\left\{
      \max_{i\in J}(U_i-s_i),
      \max_{j\in Z}|U_j|
   \right\}\\
 &\ge\delta_* .                                      \tag{20.3}
 \end{split}
\]

The zero-coordinate conditions can strengthen the distance, but no uniform
extra positive amount follows from the minimum theorem.  The singleton
condition alone gives the displayed `delta_*` floor.

### Proposition 20.1 (an affine-face passage spends fixed exact hazard)

Assume annotations and rewards are bounded in absolute value by `R`.  Every
finite exact Nash--Bellman block whose initial annotation lies in `K_*` and
whose terminal continuation lies in `F_(J,Z)` has marginal-hazard charge at
least

\[
 H(B)\ge {\operatorname{dist}_\infty(K_*,F_{J,Z})\over2R}
       \ge {\delta_*\over2R}.                         \tag{20.4}
\]

#### Proof

For one exact Bellman row with absorption `a_t`, boundedness gives

\[
 \|v_t-v_{t+1}\|_\infty\le2R a_t.
\]

Sum over the block, use the endpoint distance (20.3), and use
`a_t<=sum_i q_(t,i)`.  \(\square\)

Let `H_cap<infinity` be the checked counterexample-side upper bound on the
charge of every finite exact Nash--Bellman block in the canonical box.  If
several source-to-face passages occur as disjoint subblocks of one literal
exact chronology, every finite prefix is itself one finite exact block.
Consequently that chronology contains at most

\[
 {2R H_{cap}\over\delta_*}                            \tag{20.5}
\]

such passages.  This conclusion is unavailable for independently reselected
blocks; exact composability is essential.

### Proposition 20.2 (coherent entry repairs have summable entrant mass)

Suppose one literal exact chronology contains a sequence of pairwise disjoint
strategy-entry repair subblocks, and suppose each repair is one of the two
alternatives in (19.4):

1. a source-to-affine-face passage as in Proposition 20.1; or
2. a pre-`L` prefix repair from Proposition 19.1, with entering prescribed
   mass `h_k`, chosen sufficiently close to first entry that
   `kappa_k>=D_*/8`.

Then only finitely many repairs have type 1, and the type-2 masses obey

\[
 \sum_{k:\,\mathrm{type} 2}h_k
 \le {16R H_{cap}\over D_*}.                          \tag{20.6}
\]

In particular the full entrant-mass series is summable.

#### Proof

The first assertion is (20.4)--(20.5).  For a type-2 repair, the proof of
Proposition 19.1 gives unconditional prescribed absorption at least

\[
 h_k{\kappa_k\over2R}\ge h_k{D_*\over16R}.
\]

These absorption events belong to disjoint chronological subblocks.  Their
sum in every finite prefix is bounded by that prefix's marginal-hazard
charge, hence by `H_cap`.  Letting the number of repairs increase proves
(20.6).  The finitely many type-1 entrant masses add a finite amount.
\(\square\)

This is a conditional consumer for a **supplied coherent exact repair
chronology**.  It does not say that independently chosen strategy-entry
components concatenate, nor that their artificial penalties have already
been implemented by exact cap-Nash prefixes.

## 21. What coherent summable entry actually compactifies

Entrant-mass summability alone is not enough: old clock mass may be reshuffled
at every expansion.  The exact missing field is measured by censoring.

Use the deadline convention

\[
 A_N=\{0,1,\ldots,N-1,\infty\}.
\]

Let `p^N` be an exact mixed Nash law on `A_N`.  At the next deadline put

\[
 b_{N,i}=p_i^{N+1}(N),
 \qquad
 e_{N,i}=\operatorname{TV}
  \left(p_i^N,C_Np_i^{N+1}\right),                    \tag{21.1}
\]

where `C_N` censors the new date `N` back to Never.  The `b_(N,i)` are the
entrant masses; the `e_(N,i)` are the old-law coherence seams.  No nesting is
assumed.

### Theorem 21.1 (summable censor coherence compiles to terminal Nash)

If

\[
 \sum_N\sum_i e_{N,i}<\infty,                         \tag{21.2}
\]

then

\[
 \sum_N\sum_i b_{N,i}<\infty,                         \tag{21.3}
\]

the literal lifts of `p^N` are Cauchy in total variation, and their limit is
an actual unrestricted terminal Nash profile.  In particular (21.2) is
impossible under `D_*>0`.

#### Proof

For one player let

\[
 F_{N,i}=1-p_i^N(\infty)
\]

be its total exposed finite-clock mass.  Censoring removes the new atom from
the exposed mass, and total variation controls every event probability, so

\[
 \left|F_{N,i}-\bigl(F_{N+1,i}-b_{N,i}\bigr)\right|
 \le e_{N,i}.
\]

Therefore

\[
 b_{N,i}\le F_{N+1,i}-F_{N,i}+e_{N,i}.                \tag{21.4}
\]

Summing telescopically gives

\[
 \sum_{N=N_0}^{M}b_{N,i}
 \le1+\sum_{N=N_0}^{M}e_{N,i},                        \tag{21.5}
\]

which proves (21.3).

Let `L_Np^N` be the literal lift assigning zero mass to the new date.  The
finite-versus-Never decomposition gives

\[
 \operatorname{TV}(L_Np_i^N,p_i^{N+1})
 \le e_{N,i}+b_{N,i}.                                 \tag{21.6}
\]

Equations (21.2)--(21.3) make the embedded stopping laws Cauchy in total
variation.  Let their product limit be `p^infinity`.  Total-variation
convergence passes prescribed terminal payoffs and every fixed pure-time
response payoff to the limit.  Once `N` exceeds a fixed finite response
time, its Nash inequality is one of the inequalities for `p^N`; the Never
inequality is present at every deadline.  Hence every finite pure time and
Never have nonpositive gain at the limit.  Pure-time extremality covers every
behavioral deviation, and canonical hazard reconstruction gives an actual
terminal Nash profile.  Its total debt is zero, contradicting `D_*>0`.
\(\square\)

Exact projective compatibility is the special case `e_(N,i)=0`.  In that
case (21.5) shows directly that all entrant masses are summable; the theorem
recovers the stronger known fact that an exact compatible family already
solves the terminal problem.

### Corollary 21.2 (summable entrants without coherence recreate the waist)

Assume `D_*>0` and choose arbitrary exact deadline Nash laws `p^N`.  For every
adjacent pair,

\[
 \sum_i(e_{N,i}+b_{N,i})\ge {D_*\over16R}.            \tag{21.7}
\]

Consequently, if the entrant masses are summable, then for all sufficiently
large `N`,

\[
 \sum_i e_{N,i}\ge {D_*\over32R}.                     \tag{21.8}
\]

At the same time every `p^N` has a payer `i_N` satisfying

\[
 r_{i_N}(\{i_N\})
 \prod_{j\ne i_N}p_j^N(\infty)\ge D_*/4.              \tag{21.9}
\]

After stabilizing the payer on a subsequence, (21.9) is the same fixed-label
paid-Never cylinder as in Section 4.

#### Proof

The old profile `p^N` has some missing-new-date gain at least `D_*/4`; the
new profile `p^(N+1)` makes that gain nonpositive.  The `4R` response-gain
Lipschitz estimate gives total adjacent variation at least `D_*/(16R)`.
Equation (21.6), summed over players, proves (21.7).  Summability makes the
total `b_N` tend to zero, yielding (21.8).  Finally Never is an old-menu
action, so the new-date gain is bounded above by its exact
late-Quit-versus-Never difference, which is the left side of (21.9).
\(\square\)

Thus the summable case has a sharp verdict.

* Summable entrant mass **plus summable censor coherence** compactifies all
  the way to an exact unrestricted terminal equilibrium.
* Summable entrant mass without that coherence does not compactify.  It
  forces a macroscopic old-law reshuffle at every sufficiently late menu and
  retains a paid-Never cylinder on a fixed-label subsequence.

The second arm is not yet a chronology: the cylinders live at the separately
selected finite Nash laws.  A successful continuation argument must make the
homotopy components themselves satisfy a summable censor seam, or attach the
macroscopic reshuffling edge to one actual successor.  Theorem 21.1 shows
that the former would already contradict `D_*>0`; Corollary 21.2 identifies
the latter as the only surviving output.

## 22. Source-dependent strategy-entry operator

The exact-scale lower tree can be augmented by a pointwise profitable tester
at a reconstructed finite-clock center (Section 10 of
`CODEX_SPINOZA__FINITE_TESTER_SEPARATION_AND_TWO_ESCAPE_BOUNDARY.md`).  To get
a full Nash guard one must re-solve the expanded finite game.  The natural
operator has a clean fixed-menu graph, but two distinct obstructions prevent
the proposed compact recurrence argument.

Let \(A\) be a finite set of pure clocks containing Never, let \(e\notin A\),
and let \(G_\kappa(A,e)\) be the game obtained by adding \(e\) to every
player's menu and charging \(\kappa\) to each player who uses it.  Fix
\(K>2R\), so \(e\) is strictly dominated at \(\kappa=K\).  Write

\[
 Z(A,e)=\{(\kappa,x):0\le\kappa\le K,
          \ x\in\operatorname{NE}(G_\kappa(A,e))\}.  \tag{22.1}
\]

### Proposition 22.1 (fixed-menu compact relation and anchoring gap)

The set \(Z(A,e)\) is compact semialgebraic and has finitely many compact
connected components.  Let \(\mathcal C(A,e)\) be the components meeting both
parameter faces.  Then

\[
 \mathcal R_{A,e}=\bigcup_{C\in\mathcal C(A,e)}
   \bigl(C_K\times C_0\bigr),                       \tag{22.2}
\]

where \(C_t=\{x:(t,x)\in C\}\), is a nonempty compact relation from old-menu
Nash equilibria to actual expanded-menu Nash equilibria.

This relation need not be total on the old Nash set.  The continuation theorem
used in Theorem 16.1 has quantifiers

\[
 \exists C\quad C_K\ne\varnothing\ne C_0,          \tag{22.3}
\]

not

\[
 \forall p\in\operatorname{NE}(A)\ \exists C,
 \qquad p\in C_K,\quad C_0\ne\varnothing.           \tag{22.4}
\]

Therefore it does not define an operator at an arbitrarily supplied source
\(p\).  Iteration would require the additional seriality statement that some
bottom equilibrium in every selected spanning component belongs to the top
of a spanning component for its own newly selected full-gap response.

**Proof.**  Finite-game Nash inequalities are polynomial equalities and weak
inequalities in \((\kappa,x)\), giving compact semialgebraicity.  Such a set
has finitely many connected components, each compact.  Browder continuation
gives at least one component meeting both faces, so (22.2) is a nonempty
finite union of compact products.  The last assertion is the literal
quantifier content of Browder's conclusion; no named checked or reviewed
theorem in the current route strengthens (22.3) to (22.4).  \(\square\)

One could try to repair the anchoring gap with equilibrium-component index.
A nonzero-index old component has a local continuation obligation, but the spanning
component may move horizontally inside the entire old Nash component before
the entrant appears.  A usable theorem would still have to preserve a chosen
actual source or charge that horizontal displacement.  No such index-to-source
adapter is presently supplied.

### Proposition 22.2 (every actual re-equilibration has macroscopic work)

Assume \(D_*>0\).  For every old-menu Nash equilibrium \(p\) and every actual
expanded-menu Nash equilibrium \(q\), with \(p\) lifted by zero entrant mass,

\[
 \sum_i\operatorname{TV}(p_i,q_i)\ge {D_*\over16R}. \tag{22.5}
\]

In particular every arrow of \(\mathcal R_{A,e}\) has this displacement.  At
the first entrant point of a spanning component, the shadow price is at least
\(D_*/4\); along the positive-entry side its prescribed reached entrant atom
is at least

\[
 {D_*\over8R}\,x_i(e).                              \tag{22.6}
\]

These are genuine transition-work lower bounds, but neither telescopes.
Total variation is a metric displacement rather than a bounded monotone
potential, while the artificial price is reset to \(K\) for every new entrant.
Moreover \(x_i(e)\) may tend to zero, so the actual probability in (22.6) may
be summable.  Thus the existing shadow-price account does not rule out an
infinite operator orbit.

**Proof.**  Equation (22.5) is Theorem 16.1(3), applied to the two parameter
faces.  The first-entry price and reached-atom statements are Theorem
16.1(4).  The final assertions follow because neither right-hand side is the
decrease of a state function, and (22.6) has no positive lower bound
independent of the entrant mass.  \(\square\)

### Theorem 22.3 (strong recurrence would solve; weak recurrence is singular)

Use the exhaustive prefix menus

\[
 A_N=\{0,1,\ldots,N-1,\mathsf{Never}\}
\]

and let \(p^N\in\operatorname{NE}(A_N)\), whether selected by spanning
components or otherwise.  Under \(D_*>0\):

1. the sequence has no total-variation convergent subsequence;
2. after passing to a subsequence there is one fixed player \(i\) such that

   \[
   r_i(\{i\})\prod_{j\ne i}p_j^N(\mathsf{Never})
      \ge D_*/4;                                    \tag{22.7}
   \]

3. after also taking a weakly convergent source subsequence, in the weak
   one-point compactification the new response
   \(\delta_N\) converges to \(\delta_{\mathsf{Never}}\), but censoring those
   two actions loses the payoff difference in (22.7).  Hence the
   response-payoff data have a jump of at least \(D_*/4\) along this
   subsequence, and Nash inequalities cannot be passed through this weak
   identification.

**Proof.**  If \(p^{N_k}\to p\) in total variation, then for every fixed
finite pure clock \(t\), the \(t\)-deviation Nash inequality belongs to every
sufficiently large menu.  Terminal payoff and the payoff of that fixed
deviation are continuous in product total variation, so the inequality passes
to \(p\).  The Never inequality passes in the same way.  Pure-time extremality
then controls every behavioral deviation, making \(p\) an unrestricted
terminal Nash profile, contrary to \(D_*>0\).  This proves part 1.

For each \(N\), old-menu Nash controls Never and every time below \(N\).
Against opponents supported in \(A_N\), all finite times at or after \(N\)
have one common payoff.  Selecting a maximum-debt player gives the checked
finite-deadline escape bound; stabilization among four identities yields
(22.7).  Finally \(\delta_N\Rightarrow\delta_{\mathsf{Never}}\), while the
exact late-Quit-versus-Never identity says that their payoff difference
against \(p^N_{-i}\) is the left side of (22.7).  Thus identifying the new
clock with Never destroys a response inequality by at least \(D_*/4\), which
proves part 3.  \(\square\)

There is no payoff-preserving finite-clock translation that avoids this
boundary.  Indeed, an order-preserving injection sending the entrant \(N\) to
one fixed finite rank \(K_0\) would have to place the \(N+1\) distinct clocks
\(0,\ldots,N\) into the \(K_0+1\) ranks below \(K_0\), impossible for
\(N>K_0\).  Translating into negative times instead loses the common date-zero
source needed for chronological concatenation.

### Exact operator verdict

At fixed menu size, source re-equilibration has a compact exact graph and
full Nash guards at its bottom face.  What fails is precisely what the
infinite guarded schedule needs:

* Browder continuation is not anchored at every supplied old equilibrium;
* actual expanded equilibria are a fixed total-variation distance from the
  entire old Nash face;
* no bounded monotone work account is carried by that displacement; and
* the only automatic compact recurrence is weak recurrence, where positive
  \(D_*\) forces the macroscopic Late/Never payoff jump (22.7).

Thus an infinite serial component orbit, even if separately proved, would not
compile by compact recurrence.  A successful version needs one genuinely new
field: either a source-anchored nonzero-index continuation with a telescoping
potential, or a tight/summable censor seam.  The latter is already consumed
by Theorem 21.1 and contradicts \(D_*>0\).

## 23. Finite-length global carriers and degree at infinity

Although Proposition 22.1 rules out continuation from an arbitrarily
prescribed equilibrium, Browder continuation can be applied once to an entire
finite sequence of strategy entries.  This gives a global finite carrier, but
not yet a renewable chain of adjacent source-matched components.

Fix \(m\ge1\) and work in the single finite action simplex

\[
 A_m=\{0,1,\ldots,m-1,\mathsf{Never}\}.
\]

For \(t\in[0,m]\), give clock \(n<m\) the penalty

\[
 \kappa_n(t)=
 \begin{cases}
 K,&t\le n,\\
 K(n+1-t),&n\le t\le n+1,\\
 0,&n+1\le t.
 \end{cases}                                       \tag{23.1}
\]

Never is unpenalized.  At integer \(t=n\), the clocks \(n,\ldots,m-1\)
are strictly dominated by Never, so the equilibrium set is exactly the
zero-padded copy of \(\operatorname{NE}(A_n)\).

### Theorem 23.1 (arbitrarily long global component carrier)

For every finite \(m\), the Nash graph of (23.1) has a compact connected
semialgebraic component \(C^{(m)}\) whose parameter projection is all of
\([0,m]\).  In particular, for every integer \(0\le n\le m\), its slice
contains a zero-padded exact equilibrium

\[
 p^{m,n}\in\operatorname{NE}(A_n).                 \tag{23.2}
\]

**Proof.**  On the fixed simplex \(A_m\), the standard Nash map varies
continuously with \(t\).  Rescale \([0,m]\) to the unit interval and apply
Browder's theorem.  The resulting fixed-point component projects onto the
whole interval.  At integer \(n\), strict domination of all future clocks
identifies its slice with literal equilibria of \(A_n\).  The Nash graph is
semialgebraic, hence so is each of its finitely many connected components.
\(\square\)

The theorem does **not** imply a source-matched adjacent chain.  A path inside
\(C^{(m)}\) may fold in the parameter, leave and re-enter the same slab, and
meet the face \(t=n\) at different equilibria before it reaches \(t=n+1\).
Connectedness and surjective projection do not give a continuous section.
Equivalently, after cutting \(C^{(m)}\) into slab components, the finite
adjacency path from the first face to the last may backtrack through earlier
slabs.  Therefore the integer points in (23.2) cannot be chosen from the
current theorem so that one single-strategy component has the same bottom
point as the next component's top point.  The tempting König argument fails
because arbitrarily long *global* carriers do not produce arbitrarily long
monotone compatible words of slab components.

### 23.2 What equilibrium index adds

For a finite game the indices of all equilibrium components sum to one.
At \(t=n\), adding the future clocks with penalty \(K>2R\) adds only strictly
dominated, hence redundant, strategies.  The finite-game index is invariant
under that padding.  Homotopy invariance therefore carries total degree one
through every finite construction (23.1).

The stronger component theorem one would need is:

> **No-cancellation carrier.**  One may choose the components in Theorem 23.1
> so that each common integer-face equilibrium component has nonzero index,
> and the same nonzero local degree is carried through the next slab.

Standard index invariance does not imply this statement.  A connected
component of the full parameterized equilibrium graph may meet several
components on one parameter face.  Their signed indices can cancel before
the graph reaches the other face.  What homotopy preserves is the aggregate
index in an isolating neighborhood, not the identity or nonzero index of each
constituent component.  At a slab seam, the bottom nonzero component chosen by
one carrier may belong to a different cancellation cluster for the next
entrant.

The one-new-clock structure does not make this elementary.  On a fixed
support face the Nash complementarity equations are polynomial and the
penalty is affine, but support changes join those faces and permit exactly the
branch mergers on which index cancellation occurs.  Quitting rewards impose
order restrictions on the timing payoffs but no potential or sign rule for
the Jacobian of this four-player complementarity system.  An oriented version
would therefore require the full fixed-point-index/degree machinery plus a
new proof that the relevant boundary faces carry no canceling degree.

### Proposition 23.2 (the finite degree carrier escapes at infinity)

Assume \(D_*>0\).  For every deadline \(N\), choose any equilibrium from a
nonzero-index component of the finite timing game \(A_N\); such a component
exists because the total index is one.  Then no such sequence has a
total-variation convergent subsequence, while after weak subsequence selection
it satisfies the fixed-payer boundary estimate (22.7).

Thus nonzero finite-game degree does not disappear as clocks are added.  It
escapes every total-variation compact subset and accumulates on the split
Late/Never boundary.  In the unsplit one-point clock compactification the two
boundary actions are identified even though their payoff difference remains
at least \(D_*/4\).  This is the precise degree-at-infinity contribution
forced by the positive-gap branch.

**Proof.**  Existence of a nonzero-index component is the total-index-one
identity.  Every selected point is still an exact finite-deadline Nash
profile, so Theorem 22.3 applies verbatim.  \(\square\)

Theorem 23.1 is the strongest elementary global component carrier presently
available.  Proposition 23.2 shows why adding the index label alone does not
close the game: a compiler must either turn the degree-at-infinity boundary
into an actual Late strategy (impossible in the original game) or pair its
macroscopic \(D_*/4\) payoff jump with a source-attached absorbing block.

Additional sources inspected:

* `formalized/FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md`;
* `formalized/FIN4_STRICT_MINIMUM_PLATEAU_RESTART_MOAT.md`;
* `formalized/UNBOUNDED_FINITE_HAZARD_CAPACITY_COMPILER.md`;
* `formalized/CUMULATIVE_CHARGE_NEAR_RETURN_AND_SUMMABLE_PORT.md`; and
* `questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md`.

Literature boundary checked:

* Eilon Solan and Omri N. Solan, *Browder's Theorem through Brouwer's Fixed
  Point Theorem* (Theorem 1.1): a parameterized continuous self-map of a
  finite cube has **some** fixed-point component projecting onto the whole
  parameter interval.  It does not prescribe either endpoint.
* Srihari Govindan and Robert Wilson, *Equivalence and Invariance of the Index
  and Degree of Nash Equilibria*, Games and Economic Behavior 21 (1997),
  56--61, DOI `10.1006/game.1997.0516`: component index equals local degree
  and is invariant under adding or deleting redundant strategies.  This
  justifies the strictly dominated padding at the integer faces; it does not
  supply the no-cancellation carrier across the large penalty homotopy.

## 24. Exact vertical-fibre regression for one strategy entry

The absence of a continuous section in Section 23 is not merely a possible
pathology of general finite games.  It occurs in a two-active-player quitting
timing game after one literal pure-time strategy is added to one player.

Consider four players.  Players 3 and 4 have the singleton restricted menu
`Never`.  Player 2 has the restricted menu

\[
 \{Q_1,\mathsf{Never}\},
\]

while player 1 initially has only `Never` and is offered the entrant (Q_1)
with artificial cost \(\kappa\in[0,3]\).  The only reward coordinates relevant
on these menus are

\[
 r_1(\{1,2\})=1,\qquad r_1(\{2\})=0,
\]

and

\[
 r_2(\{2\})=r_2(\{1,2\})=1,\qquad r_2(\{1\})=0.
                                                        \tag{24.1}
\]

Set every other reward coordinate to zero.  Subtract \(\kappa\) from player
1's payoff whenever player 1 chooses (Q_1).  All unpenalized rewards lie in
\([0,1]\), so the initial penalty (K=3) is larger than twice the payoff
width.

### Proposition 24.1 (vertical fibre and failure of continuous selection)

The complete Nash correspondence of the penalized restricted game is

\[
 \begin{cases}
  \{(Q_1,Q_1,\mathsf{Never},\mathsf{Never})\},&0\le\kappa<1,\\[2mm]
  \{(xQ_1+(1-x)\mathsf{Never},Q_1,
       \mathsf{Never},\mathsf{Never}):0\le x\le1\},&\kappa=1,\\[2mm]
  \{(\mathsf{Never},Q_1,\mathsf{Never},\mathsf{Never})\},&1<\kappa\le3.
 \end{cases}                                           \tag{24.2}
\]

Consequently its graph is one compact connected semialgebraic component
projecting onto the whole penalty interval, but there is no continuous map

\[
 s:[0,3]\longrightarrow\prod_i\Delta(A_i)
 \quad\hbox{with}\quad s(\kappa)\in\operatorname{NE}(G_\kappa)
                                                        \tag{24.3}
\]

for every \(\kappa\).

**Proof.**  For player 2, (Q_1) gives payoff one whether player 1 chooses
(Q_1) or Never.  Player 2's Never gives payoff zero in either case.  Thus
(Q_1) is strictly dominant for player 2.  Against that action, player 1's
entrant gives (1-\kappa), while Never gives zero.  Therefore player 1
uniquely chooses the entrant below \(\kappa=1\), uniquely chooses Never above
\(\kappa=1\), and may use every mixture at equality.  This proves (24.2).

If a continuous selection existed, its player-1 coordinate would equal
\(\delta_{Q_1}\) on \([0,1)\) and \(\delta_{\mathsf{Never}}\) on \((1,3]\).
Its two one-sided limits at one are distinct, a contradiction.  \(\square\)

### Exact consequence for the component route

The example is a literal quitting-payoff game, not an arbitrary bimatrix
embedding.  It shows that neither chronology nor the one-strategy-entry form
provides the implicit-function/Jacobian sign needed to turn a Browder
component into a continuous point continuation.  The obstruction is exactly
a macroscopic horizontal motion inside one penalty fibre.  Aggregate degree
can pass through that fibre, but it does not choose a source-coherent point or
charge the horizontal displacement.

This does not disprove a stronger set-valued component compiler equipped with
an independent way to consume vertical-fibre motion.  It does disprove the
specific no-fold claim needed to renew the Section 23 construction by
continuous equilibrium sections.  Since the current Fin4 route has no
consumer for an uncharged same-parameter reshuffle, point/component
continuation is abandoned here rather than importing more general index
machinery.
