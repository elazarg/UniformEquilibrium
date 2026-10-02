# Cross-audit of exposure-aware singleton disintegration

Reviewer: `NOTE_MINING_STRENGTHENER`

## Claim audited

The proposed connection combines:

- the anchored deterministic-clock disintegration and Jensen dichotomy in
  `CODEX_JOULE__JENSEN_ACTIVE_PASSPORT_DICHOTOMY.md`; and
- the exposure/payoff selection and high/low polarity in
  `STRENGTHENER__JOINT_EXPOSURE_INCENTIVE_SELECTION.md`.

The hoped-for conclusion is either a response square co-localized with a
mass-good singleton clock, or a renewable minimum-source transition obtained
from the adverse high/low-exposure chord.

## Verdict

The connection is mathematically well motivated, but it is not presently a
consumer of the concentrated-singleton node.  There are two rigorous
strengthenings:

1. any separated response square can be affinely anchored to a mass-good
   completion with exact quantitative control; and
2. any mass-good completion can be radially reattached to the near-minimum
   source, producing a normalized marked-incidence tangent family.  In the
   flat-total-slope arm, the checked common-response compiler then computes
   every nonowner cap displacement with error small relative to the tangent
   scale.

Neither strengthening proves a terminal consumer or a renewable rank.  The
first exposes a mass-versus-response-regret tradeoff which the stated data do
not improve.  The second lands in the already open positive-slope or
flat-tangent atlas arms.

There is also an important correction to the proposed missing lemma:

> Localizing positive cap curvature between mass-good completions is not by
> itself enough to invoke the current minimum-response-chord consumer.

That consumer requires the relevant endpoint and response limits to lie on
the global minimum-total-debt fibre.  The Jensen square controls only the
selected outsider's response regret.  It gives no upper bound on the other
three coordinates' cap leakage and hence no minimum-fibre conclusion for
either response endpoint.

Accordingly this connection does **not** pass the export gate.  The smallest
remaining bridge is a cross-coordinate leakage theorem which either places
the selected response endpoints on the minimum fibre or turns their strict
ascent into a renewable source transition.

## 1. Source audit

The following facts used below are checked.

- Complete stopping-law mixing is affine for chronological stage masses,
  terminal laws, prescribed payoffs, and every fixed unilateral response:
  `quittingStageCoalitionMass_stoppingLawMixture_eq`,
  `quittingTerminalOutcomeMass_stoppingLawMixture_eq`, and
  `quittingTerminalPayoff_stoppingLawMixture_eq` in the stopping-law mixture
  and debt-convexity modules.
- Every semantic-debt coordinate is convex along such a mixture:
  `quittingTerminalSemanticDebt_stoppingLawMixture_le`.
- A common approximate response at two endpoints quantitatively controls the
  intervening cap kink:
  `quittingContinuationBestResponseValue_stoppingLawMixture_chordGap_le_of_commonApproxWitness`
  in `Research/Quitting/StoppingLawMixtureWitnessStrata.lean`.
- If both sides of a one-player seam approach the same global minimum total
  debt, one pure time is simultaneously asymptotically optimal at both sides:
  `nonempty_stoppingLawCommonPureTimeCompiler_of_minimumFiber` and
  `QuittingStoppingLawCommonPureTimeCompiler.capDifference_sub_responseDifference_tendsto_zero`
  in
  `Research/Quitting/StoppingLawMinimumFiberCommonResponseCompiler.lean`.
- The checked minimum response-chord structure
  `FinFourMinimumResponseRectanglePacket` explicitly assumes both
  `endpoint_debtSum_eq_source` and `response_debtSum_eq_source`.
  `FinFourMinimumResponseRectangleSequence.strictResponseAscent_or_compiledRectangle`
  returns a strict response ascent when the second equality is unavailable;
  it does not consume that ascent.
- `QuittingMinimumResponseChordLaw.chord_debt_eq_affine` and its support
  consequences apply only after the endpoint-minimum and response-fibre
  hypotheses have been supplied.
- `FinFourStrongConcentratedPacketConsumerResult` still has the unresolved
  `QuittingConcentratedCollisionMinimumResidual` arm.  Manufacturing another
  marked paid row or another strong concentrated packet is therefore not a
  terminal consumer.

The two source notes and both of their earlier reviews correctly state their
own limitation: owner debt is controlled, while the other players' complete
behavioral caps are not.

## 2. Exact mass anchoring of a separated response square

This is the strongest unconditional co-localization available from affinity
and the reward bound alone.

Fix one rank and suppress it from the notation.  Let `j` be the owner whose
stopping law is disintegrated and let `i != j` be the selected outsider.  Let
`P_h`, `P_s`, and `P_t` be deterministic-clock completions, all with the same
opponents and copied outer prefix.  Assume that at date `h`,

\[
 \Pr_{P_h}(\{j\}\text{ terminal at }h)\ge m_0>0.
 \tag{2.1}
\]

Let `q^-` and `q^+` be two complete pure-time responses of `i`, including
`Never`, and put

\[
 f_u=U_i(P_u[i\leftarrow q^+])-U_i(P_u[i\leftarrow q^-]).
 \tag{2.2}
\]

Assume

\[
 f_t\ge g,
 \qquad f_t-f_s\ge g,
 \qquad g>0,
 \tag{2.3}
\]

and

\[
 d_i(P_t[i\leftarrow q^+])\le\varepsilon,
 \qquad
 d_i(P_s[i\leftarrow q^-])\le\varepsilon.
 \tag{2.4}
\]

Suppose `0<=R` and all rewards have absolute value at most `R`.  For
`0<rho<1`, form
the actual owner-law mixtures

\[
 T_\rho=\rho P_h+(1-\rho)P_t,
 \qquad
 S_\rho=\rho P_h+(1-\rho)P_s.
 \tag{2.5}
\]

Here the notation means complete stopping-law mixing of player `j`; it is an
actual behavioral profile and retains the common copied prefix and every
opponent.

Then:

\[
 \Pr_{T_\rho}(\{j\}\text{ terminal at }h),
 \Pr_{S_\rho}(\{j\}\text{ terminal at }h)
 \ge \rho m_0,
 \tag{2.6}
\]

\[
 \bigl(f_{T_\rho}-f_{S_\rho}\bigr)
 =(1-\rho)(f_t-f_s)\ge(1-\rho)g,
 \tag{2.7}
\]

and

\[
 f_{T_\rho}=\rho f_h+(1-\rho)f_t
 \ge (1-\rho)g-2R\rho.
 \tag{2.8}
\]

Finally, coordinatewise debt convexity gives

\[
 d_i(T_\rho[i\leftarrow q^+]),
 d_i(S_\rho[i\leftarrow q^-])
 \le 2R\rho+(1-\rho)\varepsilon.
 \tag{2.9}
\]

### Proof

Equation (2.6) is exact stage-mass affinity; the unlisted endpoint
contribution is nonnegative.  Fixed-response payoff affinity and commutation
of the `i` and `j` replacements give (2.7) and the equality in (2.8).  Since
each response payoff lies in `[-R,R]`, `f_h>=-2R`, proving the last inequality
in (2.8).  Applying coordinatewise debt convexity after fixing `q^+` or
`q^-`, then using `0<=d_i<=2R`, proves (2.9).

For the mass-good floor in the Jensen note, `m_0=mu/2`.  Choosing

\[
 \rho_0={g\over 2(g+2R)}
 \tag{2.10}
\]

gives

\[
 \text{marked mass}\ge {\mu g\over4(g+2R)},
 \qquad
 f_{T_{\rho_0}}\ge {g\over2},
 \qquad
 f_{T_{\rho_0}}-f_{S_{\rho_0}}\ge {g\over2}.
 \tag{2.11}
\]

The constants use only the displayed data.  The worst allowed base response
difference `f_h=-2R` attains the receiving-gain tradeoff in (2.8), so a better
universal mass/gain coefficient requires additional strategic information at
`P_h`.

### Exact limitation

At fixed positive `rho`, the available bound (2.9) leaves an order-`rho`
endpoint regret.  Sending `rho` to zero makes that bound vanish but also
sends the retained marked mass in (2.6) to zero.  More importantly, (2.6)
concerns the two unresponded
base profiles.  A response `q^-` or `q^+` may preempt date `h`, so there is no
unconditional marked-mass floor at the response endpoints.

Thus this anchoring lemma does not construct a
`FinFourMinimumResponseRectanglePacket`.  It is a precise quantitative
version of the still-missing co-realization, not its solution.

## 3. Radial reattachment to the minimum source

There is a second rigorous composition which avoids fixed endpoint regret at
the cost of working at a vanishing scale.

Let `sigma_n` be the source profiles with

\[
 D(\sigma_n)=D_*+e_n,
 \qquad e_n\to0,
 \tag{3.1}
\]

and choose any mass-good completion `P_{n,h_n}`.  Let `lambda_n>0` tend to
zero and form

\[
 R_n=(1-\lambda_n)\sigma_n+\lambda_nP_{n,h_n}
 \tag{3.2}
\]

by mixing only the owner's complete stopping law.  In Fin4, if rewards are
bounded by `R`, then `D<=8R`; hence

\[
 D(R_n)-D_*\le e_n+8R\lambda_n.
 \tag{3.3}
\]

At the selected date,

\[
 \Pr_{R_n}(\{j\}\text{ terminal at }h_n)
 \ge \lambda_n\mu/2.
 \tag{3.4}
\]

After a subsequence one may choose `lambda_n` with
`e_n/lambda_n -> 0` and extract every normalized debt coordinate.  Indeed,
both the prescribed payoff and the behavioral cap are `2R`-Lipschitz in the
mixture weight, so each normalized debt change is bounded in absolute value
by `4R`.  This gives an actual source-attached radial tangent passport
carrying normalized marked incidence at least `mu/2`.

For every nonowner `i`, the quantitative common-response theorem gives a pure
time whose regret at both `sigma_n` and `R_n` is at most

\[
 2\bigl(\operatorname{SeamExcess}_n+\epsilon_n\bigr).
 \tag{3.5}
\]

If in addition the radial direction is flat,

\[
 {D(R_n)-D(\sigma_n)\over\lambda_n}\longrightarrow0,
 \tag{3.6}
\]

then the seam excess is `o(lambda_n)`.  Taking
`epsilon_n=o(lambda_n)` makes the common-response regrets
`o(lambda_n)`.  The same pure response therefore computes the true
nonowner cap displacement with vanishing **normalized** error.

If (3.6) fails positively and the owner belongs to the incoming positive-debt
support, the radial family enters the checked positive-total-slope tangent
machinery.  The latter supplies a source-matched endpoint/atom passport, but
explicitly no return or contradiction.  If the owner is inactive, a positive
radial slope is instead a support-entry/ascent datum; the active-mover
positive-slope theorem must not be applied to it.  If (3.6) holds, the flat
tangent still requires the existing support-entry/no-entry and regeneration
consumers.

This is the strongest rigorous synthesis I found:

```text
mass-good completion
  -> source-attached radial tangent with normalized marked incidence
  -> positive total slope
       or flat seam with common all-behavior cap witnesses.
```

It does not strictly contract
`questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md`; both outputs are live atlas
obligations.  The positive-minimum hypothesis is used to orient the tangent,
but it does not force the radial slope to be positive.  Convex functions can
be flat near an interior minimum and rise only later along the same segment.

## 4. Exact Jensen localization by exposure strata

The outsider Jensen curvature admits a useful exact decomposition, but it
also shows why localization is not automatic.

Let `G` be the mass-good clocks, `w=alpha(G)`, and, when `0<w<1`, let `H` and
`L` be the owner-law mixtures conditional on `G` and its complement.  For one outsider
`i`, write `B` for its complete behavioral cap and

\[
 J^G_i=\mathbb E_G B(P_t)-B(H),
 \qquad
 J^L_i=\mathbb E_L B(P_t)-B(L),
 \tag{4.1}
\]

\[
 K_i=wB(H)+(1-w)B(L)-B(\sigma).
 \tag{4.2}
\]

Fixed-response affinity and cap convexity give

\[
 \boxed{J_i=wJ^G_i+(1-w)J^L_i+K_i,}
 \qquad J^G_i,J^L_i,K_i\ge0.
 \tag{4.3}
\]

Consequently a fixed positive `J_i` has one of three locations:

1. witness switching within the mass-good class;
2. witness switching entirely within the mass-poor class; or
3. witness switching across the conditional high/low chord.

If `wJ^G_i` carries a fixed share, the independent-pair Jensen argument from
the source note may be rerun under the conditional law on `G`.  It then
selects both deterministic clocks in `G`, with the same response-square and
endpoint-regret conclusions.  This is a valid sufficient condition for
mass-good localization.

Nothing in global convexity forces the first term to be positive.  In the
two-date matching regression, `G` can be a singleton, so `J^G_i=0`, while the
entire curvature is the between-block term `K_i`.  More generally, curvature
can live in the mass-poor block.  The sharp exposure/payoff selection theorem
controls the owner's payoff on the high/low chord; it imposes no sign or
smallness condition on the outsider terms in (4.3).

If `w=1`, the low and between-block terms disappear and the curvature is
entirely within `G`; this is the harmless boundary case in which conditional
mass-good localization is immediate.

This decomposition is a useful Lean-level diagnostic because it turns the
informal word "localize" into a finite exhaustive split.  It still has no
consumer for alternatives 2 and 3.

## 5. The smallest cross-coordinate lemma

For a profile `P`, outsider `i`, and response `q`, define the other-coordinate
leakage

\[
 L_i(P,q)=\sum_{k\ne i}\bigl(d_k(P[i\leftarrow q])-d_k(P)\bigr).
 \tag{5.1}
\]

If `q` is `epsilon`-optimal, own-cap invariance gives

\[
 D(P[i\leftarrow q])-D_*
 =D(P)-D_*-d_i(P)+d_i(P[i\leftarrow q])+L_i(P,q).
 \tag{5.2}
\]

Global minimality supplies only the lower bound

\[
 L_i(P,q)
 \ge d_i(P)-(D(P)-D_*)-\epsilon.
 \tag{5.3}
\]

The missing information is the reverse inequality, to vanishing error, at
the response endpoints selected by the square:

\[
 L_i(P,q)
 \le d_i(P)-(D(P)-D_*)+o(1).
 \tag{5.4}
\]

Equations (5.2)--(5.4) put the response endpoint on the minimum fibre.  If
they hold at both relevant corners, the existing minimum-response-chord
compiler can be invoked.  If (5.4) fails by a fixed amount, the response
endpoint is a strict ascent; what is required instead is a source-preserving
renewable transition consuming that ascent.

Thus a precise sufficient missing theorem is:

```text
source-attached mass-good separated response square
  -> minimum-fibre response endpoints satisfying (5.4)
     or a complete regenerated strict-ascent child with a decreasing
        natural-valued rank and backward compiler.
```

This is strictly stronger, and more accurate, than merely asking that the
two owner clocks belong to `G`.

## 6. Why current convexity and minimum-fibre results do not supply it

1. `quittingTerminalSemanticDebt_stoppingLawMixture_le` controls a mixture
   by its endpoints.  It does not upper-bound an endpoint after a different
   player changes strategy.
2. `quittingTerminalSemanticDebt_stoppingLawMixture_eq_chord_of_minimumFiber`
   proves affinity only after the second endpoint is already known to lie on
   the minimum fibre.  Using it to prove (5.4) would be circular.
3. The common-response compiler controls cap displacement only when both
   sides of the seam are near the same minimum.  The mass-good deterministic
   components in the separated Jensen arm are explicitly bounded away from
   that fibre.  Its relative `o(lambda)` form becomes available only in the
   flat radial construction of Section 3.
4. The response-chord law derives support union and strict support loss only
   after both endpoint debt sums equal the minimum.  Its actual decoder
   explicitly retains a `strictResponseAscent` alternative otherwise.
5. The renewable support-drop theorem requires a minimum-fibre endpoint,
   flatness, no support entry, and full-replacement provenance.  The Jensen
   or high/low chords supply none of those conditions automatically.
6. Global minimality points in the wrong direction for leakage control: it
   proves (5.3), not (5.4).  The fixed owner gain in the adverse exposure arm
   therefore forces compensating debt transfer rather than descent.

The checked witness-switch kink in
`StoppingLawMixtureWitnessStrata.lean`, the two-date matching regression in
the Jensen note, and the equality regression in the exposure-selection note
all test the same boundary.  They have `D_*=0`, so they do not rule out a new
theorem using positive minimum debt and hard-residual geometry.  They do rule
out deriving (5.4) from stopping-law affinity, two moment identities, or cap
convexity alone.

## 7. Lean handoff for the valid partial results

The mass-anchoring result can be packaged without a new quitting-game
structure.  A suitable theorem surface is:

```text
theorem quittingResponseSquare_anchor_mass_gain_and_debtBounds
    (rewardBound : every reward coordinate has absolute value at most R)
    (owner_ne_observer : owner is distinct from observer)
    (massGood : m0 <= stageMass endpointHigh mark singleton)
    (receive : g <= responseDiff endpointTarget qMinus qPlus)
    (cross : g <= responseDiff endpointTarget qMinus qPlus -
      responseDiff endpointSource qMinus qPlus)
    (targetRegret : debt after qPlus at endpointTarget <= eps)
    (sourceRegret : debt after qMinus at endpointSource <= eps)
    (rho_pos : 0 < rho) (rho_lt_one : rho < 1) :
  -- exact stage-mass, cross-difference, receiving-gain, and endpoint-debt
  -- inequalities (2.6)--(2.9)
```

Its proof should use only the checked stage-mass/payoff affinity and debt
convexity declarations named above.

The curvature split should first be formalized as an abstract finite or
countable convex-envelope identity:

```lean
theorem jensenGap_eq_high_within_add_low_within_add_between
```

and then specialized to stopping-law caps.  A conditional producer

```lean
theorem exists_massGood_responseSquare_of_restrictedJensenGap
```

is valid, but should state only the square and response-regret data.  It must
not claim minimum endpoints or a response-chord consumer.

For radial reattachment, the useful theorem surface is:

```lean
theorem massGoodCompletion_exists_radialTangentPassport
```

retaining the literal source, selected completion/date, scale, normalized
stage-mass floor, total-debt slope, and—conditional on zero total slope—the
common pure-time response compilers.  It should conclude with the explicit
positive-slope/flat split, not with a uniform-equilibrium or rank claim.

No new Lean theorem should encode (5.4) as a structure field and then call
the resulting conditional wrapper a producer.  Equation (5.4), or the
strict-ascent renewable alternative, is the mathematical work still missing.

## 8. Gate conditions

### PASS as an internal connection

- Keep the exact mass-anchoring theorem (2.6)--(2.9).
- Keep the radial normalized-incidence construction and its honest
  positive-slope/flat split.
- Keep the Jensen curvature-strata identity (4.3).
- State explicitly that all-behavior caps are used and that `Never` remains
  in the response class.
- Replace "mass-good response square feeds the response-chord consumer" by
  the stronger minimum-endpoint or strict-ascent alternative in Section 5.

### FAIL for export or for answering the concentrated-singleton question

- Merely selecting both owner clocks in the mass-good set.
- Producing another fixed marked paid row or strong concentrated packet.
- Using owner-debt control as an upper bound on total debt.
- Applying minimum-fibre affinity before proving both endpoint debt sums are
  minimal.
- Calling the radial positive-slope or flat-tangent split a finite-rank
  contraction without a consumer.
- Treating the conditional response-chord compiler as a producer of (5.4).

### PASS for a future export

Prove either:

1. the leakage upper bound (5.4) at the two source-attached response
   endpoints, with the retained marked-law data needed by the existing
   response-chord compiler; or
2. a complete source-preserving consumer of the strict response-ascent arm,
   with a renewable natural-valued rank and backward compiler.

Either result would make this connection a strict conjecture-facing advance.
