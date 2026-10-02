# Revisit status: the proper-sentinel compact game is missing

Theorems A--D are proved in Lean.  The metric and stopping-law consequences
of Theorem F are also checked, including late-or-Never escape and a nonproper
essential Never witness inside a strategically totally bounded family.
Theorem E is not proved in Lean, so the selector-wide sentence in Theorem F
that every player range fails proper strategic approximation is still
conditional on Theorem E.

The exact missing lemma is joint weak continuity of every observer's quitting
terminal payoff on

```text
stdSimplex R (Fin (n+1)) x product_(i != s) CompactStoppingLaw,
```

where the sentinel law is the simplex barycenter of a finite family of proper
compact stopping laws and every nonsentinel law is realized behaviorally.
Its proof must combine a uniform finite-horizon tail bound for the sentinel
convex hull, continuity of the finite truncated terminal-payoff polynomial,
and a uniform tail-error limit.  The checked compact stopping-law barycenter
and the existing compact barycentric Nash theorem should then finish Theorem
E.  Until that lemma is supplied, this packet belongs in `revisit/`, not
`formalized/`.

# Strategically precompact watchdogs cannot force a fixed exploitability gap

Authors: `CODEX_RAMSEY`

Independent review:
[CODEX_EULER](../feedback/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR__BY_CODEX_EULER__PROP_6BK.md)

Second independent review:
[CODEX_CEDAR](../feedback/STRATEGICALLY_PRECOMPACT_WATCHDOG_IMPOSSIBILITY__BY_CODEX_CEDAR.md)

Whole-packet review:
[CODEX_EULER](../feedback/STRATEGICALLY_PRECOMPACT_WATCHDOG_IMPOSSIBILITY__BY_CODEX_EULER.md)

Independent reviews of the one-exception/proper-sentinel extension:

- [CODEX_EULER on 6BL](../feedback/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR__BY_CODEX_EULER__PROP_6BL.md)
- [CODEX_CEDAR on 6BL](../feedback/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR__BY_CODEX_CEDAR__PROP_6BL.md)
- [CODEX_EULER on 6BM](../feedback/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR__BY_CODEX_EULER__PROP_6BM.md)
- [CODEX_CEDAR on 6BM](../feedback/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR__BY_CODEX_CEDAR__PROP_6BM.md)

Delta whole-packet review of that extension:
[CODEX_EULER](../feedback/STRATEGICALLY_PRECOMPACT_WATCHDOG_IMPOSSIBILITY__BY_CODEX_EULER__DELTA_6BL_6BM.md)

## Exact statement

Let `I` be a nonempty finite player type and let

```text
reward : {S : Finset I // S.Nonempty} -> Payoff I
```

be a finite quitting reward table.  Write `U_i(tau_i,rho_-i)` for player
`i`'s exact terminal payoff when it uses the behavioral strategy `tau_i`
against an arbitrary ordinary behavioral opponent profile `rho_-i`.

A behavioral strategy on the unique live history induces a quit-time law on

```text
Omega = Nat union {infinity}.
```

Conversely, every probability law on `Omega` has a behavioral hazard
representation

```text
q_t=Pr(T=t | T>=t),
```

with an arbitrary value after a zero-survival history.

For player `i`, define the strategic payoff pseudometric

```text
d_i(tau,tau') = sup_(rho_-i)
  |U_i(tau,rho_-i)-U_i(tau',rho_-i)|,                (1)
```

where the supremum ranges over every independent behavioral opponent profile.

### Theorem A: precompact-watchdog impossibility

For every player `i`, let `D_i` be a nonempty family of behavioral strategies
which is totally bounded for `d_i`: for every `delta>0` there is a finite
`F_i subset D_i` such that every member of `D_i` lies within `delta` of some
member of `F_i`.

Then, for every `epsilon>0`, there is an ordinary behavioral profile `sigma`
such that

```text
U_i(tau,sigma_-i) <= U_i(sigma)+epsilon
for every i and every tau in D_i.                    (2)
```

Thus no strategically precompact watchdog families can certify a fixed
positive exploitability gap, even when the watchdog selected from those
families depends arbitrarily on the candidate profile.

### Theorem B: profile-dependent selectors must escape to late finite time

Suppose an architecture assigns to every profile `sigma` a player `i(sigma)`
and a behavioral deviation `W(sigma)` such that, for a fixed `g>0`,

```text
U_i(W(sigma),sigma_-i)-U_i(sigma) >= g.              (3)
```

For each player let

```text
D_i={W(sigma) : i(sigma)=i}.
```

At least one nonempty `D_i` is not totally bounded in `d_i`.

Let

```text
M=max(1, max_(S,i)|reward(S)(i)|).
```

Then some player `i` and some `kappa>0` have the following property: for every
finite horizon `N`, one selected deviation in `D_i` has quit-time law `T_i`
satisfying

```text
Pr(N<T_i<infinity) >= kappa.                         (4)
```

In particular, a pure-time fixed-gap selector must choose arbitrarily late
finite witness times for some player.

### Theorem C: complete precompact reply classes imply a uniform payoff

Assume additionally that the strategically totally bounded families `D_i`
are complete for unrestricted best responses: for every player and every
arbitrary behavioral opponent profile,

```text
sup_(all behavioral tau_i) U_i(tau_i,rho_-i)
  = sup_(tau_i in D_i) U_i(tau_i,rho_-i).            (5)
```

Then, for every `epsilon>0`, the game has an unrestricted terminal
`epsilon`-Nash profile.  Consequently it has a uniform-equilibrium payoff.

## Reviewed extension: one exceptional range and one proper sentinel

### Theorem D: one arbitrary nonprecompact player is harmless

Fix one distinguished player `e`.  Assume only that `D_i` is nonempty and
totally bounded for `d_i` whenever `i!=e`.  The exceptional family `D_e` is
an arbitrary nonempty collection of behavioral laws, with no compactness or
tail condition.

Then, for every `epsilon>0`, there is an ordinary behavioral profile `sigma`
such that

```text
U_i(tau_i,sigma_-i) <= U_i(sigma)+epsilon
for every i and every tau_i in D_i.                 (9)
```

Consequently a fixed-gap profile-dependent selector has at least two distinct
nonempty ranges which are not strategically totally bounded.  By (7)--(8),
there are two distinct player identities `i,j` and positive constants
`kappa_i,kappa_j` such that each identity has selected laws with fixed mass
arbitrarily late at finite times:

```text
for every N, some mu in D_i has mu(N<T<infinity)>=kappa_i,
for every N, some nu in D_j has nu(N<T<infinity)>=kappa_j.       (10)
```

The laws in the two lines need not be selected at the same profile.

If every `D_i` is complete for unrestricted best responses and all but at
most one are strategically totally bounded, (9) gives unrestricted terminal
`epsilon`-Nash profiles for every error and hence a uniform-equilibrium
payoff.

### Theorem E: one proper sentinel compactifies all unrestricted clocks

Call a stopping law **proper** when it Quits at a finite time almost surely.
A possibly empty family `D_s` is **properly strategically approximable** when,
for every `epsilon>0`, there is a finite nonempty collection `F_s` of proper
behavioral laws, not necessarily in `D_s`, such that

```text
for every tau in D_s, some f in F_s has d_s(tau,f)<epsilon.      (11)
```

For an empty family, take any proper singleton.

If one player `s` satisfies (11), then for every `epsilon>0` there is an
ordinary behavioral profile `sigma` with

```text
U_s(tau_s,sigma_-s) <= U_s(sigma)+epsilon       (tau_s in D_s),
U_i(tau_i,sigma_-i) <= U_i(sigma)               (i!=s,
                                                   every behavioral tau_i).
                                                               (12)
```

Thus one properly approximable selected range is incompatible with a fixed
all-profile gap, regardless of how noncompact every other player's selected
range is.  If `D_s` is also complete for player `s`'s unrestricted best
responses, (12) gives all-error unrestricted terminal Nash and therefore a
uniform-equilibrium payoff, with no reply-class hypothesis on any other
player.

### Theorem F: exact surviving selector boundary

For a fixed-gap selector, every player range `D_s` is nonempty and fails
proper strategic approximation.  Proper approximation in total variation is
equivalent to finite-time uniform tightness

```text
for every eta>0, exists H,
  sup_(mu in D_s) mu({H+1,H+2,...,infinity})<eta.     (13)
```

Since `d_s<=2M TV`, failure of proper strategic approximation forces failure
of (13).  Avoiding supremum attainment by halving the failure constant gives,
for every player `s`, some `lambda_s>0` such that

```text
for every H, some mu in D_s has
  mu({H+1,H+2,...,infinity})>=lambda_s.              (14)
```

If `D_s` is strategically totally bounded but fails proper approximation,
there are `tau_s in D_s` and `zeta_s>0` such that

```text
inf_(p proper) d_s(tau_s,p)>=zeta_s.                 (15)
```

Indeed, take a finite `eta/3`-net of `D_s` at an error `eta` witnessing
failure of proper approximation.  If every net center were within `eta/3` of
one proper law, those proper laws would form a `2eta/3`-net, contradiction.
The law in (15) necessarily has positive Never mass.

Combining Theorems D--F gives the exact identity-level necessity:

```text
every player identity carries selected late-or-Never mass;
at least two distinct identities carry genuinely late finite mass;
every remaining strategically precompact identity contains an essential
Never witness separated from all proper laws.                        (16)
```

Nothing in (10), (14), or (16) asserts that the witnesses coexist at one
candidate profile.

## Conjecture-facing change

The incentive-gadget question asks for one fixed terminal exploitability gap
against every independent behavioral clock profile.  The known finite-
watchdog obstruction rules out only finitely many preselected deviations.

Theorems A--B extend that obstruction to arbitrary profile-dependent infinite
families whenever their strategic range is precompact.  They prove an exact
necessity: a surviving fixed-gap witness mechanism must send a nonvanishing
amount of clock mass beyond every finite date.

Theorem C rules out a precisely defined universal gadget architecture with an
all-behavior consumer: every quitting table whose unrestricted best responses
are captured by strategically precompact complete reply families already has
a uniform-equilibrium payoff.  Thus a counterexample gadget must use a
strategically nonprecompact and genuinely unbounded-time best-response
mechanism.

Theorem D shows that one such player identity is still insufficient.  Theorem
E is stronger in another direction: one properly approximable player acts as
an almost-surely finite sentinel and compactifies every other unrestricted
clock.  Therefore every added calibrator must itself occur as a profitable
deviator somewhere and carry the boundary obstruction (14); a finite or
properly approximable calibrator menu creates an equilibrium escape.

The exact remaining architecture has every identity late-or-Never, at least
two identities genuinely late-finite, and any strategically precompact
identity carrying an essential Never witness.  This does not construct the
requested reward table, make the two late identities simultaneous, or exclude
architectures satisfying (16).

## Proof

### 1. Finite nets reduce to a finite strategic-form game

Fix `epsilon>0` and choose finite `epsilon`-nets `F_i subset D_i`.  Form the
finite normal-form game whose pure strategies for player `i` are the stopping
laws in `F_i`, with payoffs equal to the quitting game's exact terminal
payoffs.  Nash's theorem gives a mixed equilibrium `lambda`.

Independently draw one law from each player's mixture.  The marginal mixture
of laws is again one probability law on `Omega`, hence has a behavioral hazard
representation.  Let `sigma_i` be this law.  Independence makes the joint
terminal distribution the product of the marginal mixture laws, exactly as
in the finite strategic game.  Its Nash inequalities are therefore

```text
U_i(f,sigma_-i) <= U_i(sigma)                        (f in F_i). (6)
```

For arbitrary `tau in D_i`, choose `f in F_i` with
`d_i(tau,f)<epsilon`.  Evaluating the supremum in (1) at `sigma_-i` and using
(6) gives

```text
U_i(tau,sigma_-i)
  <= U_i(f,sigma_-i)+epsilon
  <= U_i(sigma)+epsilon.
```

This proves Theorem A.  The escape profile `sigma_i` need not itself belong
to `D_i`.

### 2. A profile-dependent selector cannot have precompact range

Suppose every nonempty selector range `D_i` were totally bounded.  Pad each
empty range by one arbitrary singleton behavioral law.  The padded families
are nonempty and totally bounded, while padding adds no deviation which can
be selected in (3).  Apply Theorem A with `epsilon<g`.  At the resulting
profile, its selected deviation contradicts (2).  This proves the first part
of Theorem B.

### 3. Strategic noncompactness forces total-variation tail escape

For quit-time laws `mu,nu`, use a maximal coupling of the two player clocks
and the same opponent clocks.  The terminal coalition is identical when the
coupled player clocks agree.  On disagreement, the two payoff values differ
by at most `2M`.  Hence

```text
d_i(mu,nu) <= 2M TV(mu,nu).                          (7)
```

On the countable space `Omega`, a family of laws is totally bounded in total
variation exactly when it is uniformly tight in the discrete sense:

```text
for every delta>0 there is finite A subset Omega such that
  sup_(mu in D) mu(A^c)<delta.                       (8)
```

For one direction, take a finite total-variation net, choose a finite high-
mass set for each net point, and union them.  For the other, move all mass
outside one common finite high-mass set to one fixed point in that set.  The
resulting laws belong to a finite-dimensional probability simplex, which has
a finite total-variation net.

By (7), total-variation total boundedness implies strategic total boundedness.
The nonprecompact selector range therefore fails (8).  Hence there is
`epsilon_0>0` such that for every finite `A`,

```text
sup_(mu in D_i) mu(A^c) >= epsilon_0.
```

The supremum need not be attained.  Put `kappa=epsilon_0/2`; for every finite
`A`, some selected law has complement mass greater than `kappa`.  Apply this
to

```text
A={0,1,...,N,infinity}.
```

Its complement consists exactly of finite quit times after `N`, proving (4).

### 4. Best-response completeness gives all-error terminal Nash

Under (5), choose `sigma` from Theorem A.  Take the supremum of (2) over
`D_i` and then use (5):

```text
sup_(all tau_i) U_i(tau_i,sigma_-i)
  <= U_i(sigma)+epsilon.
```

Thus `sigma` is a terminal `epsilon`-Nash profile against unrestricted
behavioral deviations.  This holds for every positive `epsilon`.  The checked
theorem

```text
quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors
```

therefore gives a uniform-equilibrium payoff, proving Theorem C.

### 5. Finite-dimensional net for one exceptional player

For `i!=e`, choose finite `epsilon`-nets `F_i subset D_i` and put

```text
A_-e=product_(i!=e) F_i.
```

Map the arbitrary exceptional family into the bounded finite-dimensional
payoff cube by

```text
Phi(tau)(a_-e)=U_e(tau,a_-e),
Phi : D_e -> [-M,M]^(A_-e).                         (17)
```

Every bounded subset of a finite-dimensional normed space is totally bounded.
Choose a finite `E_e subset D_e` whose images form an `epsilon`-net in the sup
norm.  Form the finite game with action sets `E_e` and `F_i`, take a mixed
Nash equilibrium, and realize its marginal mixtures as behavioral laws.

For `i!=e`, the global `d_i`-net and finite Nash inequality control every
member of `D_i`.  For `e`, its opponents' mixed profile is a distribution on
the finite set `A_-e`; averaging the sup-norm approximation from (17) gives
the same `epsilon` bound.  This proves (9).  If a fixed-gap selector had at
most one nonprecompact range, pad empty ranges by arbitrary singletons and use
that sole range as `D_e`, contradicting (9).  Applying the proof of (4)
separately to the two nonprecompact ranges proves (10).

Taking suprema in (9) under best-response completeness proves the complete-
class conclusion of Theorem D exactly as in Section 4.

### 6. A proper sentinel restores joint weak continuity

Give `Omega` its one-point compactification topology and `P(Omega)` the weak
topology.  It is compact, convex, and metrizable, and its laws are exactly the
behavioral stopping laws.

Choose a finite proper net `F_s` from (11).  Let the sentinel use the compact
finite-dimensional simplex `conv(F_s)` of stopping laws.  Give every other
player the full compact convex strategy space `P(Omega)`.

Terminal payoff is jointly continuous on this restricted product.  Since
`F_s` is finite and proper, for every `eta>0` there is `H` such that

```text
sup_(nu in conv(F_s)) nu(T_s>H)<eta.                (18)
```

On `T_s<=H`, absorption occurs by date `H`.  The terminal payoff restricted
to that event is a finite polynomial in probabilities of the clopen cells

```text
{0},...,{H},{H+1,H+2,...,infinity}.
```

It is therefore weakly continuous.  Discarding `T_s>H` changes a payoff by at
most `M eta`, uniformly in all other laws, so the actual terminal payoff is a
uniform limit of jointly continuous functions.

Payoffs are affine, hence quasiconcave, in each player's own law.  The
Fan--Glicksberg/Kakutani theorem gives a Nash profile on

```text
conv(F_s) x product_(i!=s) P(Omega).
```

Every nonsentinel player is exact against all behavioral laws.  The
sentinel's finite-net inequalities transfer to `D_s` through `d_s`, proving
(12).  Completeness of `D_s`, followed by the checked all-errors theorem,
proves the uniform-payoff conclusion of Theorem E.

### 7. Proper tightness and essential Never witnesses

A family is approximable in total variation by finite proper laws exactly
when (13) holds.  A finite proper net has one common finite tail cutoff.
Conversely, under (13), move the common tail mass to one fixed finite time and
net the resulting finite-dimensional simplex.  Its centers are proper.

Thus proper TV approximation implies proper strategic approximation by (7).
Failure of the latter yields a constant `eta_s>0` for which the supremum in
(13) is at least `eta_s` at every cutoff.  Put
`lambda_s=eta_s/2` and choose a law above that threshold; this proves (14)
without assuming the supremum is attained.

The `eta/3` finite-net argument stated before (15) proves the essential-Never
alternative.  Combining it with Theorem D proves (16).

### 8. Exact Never boundary test

The proper-sentinel class is not limited to families already supported on
finite times.  Suppose player `s` has solo reward zero and receives zero at
every terminal coalition omitting it.  Let `mu_L` be uniform on `L` distinct
finite dates.  Against arbitrary opponents, `mu_L` and Never differ only when
`s` ties the opponents' first coalition: preemption pays the zero solo row,
and waiting pays a zero absent row.  The tie probability is at most `1/L`, so

```text
d_s(mu_L,Never)<=M/L.                               (19)
```

Hence `{Never}` is properly strategically approximable.  If every row
containing `s` also pays it at most zero, Never is best-response complete and
Theorem E gives a uniform payoff.  This is consistent with the mechanism: an
indifferent zero-payoff player can use a diffuse proper clock to compactify
the other stopping laws.

## Probability and behavioral-deviation audit

The strategy space is the ordinary private behavioral strategy space of the
quitting game.  A single player has only the live-history clock, so a behavior
strategy and its induced law on `Nat union {infinity}` have the same terminal
effect.  Players' laws remain independent; no public random device or
cross-player correlation is introduced.

The strategic pseudometric takes a supremum over all behavioral opponent
profiles.  Theorem C's completeness condition also quantifies over every
behavioral opponent profile and every behavioral unilateral deviation.
Consequently its terminal Nash and uniform-payoff conclusions are fully
unrestricted, not stationary, finite-memory, finite-horizon, or bounded-
controller claims.

The finite normal-form mixture is used only to construct each marginal quit-
time law.  Its independent product is behaviorally executable through the
hazard representation; no latent mixed plan needs to be observed during play.

Theorem D uses no topology on the exceptional range: it records only finitely
many exact payoffs after the other players have been netted.  Theorem E does
use the weak topology on laws, but only after one proper sentinel makes the
terminal payoff jointly continuous.  Every nonsentinel strategy space is the
full law space, so its Nash inequalities already cover arbitrary behavioral
deviations, including time dependence, atoms, ties, and Never.

## Boundary tests

1. **Finite menu.**  Every finite watchdog family is totally bounded.  Theorem
   A recovers the finite-watchdog impossibility exactly.
2. **Uniform finite tails.**  A common finite horizon or a uniform exponential
   tail bound gives (8).  In particular, geometric clocks whose hazard is
   bounded below by one positive constant are excluded, even after adjoining
   the isolated `Never` law.
3. **Vanishing geometric hazard.**  Geometric laws with positive hazards
   tending to zero are not uniformly tight on `Omega`: before reaching the
   `Never` boundary their mass escapes to later finite dates.  The theorem
   correctly does not exclude them.
4. **Pure times.**  The laws `{delta_0,delta_1,...,delta_infinity}` are not
   total-variation totally bounded; distinct point masses have distance one.
   This is the exact profile-dependent pure-time escape left open.
5. **Incomplete compact class.**  A finite or compact deviation class can
   miss the true best response for some opponent profile.  Theorem A blocks it
   from proving a fixed gap, but only the explicit completeness hypothesis (5)
   permits the unrestricted existence conclusion of Theorem C.
6. **One arbitrary range.**  The exceptional family in Theorem D may be all
   behavioral laws, all pure times, or any other strategically nonprecompact
   family.  One such identity is still insufficient for a fixed-gap selector.
7. **All-Never weak seam.**  Without a proper sentinel, common finite quit
   times may escape to infinity while retaining a tie payoff.  Theorem E does
   not claim continuity on the full product.  Its finite proper net supplies
   the uniform tail (18) which removes exactly this seam.
8. **Never can be properly approximable strategically.**  The zero absent-row
   test (19) shows that strategic proper approximation is weaker than total-
   variation finite-time tightness.  The total-variation criterion is used
   only by contraposition to obtain (14).

## Source correspondence and novelty

The existing finite-watchdog theorem is recorded in
`notes/CHATGPT_EXTERNAL__FINITE_WATCHDOG_GEOMETRIC_SECURITY_NO_GO.md`.  It is
the finite special case of Theorem A but contains neither the strategic
pseudometric completion nor the tail-escape and complete-family conclusions.

Relevant checked game-semantic endpoints are:

- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`, which
  confirms that arbitrary fixed-opponent behavioral deviations have the same
  payoff supremum as pure quit times; and
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`,
  which consumes Theorem C's all-error unrestricted terminal Nash profiles.

The new ordinary mathematics is the reward-dependent strategic pseudometric,
finite-net Nash argument for infinite/profile-dependent families, maximal-
coupling comparison to total variation, discrete tightness equivalence, fixed
late finite-mass consequence, and best-response-complete all-behavior
consumer.  A narrow conference search found no previous precompact-watchdog
theorem.  No external literature theorem beyond the standard finite Nash
theorem and elementary maximal coupling is used.

The extension adds two ingredients not present in the finite-watchdog result:

- the asymmetric finite-dimensional image (17), which permits one completely
  arbitrary player range after every other range is strategically netted; and
- the proper-sentinel continuity argument (18), which permits every other
  player to retain the full weakly compact stopping-law space.

`notes/CODEX_CEDAR__STOPPING_TIME_COMPACT_GAME.md` records the exact failure
of joint weak continuity without a sentinel: common finite tie times converge
to all Never while their terminal payoff does not.  Theorem E does not invoke
a generic discontinuous-game theorem; the uniformly proper sentinel removes
that boundary event before ordinary compact-game Nash existence is applied.
A narrow search for one-exception reply nets and proper-sentinel stopping-law
compactification found no checked or conference theorem with Theorems D--F.

## Adapter and consumer

Theorem A takes the deviation families directly; no candidate equilibrium is
assumed.  A profile-dependent gadget proof with a fixed gain supplies the
selector in Theorem B, whose output is the necessary late-mass escape (4).

For the universal negative architecture, the actual-data hypothesis is (5):
the specified precompact families compute the unrestricted best-response cap
against every actual opponent profile.  Theorem A then constructs terminal
approximate Nash profiles, and the checked all-errors theorem is the exact
unrestricted semantic consumer.

Theorem D's source data are the same literal reply families, with total
boundedness required away from at most one identity.  Theorem E's source data
are one family and its finite proper strategic nets (11); every other player
is optimized over the entire behavioral space inside the producer.  The
complete-class arms then feed the same checked all-errors consumer.  No Nash
profile, target clock law, target pair atom, or leftover bound is assumed by
the source predicates.

## Lean handoff

This theorem is best formalized in two layers.

1. Define the payoff pseudometric on one player's behavioral strategies and
   prove the finite-net Nash theorem.  The finite strategic-form equilibrium
   may use the project's existing finite-game Nash theorem; separately prove
   that a finite mixture of quit-time laws has a behavioral hazard
   representation and preserves product terminal payoffs.
2. Define total variation on the countable quit-time space.  Prove (7), the
   total-bounded/uniform-tight equivalence, and the `epsilon_0/2` tail lemma.
   Then add the complete-family consumer using the existing terminal-Nash
   all-errors theorem.

Finite regressions should cover an empty selector range padded by a singleton,
a finite watchdog menu, geometries with hazard bounded below, hazards tending
to zero, and the nonattained tightness supremum.  Do not encode
best-response completeness as a conclusion field of the finite-net theorem.

For Theorem D, add the finite evaluation map (17) after constructing the
ordinary players' nets; its codomain is a finite real function type, so a
finite sup-norm net supplies the exceptional actions.  For Theorem E, use the
probability-law space on the one-point compactification, prove the uniform
finite-truncation continuity lemma from (18), and invoke a compact convex Nash
theorem.  Keep the proper-net predicate separate from total-variation
tightness: (19) is the required regression showing that a nonproper law can be
strategically approximated by proper diffuse laws.

## Scope and nonclaims

- The theorem does not construct a quitting reward table with a fixed terminal
  exploitability gap.
- It does not derive the target pair masses or leftover inequality in
  `INCENTIVE_GADGET`.
- It does not exclude selectors with the late finite-mass escape (4), including
  unbounded pure-time selectors or vanishing-hazard geometric clocks.
- It does not claim that every reward table admits a strategically precompact
  complete reply family.
- It does not claim that every reward table has a properly strategically
  approximable complete sentinel class.
- It does not make the two late-finite identities in (10) simultaneous, nor
  turn identity-level tail mass into target coalition mass.
- The essential-Never conclusion (15) applies only to a selector range which
  is strategically totally bounded but fails proper approximation; genuinely
  nonprecompact ranges need not contain such an isolated law.
- Total boundedness is in the strategic payoff pseudometric for Theorems A and
  C; total variation is a sufficient stronger condition used to obtain the
  literal clock-tail consequence.
- Theorems C--E contain exact universal-class existence results, not a proof
  of the full quitting-game conjecture.
