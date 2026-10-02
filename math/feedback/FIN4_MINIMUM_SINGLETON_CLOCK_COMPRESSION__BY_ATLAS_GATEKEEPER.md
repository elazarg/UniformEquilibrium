# Export-gate audit of Fin4 minimum-singleton clock compression

Reviewer: ATLAS_GATEKEEPER

## Claim audited

The note proves that the terminal mass of a singleton \(\{j\}\) in an
arbitrary behavioral quitting profile is a subprobability-weighted average of
the opponent-survival masses exposed by forcing \(j\) to Continue until one
date and Quit there.  Its anchored form is then applied after the exact source
cap prefixes of a Fin4 minimum-law singleton source.  The proposed conclusion
is a cofinal family of actual profiles with one fixed positive singleton
stage-mass floor, a literal unchanged source prefix, and literal post-stage
live-root equality.

I audited the mathematical proof, its relation to
`questions/FIN4_ATLAS_DIFFUSE_MINIMUM_SINGLETON.md`, nearby checked results,
and every current Lean use of the concentrated-endpoint API.  This is not a
compilation review.

## Verdict

**EXPORT in a corrected narrow form.**

The result is a complete answer to the concentration arm of
`FIN4_ATLAS_DIFFUSE_MINIMUM_SINGLETON`.  It strictly removes the
`minimumLawSingleton` temporal-diffusion leaf by mapping its actual source data
to a cofinal fixed-resolution singleton-endpoint family.  It does not consume
the resulting concentrated-singleton endpoint and does not produce a Nash,
low-tail, debt, punishment-floor, return, or uniform-payoff certificate.

The current note is not suitable for export verbatim.  The packet must use the
exact statement below, repair the trivial negative-threshold proof gap, and
present a generalized endpoint interface which does not fabricate a
`FinFourLowTailRow` or target cap-stack exactness.

## Mathematical audit

Let \(q_i(t)\) and \(c_i(t)=1-q_i(t)\) be the live-history Quit and Continue
probabilities.  For fixed owner \(j\), put

\[
  \alpha_t=\Bigl(\prod_{r<t}c_j(r)\Bigr)q_j(t),
  \qquad
  s_t=\prod_{i\ne j}\prod_{r\le t}c_i(r).
\]

`quittingHazardStopMass_eq_survival_mul_stop` and
`hasSum_quittingHazardStopMass` identify \(\alpha\) as the finite-stop part of
the owner's stopping law and give \(\sum_t\alpha_t\le 1\).  Product
randomization at the unique live history gives

\[
  \operatorname{StageMass}_\sigma(t,\{j\})=\alpha_t s_t.
\]

Together with `quittingTerminalOutcomeMass_eq_timeDisintegration`, this gives

\[
  \operatorname{Law}_\sigma(\{j\})=\sum_t\alpha_t s_t.
\]

Forcing \(j\) to Continue before \(t\), Quit surely at \(t\), and restoring
its source live roots after \(t\) is one legal complete behavioral strategy.
All opponents remain literally unchanged, so the target's singleton stage
mass is exactly \(s_t\).  If
\(0\le\lambda<\operatorname{Law}_\sigma(\{j\})\), the supposition
\(s_t\le\lambda\) on the positive support of \(\alpha\) would imply

\[
  \operatorname{Law}_\sigma(\{j\})
    \le \lambda\sum_t\alpha_t\le\lambda,
\]

a contradiction.  No stationarity, finite support, or finite-memory premise
is used.

The note states the generic theorem for every real
\(\lambda<\operatorname{Law}_\sigma(\{j\})\), but its written proof only
covers \(\lambda\ge0\).  The stronger statement is still true when
\(\lambda<0\), since every \(s_t\ge0>\lambda\), but the clean export statement
should simply assume \(0\le\lambda\).

For an anchor \(a\), the second factor must contain the entire joint source
survival before \(a\):

\[
 s_{a,t}=
 \Bigl(\prod_{r<a}\prod_i c_i(r)\Bigr)
 \Bigl(\prod_{r=a}^{t}\prod_{i\ne j}c_i(r)\Bigr).
\]

The note includes this factor and has the endpoints of both products correct:
the owner Continues on \([a,t)\), while every opponent must Continue through
\(t\).  Thus the anchored averaging argument is valid.

For the minimum-law source, joint law convergence gives
\(m_j(\sigma_n)\to\mu\).  The theorem
`QuittingNonsingletonMinimumLawTransfer.tendsto_capNashStackContinueProduct_one`
has no coalition-cardinality premise, so the exact **source** stack Continue
products \(P_n\) tend to one.  The exact transport theorem
`quittingStageCoalitionMass_literalRootStack_add_length` and time
disintegration give suffix singleton mass

\[
  P_n m_j(\sigma_n)\longrightarrow\mu.
\]

Applying the anchored compression to the already-prefixed source therefore
produces, for every fixed \(0<\lambda<\mu\) and all sufficiently large ranks,
an actual marked singleton stage of mass greater than \(\lambda\).  The
canonical atlas choice \(\lambda=\mu^2/8\) is valid because
\(0<\mu\le1\).

## Essential source/target qualification

The root word before the suffix anchor is copied literally into the target.
Its exact cap--Nash certificate, however, is a theorem about the original
source suffix.  Compressing the owner's later clock can change every player's
behavioral cap, so the copied word is not automatically cap--Nash against the
compressed target.

This is not needed by the concentration proof.  The correct provenance record
contains both:

- the unmodified source chronology and its exact cap-stack certificate; and
- the compressed target, which agrees literally with that source before the
  anchor and strictly after its marked date.

It must not contain a theorem asserting exactness of the copied stack against
the target.  With this distinction, the output meets the named question's
first arm: that arm asks for actual marked dates, one fixed positive stage
floor, and literal source/tail provenance, not target-prefix cap exactness.

## Freshness and duplicate audit

The following checked declarations contain ingredients but not this result:

- `quittingHazardStopMass_eq_survival_mul_stop`,
  `hasSum_quittingHazardStopMass`, and
  `quittingBehaviorStoppingLaw_some_toReal` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean` provide the
  owner's subprobability stopping ledger.
- `quittingTerminalOutcomeMass_eq_timeDisintegration` and
  `quittingStageCoalitionMass` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauTimeDisintegration.lean`
  provide chronological terminal-law disintegration.
- `quittingStageCoalitionMass_literalRootStack_add_length` and
  `QuittingMinimumLawCausalSuffixAtom.chronology` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`
  provide exact source-prefix transport and the actual causal family.
- `tendsto_capNashStackContinueProduct_one` in
  `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean` provides the
  source-stack survival limit.  Despite its namespace, the declaration does
  not assume a nonsingleton terminal.
- `weightedOwnQuitMass_le_one` in
  `Research/Quitting/StochasticButtonUnilateralCompression.lean` uses the
  same subprobability-ledger idea to bound diffuse overlap, but it neither
  proves the singleton weighted-average identity nor constructs the anchored
  source-restoring endpoint.
- `continuePrefix_atomAlternative_eventually` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Atom/ContinuePrefixAccess.lean`
  constructs a different Continue-through deviation for an atom stack and
  does not expose a fixed singleton stage by the present averaging argument.
- `quittingPureTimeBehaviorStrategy` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` can
  expose the same on-path date but replaces the off-path future by Never,
  losing the required post-date source-tail equality.
- `quittingLiteralOneDateOverride` in
  `Research/Quitting/SameStageEndpointMonodromy.lean` changes only the marked
  date and does not force the owner to Continue beforehand.
- `quittingContinueUntilRoots` in
  `UniformEquilibrium/Quitting/Classification/Existence/PureTimeDeviationLedger.lean`
  forces the finite Continue prefix but does not add the pure-Quit splice at
  its endpoint.  `quittingContinueUntilThenHazard` in
  `UniformEquilibrium/Quitting/Boundary/Holonomy/InfiniteBehavioralTailEvaluation.lean`
  is another useful splice ingredient, not the complete theorem.

No exact duplicate was found.  The new content is the singleton-law averaging
selection, its anchored source-restoring implementation, and its cofinal
composition with the minimum-law source stacks.  It is repository-derived
elementary probability mathematics; no external paper result is being
translated or attributed.

## Endpoint API audit

The current `FinFourAtlasConcentratedSingletonOrigin` in
`Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean` has only two
constructors, and both carry a `FinFourLowTailRow`.  Consequently the current
common accessors expose `low`, use `low.lambda` as the stage floor, and compare
the target's post-date tail with `low.profile`.

The new singleton-minimum source has no `FinFourLowTailRow`: that type includes
the nonsingleton selected-row family and a strict low-tail excess inequality.
Neither follows from clock compression.  Importing or fabricating such a row
would be mathematically false.

An exact repository search found all current Lean uses of
`FinFourAtlasConcentratedSingletonEndpoint` and
`FinFourAtlasConcentratedSingletonOrigin` inside
`SemanticConnections.lean` itself.  The directed node is used only there and
in `SemanticCoverage.lean`; no downstream theorem consumes the universal
`low` projection.  Thus a broader common endpoint can be introduced without
invalidating an existing mathematical consumer.

The safest design is not to discard the existing strong endpoint data.  Add a
weaker common endpoint core, or generalize the origin while keeping the old
low rows inside their two origin-specific constructors.  Its genuinely common
fields are:

- a retained provenance object indexed by the same
  `FinFourMinimumAtomProducer`;
- an actual reference/source profile;
- an actual target profile;
- a marked date and singleton terminal;
- the canonical source scale \(\mu^2/8>0\) (or an explicit positive scale);
- the unconditional target stage-mass floor; and
- literal equality of target and reference live roots strictly after the
  marked date.

For the new origin, the provenance object must retain the selected causal
profiles, root words, rank/anchor, their length, and the exact cap-stack proof
for the **original** suffix.  For the old origins it retains their complete
`FinFourLowTailRow` data.  A partial/origin-specific `low` accessor is sound;
a universal one is not.

This generalized endpoint is a valid actual-data endpoint without importing
`FinFourLowTailRow`.  It is not yet a semantic consumer to uniform payoff.
Its conjecture-facing role is instead the strict reduction expressly accepted
by `FIN4_ATLAS_DIFFUSE_MINIMUM_SINGLETON`.  It also matches the common entrance
listed in `questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md`, whose exact
consumer uses the actual profile, singleton mass floor, and preserved tail,
not a universal low-tail inequality.

## Exact allowed export claim

The export may claim the following two theorems and no stronger conclusion.

### Generic anchored singleton compression

For every finite player set, quitting reward table, behavioral profile
\(\sigma\), player \(j\), anchor \(a\), and real \(\lambda\) satisfying

\[
  0\le\lambda<
  \sum_{t\ge a}\operatorname{StageMass}_\sigma(t,\{j\}),
\]

there are a date \(t\ge a\) and a legal behavioral profile \(\tau\), obtained
by changing only \(j\), such that:

1. \(\tau\) agrees with \(\sigma\) before \(a\);
2. \(j\) Continues surely on \([a,t)\) and Quits surely at \(t\);
3. every opponent strategy is unchanged;
4. \(\operatorname{StageMass}_\tau(t,\{j\})>\lambda\); and
5. the complete live-root profiles of \(\tau\) and \(\sigma\) agree at every
   date strictly after \(t\).

The proof must include the exact weighted-average identity and the
subprobability bound, not take the displayed conclusion as a structure field.

### Fin4 minimum-law adapter

For every `FinFourMinimumAtomProducer reward bound` whose selected terminal is
a singleton, let \(\mu>0\) be its selected law mass.  For every fixed
\(0<\lambda<\mu\) and every requested depth, some later source rank admits:

1. the original actual causal suffix and original exact cap-root stack;
2. the literally prefixed original source profile;
3. a compressed actual target agreeing with that source before the suffix
   anchor;
4. an actual marked singleton stage in the target of mass greater than
   \(\lambda\); and
5. literal post-stage live-root equality between target and source.

Taking \(\lambda=\mu^2/8\) gives an adapter from the minimum-law singleton
leaf to the generalized fixed-resolution singleton endpoint.  The exact
cap-stack proof applies only to item 1, not to the compressed target in item
3.

## Required packet repairs and nonclaims

Before export, the packet must:

1. restrict the generic threshold to \(0\le\lambda\), or add the missing
   one-line negative-threshold case;
2. replace any wording that the target “retains the minimum law” by the exact
   statement that it retains a pointer to the minimum-law source and its
   provenance—the target's law and semantic pair generally change;
3. distinguish literal copied source roots from cap--Nash exactness, which is
   certified only for the original source suffix;
4. specify the generalized common endpoint without a universal
   `FinFourLowTailRow` field;
5. retain the full original low-row data in the old origin tags and the full
   causal/exact-stack source data in the new origin tag;
6. call the output a **cofinal fixed-resolution endpoint family**, not a
   return or recurrence chronology; and
7. state explicitly that the result does not consume
   `FIN4_ATLAS_CONCENTRATED_SINGLETON`, control arbitrary deviations at the
   target, or prove terminal approximation or uniform equilibrium.

With these repairs there is no unresolved mathematical objection, and the
packet meets the export gate through the named-question clause rather than by
claiming a downstream uniform-equilibrium consumer.

## Addendum: the sharp first-supported-date form

I separately audited the strengthening proposed in
`feedback/FIN4_MINIMUM_SINGLETON_CLOCK_COMPRESSION__BY_STRENGTHENER.md`.
It is correct and should replace the weaker generic compression theorem in the
export packet.

For the anchored notation above, put

\[
  A_a=\sum_{t\ge a}\alpha_{a,t},
  \qquad
  m_a=\sum_{t\ge a}\alpha_{a,t}\beta_{a,t}.
\]

Assume \(m_a>0\).  Then \(A_a>0\), so the positive support of
\(\alpha_{a,\bullet}\) is nonempty.  Let \(t_0\) be its least member.  The
sequence \(\beta_{a,t}\) is nonincreasing because each new date multiplies
opponent survival by Continue probabilities in \([0,1]\).  Therefore

\[
  m_a
  =\sum_{t\ge a}\alpha_{a,t}\beta_{a,t}
  \le \beta_{a,t_0}\sum_{t\ge a}\alpha_{a,t}
  =A_a\beta_{a,t_0}.
\]

Since \(0<A_a\le1\), this gives the sharp bounds

\[
  \beta_{a,t_0}\ge \frac{m_a}{A_a}\ge m_a.
\tag{A1}
\]

There is no hidden interval modification.  Positivity of
\(\alpha_{a,t_0}\) implies that the owner's survival product before \(t_0\)
is positive.  Minimality of \(t_0\) then forces its live Quit probability to
be zero at every \(a\le r<t_0\); on Boolean actions those source live roots
are already pure Continue.  Thus the target can be the existing

```text
quittingLiteralOneDateProfile reward sigma j t0 true
```

rather than a new multi-date splice.  It changes the complete profile only at
\(t_0\), and
`quittingProfileLiveRoot_literalOneDateProfile_tail_eq` gives the desired
literal post-date tail equality.  Its singleton stage mass is exactly
\(\beta_{a,t_0}\).

### Falsification and sharpness

The least-support argument survives owner Never mass: it only makes
\(A_a<1\) and strengthens the quotient in (A1).  It also survives zero
pre-anchor reach only vacuously, because then \(m_a=0\).

The quotient is optimal.  Take two players, let the opponent survive to the
owner's first possible post-anchor date with probability \(c\) and Never quit
afterward, and let the owner's entire conditional finite-stop mass \(A\) occur
at that date.  Then

\[
  m_a=Ac,
  \qquad
  \beta_{a,t_0}=c=m_a/A_a.
\]

With \(A=1\), equality \(\beta_{a,t_0}=m_a\) holds.  Hence no universal
source-level bound strictly larger than \(m_a\) is possible.  This corrects
the original note's boundary claim: strict \(\lambda<m_a\) is not sharp for
one actual source profile.  Strictness remains necessary in the atlas limit,
because the actual anchored masses \(P_nm_j(\sigma_n)\) may converge to
\(\mu\) from below; one cannot promise the limiting floor \(\mu\) at every
large rank.

### Revised export and Lean handoff verdict

The export should state the sharp anchored theorem as follows:

> If an actual behavioral profile has positive singleton terminal mass
> \(m_a\) at or after anchor \(a\), then the first post-anchor date with
> positive owner stopping mass admits a literal one-date pure-Quit update whose
> singleton stage mass is at least \(m_a/A_a\), hence at least \(m_a\).  The
> target is identical to the source at every other date and for every other
> player.

The earlier weighted-average selection is a valid corollary but is not the
best formal target.  In particular, the export should remove any claim that a
new finite live-root splice definition is required.

For the Fin4 adapter, the source after-anchor singleton mass is still

\[
  P_nm_j(\sigma_n)\longrightarrow\mu.
\]

The sharp theorem now exposes at least that whole actual mass with one
literal update.  Consequently every fixed \(0<\lambda<\mu\) still occurs
cofinally, while the convenient canonical floors \(\mu/2\) and
\(\mu^2/8\) are immediate corollaries.  The common old/new atlas interface
should retain \(\mu^2/8\) if one wants a single scale shared with the two
existing origins; the new origin itself supports the stronger cofinal
\(\lambda<\mu\) family.

The narrow Lean order is now:

1. define or reuse the anchored owner finite-stop mass \(A_a\) and post-anchor
   singleton mass \(m_a\);
2. select the least positive owner stop mass with `Nat.find`;
3. prove the division-free inequality
   \(m_a\le A_a\,\beta_{a,t_0}\), then derive both bounds in (A1);
4. use `quittingLiteralOneDateProfile`,
   `quittingLiteralOneDateOverride_of_ne`, and
   `quittingProfileLiveRoot_literalOneDateProfile_tail_eq` for the actual
   target and provenance;
5. sum `quittingStageCoalitionMass_literalRootStack_add_length` and combine it
   with `tendsto_capNashStackContinueProduct_one`; and
6. construct the additive broader endpoint wrapper described above, keeping
   target-side cap-stack exactness and low-tail data out of its common fields.

The source/target warning in the main audit is unchanged: the copied prefix is
literal, but exact cap--Nash status is certified only for the unmodified
source suffix.  No new semantic consumer is obtained.  Subject to replacing
the obsolete strict-threshold sharpness and splice claims, the strengthened
result remains **EXPORT in corrected narrow form** and is the preferred
packet statement.
