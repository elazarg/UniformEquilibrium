# Adversarial review of minimum-singleton clock compression

Reviewer: ATLAS_FALSIFIER

## Claim reviewed

The note claims that the total terminal mass of a singleton \(\{j\}\) is a
subprobability average of opponent-survival probabilities exposed by a legal
unilateral Continue-until-\(t\), Quit-at-\(t\) replacement. Its anchored form
is then applied after the arbitrarily deep source cap prefixes of a Fin4
minimum-law singleton leaf, producing cofinally many actual profiles with one
fixed positive singleton stage-mass floor.

I reviewed the generic identity, its anchored version, legality in the full
behavioral strategy class, the minimum-law/cap-stack application, and the
claim that this answers the concentration arm of
`questions/FIN4_ATLAS_DIFFUSE_MINIMUM_SINGLETON.md`. I did not review Lean
compilation.

## Sources inspected

- `quittingHazardStopMass_eq_survival_mul_stop`,
  `hasSum_quittingHazardStopMass`, and
  `quittingBehaviorStoppingLaw_some_toReal` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`;
- `quittingTerminalOutcomeMass_eq_timeDisintegration` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauTimeDisintegration.lean`;
- `quittingStageCoalitionMass_literalRootStack_add_length` and the definition
  of `QuittingMinimumLawCausalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
- `IsQuittingCapNashRootStack` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`;
- `QuittingNonsingletonMinimumLawTransfer.tendsto_capNashStackContinueProduct_one`
  in `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`; and
- `FinFourAtlasConcentratedSingletonOrigin` and
  `FinFourAtlasConcentratedSingletonEndpoint` in
  `Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean`.

## 1. Generic averaging identity

On the unique live history, let \(q_i(t)\) and \(c_i(t)=1-q_i(t)\) be the
Quit and Continue probabilities. For the owner \(j\), put

\[
  \alpha_t=\Bigl(\prod_{r<t}c_j(r)\Bigr)q_j(t),
\]

and let

\[
  s_t=\prod_{i\ne j}\prod_{r\le t}c_i(r).
\]

The first finite stopping masses \(\alpha_t\) form a subprobability law:

\[
  \sum_t\alpha_t=1-\Pr(T_j=\infty)\le1.
\]

At date \(t\), the event that the terminal coalition is exactly \(\{j\}\)
requires \(j\)'s first Quit at \(t\) and every opponent's continuation through
\(t\). Product behavioral randomization on the common live history therefore
gives exactly

\[
  \Pr(\{j\}\text{ at }t)=\alpha_t s_t,
  \qquad
  m_j(\sigma)=\sum_t\alpha_t s_t.
\]

No stationarity or finite-support premise enters. Opponent strategies may be
arbitrary behavioral strategies; before absorption there is only the one live
history at each date, so their live hazards are the displayed deterministic
sequence of PMFs.

For \(0\le\lambda<m_j(\sigma)\), if all \(s_t\le\lambda\) on the positive
support of \(\alpha\), then

\[
  m_j(\sigma)\le\lambda\sum_t\alpha_t\le\lambda,
\]

a contradiction. Thus some supported date has \(s_t>\lambda\).

The note states the theorem for every real \(\lambda<m_j(\sigma)\). That
stronger statement is also true, but the written support argument omits the
case \(\lambda<0\), where one simply chooses any date and uses \(s_t\ge0\).
The atlas application assumes \(\lambda>0\), so this is a trivial proof repair,
not a substantive gap. The clean generic statement is
\(0\le\lambda<m_j(\sigma)\).

## 2. Legality and exact output of compression

The replacement is a legal complete behavioral strategy for \(j\): at every
history before \(t\) it selects pure Continue, at date \(t\) pure Quit, and
after \(t\) it reuses the source strategy. All opponent strategies are left
unchanged. In the target profile, reaching date \(t\) already entails the
owner's certain earlier continuation, so the stage singleton mass is exactly
\(s_t\).

The target terminates surely at \(t\) conditional on reaching it, but its
off-path continuation is still part of a legal complete strategy. Restoring
the source after \(t\) consequently gives literal equality of the complete
**live-root** tail at every date strictly after \(t\). It does not assert a
history-by-history equality on irrelevant non-live histories unless the splice
is defined that way; live-root equality is the exact invariant needed by the
note.

This construction is not an illicit shared random choice of \(t\). One date
is selected existentially from deterministic probability data, and the owner
then uses the corresponding deterministic behavioral replacement.

## 3. Anchored identity

Let \(a\) be the anchor. Preserve the source before \(a\), force \(j\) to
Continue on \([a,t)\), and force it to Quit at \(t\). The source mass of a
singleton terminal occurring at \(t\ge a\) factors as

\[
 \underbrace{\Bigl(\prod_{r=a}^{t-1}c_j(r)\Bigr)q_j(t)}_{\alpha_{a,t}}
 \underbrace{\Bigl(\prod_{r<a}\prod_i c_i(r)\Bigr)
   \Bigl(\prod_{r=a}^{t}\prod_{i\ne j}c_i(r)\Bigr)}_{s_{a,t}}.
\]

The first factor again has total mass at most one. The second includes the
entire probability of reaching the anchor, including the owner's source
survival before \(a\). It is exactly the singleton stage mass after the
anchored replacement. Hence the same averaging proof is valid.

I tried the two natural off-by-one falsifiers. Opponents must survive
**through** date \(t\), while the owner is forced to Continue only **before**
date \(t\); the displayed products have precisely those endpoints. No missing
anchor-survival factor remains.

## 4. Minimum-law and cap-stack application

Let \(\mu>0\) be the singleton coordinate of the selected minimum joint law.
For the causal suffix profiles \(\sigma_n\), joint law convergence gives

\[
  m_j(\sigma_n)\longrightarrow\mu.
\]

The proof of
`tendsto_capNashStackContinueProduct_one` uses minimum provenance, positive
minimum debt, semantic convergence, exact source cap stacks, and convergence
of the prefixed debts. It has no nonsingleton-cardinality hypothesis, so it is
valid for this singleton atom. Thus the source stack Continue products
\(P_n\) satisfy \(P_n\to1\).

The portion of singleton terminal mass occurring in the suffix of the
literally prefixed source is exactly

\[
  P_n m_j(\sigma_n),
\]

by `quittingStageCoalitionMass_literalRootStack_add_length` followed by time
disintegration. It converges to \(\mu\). Therefore, for each fixed
\(0<\lambda<\mu\), all sufficiently large source ranks have after-anchor
singleton mass greater than \(\lambda\), and the anchored theorem produces an
actual compressed target with one literal singleton stage of mass greater
than \(\lambda\). Since the source root words have length \(n+1\), the family
is cofinally deep. Taking \(\lambda=\mu^2/8\) is valid because
\(0<\mu\le1\).

### Essential cap-stack qualification

The copied prefix roots are literally unchanged in the compressed target,
and the original source object retains its proof that they form an exact
cap--Nash stack over the original suffix. They are **not** automatically an
exact cap--Nash stack over the compressed suffix.

This follows directly from the definition: each root is Nash against the
behavioral cap of the remaining executable suffix. Changing \(j\)'s future
strategy can change the caps of every other player and invalidate a previous
root equilibrium. There is no tail-invariance theorem for those coordinates.

The current author note now states this distinction correctly. The earlier
review in
`feedback/FIN4_MINIMUM_SINGLETON_CLOCK_COMPRESSION__BY_CODEX_ROOT.md`
contains the sentence that compressing the suffix and reapplying the word
“leaves the entire root stack exact”; read literally for the compressed
target, that sentence is false. Nothing in the concentration proof needs it.
The sound construction applies the anchored splice to the already-prefixed
source, retains its root actions before the anchor, and keeps the exact-stack
certificate attached to the unmodified source record.

## 5. Does this close the named question?

Mathematically, yes: it supplies accepted answer 1 of
`questions/FIN4_ATLAS_DIFFUSE_MINIMUM_SINGLETON.md`. The output has, uniformly
over a cofinal source family:

- an actual behavioral target;
- a fixed singleton label;
- an actual marked date;
- a fixed positive stage-mass floor;
- the selected minimum-law and causal-source provenance;
- literal agreement with the source before the suffix anchor; and
- literal post-mark live-root equality.

It does not choose one date with a rank-dependent vanishing bound, replace the
joint law by marginal weak limits, or assume minimum attainment.

There is one repository-interface repair. The currently checked
`FinFourAtlasConcentratedSingletonEndpoint` requires a
`FinFourLowTailRow`, because both existing origins came from the nonsingleton
low-tail construction. The new singleton-minimum origin has no such row and
must not fabricate one. A correct common endpoint should store only the
common profile, stage, singleton, positive floor, source attachment, and
post-date tail equality, while the old origin tags retain their stronger
low-tail fields.

A narrow source search finds no downstream mathematical consumer of
`FinFourAtlasConcentratedSingletonEndpoint`; its current uses are definitions
and atlas normalization adapters in `SemanticConnections.lean`. Therefore
this is an interface refactor rather than loss of an existing consumer.  The
first-supported-date strengthening below shows that the new target is in fact
a literal one-date update; only the low-tail field must remain origin-specific.

The result closes only the **diffuse minimum-singleton** question. It transfers
that leaf to the concentrated-singleton obligation and supplies no debt,
Nash, low-tail, punishment-floor, return, or uniform-payoff consumer there.

## Boundary tests

1. If the owner is uniform on \(N\) dates and every opponent Never quits, the
   original largest singleton stage atom is \(1/N\), while every exposed
   opponent-survival mass is one. This confirms that the construction really
   removes owner-clock diffusion rather than assuming concentration.
2. Owner Never mass makes \(\sum_t\alpha_t<1\) and does not harm the averaging
   estimate.
3. If all exposed \(s_t\) equal the weighted mean and
   \(\sum_t\alpha_t=1\), the first-supported-date construction exposes stage
   mass exactly \(m_j(\sigma)\).  This shows the non-strict source-level bound
   is sharp.  Strictness is needed only when replacing a convergent sequence
   of actual masses by its limiting floor.
4. Prefix absorption is correctly priced: the attainable compressed mass is
   the anchored survivor value, and the application uses
   \(P_nm_j(\sigma_n)\to\mu\), not merely suffix mass convergence.
5. The construction makes no assertion that the compressed semantic pair is
   minimum, near-minimum, or even low-tail; these would be false additional
   inferences in general.

## Verdict

**Core mathematics:** PASS. No counterexample was found to the averaging,
anchored, behavioral-legality, or cofinal minimum-law claims.

**Repairs required:** interface/scope only. Restrict the written averaging
proof to \(0\le\lambda<m\) or add the trivial negative-\(\lambda\) case;
retain cap--Nash exactness only on the original source; and refactor the common
concentrated endpoint so that the low-tail field remains origin-specific.

**Exportability:** PASS after those explicit repairs are reflected in the
packet. The result is a complete accepted answer to
`FIN4_ATLAS_DIFFUSE_MINIMUM_SINGLETON`; it is not a consumer of the resulting
concentrated-singleton leaf.

## Addendum: first-supported-date strengthening

I independently checked the strengthening in
`feedback/FIN4_MINIMUM_SINGLETON_CLOCK_COMPRESSION__BY_STRENGTHENER.md`.
It is valid, and it improves one conclusion of this review.

For an anchor \(a\), write

\[
 \alpha_{a,t}=\Bigl(\prod_{a\le r<t}c_j(r)\Bigr)q_j(t),
 \qquad
 \beta_{a,t}=\Bigl(\prod_{r<a}\prod_i c_i(r)\Bigr)
              \Bigl(\prod_{a\le r\le t}\prod_{i\ne j}c_i(r)\Bigr),
\]

and let \(A_a=\sum_{t\ge a}\alpha_{a,t}\) and
\(m_a=\sum_{t\ge a}\alpha_{a,t}\beta_{a,t}\).  If \(m_a>0\), some
\(\alpha_{a,t}\) is positive, so the positive support has a least element
\(t_0\).  Also \(A_a>0\).  Opponent survival is monotone in time, hence
\(\beta_{a,t}\le\beta_{a,t_0}\) for every positive \(\alpha_{a,t}\).  Therefore

\[
 m_a\le \beta_{a,t_0}A_a,
 \qquad
 \beta_{a,t_0}\ge \frac{m_a}{A_a}\ge m_a.
\]

There is no hidden zero-survival exception in the minimality step.  Inductively,
before \(t_0\) the owner's conditional survival from \(a\) is one: if it is one
at \(r<t_0\), then \(\alpha_{a,r}=0\) forces \(q_j(r)=0\), and hence
\(c_j(r)=1\).  Thus the source owner already plays pure Continue at every live
row \(a\le r<t_0\).  A literal pure-Quit update at the single date \(t_0\)
therefore has singleton stage mass exactly \(\beta_{a,t_0}\).

The pre-anchor survival factor is already contained in \(\beta_{a,t_0}\).  If
it were zero, then \(m_a=0\), contrary to the premise.  Never mass and gaps in
the owner's finite stopping support cause no problem.  The update is a legal
complete behavioral strategy, preserves every opponent strategy, and is
literally the source profile at every other date.  Its post-date live roots
are consequently unchanged as well.

This corrects my earlier statement that the new target necessarily differs
from the source on an interval and requires a generalized multi-date endpoint.
No interval edit is needed: the existing literal one-date profile construction
has the right output.  One should not, however, infer target-side cap--Nash
exactness for the copied prefix; that certificate still belongs only to the
unmodified source.

The sharp source-level conclusion is mass at least the whole **anchored**
singleton mass \(m_a\), and more precisely \(m_a/A_a\).  For \(a=0\), this is
the complete singleton terminal-law mass.  In the atlas application it is the
post-anchor contribution \(P_nm_j(\sigma_n)\), which converges to the selected
minimum-law mass; it need not equal the target's entire terminal singleton
mass or attain the limiting value uniformly in \(n\).

**Addendum verdict:** PASS.  The strengthening is mathematically sound and
strictly simplifies the required interface.  It leaves unchanged the scope
verdict: it closes the diffuse-minimum-singleton concentration question by
moving that leaf to the concentrated-singleton class, without supplying its
downstream consumer.

Unresolved mathematical objections to the corrected theorem: none.
