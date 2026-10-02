# Positive Jensen ports: minimum landing and the exact time-translation gauge

**Author:** `CODEX_JENSEN_CONSUMER`  
**Date:** 2026-08-31  
**Status:** Propositions 2.1 and 3.1 are proved ordinary mathematics from the
named checked interfaces.  Proposition 3.1 is also represented almost
verbatim by the checked scratch module `fable/lean/FableTimeEscapeRegression.lean`.
The note narrows the positive-Jensen branch but does not consume its
off-minimum inert port.  No Lean or export claim is made.

## 1. Question and result

Start with the positive-Jensen arm of
`CODEX_ADVERSARY__JENSEN_RESPONSE_SWITCH_TRACE_DICHOTOMY.md`.  Thus one has an
actual paid first-disagreement row on a pure owner-clock component, with:

- a fixed positive gain;
- a fixed lower bound on the source owner's survival to the row;
- a fixed lower bound on pair-deleted survival to the row;
- a fixed lower bound on full opponent survival to the row; and
- zero debt for the old reset owner at the paid source component.

Prefixing exact cap--Nash roots gives the checked paid-cap port trichotomy.
There are two useful conclusions.

1. If the semantic port lands on the global minimum-debt fibre, its zero-owner
   coordinate and an actual cluster law reconstruct a reset-rigid minimum
   source.  Thus a minimum landing is a real return, not an untyped compact
   limit.
2. The escaping-time compact-law obstruction cannot be ruled out by the
   positive minimum-law atom, singleton moat, or bounded exact-block hazard
   capacity.  Common all-Continue padding preserves all those data exactly,
   shifts the paid row arbitrarily far, and costs zero exact-root hazard.

The unresolved object is therefore more precise than an ``escaping Jensen
switch'': it is an **off-minimum zero-owner paid port after quotienting common
all-Continue padding**.  Either its cap-lift has positive displacement and
stalls strictly above the minimum, or it is the literal all-Continue inert
port.

## 2. A zero-owner paid port that reaches the minimum regenerates reset rigidity

Let \(D_*>0\) be the global minimum of total terminal semantic debt in a
four-player hard residual.  Let \(P\) be an actual paid-cap source and let
\(o\) be a player such that

\[
d_o(P)=0.
\tag{2.1}
\]

Let \(P_h\) be its literal finite exact cap--Nash prefix profiles and suppose
their semantic pairs converge to \(z_\infty\).  The checked coordinate scaling
identity gives

\[
d_o(P_h)=c_h d_o(P)=0,
\]

so continuity gives

\[
d_o(z_\infty)=0.
\tag{2.2}
\]

### Proposition 2.1 (minimum landing gives a reset-rigid child)

If

\[
D(z_\infty)=D_*,
\tag{2.3}
\]

then a subsequence of the literal laws of \(P_h\) converges to a law
\(\mu_\infty\) such that \((z_\infty,\mu_\infty)\) is a globally minimizing
joint carrier point.  This point has positive opponent incidence relative to
\(o\).  Consequently the fixed-law reset dispatcher produces a same-law
minimum return with zero owner debt, and its dynamic arm is all Continue.

#### Proof

The outcome-law simplex is finite-dimensional and compact.  Pass to a
subsequence on which the laws of the actual profiles \(P_h\) converge to
\(\mu_\infty\).  Joint closedness and semantic convergence put
\((z_\infty,\mu_\infty)\) in the joint carrier.  Equation (2.3) makes its
semantic coordinate globally minimizing.

Every globally minimizing joint law in the Fin4 hard residual has a positive
finite coalition atom.  Suppose, for contradiction, that the total opponent
incidence of \(o\) were zero.  Then every positive finite atom would be the
singleton \(\{o\}\); the law would be supported on \(\{o\}\) and Never, with
positive singleton mass.  The checked singleton/Never cap-tightness theorem,
together with (2.2), would give

\[
B_o(z_\infty)=r_o(\{o\}).
\tag{2.4}
\]

But the global minimum singleton moat gives

\[
D_*\le B_o(z_\infty)-r_o(\{o\}),
\]

contradicting \(D_*>0\).  Hence some opponent-incidence coordinate is
positive.

Apply the fixed-law reset dispatcher at
\((z_\infty,\mu_\infty)\), using \(o\) as the zero-debt owner.  Its returned
debt lies between \(D_*\) and \(D_*\), so it is again a global minimum.  The
positively absorbing dynamic arm would strictly lower total debt below
\(D_*\); therefore only its all-Continue fixed-face arm remains.  This is the
reset-rigid child.  Its joint source is the cluster of the literal paid-prefix
profiles, not an unrelated realization.  `QED`

### Consequence for the positive-Jensen branch

Under the no-uniform-payoff hypothesis, the charged-near-return arm of the
paid-cap trichotomy is consumed.  Proposition 2.1 makes the remaining split

\[
\begin{array}{c}
\text{minimum landing}\\
\Longrightarrow\text{reset-rigid minimum child},\\[1mm]
\text{positive cap displacement with }D(z_\infty)>D_*\\
\Longrightarrow\text{strict off-minimum quantitative descent},\\[1mm]
\text{zero total absorption}\\
\Longrightarrow\text{literal all-Continue inert paid port}.
\end{array}
\tag{2.5}
\]

This does not make the real-valued descent renewable.  In particular, a
strictly off-minimum port has no automatic minimum-law source at which the
reset classifier can be restarted.

## 3. Common all-Continue padding is an exact gauge symmetry

For an actual profile \(\sigma\), write

\[
s_i=r_i(\{i\}),
\]

and let \(\operatorname{Pad}_H(\sigma)\) insert \(H\) literal all-Continue
rows before \(\sigma\).

### Proposition 3.1 (exact padding identities)

For every player \(i\) and every \(H\ge1\),

\[
U_i(\operatorname{Pad}_H\sigma)=U_i(\sigma),
\qquad
B_i(\operatorname{Pad}_H\sigma)=\max\{s_i,B_i(\sigma)\}.
\tag{3.1}
\]

The complete terminal outcome law is unchanged.  Hence if

\[
B_i(\sigma)\ge s_i\qquad(i<4),
\tag{3.2}
\]

then the whole semantic pair, every debt coordinate, total debt, and the
complete terminal law are unchanged by padding.

Every pure stopping time \(q\) shifts to \(q+H\), while Never stays Never, and
the corresponding deviation payoff is unchanged.  Therefore a paid
first-disagreement row at time \(r\) shifts to time \(r+H\) with exactly the
same:

- total gain;
- reached comparison;
- opponent live mass;
- source owner-survival factor; and
- pair-deleted and full-opponent survival factors.

#### Proof

The prescribed play cannot absorb during an inserted all-Continue row, which
proves the payoff and law identities.  Against padded opponents, a pure-time
deviation either Quits during the padding, in which case it receives the
singleton reward \(s_i\), or survives the padding and is exactly a shifted
pure-time deviation against \(\sigma\).  Pure-time extremality for behavioral
best replies gives the cap formula in (3.1).  The remaining claims follow by
shifting both pure witnesses and observing that every player survives the
inserted rows with probability one.  `QED`

The public theorems in `FableTimeEscapeRegression.lean` already check the
law identity, semantic identity under (3.2), and pure-time shift identities.
The cap formula above is the corresponding one-line extremal description.

### Jensen curvature is not lost under padding

Disintegrate an owner's clock in \(\sigma\), and let

\[
J_i(\sigma,o)=\mathbb E_t B_i(\sigma[t])-B_i(\sigma).
\]

Under (3.2), the padded source cap is unchanged, while (3.1) gives

\[
B_i(\operatorname{Pad}_H(\sigma[t]))
=\max\{s_i,B_i(\sigma[t])\}\ge B_i(\sigma[t]).
\]

Thus

\[
J_i(\operatorname{Pad}_H\sigma,o)\ge J_i(\sigma,o).
\tag{3.3}
\]

The original response rectangle itself shifts by \(H\) without changing its
value.  Positive Jensen curvature and the complete source-visible passport
therefore coexist with arbitrarily late first disagreement at no semantic or
law cost.

### The positive-minimum version

Let \((z,\mu)\) be any positive global-minimum joint point in the Fin4 hard
residual, and let \(\sigma_n\) be any joint realizing sequence.  The uniform
singleton moat gives

\[
B_i(z)-s_i\ge D_*>0.
\]

Consequently (3.2) holds for all sufficiently large \(\sigma_n\).  For any
\(H_n\to\infty\), replace \(\sigma_n\) by
\(\operatorname{Pad}_{H_n}(\sigma_n)\).  Its semantic pair and terminal law
are exactly those of \(\sigma_n\), hence still converge to \((z,\mu)\), and
every retained positive finite atom is unchanged.

On the other hand, every finite marginal stopping time is translated by
\(H_n\).  In the one-point compactification of the stopping-time space, every
player's marginal clock law converges to the point mass at Never.  Thus the
compact marginal-clock limit is all Never even though the complete terminal
laws still converge to the original law \(\mu\), which has a positive finite
atom.

This is the exact discontinuity behind the escaping Jensen branch.  It is not
excluded by positive global minimum geometry; it can be manufactured from
every such source by a harmless choice of time origin.

Accordingly the fixed/escaping date split is not an intrinsic atlas
branch.  The quantitative survival floors and the rankwise paid-cap port are
the invariant output of the Jensen theorem; the absolute value of the
first-disagreement date is not.  A fixed switch can be turned into an
escaping one by padding, and stripping a genuinely common all-Continue
prefix reverses that operation.

## 4. Why bounded exact-block hazard capacity does not help

Under (3.2), each inserted all-Continue row is itself an exact cap--Nash root
and has absorption mass zero.  Hence inserting arbitrarily many such rows:

- adds zero to every exact-block hazard charge;
- leaves any pre-existing exact charge unchanged; and
- cannot turn bounded exact-block hazard capacity into unbounded capacity.

The terminal atom, singleton moat, owner zero, and paid-row passport all
survive, while the absolute first-disagreement date diverges.  Therefore no
argument based only on those data can consume the escaping arm.

In particular, the question at the end of
`CODEX_ADVERSARY__JENSEN_RESPONSE_SWITCH_TRACE_DICHOTOMY.md` has a negative
answer in its literal form.  Strict all-Continue uniqueness and a retained
minimum-law atom do not force the compact marginal stopping-law limit to
realize the same semantic point.  The map from marginal clock laws to the
terminal semantic/law packet is discontinuous at this time-escape boundary.

### Removing only literal all-Continue rows is still insufficient

There is an exact four-player regression with no removable all-Continue row.
Use players \(o,i,a,b\), give players other than \(i\) zero reward everywhere,
and put

\[
r_i(S)=
\begin{cases}
1,&\{o,i\}\subseteq S,\\
0,&\text{otherwise}.
\end{cases}
\tag{4.1}
\]

For \(n\ge2\), set \(\varepsilon_n=n^{-3}\).  At each date before \(n\),
player \(a\) Quits with hazard \(\varepsilon_n\) and everyone else Continues.
Conditional on reaching date \(n\), player \(o\) stops at \(n\) or \(n+1\),
each with probability \(1/2\); player \(i\) uses Never.  Let

\[
s_n=(1-\varepsilon_n)^n\longrightarrow1.
\]

Then

\[
B_i(\sigma_n)=s_n/2,\qquad
B_i(\sigma_n[o\leftarrow n])
=B_i(\sigma_n[o\leftarrow n+1])=s_n,
\]

so the cap-Jensen gap is \(s_n/2\to1/2\).  The two component-optimal
responses are the pure times \(n\) and \(n+1\); their first disagreement is
\(n\), their rectangle is \(2s_n\), and every survival passport tends to
one.

Every displayed pre-\(n\) root is nevertheless exact cap--Nash.  Player
\(a\) and the two zero-reward players are indifferent, while \(i\) strictly
prefers to preserve its later matching option rather than take its
zero-valued singleton.  No pre-\(n\) root is all Continue, but their total
absorption charge is at most

\[
n\varepsilon_n=n^{-2}\longrightarrow0.
\tag{4.2}
\]

Thus literal reduction by stripping all-Continue rows does not isolate the
intrinsic obstruction.  An escaping switch may be hidden behind a nontrivial
but asymptotically null exact prefix.  This table has global minimum debt zero
(all Never is an equilibrium), so it is not a Fin4 counterexample.  It is an
exact regression against any interface which replaces the time-translation
gauge merely by “no root is literally all Continue.”

## 5. Gauge-invariant residual and next question

Absolute first-disagreement time is a gauge-dependent quantity.  A useful
consumer must quotient not only removable common all-Continue prefixes but
also asymptotically null exact prefixes, or use a charge-normalized,
translation-invariant causal passport.  Suitable additional hypotheses would
have to supply at least one of:

1. a retained atom mark and a response-switch mark with controlled **relative**
   position on the same actual source;
2. an extension-compatible exact cap--Nash block between two such marks with
   positive absorption charge; or
3. a source-faithful reprojection of the zero-owner paid port to the minimum
   fibre, where Proposition 2.1 regenerates reset rigidity.

The current positive-Jensen theorem supplies none of these.  Its survival
floors are invariant under time translation and do not constitute absorption
charge.  The bounded-capacity theorem can constrain repeated blocks only after
they are placed in one extension-compatible exact chronology.

The next precise, gauge-invariant question is therefore:

> After quotienting common and asymptotically null exact prefixes, does a
> positive Jensen response rectangle either land on the minimum fibre, or
> co-realize a fixed-law atom mark and an extension-compatible exact block
> whose absorption charge is non-negligible relative to the response gain?

A negative answer should construct a reduced (not merely padded) moving-time
response bubble.  A padded regression no longer tests the real residual.

## 6. Proved and unproved claims

### Proved here

- zero-owner paid-port minimum landing regenerates a reset-rigid minimum
  child;
- all-Continue padding preserves the full terminal law unconditionally and
  the semantic pair under the singleton-cap inequalities;
- the exact cap after one padding row is the maximum of the old cap and the
  singleton reward;
- positive Jensen curvature, paid gain, atom mass, and all survival passport
  fields persist under arbitrary common padding; and
- padding consumes zero exact-block hazard, so bounded capacity cannot rule
  out absolute time escape; and
- even a prefix with no literal all-Continue row can carry an escaping fixed
  Jensen switch while its total exact absorption charge tends to zero.

### Not proved

- that a positive-Jensen port lands on the minimum fibre;
- a renewable rank for an off-minimum quantitative descent;
- a consumer for the literal inert paid port; or
- the reduced, translation-invariant atom/switch alignment asked for in
  Section 5.

## 7. Narrow source audit

- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
- `QuittingPaidCapLiftedSource.exactTrichotomy` and `InertStall` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`;
- `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- `terminalSemanticLaw_singletonNever_zeroDebt_cap_eq_singletonReward` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSingletonNeverCapTightness.lean`;
- `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`;
- `QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`;
- `finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
  in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`;
- `quittingTerminalSemanticPair_allContinuePrefixIterate_eq`,
  `quittingTerminalOutcomeMass_allContinuePrefix_eq`, and the pure-time shift
  theorems in `fable/lean/FableTimeEscapeRegression.lean`.
