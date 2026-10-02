# Four-profile descendant-slice neutralization

Authors: `CODEX_DESCENT`

Independent review:
[`PAIRED_HULL_REVIEW`, delta PASS after the four-profile revision](../feedback/CODEX_ROOT__PAIRED_SIGNED_ATOM_CAP_NASH_SATURATION__BY_PAIRED_HULL_REVIEW.md)

Research record:
[`CODEX_DESCENT__BORN_ROOT_DESCENDANT_SLICE_MINIMIZATION.md`](../notes/CODEX_DESCENT__BORN_ROOT_DESCENDANT_SLICE_MINIMIZATION.md)

## Exact statement

Let \(I=\operatorname{Fin}4\), and let a bounded quitting reward table assign
\(r(S)\in\mathbb R^I\) to every nonempty coalition \(S\subseteq I\).  For a
behavioral profile \(\sigma\), write

\[
 J(\sigma)=(\operatorname{Sem}(\sigma),\mu_\sigma)
            =((U(\sigma),B(\sigma)),\mu_\sigma)
\]

for its terminal semantic pair and complete terminal law on the fifteen
nonempty coalitions and Never.  Here

\[
 B_i(\sigma)=\sup_{\tau_i}U_i(\tau_i,\sigma_{-i})
\]

uses every unilateral behavioral replacement, including Never and unbounded
pure or randomized stopping times.  Put

\[
 d_i(U,B)=B_i-U_i,
 \qquad D(U,B)=\sum_{i\in I}d_i(U,B),
\]

and let

\[
 D_*:=\min_{x\in\mathcal C}D(x)>0,
\]

where \(\mathcal C\) is the terminal semantic carrier.  Let
\(\mathcal C^{\rm law}\) be the compact joint semantic/law carrier.

Assume the maintained four-player hard residual.  The proof uses only the
following consequences:

1. every globally minimizing joint-law point has positive mass on at least
   one finite terminal coalition;
2. at every positive global minimum,

   \[
   D_*\le B_i-r_i(\{i\})\qquad(i\in I);
   \tag{1}
   \]

3. a singleton/Never minimum law with positive singleton mass and zero owner
   debt has owner cap equal to the owner's singleton reward; and
4. a global-minimum joint-law point with a zero-debt owner and positive total
   opponent incidence enters the checked law-tight reset-rigid chamber.

Suppose a positive-minimum tangent family and its vanishing-response rectangle
branch supply, at one strict sequence of ranks \(k_n\), the following four
literal profiles:

\[
\begin{array}{ll}
S_n:&\text{the original tangent source},\\
E_n:&\text{the full replacement of one active mover }p\text{ in }S_n,\\
R_n:&\text{the profile }E_n\text{ with the selected pure-time response of }j,\\
Q_n:&\text{the profile }S_n\text{ with that same response of }j.
\end{array}
\tag{2}
\]

The mover \(p\) belongs to the positive-debt support of the tangent base,
and \(j\ne p\).  Fix a nonempty terminal coalition \(T\), put

\[
K=\bigl|\{\text{nonempty coalitions of }I\}\cup\{\mathrm{Never}\}\bigr|=16,
\]

and define the two literal passports

\[
A_n=K\bigl(\mu_{R_n}(T)-\mu_{Q_n}(T)\bigr)r_j(T),
\qquad
G_n=U_p(E_n)-U_p(S_n).
\tag{3}
\]

Assume the supplied rectangle and tangent conclusions

\[
A_n\ge\gamma>0,
\qquad
d_j(J(R_n).1)\longrightarrow0,
\tag{4}
\]

and

\[
G_n\longrightarrow d_p(z_*)>0,
\tag{5}
\]

where \(z_*\) is the positive-minimum tangent base.  Assume also that, after
one common subsequence,

\[
J(R_n)\longrightarrow x^R,
\qquad
J(Q_n)\longrightarrow x^Q,
\tag{6}
\]

and jointly compactify \(J(E_n)\) and \(J(S_n)\) along a further subsequence.
Every further rank map remains strict and hence tends to infinity, so (4)--(5)
remain valid on this common subsequence.  Write

\[
L=D(x^R.1)\ge D_*>0.
\]

The same checked rectangle reset-face dispatch supplies an external semantic
pair \(m\) such that

\[
d_j(m)=0,
\qquad D_*\le D(m)\le L,
\qquad
\operatorname{Nash}(B(m))=\{\mathbf C\}.
\tag{6a}
\]

No law equality or chronological relation between \(m\) and the four literal
profiles is supplied.

For a finite word \(W\) of arbitrary product roots, prefix the same word to
all four profiles and shift every retained date by \(|W|\).  Let

\[
\mathcal O=
 \left\{
  \bigl(J(W\star R_n),J(W\star Q_n),J(W\star E_n),J(W\star S_n)\bigr):
  n\in\mathbb N, W\text{ a finite product-root word}
 \right\}
\tag{7}
\]

and let \(\mathcal K=\overline{\mathcal O}\) in
\((\mathcal C^{\rm law})^4\).  For
\(X=(X^R,X^Q,X^E,X^S)\in\mathcal K\), define

\[
A(X)=K\bigl(\mu^{R}(T)-\mu^{Q}(T)\bigr)r_j(T),
\qquad
G(X)=U_p^{E}-U_p^{S}.
\tag{8}
\]

Choose constants

\[
0<\theta<{A(X_0)\over D(X_0^R.1)},
\qquad
0<\psi<{G(X_0)\over D(X_0^R.1)},
\tag{9}
\]

where \(X_0\) is a common four-profile cluster of the empty-word sequence.
Such constants exist by (4)--(6).  Define the closed normalized descendant
slice

\[
\mathcal K^0_{\theta,\psi}=
\left\{X\in\mathcal K:
 d_j(X^R.1)=0,
\ A(X)\ge\theta D(X^R.1),
\ G(X)\ge\psi D(X^R.1)
\right\}.
\tag{10}
\]

### Theorem A: descendant-slice neutralization

The set \(\mathcal K^0_{\theta,\psi}\) is nonempty and compact.  It has a
point \(X_{\min}\) minimizing \(D(X^R.1)\).  Put

\[
z_{\min}=X_{\min}^R,
\qquad \ell=D(z_{\min}.1).
\]

Then

\[
D_*\le\ell\le L,
\qquad d_j(z_{\min}.1)=0,
\tag{11}
\]

\[
A(X_{\min})\ge\theta\ell\ge\theta D_*>0,
\qquad
G(X_{\min})\ge\psi\ell\ge\psi D_*>0,
\tag{12}
\]

and the exact product-root Nash correspondence at the cap of
\(z_{\min}.1\) is the singleton all-Continue root:

\[
\boxed{
 q\text{ is exact cap--Nash against }B(z_{\min})
 \quad\Longleftrightarrow\quad q=\mathbf C.
}
\tag{13}
\]

### Theorem B: exhaustive four-player landing

Exactly one of the following numerical alternatives holds.

1. **Minimum landing.**  \(\ell=D_*\).  Then \(z_{\min}\) has positive
   total opponent incidence for the zero-debt observer \(j\), and therefore
   enters the law-tight reset-rigid chamber.  The positive signed atom and
   the separate positive actual-gain passport in (12) remain present in the
   closed four-profile descendant carrier.

2. **Strict descendant-neutral port.**  \(D_*<\ell\).  Then
   \(z_{\min}\) is strictly off the minimum fibre, has zero \(j\)-debt, and
   has all Continue as its unique exact cap root, while both quantitative
   passports (12) survive.  The reset-face point \(m\) from (6a) is a second
   unique-all-Continue point and remains an external same-origin certificate.
   No law match, descendant relation, or temporal composability between
   \(m\) and \(z_{\min}\) is asserted.

The selected point has **closed-descendant provenance**: it is a limit of
literal common-prefix descendants from (7).  The theorem does not recover
one finite prehistory code, one marked date, or an extension-compatible
chronology from that closure point.

## Conjecture-facing change

The named live obligation is the strictly off-minimum vanishing-response
endpoint in
[`FIN4_FULL_DEBT_CHAMBER_CONSUMER.md`](../questions/FIN4_FULL_DEBT_CHAMBER_CONSUMER.md),
and more specifically the non-well-founded born-root descent below that
endpoint.

Before this theorem, every positive-absorption root born at a limiting cap
gave a strict real-valued debt decrease, but an infinite sequence of such
decreases could converge above \(D_*\) and supplied neither a finite rank nor
a charged return.  Theorems A and B replace the whole infinite descendant
choice by one compact minimization:

```text
off-minimum born-root descendant family
  -> minimum-fibre reset-rigid entry
     or strictly off-minimum unique-all-Continue descendant port,
```

while preserving both the signed response/sibling atom and the distinct
source/full-replacement payoff gain at fixed positive debt-relative scales.
This strictly narrows the third target-side alternative in the full-debt
question.  It does not consume the reset-rigid chamber or the strict
descendant-neutral port.

## Definitions and assumptions

Before absorption, the public history is the all-Continue string.  Behavioral
strategies may use the full history and independent private randomization.
The cap is over complete unilateral behavioral replacements; no stationary,
finite-time, finite-memory, or cap-attainment restriction is imposed.

A product root is one independent mixed action for each player at one date.
For a root \(q\), write

\[
s(q)=\prod_i q_i(\mathsf{Continue})
\]

for joint survival.  A finite root word is executed in its displayed order
before the original behavioral profile.  The theorem uses arbitrary words
only to construct the closed carrier.  Exact Nash is imposed only on the
single root used in the minimization argument.

The terminal law is time-forgetting.  Closure in
\(\mathcal C^{\rm law}\) therefore retains the complete terminal outcome law
and all unrestricted cap coordinates, but it does not retain a stopping-law
path, marked date, or finite ancestry code.  No such recovery is used in the
proof.

## Source correspondence

The supplied four profiles in (2) are literal project profiles:

- `QuittingStoppingLawVanishingDebtRectangleSequence` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/OffDiagonal/AtomRectangleSequenceAlternative.lean`
  supplies the active mover, observer, strict rank map, common pure response,
  terminal label, positive signed atom, and vanishing observer debt.  Its
  first atom endpoint is \(R_n\), and its same-response comparison endpoint
  is \(Q_n\).
- `QuittingPositiveMinimumDebtTangentFamily.fullReplacementProfile` and
  `fullReplacementPrescribedGain_tendsto_baseDebt` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PositiveTotalSlopeFullReplacement.lean`
  supply \(E_n,S_n\) and (5).  Positivity follows because the rectangle
  mover is a subtype member of `positiveDebtSupport`.
- `QuittingStoppingLawRectangleResetFaceDispatch` and its exact
  `unique_capNash` field in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/RectangleResetFaceMinimizer.lean`
  supply the external point \(m\) in (6a); no relation stronger than the
  stored same-origin conjunction is used.
- The common-word semantic/law action and the exact scaling of an actual
  payoff difference are modeled by `QuittingMarkedPairDecoratedFamily`,
  `terminalPayoff_sub_rootThenContinuation`,
  `rawDecoration_actualGain_eq`, and `prefixMap_mem_carrier` in
  `Research/Quitting/NormalizedPassportPrefixOrbit.lean`.
- The compact-minimization engine is the direct four-coordinate extension of
  `normalizedPassportSlice_isCompact`,
  `prefixMap_mem_normalizedPassportSlice_of_isZeroNash`,
  `minimum_normalizedPassportSlice_exactRoot_eq_allContinue`, and
  `exists_minimum_normalizedPassportSlice_eq_or_strict_inert` in
  `Research/Quitting/NormalizedPassportMinimizer.lean`.
- Minimum landing uses
  `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`,
  `terminalSemanticLaw_singletonNever_zeroDebt_cap_eq_singletonReward` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSingletonNeverCapTightness.lean`,
  `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`,
  and `exists_quittingLawTightResetRigidChamber` in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashStrictMinimum.lean`.
- Finite root-game Nash existence is `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`.

The checked normalized-passport theorem treats one marked endpoint, one fixed
tail coordinate, one marked-mass passport, and one actual-gain pair.  It does
not identify the response/sibling atom pair with the source/replacement gain
pair.  The new mathematics is the exact four-profile adapter (2), the common
subsequence argument (4)--(6), and the fourfold closed slice (7)--(10).  No
paper theorem is invoked.

## Proof

### 1. One common four-profile cluster has both positive passports

The rectangle rank map \(k_n\) is strict, hence \(k_n\to\infty\).  The
literal rectangle inequality gives \(A_n\ge\gamma>0\) at every rank.  The
full-replacement theorem gives

\[
G_n=
\operatorname{fullReplacementPrescribedGain}(p,k_n)
 \longrightarrow d_p(z_*)>0.
\tag{14}
\]

The compactness selection producing (6) may be refined so that \(J(E_n)\)
and \(J(S_n)\) also converge.  A strict or cofinal further subsequence still
tends to infinity, so it preserves (14), the uniform bound on \(A_n\), and
the convergence \(d_j(R_n)\to0\).  Its empty-word cluster \(X_0\) therefore
satisfies

\[
d_j(X_0^R.1)=0,
\qquad A(X_0)>0,
\qquad G(X_0)>0,
\qquad D(X_0^R.1)=L\ge D_*>0.
\tag{15}
\]

Choose \(\theta,\psi\) as in (9).  Then
\(X_0\in\mathcal K^0_{\theta,\psi}\), proving nonemptiness.

### 2. The arbitrary-word carrier is compact and prefix closed

The fourfold joint carrier is compact, so \(\mathcal K=\overline{\mathcal O}\)
is compact.  Prefixing by one fixed product root is continuous on every
semantic and law coordinate.  It sends the raw point indexed by \((n,W)\) to
the raw point indexed by \((n,q::W)\).  Therefore it maps \(\mathcal K\) into
itself by continuity.

For a root \(q\) with joint survival \(s=s(q)\), the fresh root contributes
the same absorbing terminal law to the two response coordinates.  The fresh
contribution cancels in their law difference, so

\[
A(q\star X)=sA(X).
\tag{16}
\]

It likewise contributes the same prescribed payoff to \(E\) and \(S\), so

\[
G(q\star X)=sG(X).
\tag{17}
\]

These identities hold for arbitrary roots; no Nash condition is needed.

If \(q\) is exact cap--Nash against the cap of \(X^R\), exact root transport
also gives, coordinatewise,

\[
d_i(q\star X^R)=s\,d_i(X^R),
\qquad D(q\star X^R)=sD(X^R).
\tag{18}
\]

Equations (16)--(18) show that exact prefixing preserves all three conditions
in (10).  Thus the closed slice is exact-prefix invariant.  It is compact
because its defining functions are continuous.

### 3. Minimization forces root neutrality

Choose a debt minimizer \(X_{\min}\) of the compact nonempty slice.  Every
first endpoint in the slice belongs to the terminal semantic carrier, so
global minimality gives \(D_*\le\ell\).  Since \(X_0\) lies in the slice,
\(\ell\le L\).  The remaining inequalities (11)--(12) are the defining slice
conditions.

Let \(q\) be any exact product root against \(B(z_{\min})\), and let
\(s=s(q)\).  Exact-prefix invariance puts \(q\star X_{\min}\) back in the
same slice.  Its first debt is \(s\ell\), so minimality gives

\[
\ell\le s\ell.
\]

Because \(\ell\ge D_*>0\) and \(s\le1\), one has \(s=1\).  A product root
has joint survival one exactly when every player's root action is surely
Continue.  Thus every exact root is all Continue.  Finite root-game Nash
existence supplies at least one exact root, so all Continue itself is exact.
This proves (13).

### 4. Minimum landing has automatic opponent incidence

Suppose \(\ell=D_*\).  The joint point \(z_{\min}\) is globally minimizing,
so the hard residual supplies a finite terminal coalition \(C\) with
\(\mu^{R}(C)>0\).

Assume, for contradiction, that total opponent incidence for \(j\) is zero.
Every positive finite terminal coalition must then equal \(\{j\}\).  Since
the finite terminal set is finite, the entire law is supported on
\(\{j\}\) and Never, with positive singleton mass.  The zero-debt identity
in (10) and singleton/Never cap tightness give

\[
B_j(z_{\min})=r_j(\{j\}).
\tag{19}
\]

The global singleton margin (1) gives

\[
0<D_*\le B_j(z_{\min})-r_j(\{j\})=0,
\]

a contradiction.  Hence opponent incidence is positive.  Taking the
origin, saturation minimum, and displayed point to be this same global
minimum joint-law point meets the law-tight reset-rigid adapter, proving
Alternative 1 of Theorem B.  If \(\ell>D_*\), Alternative 2 is simply the
strict case of (11)--(13).

## Boundary tests

### The signed atom cannot replace the actual-gain pair

Take two literal date-zero pure-root profiles, one terminating in coalition
\(T\) and the other in a different coalition \(T'\).  Choose rewards

\[
r_j(T)=1,\qquad r_p(T)=-1,\qquad r_p(T')=0.
\]

At terminal coordinate \(T\), the observer's signed law atom from the first
profile relative to the second is \(+1\), while the mover's prescribed-payoff
difference is \(-1\).  Thus a positive response/sibling atom does not imply a
positive payoff gain.  The distinct \((E_n,S_n)\) pair in (2) is essential.

### Strict real descent need not terminate or carry late charge

Fix \(D_*<\ell<L_0\) and set

\[
L_k=\ell+2^{-k}(L_0-\ell),
\qquad c_k={L_{k+1}\over L_k}.
\]

Every \(c_k\in(0,1)\) is the survival of a product root.  Setting
\(A_k=\theta L_k\) and \(G_k=\psi L_k\) obeys all scalar scaling identities,
but no finite level equals \(D_*\), and

\[
\prod_{k<N}c_k={L_N\over L_0}\longrightarrow{\ell\over L_0}>0.
\]

Moreover every sufficiently late block has vanishing total absorption.
Hence debt descent and invariant passport ratios alone cannot replace the
compact minimization.

### Closed descendant provenance does not recover ancestry

Let every reward coordinate be zero.  The profile in which all players Quit
at date zero and the profile in which all Continue once and all Quit at date
one have the same semantic pair and the same time-forgetting terminal law,
but different finite prehistories and marked dates.  A point of the closed
semantic/law carrier cannot distinguish these codes.  The theorem therefore
claims only closed-descendant provenance, exactly as required.

### The positive-minimum hypothesis is essential

If \(D_*=0\), the inequality \(\ell\le s\ell\) at a zero-debt minimizer gives
no information about \(s\).  Absorbing exact roots may coexist with the
minimizer.  The proof of unique all-Continue uses \(\ell\ge D_*>0\) at its
only division/sign step.

## Adapter and consumer

The actual-data adapter is the four-profile construction (2) on the strict
rank sequence already supplied by the vanishing-response rectangle.  It does
not infer one passport from the other.  Equation (14) gives the second
passport on those exact ranks, and one common compact subsequence gives the
initial point of the slice.  Applying the same arbitrary finite word to all
four literal profiles proves the carrier action directly.

The output is consumed as a strict reduction, not as a uniform-equilibrium
endpoint:

- minimum landing enters the existing reset-rigid chamber question; and
- strict landing replaces every finite or infinite born-root descent below
  the off-minimum response endpoint by one uniquely all-Continue
  descendant-neutral port carrying both positive passports.

No theorem here converts that strict port into terminal approximate Nash
profiles, a charged chronological return, or a renewable finite-rank child.

## Lean handoff

The narrow implementation should define a four-profile decoration rather
than add a free scalar gain field to the existing response pair.  Suggested
components are:

```text
QuittingFourProfileResponseDecoration
  response        : QuittingTerminalSemanticLawPoint (Fin 4)
  sibling         : QuittingTerminalSemanticLawPoint (Fin 4)
  replacement     : QuittingTerminalSemanticLawPoint (Fin 4)
  source          : QuittingTerminalSemanticLawPoint (Fin 4)

QuittingFourProfileResponseFamily
  packet          : QuittingStoppingLawVanishingDebtRectangleSequence frontier
```

The base decoration should be definitionally built from the four literal
profiles in (2).  The prefix map applies
`quittingTerminalSemanticPrefix` and
`quittingTerminalOutcomeLawPrefix` to all four coordinates.  Define its raw
orbit by a rank and a finite arbitrary root word, then take closure.  Prove:

```text
fourProfile_raw_atom_eq
fourProfile_raw_actualGain_eq
fourProfile_actualGain_tendsto_baseDebt
fourProfile_prefixMap_mem_carrier
fourProfile_prefix_atom_eq_continueMass_mul
fourProfile_prefix_gain_eq_continueMass_mul
fourProfile_normalizedSlice_isCompact
fourProfile_prefix_mem_slice_of_isZeroNash
fourProfile_minimizer_exactRoot_iff_allContinue
fourProfile_minimizer_eq_globalMinimum_or_strict
```

The gain convergence should invoke
`fullReplacementPrescribedGain_tendsto_baseDebt` composed with
`packet.rank_strictMono.tendsto_atTop`; it must not be introduced as a
structure assumption.  The minimum-landing wrapper should invoke the four
named hard-residual declarations in the source correspondence rather than
store positive incidence as a field.

Useful finite checks are:

1. prefix a four-profile decoration by a root of rational survival and check
   both passport scalings exactly;
2. verify that the response debt scales only when the root is exact against
   the response cap; and
3. instantiate the atom/gain sign regression above to ensure the two profile
   pairs cannot be conflated.

## Scope and nonclaims

This theorem does not prove a four-player uniform-equilibrium payoff.  It
does not consume the reset-rigid chamber or the strict descendant-neutral
port.  It does not produce a chronological near-return, a positive exact
root at the minimizer, a well-founded recursive rank, or a replayable block.

It does not preserve one literal prehistory, absolute marked date, stopping
law, or source code through compact closure.  It does not assert that the
external reset-face point is law matched to, descended from, or temporally
composable with the new minimizer.  The result concerns the complete
behavioral cap and terminal semantic/law carrier; it is not restricted to
stationary or bounded stopping-time deviations.

## Lean formalization record

Pre-formalization packet SHA-256:
`864d4b4ccce597fb6449a48365e95d59a9b2b46f60cd75df71b6f99d858640cd`.

The checked generic descendant-slice geometry and the Fin4 rectangle landing
are integrated in commit
`6bfc4adca29b13cf2afb60949a7819c6a6c1ffce`. Their production owners are
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFourProfileDescendantSlice.lean`
and
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourProfileDescendantSliceLanding.lean`.

The principal generic declarations are
`QuittingFourProfileResponseFamily.ConvergentFourProfilePassport`,
`QuittingFourProfileResponseFamily.normalizedDescendantSlice`,
`QuittingFourProfileResponseFamily.normalizedDescendantSlice_isCompact`,
`QuittingFourProfileResponseFamily.exists_minimum_normalizedDescendantSlice`,
`QuittingFourProfileResponseFamily.minimum_normalizedDescendantSlice_isZeroNash_iff_allContinue`,
and
`QuittingFourProfileResponseFamily.exists_minimum_normalizedDescendantSlice_eq_or_strict_inert`.
The source-facing declarations are
`QuittingStoppingLawRectangleJointAtomLimit.exists_convergentFourProfilePassport`,
`QuittingFourProfileDescendantSliceLanding`, and
`exists_fourProfileDescendantSliceLanding`.

Evidence seals are `M` and `L`, together with a branch-local `A`: the final
adapter consumes a supplied rectangle joint-law limit and a supplied Fin4
hard residual. It does not produce that rectangle or residual. There is no
downstream `C`; neither the minimum reset-rigid arm nor the strictly
off-minimum arm is consumed.

The formalized result supplies no ancestry or executable chronology, no
renewable reconstruction, and no iteration of either landing arm. It does
not construct a uniform-equilibrium payoff. The reset-rigid witness is a
static semantic/law conclusion, and the strictly off-minimum alternative is
only a classified port, not a chamber consumer.
