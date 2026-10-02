# Persistent-base fixed-law cap rigidity

Author: `GPT`

Independent reviews:
[adversarial falsification](../feedback/MIN_RET_FOLLOWUP__BY_GATE_FALSIFIER.md),
[strengthening review](../feedback/MIN_RET_FOLLOWUP__BY_GATE_STRENGTHENER.md), and
[source and freshness audit](../feedback/MIN_RET_FOLLOWUP__BY_GATE_SOURCE_AUDIT.md)

## Exact statement

Let \(I\) be a finite player set. Terminal outcomes are

\[
\Omega=\{\mathsf{Never}\}\cup
\{S\subseteq I:S\ne\varnothing\}.
\]

Let \(\mathcal J\) be the joint terminal semantic/law carrier: the closure of
the pairs

\[
\bigl(\operatorname{Sem}(\sigma),
      \operatorname{Law}(\sigma)\bigr)
\]

over actual behavioral profiles \(\sigma\). For a semantic pair \(z\), write
\(U_i(z)\) for prescribed payoff, \(B_i(z)\) for the unrestricted unilateral
behavioral cap, \(d_i(z)=B_i(z)-U_i(z)\), and
\(D(z)=\sum_i d_i(z)\).

### Theorem A: carrier erasure bound

Let \((y,\mu)\in\mathcal J\), let \(i\ne j\), and suppose

\[
\mu(\mathsf{Never})=0,\qquad
\mu(S)=0\quad\text{whenever }j\notin S.
\tag{A1}
\]

Define

\[
E_i(\mu,j)=
\sum_{\substack{S\ne\varnothing\\j\in S}}
  \mu(S)\,r_i(S\setminus\{i\}).
\tag{A2}
\]

The coalition \(S\setminus\{i\}\) is nonempty because \(j\ne i\). Then

\[
\boxed{E_i(\mu,j)\le B_i(y).}
\tag{A3}
\]

### Theorem B: cap rigidity on a sure-quitting base

Let \(B\subseteq I\) with \(|B|\ge2\). Let \(q\) be a product root at which
every member of \(B\) Quits surely, followed by an arbitrary behavioral
continuation. Let \(\sigma\) be the resulting actual profile and put

\[
x=\operatorname{Sem}(\sigma),\qquad
\nu=\operatorname{Law}(\sigma).
\]

For every \((y,\nu)\in\mathcal J\),

\[
U(y)=U(x)
\tag{B1}
\]

and

\[
\boxed{B_i(x)\le B_i(y)\qquad(i\in B).}
\tag{B2}
\]

No assumption on the players outside \(B\) is needed for (B2).

### Theorem C: unique fixed-law debt minimum

In the setting of Theorem B, suppose additionally that every player outside
\(B\) is solved at \(x\):

\[
B_k(x)=U_k(x)\qquad(k\notin B).
\tag{C1}
\]

Then, for every \((y,\nu)\in\mathcal J\),

\[
B_i(x)\le B_i(y)\qquad(i\in I)
\tag{C2}
\]

and

\[
D(x)\le D(y).
\tag{C3}
\]

Consequently, if \(D(y)\le D(x)\), then

\[
\boxed{y=x.}
\tag{C4}
\]

Thus \(x\) is the unique semantic minimizer of debt on the joint-carrier fibre
over \(\nu\).

### Theorem D: Fin4 pair-base reset alignment

For the explicit four-player pair-base paid/reset target already constructed
in the repository, let \(x\) be its literal stationary semantic pair and
\(\nu\) its literal terminal law. Let \(y\) be the returned semantic pair of
its fixed-law reset dispatch. Then

\[
\boxed{y=x.}
\tag{D1}
\]

In particular, the reset return is attained by the original literal
pair-base stationary profile; no separate fixed-law cap-minimizer remains.

## Conjecture-facing change

Before this result, the Fin4 pair-base reset route retained two semantic
objects with the same prescribed payoff and terminal law:

- the literal stationary paid/reset target; and
- a separately selected fixed-law returned point known only to have no larger
  debt.

Theorem D identifies them as complete semantic pairs, including every
unrestricted cap coordinate. This closes the fixed-law cap-comparison and
source-alignment seam on that branch.

The checked ordinary reset dispatch can therefore be applied at the literal
pair-base target itself. Its exact output is:

- a positive-absorption exact cap root whose literal prefix is an actual
  strict-debt child with a changed terminal law; or
- all-Continue is an exact cap root and fixes the target semantic pair.

This result does not make the strict real-valued decrease renewable and does
not consume the all-Continue fixed-face arm. A separate already-checked
maximal-root theorem strengthens the latter arm to uniqueness; that
strengthening is not new content of this packet.

## Definitions and assumptions

The joint carrier uses the complete terminal law, including
\(\mathsf{Never}\), and the complete terminal semantic pair. Its cap
coordinates are suprema over all unilateral behavioral strategies, not only
stationary strategies or finite deadlines.

The literal source in Theorem B has one sure-quitting root. Since
\(B\ne\varnothing\), absorption is certain at that root. Its continuation is
unreachable under the prescribed profile. Since \(|B|\ge2\), after any one
base member changes to Continue, another member of \(B\) still Quits surely,
so the continuation remains unreachable.

The solved-complement hypothesis is used only to extend cap domination from
the sure base to all coordinates. It is not part of Theorem B.

## Source correspondence

The joint carrier and the fact that one terminal law fixes its prescribed
reward moment are in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`,
notably `terminalSemanticLawCarrier_rewardMoment`.

The literal Fin4 source and its solved complementary players are supplied by
`FinFourPairBaseStationaryDebtLocalization` and
`FinFourPairBaseStationaryDebtLocalization.free_solved` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBaseStationaryDebtLocalization.lean`.

The paid/reset target and fixed-law dispatch are in
`PairBasePaidResetAlignment.lean` and
`PairBasePaidResetPayoffAlignment.lean`. The relevant dispatch fields are
`QuittingFixedLawResetDispatch.joint` and
`QuittingFixedLawResetDispatch.target_ge` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`.

Those declarations provide

\[
(y,\nu)\in\mathcal J,\qquad D(y)\le D(x),
\]

but do not prove \(B(x)\le B(y)\) or \(y=x\). Theorems A--D supply that new
comparison.

The separate theorem
`QuittingPaidCapLiftedSource.maximalOneStepPaidResetRegeneration_or_uniqueAllContinue`
in `Research/Quitting/PaidCapMaximalOneStepRegeneration.lean` already gives
the maximal-root strict-child/unique-all-Continue alternative from the actual
paid/reset source. It is an independent downstream route and is not claimed
as new here.

No paper theorem is used.

## Proof

### Proof of Theorem A

Choose actual behavioral profiles \(\tau_n\) whose joint semantic pairs and
laws converge to \((y,\mu)\). Let \(\mu_n\) be the law of \(\tau_n\). Replace
player \(i\)'s complete strategy by Never and couple the modified play with
the original play using the same random choices for every opponent.

Call a path good when the original outcome is a finite coalition \(S\)
containing \(j\). Before the original absorption date, all players Continued.
Changing \(i\) to Never cannot cause earlier absorption. At the original
absorption date, \(j\) still Quits, so the modified play absorbs at that same
date with coalition exactly \(S\setminus\{i\}\).

The failure event consists of the genuine Never outcome together with finite
coalitions omitting \(j\):

\[
F_j=\{\mathsf{Never}\}\cup\{S:j\notin S\}.
\]

Let \(M\) bound the absolute rewards. The payoff of this one legal Never
deviation is at least

\[
\sum_{\substack{S\ne\varnothing\\j\in S}}
 \mu_n(S)r_i(S\setminus\{i\})
-M\mu_n(F_j).
\tag{P1}
\]

The full behavioral cap dominates this deviation. By (A1) and coordinatewise
law convergence, \(\mu_n(F_j)\to0\), while the finite sum in (P1) converges to
\(E_i(\mu,j)\). Joint semantic convergence sends the cap to \(B_i(y)\).
Passing to the limit proves (A3).

### Proof of Theorem B

The literal law \(\nu\) has zero Never mass and is supported on coalitions
containing \(B\). The complete law fixes the prescribed reward moment, so
every \((y,\nu)\in\mathcal J\) satisfies (B1).

Fix \(i\in B\), and choose \(j\in B\setminus\{i\}\). At the literal source,
every behavioral replacement of \(i\) is strategically determined by its
action at the first root:

- Quit gives \(U_i(x)\);
- Continue leaves \(j\) Quitting surely and gives \(E_i(\nu,j)\).

Every randomized first-root action is a convex combination of these
endpoints, and later behavior is unreachable. Therefore

\[
B_i(x)=\max\{U_i(x),E_i(\nu,j)\}.
\tag{P2}
\]

Theorem A gives \(B_i(y)\ge E_i(\nu,j)\). Nonnegativity of carrier debt and
(B1) give \(B_i(y)\ge U_i(y)=U_i(x)\). Equation (P2) now proves (B2).

### Proof of Theorem C

For \(i\in B\), use Theorem B. For \(k\notin B\), (C1), (B1), and
nonnegative carrier debt give

\[
B_k(x)=U_k(x)=U_k(y)\le B_k(y).
\]

This proves (C2). Since prescribed payoffs agree,

\[
D(y)-D(x)=\sum_i(B_i(y)-B_i(x))\ge0,
\]

which proves (C3). If the reverse debt inequality also holds, every summand
in this finite sum is nonnegative and the sum is zero. Hence every cap
coordinate agrees; (B1) then gives \(y=x\).

### Proof of Theorem D

The literal pair-base target has two sure quitters and its two complementary
coordinates are solved, so Theorem C applies. The reset dispatch's `joint`
field places \((y,\nu)\) in the same joint-carrier fibre. Thus

\[
B(x)\le B(y),\qquad D(x)\le D(y).
\]

Its `target_ge` field gives \(D(y)\le D(x)\). The equality clause of Theorem C
therefore yields \(y=x\).

## Boundary tests

### Two sure quitters are necessary

With players \(i,j\), take the singleton base \(\{i\}\). In profile \(x\),
player \(i\) Quits at date zero and player \(j\) Quits at date one. In profile
\(y\), player \(i\) again Quits at date zero and \(j\) Never Quits. Give
player \(i\) reward one at \(\{j\}\) and zero at every other coalition, and
give player \(j\) reward zero everywhere.

Both profiles have the same law, concentrated on \(\{i\}\), the same
prescribed payoff zero, and the nonbase player is solved. But \(i\) can
Continue in \(x\) and receive one when \(j\) Quits, whereas every deviation in
\(y\) pays zero. Hence \(B_i(x)=1>B_i(y)=0\).

### The common law is necessary

Let \(B=\{i,j\}\), let both players Quit at the source root, and set

\[
r_i(\{i,j\})=0,\qquad r_i(\{j\})=1,\qquad
r_i(\{i\})=0.
\]

The source cap of \(i\) is one by Continuing and leaving \(j\) to Quit.
Against an unrelated all-Never profile, \(i\)'s cap is zero. The prescribed
payoffs may agree, but the laws differ.

### The comparison may be strict

Let \(B=\{i,j\}\). At the literal source both Quit at date zero. Give \(i\)
reward zero at \(\{i,j\}\) and \(\{j\}\), but reward one at \(\{i\}\). The
source cap is zero. In another profile both players Quit at date one, so the
law and prescribed payoff are unchanged, but \(i\) can Quit alone at date
zero and obtain one. Thus the same-law comparison can be strict.

Taking \(y=x\) gives equality, so the inequalities cannot be strengthened to
strict inequalities.

## Adapter and consumer

The actual-data adapter is the existing explicit Fin4 pair-base paid/reset
target. Its persistent pair gives the sure base, and
`free_solved` supplies the solved complement.

The consumer is the fixed-law reset dispatch. Theorem D rewrites its returned
semantic pair to the literal source pair. The checked `dynamic_exit` theorem
then yields the changed-law strict child or the explicit all-Continue fixed
face at that same literal target.

The independent maximal-root theorem can instead be applied directly to the
same actual paid/reset source to obtain a strict maximal-root child or unique
all-Continue. This existing stronger root dispatch does not consume the
changed-law child or the stall.

## Lean handoff

Suggested declarations, from general to Fin4-specific:

- `terminalSemanticLawCarrier_envelope_ge_erasureMoment_of_sureMember`;
- `quittingSureBaseRoot_envelope_eq_max_prescribed_erasureMoment`;
- `quittingSureBaseRoot_cap_le_sameLaw_on_base`;
- `quittingSureBaseRoot_cap_le_sameLaw_of_complement_solved`;
- `quittingSureBaseRoot_unique_fixedLawDebtMinimizer_of_complement_solved`;
- `FinFourPairBasePaidResetTarget.returned_eq_of_fixedLawResetDispatch`; and
- `FinFourPairBasePaidResetTarget.fixedLawReset_absorbingChild_or_allContinueFace`.

The carrier erasure proof should use a joint realizing sequence and the actual
Never deviation. It must not replace the complete behavioral cap by a
stationary cap or add the desired comparison as a structure field.

## Scope and nonclaims

This theorem does not prove a uniform-equilibrium payoff, consume the
minimum-return component, make the changed-law strict child renewable, or
eliminate the all-Continue stall. It does not derive maximality or uniqueness
from fixed-law minimization. Its precise contribution is complete cap
alignment of the returned fixed-law point with the literal pair-base source.

## Formalization record

The export packet at intake had SHA-256
`2e5bdef35313e552e1df84188701e7a11cbfdbdbc6f4b4667d3e5767a5051f3f`.
The checked implementation was integrated and pushed at repository revision
`4a426737004d2440f366d9aa1f022755ae8451c5`.

The implementation is split across three production modules:

1. `UniformEquilibrium/Diagnostics/Quitting/TerminalLawErasureDeviation.lean`
   defines the full erasure failure mass, anchor mass, reward moments, and
   erasure moment.  Its capstone
   `quittingTerminalErasureMoment_sub_failure_le_envelope` proves the actual-
   profile Never-deviation estimate with the complete failure mass: the
   `Never` atom together with every finite coalition omitting the anchor.
2. `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFixedLawCapRigidity.lean`
   passes that estimate to the joint semantic/law carrier.  The declarations
   `terminalSemanticLawCarrier_envelope_ge_erasureMoment_sub_failure` and
   `terminalSemanticLawCarrier_envelope_ge_erasureMoment_of_sureMember`
   implement Theorem A.  The literal source identity is
   `quittingSureBaseRoot_envelope_eq_max_prescribed_erasureMoment`.
   `quittingSureBaseRoot_cap_le_sameLaw_on_base` implements Theorem B, while
   `quittingSureBaseRoot_cap_le_sameLaw_of_complement_solved`,
   `quittingSureBaseRoot_debt_le_sameLaw_of_complement_solved`, and
   `quittingSureBaseRoot_unique_fixedLawDebtMinimizer_of_complement_solved`
   implement Theorem C, including equality of the complete semantic pair.
3. `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/`
   `PairBasePaidResetCapRigidity.lean` attaches the generic result to the
   actual Fin4 pair-base target.  Theorem D is
   `FinFourPairBasePaidResetTarget.returned_eq_of_fixedLawResetDispatch`.
   The same-law minimum is also exposed literally by
   `FinFourPairBasePaidResetTarget.debtSum_le_of_sameLaw`.  The declarations
   `strictDebtPrefix_lawPrefix_ne_mass` and
   `fixedLawReset_absorbingChild_or_allContinueFace` state that the strict
   dynamic child changes the complete terminal law, or the dispatch takes the
   literal all-Continue fixed-face arm at the original target.

The semantic projection lemma
`terminalSemanticLawCarrier_fst_mem_carrier` retains its fully qualified API
but now lives in the lower
`TerminalSemanticResetIncidenceReturn.lean` owner.  The three new modules are
reachable from `UniformEquilibrium/Diagnostics/Quitting/All.lean` and from the
generated exhaustive `AxiomAudit.lean`.

Evidence seals:

- **M:** PASS.  The reviewed erasure coupling, complete failure event,
  sure-base cap comparison, solved-complement debt minimum, unique equality,
  and Fin4 specialization were rechecked without adding a stationary-only
  cap, unconditional dispatch, or unsupported uniqueness premise.
- **L:** PASS.  All three modules pass direct Lean checks and their production
  dependency closure.  Representative axiom probes for the carrier estimate,
  fixed-law minimum/equality, changed-law child, and Fin4 dynamic capstone
  report only `propext`, `Classical.choice`, and `Quot.sound`.
- **A:** PASS for the stated Fin4 source-attached result.  The adapter consumes
  the existing literal `FinFourPairBasePaidResetTarget`: its actual stationary
  profile and complete law, two sure-quitting base members, both solved
  complementary coordinates, and the checked fixed-law reset dispatch.  No
  new source certificate is supplied by the caller.
- **C:** PASS for fixed-law return alignment and the branch-local reset
  dispatch.  The returned semantic pair is rewritten to the literal source,
  and the strict child is consumed into a checked changed-law conclusion.
  This is not terminal `C`: neither the changed-law child nor the all-Continue
  arm reaches a uniform-equilibrium or trichotomy consumer.

Validation at revision `4a426737004d2440f366d9aa1f022755ae8451c5`
included the documentation gate, 109 script unit tests, execution of all 33
registered experiments, import-graph, proof-duplicate, reward-bound,
redundant-order, derivable-telescope, and trust checks, and a full
`lake build` of 11,072 jobs.  The generated axiom audit was exact.

Nonclaims:

- no theorem proves a uniform-equilibrium payoff or either direction of the
  AGKRS trichotomy;
- the strict child is not shown renewable, recurrent, near-minimal, or
  source-regenerating;
- the changed law is not identified, quantitatively separated from the old
  law, or connected to a return consumer;
- the all-Continue arm remains possible and is not converted into descent;
- fixed-law minimization does not imply maximal-root uniqueness; and
- the general sure-base theorems consume a supplied root, continuation, and
  same-law carrier point; only the Fin4 specialization has the checked
  actual-data adapter and branch-local consumer recorded above.
