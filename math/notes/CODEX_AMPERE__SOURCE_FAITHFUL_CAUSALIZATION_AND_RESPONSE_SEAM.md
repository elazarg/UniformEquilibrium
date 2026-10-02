# Source-faithful causalization and the exact common-response seam

## Status

Ordinary mathematics, not checked in Lean.  There is one substantive positive
producer here:

> An actual endpoint sequence which already converges to a positive-law
> minimum can itself be used as the suffix chronology of the regenerated
> minimum source.  No new realizing sequence has to be selected.

Consequently every finite family of complete response plans attached to the
endpoint sequence survives regeneration literally in the suffix and survives
the new exact cap prefix asymptotically without loss of response contrast.

There is also an exact finite seam lemma.  If one fixed observer and one
literal vertex chart are available around a paid cycle, failure to retain one
common response produces a quantitatively profitable switch between two
complete pure-time responses at one actual vertex, with the incoming response
still near-cap.

These statements do **not** finish the conjecture.  The present Fin4
regeneration can change the observer at the next paid construction.  A seam
between two different players' response values is not an executable
unilateral switch.  Even in the fixed-observer case, the seam packet reaches
the existing source-attached concentrated/minimum residual, whose
cross-coordinate cap leakage is the current open consumer.

### Response to independent review

The first independent review returned **REVISE**.  This version incorporates
both requested interface corrections.

1. The three-role endpoint adapter now takes
   \(1<|\texttt{marked}|\) explicitly.  Only with that input does the checked
   `perRank_mass_chain` give the routed mass floor at the incoming marked
   dates.
2. The output is a new source-faithful wrapper containing both the regenerated
   source and a public `FinFourMinimumAtomChronology`, with pointwise profile
   and mark equalities to the incoming endpoint sequence.  No such equality is
   inferred from the existential chronology field of the old regeneration
   type.

Section 3 now also distinguishes its checked pure-time overlap from the new
endpoint attachment and arbitrary-behavioral menu adapter.

## 1. Supplied-realizer causalization

Let \(r\) be a finite quitting table.  Let

\[
 z=(x,\nu)
\]

be a joint terminal semantic/law point satisfying

\[
 D(x)=D_*>0,
\]

where \(D_*\) is the infimum of total terminal debt over actual behavioral
profiles.  Suppose actual profiles \(\sigma_n\) are already supplied with

\[
 (\operatorname{Sem}(\sigma_n),\operatorname{Law}(\sigma_n))\to z. \tag{1.1}
\]

Fix one nonempty coalition \(T\), dates \(t_n\), and \(\lambda>0\) such that

\[
 \Pr_{\sigma_n}(T\text{ absorbs at }t_n)\ge\lambda.       \tag{1.2}
\]

For each \(n\), choose an exact cap--Nash root word \(W_n\) of length
\(n+1\) above \(\sigma_n\), and write

\[
 \widehat\sigma_n=W_n*\sigma_n,
 \qquad c_n=\Pr(W_n\text{ jointly survives}).            \tag{1.3}
\]

The checked exact cap-stack identity gives

\[
 D(\widehat\sigma_n)=c_nD(\sigma_n).                     \tag{1.4}
\]

Global minimality and \(0\le c_n\le1\) imply

\[
 D_*\le D(\widehat\sigma_n)\le D(\sigma_n).              \tag{1.5}
\]

By (1.1), \(D(\sigma_n)\to D_*\).  Squeezing in (1.5) gives

\[
 D(\widehat\sigma_n)\to D_*.                            \tag{1.6}
\]

Dividing (1.4) by \(D(\sigma_n)\), whose limit is positive, gives

\[
 \boxed{c_n\to1.}                                       \tag{1.7}
\]

The marked atom transports exactly:

\[
 \Pr_{\widehat\sigma_n}
   (T\text{ absorbs at }n+1+t_n)
 =c_n\Pr_{\sigma_n}(T\text{ absorbs at }t_n).            \tag{1.8}
\]

Hence it is eventually at least \(\lambda/2\).

Also, terminal-law convergence and (1.2) give

\[
 \nu(T)\ge\lambda>0.                                     \tag{1.9}
\]

For every sufficiently large \(n\), choose a finite cutoff \(h_n\) whose
\(T\)-stage masses sum to more than \(\nu(T)/2\).  Such a cutoff exists because
the complete \(T\)-law mass of \(\sigma_n\) tends to \(\nu(T)\), and the
complete mass is the increasing sum of its finite-stage masses.  Replace
\(h_n\) by

\[
 \max\{h_n,t_n+1\}.                                      \tag{1.10}
\]

This retains the half-law window and puts the supplied positive mark inside
the window.  Equations (1.1), (1.3), (1.6), (1.8), and (1.10) are precisely
the chronology fields needed for a `QuittingMinimumLawCausalSuffixAtom`, with
its suffix profiles definitionally equal to the supplied \(\sigma_n\).  No
closure representative or independently selected realizer is used.

### Relation to the checked theorem

`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` first
extracts realizers from joint-carrier membership and then performs exactly
the squeeze above.  The proof of the supplied-realizer version is its second
half, with the first existential extraction deleted.

## 2. Actual endpoint-law regeneration can be made literal

A `ConcentratedCollisionThreeRoleEndpointLaw` already stores an actual target
sequence

\[
 \tau_n=
 \operatorname{targetProfile}
   (\operatorname{packetProfile}(\operatorname{ranks}(n)))             \tag{2.1}
\]

such that

\[
 (\operatorname{Sem}(\tau_n),\operatorname{Law}(\tau_n))
   \to\operatorname{targetPoint}.                         \tag{2.2}
\]

It also stores one routed terminal \(T\) and marked dates \(t_n\).  Add the
explicit collision hypothesis

\[
 1<|\texttt{marked}|.                                    \tag{2.3}
\]

Only with this input does the checked theorem
`perRank_mass_chain endpoint hcollision n` give the per-rank bound

\[
 \Pr_{\tau_n}(T\text{ absorbs at }t_n)
   \ge\operatorname{packet.resolution}>0.                 \tag{2.4}
\]

In the equality arm,

\[
 D(\operatorname{targetPoint}.1)=D_*.                     \tag{2.5}
\]

Applying Section 1 to (2.1)--(2.5) constructs a regenerated
`FinFourMinimumAtomProducer` and, separately, one explicit
`FinFourMinimumAtomChronology` indexed by that source.

The public output must be a new wrapper, for example:

```text
FinFourSourceFaithfulMinimumTargetRegeneration where
  regeneration : FinFourThreeRoleMinimumTargetRegeneration source endpoint
  chronology : FinFourMinimumAtomChronology regeneration.next
  chronology_profiles_eq : forall n,
    chronology.profiles n =
      targetProfile (packetProfile packet (endpoint.ranks n))
        (packet.mark (endpoint.ranks n)) mover
  chronology_mark_eq : forall n,
    chronology.mark n = packet.mark (endpoint.ranks n)
```

It inherits or restates the existing equalities

```text
regeneration.next.point = endpoint.targetPoint
regeneration.next.atom.terminal = endpoint.routedTerminal.
```

The source and chronology are built from the same literal data, but the
pointwise equalities are public fields rather than hidden facts about one
existential witness.  The output therefore has:

* the same hard residual;
* a public equality from its point to `endpoint.targetPoint`;
* a public equality from its named terminal to `endpoint.routedTerminal`; and
* chronology profiles propositionally, pointwise equal to the actual target
  profiles (2.1), with the original marked dates propositionally retained.

This strengthens the current `nonempty_finFourMinimumTargetRegeneration`.
That declaration correctly regenerates the exact point and law, but its
documentation also correctly says that the new chronology is not asserted to
contain the incoming endpoint edge.  The supplied-realizer construction adds
exactly that missing source attachment and exposes it to downstream
consumers.

Without (2.3), a weaker source-faithful theorem still follows from
`terminalMass_floor` and `target_joint_tendsto`: retain the exact target
profiles but select new finite-window marks.  What does **not** follow from
the open endpoint object alone is equality of those new marks with the
incoming marked dates.  The stronger adapter deliberately takes (2.3).

No strategic estimate is used beyond the existing exact cap-prefix identity.
The adapter is therefore reusable for response endpoints, pure-pair
endpoints, and any other actual endpoint-law object carrying (2.2)--(2.5).

## 3. Finite response menus survive the new prefix

Fix one player \(o\).  At rank \(n\), let \(R_n^-\) and \(R_n^+\) be two
complete behavioral response plans for \(o\) against the suffix
\(\sigma_n\).  Define their shifts through \(W_n\) to Continue throughout
the prefix and then use \(R_n^-\) or \(R_n^+\) in the suffix.

Let

\[
 c_{-o,n}=\Pr(\text{every opponent of }o\text{ survives }W_n).          \tag{3.1}
\]

Before the suffix, both shifted plans prescribe exactly the same behavior by
\(o\).  Every payoff difference before the suffix therefore cancels.  The
exact prefix calculation is

\[
\begin{aligned}
 &U_o(\widehat\sigma_n[o\leftarrow\operatorname{shift}R_n^+])
 -U_o(\widehat\sigma_n[o\leftarrow\operatorname{shift}R_n^-])\\
 &\qquad =c_{-o,n}
 \left[
 U_o(\sigma_n[o\leftarrow R_n^+])
 -U_o(\sigma_n[o\leftarrow R_n^-])
 \right].                                                \tag{3.2}
\end{aligned}
\]

Joint survival implies opponent survival, so

\[
  c_n\le c_{-o,n}\le1.                                   \tag{3.3}
\]

Equation (1.7) yields

\[
 \boxed{c_{-o,n}\to1.}                                  \tag{3.4}
\]

Thus every bounded finite response menu attached to the incoming endpoint
sequence is retained literally as suffix data and its entire payoff-difference
matrix is transported through the exact prefix with asymptotic factor one.
This is stronger than retaining only the maximizing response or only the cap.

In particular, a common-response rectangle of fixed charge does not disappear
merely because its endpoint is causalized and exact cap prefixes are added,
provided it is represented as a **two-counterfactual contrast** and both
counterfactuals are shifted to Continue through the prefix.  If the lower
counterfactual is the old prescribed suffix strategy, its shifted version need
not equal the newly prefixed prescribed profile when the observer's cap root
action can Quit.  Thus (3.2) transports the response chart, not the raw
one-response gain relative to the new prescribed profile.  The latter has
different joint- and opponent-survival coefficients and is not claimed to
scale by one factor.

### Response-time edge cases

No bounded-time assumption is hidden in (3.2).

* If a response is `Never`, its shift is again `Never`.
* If a pure quitting date \(q_n\) is finite but tends to infinity, its shift
  is the finite date \(|W_n|+q_n\); (3.2) is rankwise exact and does not pass
  to a fixed calendar date.
* Two arbitrary behavioral suffix plans may be used, not only pure-time
  plans, provided their shifted versions take the same prescribed action
  throughout the finite prefix.  In a quitting game the only live public
  prefix history is all-Continue, so the shift is unambiguous.

The factor in (3.2) is opponent survival, not joint survival.  This is
necessary because the deviating observer is forced to Continue during the
prefix.  Inequality (3.3), rather than an identification of these two
survival probabilities, is what proves (3.4).

For relative pure-time responses, including `Never` and rank-dependent finite
dates, this substantially overlaps the checked theorem
`quittingRelativePureTimeTerminalValue_sub_prefixTransport`.  The checked
generic identity
`quittingRootSequenceTerminalValue_sub_eq_jointSurvivalWeight_mul` gives
another proof route once the updated live-root sequences and their survival
weight are identified.  The new claim here is therefore **not** the pure-time
transport formula.  It is that the source-faithful endpoint wrapper preserves
the exact suffix sequence on which those checked transports can be invoked at
the next producer pass.  The arbitrary-behavioral two-plan statement is a
small additional adapter to the generic identity.

## 4. Exact seam lemma on one fixed observer chart

The following is finite algebra, but it records the exact output of a failed
common-response selection.

Fix actual vertex profiles

\[
 P_0,P_1,\ldots,P_{K-1},\qquad P_K=P_0,                  \tag{4.1}
\]

one observer \(o\), and complete pure-time responses

\[
 Q_0,\ldots,Q_{K-1}.                                    \tag{4.2}
\]

Put

\[
 G_k(v)=U_o(P_v[o\leftarrow Q_k])-U_o(P_v).              \tag{4.3}
\]

Suppose edge \(k:v=k\to k+1\) satisfies

\[
 c_k\le G_k(k+1)-G_k(k),\qquad c_k>0,                   \tag{4.4}
\]

and its response endpoint is near-cap:

\[
 d_o(P_{k+1}[o\leftarrow Q_k])\le\varepsilon_k.          \tag{4.5}
\]

Summing (4.4) and reindexing gives

\[
\begin{aligned}
 \sum_kc_k
 &\le\sum_k\bigl(G_k(k+1)-G_k(k)\bigr)\\
 &=\sum_k\bigl(G_{k-1}(k)-G_k(k)\bigr).                 \tag{4.6}
\end{aligned}
\]

Hence some \(k\) satisfies

\[
 G_{k-1}(k)-G_k(k)
 \ge {1\over K}\sum_sc_s.                              \tag{4.7}
\]

The prescribed payoff cancels at this one literal vertex, so (4.7) is the
actual unilateral response switch

\[
\boxed{
 U_o(P_k[o\leftarrow Q_{k-1}])
 -U_o(P_k[o\leftarrow Q_k])
 \ge {1\over K}\sum_sc_s.}                             \tag{4.8}
\]

Moreover, by (4.5) for the incoming edge,

\[
 d_o(P_k[o\leftarrow Q_{k-1}])\le\varepsilon_{k-1}.      \tag{4.9}
\]

Thus the failed common-response choice yields more than a signed rectangle:

* one actual source profile `P_k[o <- Q_k]`;
* one actual complete unilateral replacement `Q_(k-1)`;
* fixed gain at least \((\sum c_s)/K\); and
* a target whose mover/observer debt is at most
  \(\varepsilon_{k-1}\).

If all \(P_k\) belong to one marked sibling chart and every \(Q_k\) occurs no
earlier than the common marked date, both response profiles retain the marked
atom by pure-time routing.  In Fin4, pigeonholing its routed nonempty
coalition loses only a fixed finite factor.  Hence (4.8)--(4.9) produces a
source-matched positive-atom, vanishing-target-debt switch packet.

This last atom statement includes the boundary cases:

* a response at the marked date inserts the observer into the marked
  coalition;
* a later response or `Never` erases the observer from the marked coalition;
* because the marked coalition in the response-rectangle application is
  nonsingleton, erasure still leaves a nonempty coalition; and
* response dates may diverge with the rank.  Only the rankwise order relative
  to the common mark is used.

If the two responses are attached to different marked dates or different
literal charts, none of these routing conclusions is automatic.  That is a
hypothesis of the seam lemma, not an inference from equality of limiting
laws.

This is the precise quantitative witness-switch seam.  It is not merely the
statement that two maximizing witnesses differ.

## 5. What the new producer repairs

The current actual-law regeneration loses the incoming endpoint chronology
only because it invokes the pointwise carrier causalization theorem in its
most general form.  Sections 1--2 show that this loss is avoidable.  The
actual target profiles already satisfy every hypothesis needed to serve as
the new suffix chronology.

Therefore the following field is producible from existing endpoint data:

\[
\boxed{
\begin{array}{c}
\text{the regenerated source uses the literal incoming target sequence,}\\
\text{and every finite historical response menu is retained and}\
\text{transported through its exact prefixes with factor }1-o(1).
\end{array}}                                             \tag{5.1}
\]

This removes arbitrary carrier re-realization as the explanation for
witness switching.

## 6. What still prevents a full common-response chart

There are two remaining failures.

### 6.1 Observer rotation

The endpoint-rise decoder selects the coordinate whose debt is newly paid at
that edge.  After the response, that coordinate has vanishing debt.  A later
regenerated paid construction may select a different observer.  If edge
\(k-1\) uses \(o_{k-1}\) and edge \(k\) uses \(o_k\ne o_{k-1}\), the analog of
the seam in (4.7) is a difference between **different players' payoffs**.
It is not a switch between two strategies of one player and has no direct
behavioral implementation.

Finite label stabilization fixes the cyclic word of observers; it does not
make that word constant.  The four-phase cyclic plateau is the exact local
model of this rotation.

### 6.2 The fixed-observer seam returns to the current residual

When one observer is fixed, (4.8)--(4.9) is executable and retains an atom in
the common marked chart.  But changing \(o\)'s prescribed response can raise
the other three unrestricted caps.  Global minimality supplies the matching
lower leakage needed to keep total debt above \(D_*\); it supplies no upper
or no-entry bound.

Thus the seam packet is another source-attached concentrated/minimum paid
endpoint.  The existing concentrated-packet consumer localizes exactly that
object but does not yet turn it into terminal approximants, an admissible
return, or renewable support descent.  Treating (4.8) alone as a chronology
consumer would repeat the cross-coordinate cap-leakage gap.

The unresolved finite interface has therefore narrowed to:

\[
\boxed{
\begin{array}{c}
\text{either prevent observer rotation through positive-minimum provenance,}\\
\text{or charge a change of observer by an executable cross-coordinate seam;}\\[1mm]
\text{then consume the fixed-observer near-cap switch without cap leakage.}
\end{array}}                                             \tag{6.1}
\]

## 7. Why semantic/law equality alone cannot replace (5.1)

There is a two-player exact timing regression.  Let \(c\) be a clock and
\(a\) an atom tester, with

\[
 r_c(\{c\})=-1,
 \qquad r_a(\{c,a\})=1,
\]

and all other displayed rewards zero.  For each \(N\), let \(c\) Quit
deterministically at date \(N\) and let \(a\) play Never.

Every such profile has the same prescribed payoff, behavioral cap, debt, and
complete terminal law:

\[
 U=(-1,0),\qquad B=(0,1),\qquad d=(1,1),qquad
 \operatorname{Law}=\delta_{\{c\}}.                      \tag{7.1}
\]

But the pure-time response menu of \(a\) is translated:

\[
 U_a(Q_t^a;\sigma^N_{-a})=\mathbf 1_{\{t=N\}}.          \tag{7.2}
\]

Thus the same joint semantic/law point admits actual realizers whose
maximizing pure-time witness occurs at any desired date.  A causalization
which reselects realizers cannot preserve a fixed response chart merely from
point equality.

This table has global minimum zero, so it is not a counterexample to a
positive-minimum theorem.  Its role is exact: it shows why the literal
supplied-realizer construction in Sections 1--2 is necessary and why an
abstract equality of terminal semantic/law points cannot replace it.

## Source audit

The bounded sources inspected were:

* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`;
* `Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean`;
* `Research/Quitting/FinFourProducerAtlas/ThreeRoleRegeneration.lean`;
* `Research/Quitting/FinFourProducerAtlas/Source.lean`;
* `exports/FIN4_MINIMUM_RESPONSE_CHORD_ATOM_AND_SOURCE_REGENERATION.md`;
* `exports/FIN4_MINIMUM_RESPONSE_CHORD_ACTUAL_LAW_REGENERATION.md`;
* `notes/CODEX_ROOT__COMMON_RESPONSE_POTENTIAL_MONODROMY_CONSUMER.md`.

The exact cap-stack scaling and atom transport used in Section 1 are already
checked as `quittingTerminalDebtSum_capNashRootStack_eq` and
`quittingStageCoalitionMass_literalRootStack_add_length`.  The new theorem is
the supplied-realizer packaging and endpoint adapter, not either identity.

Other named checked inputs are:

* `exists_quittingCapNashRootStack`, for an exact word of each prescribed
  length;
* `exists_finiteWindow_sum_stageCoalitionMass_gt`, for the half-law finite
  window in (1.10);
* `ConcentratedCollisionThreeRoleEndpointLaw.target_joint_tendsto` and
  `perRank_mass_chain` with the explicit collision input, for (2.2)--(2.4);
* `quittingRelativePureTimeTerminalValue_sub_prefixTransport`, for the
  pure-time/`Never` part of Section 3;
* `quittingRootSequenceTerminalValue_sub_eq_jointSurvivalWeight_mul`, for the
  generic response-difference transport route; and
* `quittingCapNashStackContinueProduct_le_one`, together with the literal
  debt-infimum lower bound, for the squeeze (1.5).

The following steps are new ordinary mathematics and are **not** claimed
checked:

1. packaging a supplied convergent sequence, its supplied mark, and the exact
   root words as a `QuittingMinimumLawCausalSuffixAtom`;
2. the endpoint-law specialization and new public wrapper which expose the
   exact chronology alongside `FinFourThreeRoleMinimumTargetRegeneration`;
3. the arbitrary-behavioral response-difference adapter (3.2); and
4. the cyclic seam calculation (4.6)--(4.9).

## Lean-facing boundary

The positive producer should be formalized separately from the unresolved
consumer:

```text
exists_deep_nearMinimum_capNashChronologies_from_supplied_causalRealizers

ConcentratedCollisionThreeRoleEndpointLaw.
  nonempty_sourceFaithful_finFourMinimumTargetRegeneration

FinFourSourceFaithfulMinimumTargetRegeneration

shiftedResponseDifference_capNashPrefix_eq_opponentSurvival_mul
```

The seam lemma is finite and can be packaged once a dependent cycle object
with one fixed observer is supplied.  A theorem which silently identifies
different observers, or which forgets that the resulting switch still has
spectator cap leakage, would overstate the result.

## Review-gate recommendation

Section 1 together with the corrected endpoint adapter and explicit wrapper
in Section 2 should re-enter the standard independent review gate as a
standalone producer.  It has a complete proof, a small Lean surface, and
removes a currently documented source-reselection loss.  Re-review should
check the explicit collision input, half-law cutoff packaging, exact supplied
mark, and public propositional profile/mark equalities.

Section 3 should be reviewed with that producer.  Its exact transport identity
is useful only if the shifted response plans are explicitly defined to agree
during the prefix; it must not be stated for arbitrary unshifted plans.

Section 4 is also mathematically complete as a supplied-object finite lemma,
but it should be reviewed/exported separately, if at all.  It does not consume
the resulting packet and therefore should not be presented as progress on the
final cap-leakage residual.

Sections 1--3 are now ready for **re-review**, not self-export.  They should
enter `exports/` only after an independent reviewer verifies these repairs.

## Next exact question

Does the Fin4 hard residual force one observer to recur with a
source-coherent response chart before another coordinate can become the
positive recipient, or can a rotating observer word be converted into a
common scalar by a table-level weighted-potential/Farkas argument?  This is
now separate from source re-realization: (5.1) removes that loss.
