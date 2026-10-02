# Audit of the question roadmap and independent routes

Reviewer: `GATE_STRENGTHENER`

## Verdict

The three principal Fin4 questions still describe the current theorem
boundary correctly: uniform tail escape, minimum return, and direct closure of
the hard residual.  The general escape-aware certificate search and the
incentive-gadget route are also genuine independent questions.

The roadmap has four substantive defects.

1. The positive-social-surplus remainder of all-player escape is not stated as
   an open question, although the complementary nonpositive-surplus chamber is
   now closed.
2. No question asks for a reduction from arbitrary finite player sets to a
   bounded cardinality, or for consumption of the exact outsider witnesses in
   a cardinal-minimal counterexample.  Canonical passive padding does not give
   such a reduction.
3. The minimum-return question names cross-coordinate cap leakage, but it does
   not state the two strongest independently attackable seams: simultaneous
   mass/minimum selection in the Jensen disintegration and response reentry
   across source regeneration.
4. Three existing questions need correction or rescoping.  The face-cycle
   question has no asymptotic index despite asking for a limit.  The Simon
   question accepts a certificate which has no conjecture-facing consequence
   without the missing production-necessity theorem and may be inconsistent
   on positive-cost self-loops.  The inert-machine search overstates its scope:
   it is a specialization of one strict normalized chamber, not a proved
   normal form for every possible Fin4 counterexample.

The recommended change is to add four focused questions, rewrite two existing
questions, and subordinate the inert search to the general search.  No current
main Fin4 capstone should be removed.

## Existing questions

### Positive-minimum face-cycle alignment: retain only after a mathematical rewrite

The intended route is independent and potentially valuable, but the present
statement is not well posed.  It starts with one finite family and later asks
that

\[
 \frac{K}{\rho_i}
 \left(\varepsilon+\frac{K\delta}{\rho}\right)\longrightarrow0.
\]

There is no index along which this expression can converge.  The question
must instead quantify over a sequence of finite phase families, with

\[
 K_n,\quad \varepsilon_n,\quad \delta_n,\quad
 \rho_{i,n}>0,\quad \rho_n=\min_i\rho_{i,n},
\]

and require

\[
 \frac{K_n}{\rho_{i,n}}
 \left(\varepsilon_n+\frac{K_n\delta_n}{\rho_n}\right)
 \longrightarrow0
\]

for every player appearing in the compiled cycle.  Every root, tail,
omitted-player gap, atom, phase order, and closing seam must come from the same
indexed actual family.

The question should also expose the strongest finite subproblem as an
acceptable route: a terminal strict-toggle class reaches a pair; at an actual
induced persistent-base Nash point for that pair, prove the missing-face
sign-and-mass inequality needed by pair-base softening, or derive a terminal
consumer.  Mere background sign cancellation is known to be insufficient.

The two corrupted control characters in the displayed error and atom symbols
must be replaced by ordinary `\varepsilon` and `\rho`.

**Disposition:** rewrite; do not archive.

### Rigid Fin4 inert-machine search: retain as a specialization

The certificate contract is sound in principle.  Local inert feasibility is
correctly separated from the global all-behavior gap, and the mandatory
regressions exclude the usual finite-horizon and stationary false positives.

The final scope sentence is too strong.  The checked roadmap does not prove
that every counterexample must reach the strict normalized inert chamber.
There remain the uniform-escape branch and terminal exits of the renewable
minimum-return descent.  Replace the assertion that every counterexample must
survive as this machine by:

> This is the exact-search specialization of the strict normalized inert
> chamber.  Eliminating the chamber closes that named branch; certifying one
> positive-gap instance refutes the conjecture.

The file should be listed beneath both the strict-inert mathematical question
and the general escape-aware search, rather than as a peer search programme.

**Disposition:** keep, rescope, and consolidate its roadmap placement.

### Escape-aware exact Fin4 search: retain

This is the correct general certification question.  Its soundness direction
is the important one: every actual behavioral profile maps into the finite
feasible set, and the finite objective is at most actual exploitability.
Therefore a positive lower certificate for the finite infimum is a genuine
lower bound for all behavioral profiles.

The question already distinguishes semidecision of positive gaps from a
decision procedure: failure to find a certificate proves nothing.  It also
requires an executable extraction before failed lower certificates can be
called a positive theorem.  No consolidation should weaken those clauses.

The inert-machine file should be linked here only as a restricted search
domain.  It is not a replacement for this general question.

**Disposition:** keep as the top-level negative/certification route.

### Simon Lyapunov certificate: replace the present task

The current requested object is not by itself conjecture-facing.  A strict
Lyapunov inequality on one production graph yields a terminal gap only after
the separate production-necessity theorem has been proved.  The present text
asks for the certificate first and says only later that necessity is needed
"to obtain a counterexample".  That conflicts with the directory's progress
criterion.

There is also a literal consistency problem.  If \((x,x)\) is an edge and
\(c(x,x)>0\), then

\[
 V(x)\le V(x)-c_0c(x,x)
\]

is impossible.  Either the production cost must satisfy
\(c(x,x)=0\) on every self-loop, or the inequality must be imposed only on
positive-motion edges with a separately stated convention for zero-motion
edges.

The replacement question should ask for one of the following complete
outputs.

1. A concrete rational table outside the stationary and immediate-punishment
   branches, a precisely defined full production correspondence and cost,
   an exact Lyapunov certificate on every positive-motion edge, **and** a
   proof that absence of arbitrary long production orbits implies a positive
   exploitability gap against every behavioral profile.
2. A proof that the production-necessity implication fails on an actual game
   satisfying the proposed hypotheses.
3. A theorem excluding such Lyapunov certificates on a class proved to
   contain every candidate left by the production classification.

A local certificate without the necessity theorem should be recorded as a
conditional algebraic result, not as an answer to the question.

The corrupted `\varepsilon` characters must also be repaired.

**Disposition:** replace; if the complete production correspondence and cost
cannot be stated now, remove the file from `questions/` until they can.

### Incentive gadget: retain with an explicit accuracy quantifier

This is a genuine independent negative route.  Its target should say exactly:

\[
 \exists\alpha>0\ \exists\varepsilon_0>0\ \forall\sigma,
 \quad
 \max_i d_i(\sigma)\le\varepsilon_0
 \Longrightarrow
 a(\sigma)\ge\alpha,
 \ b(\sigma)\ge\alpha,
 \ \ell(\sigma)<2\alpha.
\]

Here \(a,b,\ell\) must be defined as an exhaustive disjoint partition of the
first terminal outcome, including simultaneous coalitions involving
calibrators and Never.  The conclusion contradicts
\(\ell^2\ge4ab\), so every profile has exploitability greater than
\(\varepsilon_0\).

The present phrase "every sufficiently accurate" should be replaced by this
quantifier.  The table must control all behavioral deviations, not only the
four designated clocks.  The existing architecture exclusions remain useful
boundary conditions but are not premises which a construction may assume.

**Disposition:** keep with the quantified rewrite.

## Missing question 1: consume strict positive-social-surplus escape

Suggested filename:
`POSITIVE_SOCIAL_SURPLUS_ESCAPE_CONSUMER.md`.

### Mathematical data

Let \(I\) be finite, let own singleton rewards be nonnegative, and let
\(z=(u,b)\) minimize total terminal-semantic debt.  Let actual profiles
\(\sigma_n\) realize \(z\), let their marginal compactified stopping laws
converge to the actual product profile \(\bar\sigma\), and let their terminal
laws converge to \(m^*\).  If \(m\) is the terminal law of
\(\bar\sigma\), put

\[
 e(S)=m^*(S)-m(S),\qquad R(S)=\sum_i r_i(S),
\]

and assume the escape is genuinely nonattaining:

\[
 \delta=D(\bar\sigma)-D(z)>0.
\]

The supplied exact account is

\[
 e(S)\ge0,
 \qquad
 \sum_Se(S)R(S)
 =\delta+\sum_i\bigl(b_i-B_i(\bar\sigma)\bigr)>0.
\]

### Question

Use the same realizing sequence and escaped law to prove one of:

1. an actual profile with debt below \(D(z)\);
2. terminal approximate Nash profiles with one limiting payoff, or a uniform
   equilibrium payoff;
3. a source-matched positive admissible return or a renewable finite-rank
   transition; or
4. an explicit finite reward table with a certified positive exploitability
   gap against every behavioral profile which realizes this strict escaped
   social-surplus configuration.

The already settled case \(R(S)\le0\) for all nonempty \(S\) is not part of
the question.  An escaped positive-surplus coalition, without an executable
consumer, is not an answer.  Terminal-law escape may not be identified with
current root absorption.

### Reason for addition

This is the exact remainder after the social-surplus attainment theorem.  The
current hard-residual question mentions an all-player atom route but does not
state this signed residual or its sharp debt-jump identity.

## Missing question 2: bound or consume cardinal-minimal counterexamples

Suggested filename:
`CARDINAL_MINIMAL_OUTSIDER_CONSUMER.md`.

### Mathematical data

Let \(r\) be a cardinal-minimal finite quitting game with a terminal
exploitability gap \(\gamma>0\).  For every nonempty proper block
\(B\subset I\), every \(0<\varepsilon<\gamma\), and every terminal
\(\varepsilon\)-Nash profile of the induced game on \(I\setminus B\), form
the ambient quiet lift by making all members of \(B\) play Never.  The
supplied operational conclusion is that some \(d\in B\) and some finite
deterministic quitting date \(t\) give \(d\) an ambient gain at least
\(\gamma\).  For singleton \(B=\{d\}\), the witness is necessarily that same
player.

Canonical passive padding is also supplied as an exact quantitative
retraction for padded tables.  It does not reduce an arbitrary larger table.

### Question

Use the compatible family of proper-block outsider witnesses to prove one of:

1. every cardinal-minimal counterexample has at most four players;
2. more generally, a fixed finite cardinal bound together with closing base
   cases;
3. a constructive reduction of every larger game to finitely many strictly
   smaller games such that uniform equilibria of the children compile to one
   for the parent and a positive parent gap is inherited by a child; or
4. an explicit cardinal-minimal reward table with a certified positive gap
   against every behavioral profile.

The deleted block, player, finite time, survivor payoff, and lifted profile
must be coordinated across the construction.  Upward passive padding, one
block witness, or a static solo/join pressure inequality is not a cardinal
reduction.

### Reason for addition

No existing question addresses the step from Fin4 to arbitrary finite player
sets.  The padding theorem settles only the canonical padded subclass, while
the exact outsider theorem supplies the strongest known data for a genuine
cardinality induction.

## Missing question 3: Jensen selection with cross-coordinate cap control

Suggested filename:
`FIN4_JENSEN_CLOCK_SELECTION_AND_CAP_LEAKAGE.md`.

### Mathematical data

Let actual four-player profiles \(\sigma_n\) approach a positive global
minimum \(D_*\), and let one owner's stopping law carry a fixed positive
singleton terminal mass.  Disintegrate that stopping law into deterministic
finite deadlines and Never while keeping all opponents and the literal outer
source fixed.  Write \(P_{n,t}\) for the deterministic-clock completions and
let the Jensen loss be the difference between the stopping-law average of
their total debts and \(D(\sigma_n)\).

### Question

Prove an exhaustive source-attached alternative.

1. Select deterministic completions which simultaneously retain a fixed
   singleton stage-mass floor, converge to the global minimum fibre, and
   retain the paid endpoint data needed by the minimum-return consumer; or
2. localize nonvanishing Jensen cap curvature on mass-carrying completions and
   convert it into a source-matched response square, positive admissible
   return, or renewable minimum-source transition.

In either arm control the sum of the other three players' unrestricted cap
increments.  Controlling only the owner or one responding outsider does not
place the response endpoints on the minimum fibre.  If a response can preempt
the marked singleton date, its response endpoint needs a new mass argument;
mass of the unresponded completion is not enough.

An exact negative answer may construct a positive-gap table realizing the
complete source data while defeating both arms.  A fixed positive mixing
weight which retains mass but leaves order-one endpoint regret, or a
vanishing weight which loses the mass floor, is not an answer.

### Reason for addition

This is the sharpest local form of the cap-leakage obstruction in the
concentrated-singleton and minimum-return routes.  Those capstones name the
obstruction but do not state the simultaneous selection problem which can be
attacked independently.

## Missing question 4: reenter responses across source regeneration

Suggested filename:
`FIN4_RESPONSE_REENTRY_ACROSS_REGENERATION.md`.

### Mathematical data

Let an actual outgoing minimum-return endpoint reconstruct the next complete
positive-minimum source.  Retain the outgoing profiles, incoming realizing
profiles, their literal prefixes and marked dates, one fixed observer, and
two complete pure-time responses, including Never.  Response values transport
exactly through a common prefix over one fixed suffix, but the regenerated
source may use a newly selected suffix chronology.

### Question

Construct, on one common subsequence, an actual bridge from each outgoing
endpoint to the next incoming source which yields one of:

1. one response simultaneously asymptotically optimal on both sides and
   literally installed at the successor;
2. a source-matched positive first-disagreement edge or response square whose
   payoff charge survives the bridge;
3. an escaping pure-time packet with the same response labels, atom, and a
   terminal/chronological consumer; or
4. a renewable finite-rank transition or a uniform-equilibrium payoff.

The bridge may use the at most four whole-strategy player hybrids between two
profiles, but it must preserve the relevant clock shift, continuation, marked
source data, and response labels.  Equality of semantic pairs or complete
terminal laws does not manufacture this edit chronology.  Transport through
a new prefix over one unchanged suffix does not prove reentry into a newly
selected suffix.

### Reason for addition

This is the exact seam shared by the response-chord, paid-row reentry, and
regenerated-source routes.  It is not the same as the Jensen selection
problem: Jensen chooses a useful deterministic component, whereas reentry
must carry a response across the next source reconstruction.

## Consolidated roadmap

The human-readable index should have the following structure.

### Main four-player route

- uniform escape;
- minimum return;
- direct hard-residual closure.

Under minimum return, list the existing two-tier, paid/reset, paired-unique-cap,
and support-exit questions, followed by the two new focused seams:

- Jensen clock selection with cross-coordinate cap control;
- response reentry across regeneration.

### Other positive routes

- corrected positive-minimum face-cycle alignment;
- strict positive-social-surplus escape;
- cardinal-minimal outsider consumption/cardinality reduction.

### Refutation and certification routes

- general escape-aware exact Fin4 search;
  - rigid inert-machine search as its strict-inert specialization;
- quantified incompatible-clock incentive gadget;
- corrected Simon certificate **together with** production necessity.

The strict progress criterion in `questions/README.md` should remain
unchanged.  In particular, none of the four new files should accept a local
selection lemma, static screen, conditional certificate, or newly named
residual without its displayed source adapter and consumer.

## Effect of the two new complete results

The social-surplus theorem removes the entire chamber

\[
 r_i(\{i\})\ge0,
 \qquad
 \sum_i r_i(S)\le0\quad(S\ne\varnothing)
\]

from the nonattainment problem.  The corresponding question must therefore
start at strict positive escaped social surplus; re-asking for the escape
account or the nonpositive chamber would be stale.

The passive-padding theorem proves exact target-set and exploitability
retraction only for the canonical padded table.  It justifies a cardinality
roadmap and makes upward cardinal induction constructive, but it supplies no
downward reduction for an arbitrary table.  The new cardinal question must
not claim otherwise.

The note-mining reports add no further completed branch.  Their strongest
common message is that the remaining source failures are type conversions:
mass and minimum must be co-realized, responses must reenter the regenerated
source, and deleted-game outsiders must be coordinated across blocks.  The
four proposed questions state precisely those still-missing conversions.
