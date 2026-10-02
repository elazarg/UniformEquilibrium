# A positive response curl splits into optimizer switching or stable regret rise

Identity: `CODEX_CURL_FACE`

Date: 2026-08-31

Status: **ordinary mathematics proved below; not a consumer.**  The reviewed
four-point curl passport does not itself carry a nonzero cap curl.  Along its
one common descendant sequence, its exact positive response curl splits into
either a genuine pure-time optimizer switch or a stable-response regret-rise
arm.  In the switch arm, bounded witness times give an attained finite
response-face separation after one source-preserving compact refinement;
escaping witnesses give a positive-Never/all-player timing bubble, not by
themselves a second divergent quitting clock.  The stable arm is realized by
the existing exact zero-minimum regression and remains the unconsumed branch.

## 1. Question and literal four-profile input

At every finite rank of the response-curl construction, let

\[
 (R_n,Q_n,E_n,S_n)
\]

be the four actual profiles on the same common-prefix descendant sequence.
The mover is \(p\), the observer is \(j\ne p\), and the replacements commute.
Thus there are complete strategies \(a_n,c_n\) of \(j\) such that

\[
 R_n=(a_n,(E_n)_{-j}),\qquad
 Q_n=(a_n,(S_n)_{-j}),
\]

while \(c_n\) is the prescribed \(j\)-strategy in both \(E_n\) and \(S_n\).
The construction gives

\[
 d_j(R_n)\longrightarrow0,
\qquad
 \mathcal C_n\ge \chi>0,
\tag{1.1}
\]

where, in the normalized Fin4 application, one can take

\[
 \chi=\theta D_*>0,
\]

and

\[
 \mathcal C_n=
 [U_j(R_n)-U_j(E_n)]-[U_j(Q_n)-U_j(S_n)].
\tag{1.2}
\]

All subsequences below are refinements of this one common four-profile
sequence.  No corner is compactified independently and no new minimum source
is selected.

## 2. The alternating cap is zero

Changing a player's own complete strategy does not change that player's
unrestricted cap.  Therefore

\[
 B_j(R_n)=B_j(E_n),\qquad B_j(Q_n)=B_j(S_n).
\tag{2.1}
\]

In particular the alternating cap expression is identically zero:

\[
 B_j(R_n)-B_j(E_n)-B_j(Q_n)+B_j(S_n)=0.
\tag{2.2}
\]

The positive passport is consequently not a cap curl.  It is a payoff or
response-regret curl.  Using (2.1), one gets the exact identity

\[
 \boxed{
 \mathcal C_n=
 d_j(E_n)-d_j(R_n)-d_j(S_n)+d_j(Q_n).}
\tag{2.3}
\]

This identity is the correct starting point for any active-face argument.

After one further subsequence, suppose

\[
 d_j(Q_n)\longrightarrow q\ge0.
\tag{2.4}
\]

There are two different mathematical arms.

### Switch arm: \(q>0\)

The common response \(a_n\), which is asymptotically optimal against
\((E_n)_{-j}\), remains uniformly suboptimal against \((S_n)_{-j}\).

### Stable-response arm: \(q=0\)

The same response is asymptotically optimal on both backgrounds, and (2.3)
forces

\[
 \liminf_n[d_j(E_n)-d_j(S_n)]\ge\chi.
\tag{2.5}
\]

Thus a positive response curl need not mean that the cap optimizer changes.
It may mean only that the prescribed strategy \(c_n\) becomes more suboptimal
after the mover replacement while one common response remains optimal on
both sides.

## 3. Pure-time localization in the switch arm

Assume \(q>0\).  Pass to a tail on which

\[
 d_j(Q_n)\ge q/2.
\tag{3.1}
\]

Let \(\mu_n\) be the stopping law of \(a_n\).  For a pure time
\(t\in\mathbb N\cup\{\infty\}\), write

\[
 V^E_n(t)=U_j(E_n[j\leftarrow\operatorname{QuitAt}t]),
\qquad
 V^S_n(t)=U_j(S_n[j\leftarrow\operatorname{QuitAt}t]).
\]

Here \(t=\infty\) is literal Never.  Pure-time extremality and the stopping-law
representation give

\[
 \int [B_j(E_n)-V^E_n(t)]\,d\mu_n(t)=d_j(R_n),
\tag{3.2}
\]

and

\[
 \int V^S_n(t)\,d\mu_n(t)=U_j(Q_n).
\tag{3.3}
\]

Choose a pure time \(b_n\) satisfying

\[
 V^S_n(b_n)\ge B_j(S_n)-\varepsilon_n,
\qquad \varepsilon_n\downarrow0.
\tag{3.4}
\]

Put

\[
 e_n(t)=B_j(E_n)-V^E_n(t)\ge0,
\qquad
 h_n(t)=V^S_n(b_n)-V^S_n(t).
\]

Then

\[
 \int e_n\,d\mu_n=d_j(R_n)\longrightarrow0,
\tag{3.5}
\]

and, for all sufficiently large \(n\),

\[
 \int h_n\,d\mu_n
 \ge d_j(Q_n)-\varepsilon_n
 \ge q/3.
\tag{3.6}
\]

Assume terminal rewards have absolute value at most \(M>0\).  Then
\(|h_n|\le2M\).  Choose any \(\tau_n\downarrow0\) with

\[
 \Pr_{\mu_n}(e_n>\tau_n)\longrightarrow0;
\]

for example, after discarding zero terms, one may use
\(\tau_n=\sqrt{d_j(R_n)}\), with a harmless positive modification at zeros.
Equations (3.5)--(3.6) imply that for all large \(n\), the set

\[
 A_n=
 \{t:e_n(t)\le\tau_n, h_n(t)\ge q/12\}
\tag{3.7}
\]

has a fixed positive stopping-law mass.  A safe explicit bound is

\[
 \mu_n(A_n)\ge \frac{q}{24M}.
\tag{3.8}
\]

Indeed the complement of the \(e_n\)-good set has vanishing mass; on the
good set outside \(A_n\), \(h_n<q/12\), while everywhere \(h_n\le2M\).

Thus the switch is not represented merely by a support atom of arbitrarily
small probability.  A fixed fraction of the actual common response law is:

* asymptotically cap-attaining against \(E_n\); and
* beaten by the pure-time response \(b_n\) against \(S_n\) by at least
  \(q/12\).

Selecting any \(t_n\in A_n\), the checked pure-time first-disagreement
decoder gives the actual edge

\[
 S_n[j\leftarrow\operatorname{QuitAt}t_n]
 \longrightarrow
 S_n[j\leftarrow\operatorname{QuitAt}b_n]
\tag{3.9}
\]

over the literal opponent background \((S_n)_{-j}\), with gain at least
\(q/12\).  Its source endpoint is not generally the prescribed corner
\(S_n\), whose \(j\)-strategy is \(c_n\).  Thus (3.9) preserves the exact
source opponents but not the prescribed source corner.  A generic paid row
is already available at every profile under the terminal gap.  The
additional information here is the adjacent \(E_n\)-active response label
and the positive mass statement (3.8).

## 4. Bounded witnesses and the closed active-response face

First refine diagonally so that, for every finite subset of
\(\mathbb N\cup\{\infty\}\), its \(A_n\)-mass converges.  Suppose some fixed
finite set has uniformly positive limiting mass.  Finite pigeonhole then
gives one fixed \(t\) with positive limiting mass.  Refine the same descendant
subsequence so that the finitely many root coordinates needed to evaluate
`QuitAt t`, and the relevant deleted-player law if Never occurs, converge.

Then (3.7) gives a closed response-face statement:

\[
 V^E(t)=B_j(e),
\tag{4.1}
\]

where \(e\) is the stored semantic limit of \(E_n\).  If \(b_n\) also remains
in a fixed finite set, another refinement freezes it to \(b\) and gives

\[
 V^S(b)=B_j(s),
\qquad
 V^S(b)-V^S(t)\ge q/12.
\tag{4.2}
\]

This is an attained finite active-response-face separation in the enriched
closed descendant carrier whose data explicitly include those finite roots
and deleted-player laws.  The symbol \(V^E(t)\) is not a function of the bare
semantic point \(e\).  This is not yet a rank transition.  The active
face at a later regenerated source may rotate back, and neither inclusion nor
monotonicity of active response sets has been proved.

If one time is fixed while the other escapes, the first-disagreement date is
still bounded.  The output is a finite root endpoint comparison whose
Continue branch contains an escaping continuation response.  Compactness of
ordinary terminal laws alone does not identify that branch; the appropriate
deleted-player or counterfactual law must be retained.  Again this is a
closed face passport, not a renewable rank.

## 5. Escaping times give a Never bubble, not automatically a second clock

On the preceding diagonal refinement, the negation of the bounded-mass
alternative is that the mass in (3.8) escapes every finite set:

\[
 \forall H,\qquad
 \liminf_n\mu_n(A_n\cap\{t>H\})
 \ge \frac{q}{24M}.
\tag{5.1}
\]

Every compact limit of these stopping laws in the one-point compactification
\(\mathbb N\cup\{\infty\}\) then has literal Never mass at
least \(q/(24M)\).  This is a retained positive-Never marginal for the actual
common response \(a_n\), obtained on the same descendant sequence.

For every selected \(t_n\in A_n\), the pure-time gap is at least \(q/12\).
The first-disagreement identity therefore gives

\[
 \Pr((S_n)_{-j}\text{ all survive to the first disagreement})
 \ge \frac{q}{24M}.
\tag{5.2}
\]

If \(b_n\) also escapes to infinity, combine (3.8) and (5.2).  For every
fixed \(H\), a cofinal amount at least

\[
 \left(\frac{q}{24M}\right)^2
\tag{5.3}
\]

of the product stopping law has player \(j\) choose a time after \(H\) and
all three opponents survive through \(H\).  Hence a common compactification
of the four stopping clocks has positive joint Never mass.

Here the multiplication uses the ordinary quitting-game semantics: the four
players' behavioral randomizations are independent, and before absorption
the public history is the single all-Continue word.  No public correlating
device is introduced.

This last conclusion concerns the compactified stopping-clock law.  It is not
a statement about the stored date-forgetting terminal outcome law: absorption
at dates tending to infinity may retain a fixed terminal coalition coordinate
even while the pointwise limiting behavioral profile is all Continue.

This is the familiar all-player timing bubble.  It is not automatically a
second **divergent quitting clock**: positive Never mass corresponds to
finite total hazard, not divergent hazard.  Nor does (5.2) alone force an
opponent to Quit in a late window.  If one witness is Never, a positive gap
can be carried by the singleton-versus-Never payoff even when no opponent
ever Quits.  For two finite witness times, the gap does force opponent
absorption between them, but the finite/Never case must remain separate.

Thus the honest escape alternatives are:

1. a bounded first-disagreement response face;
2. a positive-Never/all-player timing bubble; or
3. in the finite/finite subcase, a late opponent-window clock event.

None of these is presently a terminal consumer solely from the curl passport.

### The common ancestry is not becoming unreachable

This timing bubble is stronger than an arbitrary compactness artifact.  Let
\(\mathcal C_0>0\) be the curl of the fixed finite quartet before common
prefixing, and let \(c_n\) be the joint survival through its common prefix.
Exact prefix scaling gives

\[
 \mathcal C_n=c_n\mathcal C_0.
\]

Since the normalized slice has

\[
 \mathcal C_n\ge\theta D(R_n)\ge\theta D_*,
\]

one has the uniform source-reach floor

\[
 \boxed{c_n\ge\frac{\theta D_*}{\mathcal C_0}>0.}
\tag{5.4}
\]

Thus the bounded or escaping response witnesses remain attached to a
uniformly reached copy of the original finite quartet.  What is missing is
not reach but a consumer for the stable-response or timing-bubble output.

## 6. The stable arm descends to the original finite quartet

Let \((R^0,Q^0,E^0,S^0)\) be the fixed literal quartet before the words
\(W_n\) are prefixed.  The exact arbitrary-root coordinate ledger is

\[
 d_j(x\star z)
 =
 \operatorname{CapDefect}_j(B(z),x)
 +c(x)d_j(z),
\tag{6.1}
\]

where \(c(x)\) is joint all-Continue mass and the cap defect is nonnegative.
Iterating (6.1) through a finite word gives

\[
 d_j(Q_n)\ge c_n d_j(Q^0).
\tag{6.2}
\]

In the stable arm, \(d_j(Q_n)\to0\), while (5.4) gives \(c_n\ge c_*>0\).
Consequently

\[
 \boxed{d_j(Q^0)=0.}
\tag{6.3}
\]

The original response used to construct \(R^0,Q^0\) was a pure-time or Never
exact best response to \(E^0_{-j}\), so \(d_j(R^0)=0\) already.  Equation
(6.3) proves that the same finite-clock response is an exact best response to
\(S^0_{-j}\) as well.  Therefore the stable arm is not produced by loss of
relative timing in the common-prefix limit.  It is already present at the
source-attached finite horizontal quartet.

In fact it fills an executable zero-\(j\)-debt face.  Mix only player \(p\)'s
complete strategy between its \(S^0\)- and \(E^0\)-values, while prescribing
the common response \(a^0_j\).  For every fixed alternative strategy of
player \(j\), its payoff difference from \(a^0_j\) is affine in this
one-player mixture.  The difference is nonnegative at both endpoints because
\(a^0_j\) is optimal at \(Q^0\) and \(R^0\).  It is therefore nonnegative
throughout the chord.  Every literal chord profile has

\[
 d_j=0.
\tag{6.4}
\]

This uses ordinary independent behavioral randomization of \(p\), not a
formal mixture of semantic points.

This is useful provenance, but it is not chronology: \(S^0,E^0,Q^0,R^0\)
remain alternative whole profiles.  Rooting a best-response cycle at their
finite calendar would silently serialize horizontal interventions.

## 7. The switch arm has a sharper base-or-prefix decomposition

Iterating the exact coordinate ledger through \(W_n\) gives nonnegative
cumulative cap-defect accounts \(A^Q_n,A^R_n\) such that

\[
\begin{aligned}
 d_j(Q_n)&=A^Q_n+c_n d_j(Q^0),\\
 d_j(R_n)&=A^R_n+c_n d_j(R^0)=A^R_n.
\end{aligned}
\tag{7.1}
\]

After refining so that \(c_n\to c\ge c_*>0\), the switch-arm limit satisfies

\[
 q=\lim_n A^Q_n+c\,d_j(Q^0),
\qquad
 A^R_n\longrightarrow0.
\tag{7.2}
\]

This gives a source-faithful sub-dichotomy.

1. If \(d_j(Q^0)>0\), the original finite quartet already contains a bounded
   pure-time response switch.  Its common pure-time/Never response is exact
   at \(E^0\) and loses \(d_j(Q^0)\) against \(S^0\); finite-clock extremality
   chooses a competing best pure time from the fixed bounded calendar plus
   Never.
2. If \(d_j(Q^0)=0\), then

   \[
    A^Q_n-A^R_n\longrightarrow q>0.
   \tag{7.3}
   \]

   The switch is created entirely inside the common historical prefixes:
   the same literal roots have vanishing cumulative \(j\)-cap defect on the
   \(R\)-background but fixed cumulative cap defect on the \(Q\)-background.

The second arm is genuine chronological information, but still only at the
cap level.  A cap defect against a continuation envelope is not automatically
a literal prescribed-payoff Bellman gain.  Even if (7.3) localizes at bounded
dates, the existing full-chord theorem applies only after one produces its
pure-time-gap and mixture-scale budgets; localization of cap defect alone is
not that adapter.  If the account diffuses over later dates, one needs the
missing cap-to-literal shadowing or clock alternative.  Root uniqueness at
the final point cannot be applied backward to erase this cumulative account.

## 8. The stable-response arm is a genuine local obstruction

The \(\kappa=1\) regression in
`CODEX_DESCENDANT__ASYMPTOTIC_PROJECTIVE_PASSPORT_AND_ROOT_BARRIER.md`
realizes the stable arm exactly.  For observer \(j=3\), its four pure profiles
satisfy

\[
 d_3(R)=0,\qquad d_3(Q)=0,\qquad d_3(S)=1,\qquad d_3(E)=2,
\]

and hence

\[
 \mathcal C=2-0-1+0=1.
\]

The common response Never is optimal against both endpoint backgrounds.  No
optimizer switch is present.  At the same time all Continue is the unique
exact product root at \(B(R)\), with the exact fixed-cap root-defect barrier.

That table has an all-Never equilibrium and global minimum debt zero.  It is
therefore not a counterexample to a theorem using \(D_*>0\).  It proves the
necessary interface fence:

\[
 \boxed{
 \text{positive response curl + unique all-Continue at the first corner}
 \not\Rightarrow
 \text{best-response switch or persistent clock}.}
\tag{8.1}
\]

Any exclusion of the stable arm must quantitatively use the retained
positive-minimum ancestry, not just the limiting quartet and its root
geometry.

The unique-all-Continue theorem at \(B(r)\) does not remove this arm.  It
classifies a **new** one-stage exact product root placed before the first
limit point \(r\).  The response curl compares complete \(j\)-strategies
against the two different opponent backgrounds \(E_n{}_{-j}\) and
\(S_n{}_{-j}\).  Neither background cap is identified with \(B(r)\), and the
historical common prefixes used to approach \(r\) cannot be read backward as
new exact roots.  Applying root uniqueness to either would silently reverse
the chronology.

### Exact positive-minimum handoff from the stable face

Suppose now that the first stable corner \(R^0\) is itself on the global
minimum fibre.  Since \(d_j(R^0)=0\), choose a pure-time/Never exact best
response \(h_p\) of \(p\) against \((R^0)_{-p}\), and let

\[
 T=R^0[p\leftarrow h_p].
\]

There is an exact exhaustive split.

1. If \(d_p(R^0)=0\), the minimum point \(R^0\) already has both \(p\) and
   \(j\) in its zero-debt set.
2. If \(d_p(R^0)>0\), then \(R^0\to T\) is an actual whole-profile
   best-response edge of gain \(d_p(R^0)\), and \(d_p(T)=0\).
   * If \(D(T)>D_*\), it is a literal off-minimum paid exit.
   * If \(D(T)=D_*\) and \(d_j(T)=0\), the minimum zero set grows.
   * If \(D(T)=D_*\) and \(d_j(T)>0\), the zero moves from \(j\) to \(p\);
     this is the exact same-minimum cap-leakage obstruction.

The stable quartet supplies one additional fact: its displayed source and
target \(p\)-strategies both preserve \(j\)'s zero debt, because
\(d_j(Q^0)=d_j(R^0)=0\).  What it does not say is that either displayed
\(p\)-strategy attains \(B_p(R^0)\).

Accordingly, a sufficient extra datum is the finite-face cap-completeness
condition

\[
 B_p(R^0)=\max\{U_p(Q^0),U_p(R^0)\}.
\tag{8.2}
\]

Under (8.2), an exact \(p\)-best-response target can be chosen from
\(\{Q^0,R^0\}\), so it preserves the old \(j\)-zero.  The output is then
either a minimum point with both displayed zeros or a literal off-minimum
paid edge.  Without (8.2), the sharp residual is an out-of-face \(p\)-best
response whose target lies on the minimum fibre and reactivates \(j\).

This conditional handoff also exposes two data absent from the generic closed
passport.  The literal finite corner \(R^0\) need not itself be the minimum
point \(r\); it may only approach \(r\) after longer common prefixes.
Moreover the paid rectangle mover \(p\) need not be a positive-debt
coordinate of \(r\).  The scalar paid-gain passport does not identify
\(d_p(r)\).

Thus positive-minimum ancestry does not presently exclude the stable arm.
It turns it into a finite source-attached face plus one exact producer
question:

> Along the same descendant sequence, can one select an actual positive-debt
> player at the minimum limit and a cap-attaining response which remains
> inside a source-attached response face on which every previously killed
> observer stays optimal?

This is the zero-preserving response lemma in finite active-face form.  It
requires both debtor/face alignment and literal minimum-source coherence;
neither follows from the four scalar limit coordinates.

## 9. Strongest valid reduction and next question

The reviewed closed curl passport yields the following exhaustive refinement
on its one common descendant sequence:

\[
\boxed{
\begin{array}{l}
\text{a finite source-attached stable common response with a fixed regret rise;}\\
\text{or a positive-mass pure-time optimizer switch, which further gives}\\
\quad\text{a bounded closed response-face separation,}\\
\quad\text{or an escaping positive-Never/timing bubble.}
\end{array}}
\tag{9.1}
\]

There is no justified finite active-face rank yet, and the escape branch does
not automatically supply two divergent quitting clocks.

The next genuinely new question is therefore the stable arm:

> At a positive-minimum source-attached common-prefix descendant, can one
> common response be asymptotically optimal on both backgrounds while the
> prescribed observer regret rises by a fixed fraction of total debt across
> a paid mover edge?  If yes, does the rise give a renewable cross-coordinate
> debt transfer; if no, which positive-minimum inequality rules it out?

A negative answer would leave the switch/escape packet above.  A positive
answer must be treated as a new response-stable chamber rather than renamed
as cap switching.

### Canonical maximum-debt selection does not supply the alignment

At the actual near-minimum approximants \(R_n\), one may certainly choose a
maximum-debt player \(k_n\).  Finite pigeonhole freezes one label \(k\), and

\[
 d_k(R_n)\ge D(R_n)/4\ge D_*/4.
\tag{9.2}
\]

This does not identify \(k\) with the rectangle mover \(p\).  The two labels
come from different operations:

* \(p\) was the mover on the earlier paid edge \(S^0\to E^0\);
* \(k\) is selected only after the \(j\)-response and common-prefix
  minimization.

A common subsequence freezes both labels but cannot prove their equality.
The exact \(\kappa=1\) regression makes the mismatch explicit:

\[
 p=2,\qquad j=3,\qquad d(R)=(1,0,0,0),
\]

so the unique maximum debtor is \(k=0\ne p\), while the common response is
stable and all Continue is the unique cap root at \(R\).  Its global minimum
is zero, so it does not refute a theorem using positive-minimum provenance;
it refutes the proposed **alignment mechanism** from the local passports.
The positive reach floor adds no equality between these finite labels.

Selecting an exact response of \(k\) at each \(R_n\) gives the sharp
same-sequence test:

1. if the response targets remain off minimum by a fixed amount, one has the
   existing off-minimum paid exit;
2. if they return to the minimum and keep \(d_j\to0\), one has the desired
   zero-preserving response;
3. if they return to the minimum and make \(d_j\) positive, one has exact
   debtor rotation.

Case 3 is compatible with every presently stored scalar passport.  Excluding
it requires a new **cap-attaining zero-face incidence** field, not another
choice of maximum-debt subsequence.

## 10. Checked interfaces and boundary

The proof uses the mathematics represented by the checked declarations:

* `sSup_range_quittingTerminalPayoff_update_eq_pureTime` and the stopping-law
  expectation identity in
  `Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
* `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
* `quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul` in
  `Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`;
* the supported pure-time averaging pattern in
  `HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at`; and
* the full-chord survival estimates in
  `StoppingLaw/TerminalSemanticCapSwitchFullChord.lean`.

The sequence-level split, positive-mass localization (3.8), and escape
classification are ordinary mathematics, not claimed as Lean declarations.
The compact active-face statement requires the explicitly mentioned finite
root/deleted-law enrichment; it does not follow from the ordinary terminal
law alone.
