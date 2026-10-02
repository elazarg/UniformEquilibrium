# Review of finite-watchdog and geometric-security no-go results

Reviewer: `CODEX_PASCAL`

Verdict: `ACCEPT AFTER MINOR BUT REQUIRED REPAIRS; KEEP INTERNAL`

I checked all five theorems against the ordinary unrestricted behavioral
stopping-time semantics in
[`../notes/CHATGPT_EXTERNAL__FINITE_WATCHDOG_GEOMETRIC_SECURITY_NO_GO.md`](../notes/CHATGPT_EXTERNAL__FINITE_WATCHDOG_GEOMETRIC_SECURITY_NO_GO.md).
The main mathematical claims are correct.  Theorem 4 needs its toggle
quantifiers and a hidden feasibility step made explicit, and Theorem 5 omits
the proof of its uniform numerical bound.  Neither issue changes the result,
but both should be repaired before the note is cited as reviewed mathematics.

The packet does not answer
[`../questions/INCENTIVE_GADGET.md`](../questions/INCENTIVE_GADGET.md) under
either accepted answer standard.  It excludes several architectures, not all
finite reward gadgets, and therefore does not pass the export gate.

## 1. Finite-watchdog theorem

The reduction is valid even when the finitely many supplied strategies are
themselves randomized behavioral strategies.

For each player, a complete behavioral strategy induces one probability law
on `Nat union {infinity}`.  Mixing finitely many such strategies at the start
produces the convex mixture of those laws.  Define the replacement hazards by

\[
q_t=\Pr(T=t\mid T\ge t)
\]

whenever the denominator is positive, and arbitrarily after a zero-survival
time.  The resulting behavioral stopping rule has exactly the mixed law,
including its atom at Never.  Since the initial finite-game mixing is
independent across players, the joint quit-time law is the product of the
mixed marginals; replacing each marginal by its hazard realization preserves
that entire joint law.  It therefore preserves both the equilibrium payoff
and the payoff from every fixed watchdog deviation against the mixed
opponents.  The finite-game Nash inequalities give exactly the displayed
conclusion.

No Kuhn-equivalence claim beyond this stopping-law calculation is needed.
The theorem concerns immunity to the selected finite family only, and the
note correctly does not promote that restricted equilibrium to a Nash
equilibrium against all behavioral deviations.

## 2. Geometric toggle security

The calculation is correct, including simultaneous quitting.  Conditional on
deterministic opponent clocks with first finite time `tau` and exact first
coalition `C`, the three disjoint events are

\[
G_\theta<\tau,\qquad G_\theta=\tau,\qquad G_\theta>\tau.
\]

Their probabilities give the stated bracket

\[
(1-\theta)^\tau
\bigl[\theta r_i(C\cup\{i\})+(1-\theta)r_i(C)\bigr].
\]

The tie event is the first term inside that bracket, so it has not been
dropped.  When all opponents Never, the geometric clock is finite almost
surely and yields the nonnegative solo payoff.  Averaging over the independent
opponent stopping-time laws proves the unrestricted-opponent statement.

For precision, the assumption should say explicitly

\[
\varnothing\ne C\subseteq I\setminus\{i\}.
\]

## 3. Never-mass splice

Theorem 3 is correct, but the limit should be written as an explicit event
decomposition rather than the current phrase "converges from below."

Couple the original and spliced strategies so that they agree before `N`.
Let `T_{-i}` be the opponents' first quit time.  The two induced outcomes can
differ only on

\[
\{N\le T_{-i}<\infty\}
\quad\text{or}\quad
\{T_{-i}=\infty\}.
\]

The first event has probability tending to zero after intersecting with
survival to `N`, and the payoff discrepancy there is uniformly bounded.  On
`T_{-i}=infinity`, both strategies give `s_i` whenever the original player
eventually quits, whereas the splice gains exactly `s_i` when the original
player also Never quits.  Conditional on survival to `N`, the opponents'
residual clocks remain independent, so Theorem 2 applies to the new tail.
Consequently

\[
\liminf_N
\bigl(U_i(\sigma_i^{(N)},\sigma_{-i})-U_i(\sigma)\bigr)
\ge s_i\Pr_\sigma(T_j=\infty\ \forall j).
\]

Taking the best-response supremum gives (2).  This argument uses bounded
terminal rewards and the convention that Never has payoff zero, both of which
are the project semantics.

This result is related to the late-solo refusal account in Proposition 39 of
[`../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`](../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md),
but it is not a duplicate.  That proposition prices opponent-Never mass
against the prescribed-over-Never premium.  Here the geometric security
condition controls all finite residual opponent configurations and isolates
the smaller joint-Never event directly.

## 4. Antisymmetric LP bound

The dual signs are correct.  The relevant primal program is

\[
\min p(A)
\quad\text{subject to}\quad
p\ge0,\quad \sum_Sp(S)=1,\quad
\sum_Sp(S)r_i(S)\ge0\ (i\in I).
\]

Its dual has variables `lambda_i >= 0` and a free scalar `y`, with

\[
\sum_i\lambda_i r_i(S)+y\le\mathbf 1_{\{S=A\}},
\]

and objective `max y`.  Thus an implication `p(A)>=alpha` yields such a
certificate with `y>=alpha` by finite-dimensional strong duality.

Two details must be added to the note:

1. The toggle assumption must be quantified as

   \[
   r_i(C\cup\{i\})=-r_i(C)
   \quad
   (\varnothing\ne C\subseteq I\setminus\{i\}).
   \]

   The empty coalition is not a terminal payoff row.  After pairing all
   nonempty `C` with `C union {i}`, the only unpaired nonempty coalition is
   `{i}`, which proves the displayed sum identity.

2. Duality is not being applied to an infeasible system.  The uniform law on
   all `2^n-1` nonempty coalitions is feasible because its expected payoff for
   player `i` is

   \[
   \frac{r_i(\{i\})}{2^n-1}\ge0.
   \]

   This also makes the obstruction transparent without relying solely on the
   dual formulation.

The word "sharp" should be removed unless an example attaining the bound is
added.  The note proves the upper bound, not sharpness.  Its present statement
also concerns absorbed probability laws on nonempty coalitions; it should not
silently be read as a statement about subprobability laws with positive Never
mass.

The uniform-coalition feasibility observation overlaps Proposition 6 of
[`../notes/CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md`](../notes/CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md).
The LP bound for general antisymmetric secured-payoff rows appears to be a new
strengthening rather than a duplicate.

## 5. Pair-local stationary escape

The exact-equilibrium calculation is correct.  Against the stationary
opponents, forced Quit gives

\[
(1-h)E+hT=0,
\]

because only the partner's current action affects the player's reward.
Forced Continue gives zero: any opponent absorption omits the player, and
unanimous continuation returns to the zero-valued live state.  Since both
endpoints are zero at every live history, every unrestricted behavioral
stopping rule has payoff zero.  This verifies terminal Nash equilibrium, not
merely one-step stationarity.

The strict-first mass formula is also correct.  Writing `x=1-h`,

\[
a=\frac{h^2(1-h)^2}{1-(1-h)^4}
 =\frac{x^2(1-x)}{1+x+x^2+x^3}.
\]

However, the note gives no proof of `a<1/12`.  It should add one.  For example,
the inequality is equivalent to

\[
13x^3-11x^2+x+1>0\qquad(0<x<1).
\]

This follows by elementary one-variable calculus (the only interior local
minimum is at `x=(11+sqrt(82))/39`, where the polynomial is positive), or a
short exact polynomial decomposition.  Until that line is supplied, (11) is
a true but unproved assertion in the note.

## Source and export assessment

A narrow phrase search found no existing Lean declaration or conference note
stating Theorems 1, 2, 4, or 5 in this form.  Theorem 3 has the related but
distinct late-solo result noted above.  Existing checked pure-time extremality
supports the ambient best-response semantics but does not prove these
architectural no-go statements.

After the two repairs, the note is worth retaining as internal research: it
cleanly explains why a profitable witness must come from an unbounded,
profile-dependent family and closes several tempting finite or stationary
designs.  It is not export-quality under `exports/README.md`, because no
theorem here gives a positive incentive gadget, excludes every finite gadget,
or otherwise matches an accepted answer in the parent question.  Splitting
out an individual lemma would not fix that missing conjecture-facing
consumer.
