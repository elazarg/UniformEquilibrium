# Persistent-core response faces and the exact handoff boundary

Identity: SOCIAL_WEIGHT_REVIEW  
Date: 2026-08-31  
Status: **ordinary mathematics proved below; not Lean-checked.**  This note
strengthens the closed-law product-base result and records the exact boundary
of its conjecture-facing handoff.  It does not prove Fin4 UE.

## 1. Setup

Let `I` be finite.  Suppose behavioral profiles `sigma_n` have selected dates
`t_n` and roots `q^n` such that the probability `E_n` of absorption before
`t_n` tends to zero.  Assume a fixed pair `P={p_0,p_1}` satisfies

\[
 q^n_{p_0}q^n_{p_1}\longrightarrow1.
\tag{1.1}
\]

Let `R_n` be the long-calendar reference profile: all players Continue before
`t_n`, use `q^n` at `t_n`, and Never thereafter.  Let `Rhat_n` be its compressed
version: one all-Continue padding row, then `q^n`, then Never.

The closed-law theorem proves that the source laws approach the laws of these
references.  Its cap proof is uniform over one player's complete behavioral
replacement.

## 2. The calendar distinction

Fix a player `i`.  Under the same arbitrary replacement of `i`, the source
profile and the **long-calendar** reference have terminal laws at total
variation distance at most

\[
 E_n+prod_{j\ne i}(1-q^n_j).
\tag{2.1}
\]

Indeed, until some source opponent stops early the public histories agree.
If no opponent stops early and a nonempty opponent coalition stops at the
selected root, the terminal outcomes agree exactly.  The only remaining bad
event is opponent all-Continue at that root.  Even when `i` is one member of
`P`, the other member remains among its opponents, so the second term tends to
zero.

The same labeled replacement need not have a nearby law against `Rhat_n`.
For example, a replacement which Quits exactly at calendar date `t_n` can
join the sure pair in `R_n` but miss a root moved to date one in `Rhat_n`.
The resulting terminal laws may have total variation one.  Thus calendar
compression preserves cap suprema, not pointwise labeled intervention laws.

### Proposition 2.1 (one-player response-law-set compression)

For `t_n>0`, the *set* of terminal laws attainable by arbitrary replacements
of one player `i` against `R_n,-i` is exactly the set attainable against
`Rhat_n,-i`.

### Proof

Against either reference, a strategy of `i` matters only through three
numbers:

\[
 \alpha=\Pr(i\text{ Quits before the product root}),
\]

\[
 \beta=\Pr(i\text{ Quits at the product root}\mid\text{survival}),
\]

and

\[
 \gamma=\Pr(i\text{ eventually Quits after product-root all-Continue}
             \mid\text{survival}).
\]

The terminal law is

\[
 \begin{aligned}
 &\alpha\,\delta_{\{i\}}\\
 &+(1-\alpha)\sum_{A\subseteq I\setminus\{i\}}p_{q^n_{-i}}(A)
 \bigl[
   \beta\,\delta_{A\cup\{i\}}
   +(1-\beta){\bf1}_{A\ne\varnothing}\delta_A
 \bigr]\\
 &+(1-\alpha)(1-\beta)p_{q^n_{-i}}(\varnothing)
   \bigl[\gamma\delta_{\{i\}}+(1-\gamma)\delta_\infty\bigr].
 \end{aligned}
\tag{2.2}
\]

Every triple in `[0,1]^3` is realizable in either calendar: aggregate all
pre-root stopping into the padding action, retain the conditional root
action, and aggregate the post-root stopping law into one eventual-stopping
probability.  Formula (2.2) proves equality of the attainable-law sets.

Consequently (2.1), Proposition 2.1, and the finite outcome simplex give
Hausdorff convergence of the source's one-player counterfactual-law sets to
the padded-root counterfactual-law sets.  This strengthens scalar cap
convergence without making the false pointwise calendar claim.

For the replacement Never, no rebasing is even needed.  Hence every
player-deleted source law converges in total variation to the corresponding
player-deleted padded-root law.

## 3. The finite response face at a positive minimum

Now let the limiting padded root be `q`, let

\[
 K=\{i:q_i=1\},\qquad |K|\ge2,
\]

and suppose its semantic pair `(U,B)` is a positive global minimum with debt
`D_*>0`.  Put `s_i=r_i({i})`.  The checked singleton margin gives

\[
 B_i-s_i\ge D_*>0.
\tag{3.1}
\]

Every player has a sure quitter among its opponents.  Thus opponent
all-Continue has probability zero and every response law is a convex
combination of only three finite laws:

1. Quit in the padding row, producing the singleton `{i}`;
2. Quit at the product root;
3. Continue at the product root.

The first law is strictly suboptimal by (3.1).  Therefore the optimal
response-law face is the convex hull of the cap-attaining members of the last
two laws.  In particular, no late pure-time or Never response is a hidden cap
maximizer in this chamber.

Write their expected payoffs as `Q_i(q_-i)` and `C_i(q_-i)`.  Then

\[
 U_i=q_iQ_i+(1-q_i)C_i,
 \qquad B_i=\max\{Q_i,C_i\}.
\tag{3.2}
\]

If every debt is positive, then `Q_i\ne C_i` for every player.  More
quantitatively,

\[
 |Q_i-C_i|\ge d_i>0,
\tag{3.3}
\]

because `d_i` is either `(1-q_i)(Q_i-C_i)` or
`q_i(C_i-Q_i)`.  The active cap endpoint is therefore locally constant as a
choice of branch.

### Proposition 3.1 (no first-order remote cap curvature)

In a neighborhood of a full-debt padded persistent-core root, each cap
coordinate is one fixed product-root endpoint polynomial.  For two
root-coordinate perturbations of sizes `O(lambda)` in distinct players `p`
and `q`, every cap coordinate has mixed finite difference `O(lambda^2)`:

\[
 B_i(q^{p,q}_\lambda)-B_i(q^p_\lambda)
 -B_i(q^q_\lambda)+B_i(q)=O(\lambda^2).
\tag{3.4}
\]

If one perturbed coordinate is `i`, its cap is independent of that coordinate
and the mixed difference is zero.

### Proof

Continuity and the strict gaps (3.1), (3.3) keep the same one of `Q_i,C_i`
strictly active in a small root neighborhood.  Each endpoint is a multilinear
product expectation in the opponents' probabilities.  Its mixed difference
in two coordinates is its bounded two-coordinate coefficient times the
product of the two increments.  This proves (3.4).

Thus a first-order cap-switching kink in this source-law arm cannot come from
an escaping stopping time.  It must either be a finite current-root endpoint
switch after leaving the full-debt neighborhood, or arise from a seam that
does not stay in the attained product-root realization.

## 4. Renewable sure-core softening

Assume full positive debt and choose `p in K`.  Since `q_p=1`, equations
(3.2)--(3.3) give

\[
 U_p=Q_p,\qquad B_p=C_p,\qquad C_p-Q_p=d_p>0.
\tag{4.1}
\]

For `0<theta<1`, replace `q_p=1` by `q_p=1-theta`, changing no
other coordinate.  The literal padded product target gains

\[
 U_p(\theta)-U_p(0)=\theta d_p(0)>0.
\tag{4.2}
\]

Player `p`'s opponents are unchanged, so its unrestricted cap is unchanged
and

\[
 d_p(\theta)=(1-\theta)d_p(0)>0.
\tag{4.3}
\]

Every other debt is continuous.  Hence there is a small positive interval on
which the target remains full debt.

Along the whole segment, every prescribed payoff and every root endpoint is
affine in `theta`, while each cap is the maximum of those affine endpoints
and the constant singleton option.  Therefore

\[
 f(\theta):=D(q^{p,\theta})
\tag{4.4}
\]

is convex.  Global minimality gives `f(theta)>=f(0)=D_*`.  A convex function
whose minimum is attained at the left endpoint is nondecreasing.

Fix a sufficiently small positive `theta` for which all debts remain
positive.  If `f(theta)>D_*`, then monotonicity gives `f(1)>D_*`: the pure
member-leaving endpoint is off minimum and carries the full gain `d_p(0)`.
If `f(theta)=D_*`, the softened profile is another attained **full-debt**
minimum.  Its maximal sure core is exactly

\[
 K\setminus\{p\}.
\tag{4.5}
\]

This equality child has literal one-step provenance and the paid gain
`theta*d_p(0)`.  If its core still has cardinality at least two, the same
argument applies again.  At core cardinality two, say `K={p,k}`, the softened
profile has positive singleton mass

\[
 \Pr(Q=\{k\})=
 \theta\prod_{j\notin K}(1-q_j)>0,
\tag{4.6}
\]

because maximality of `K` gives `q_j<1` outside `K`.

Thus in Fin4 the equality lane has at most three steps before reaching an
attained positive-singleton minimum.  The zero-Never/zero-singleton full-debt
product arm has the genuine finite-rank transition

\[
 \boxed{\text{off-minimum pure paid endpoint}
 \quad\lor\quad
 \text{source-attached positive-singleton minimum}.}
\tag{4.7}
\]

## 5. Why pure deletion alone was insufficient

After an equality handoff, full debt has been lost.  The remaining sure core
can contain no positive debtor at all, while an outsider carries all debt.
The following exact local table demonstrates the issue.

Take four players and set all singleton rewards to `-2`.  At coalition
`C={0,1,2}`, set all four rewards to zero and set

\[
 r_0(\{1,2\})=r_1(\{0,2\})=r_2(\{0,1\})=\frac14,
 \qquad r_3(\{0,1,2,3\})=\frac14.
\]

The pure triple profile has debt `(1/4,1/4,1/4,1/4)`.  Now additionally set

\[
 r_1(\{1,2\})=r_1(\{2\})=0,
 \qquad r_2(\{1,2\})=r_2(\{1\})=0,
\]

\[
 r_3(\{1,2\})=0,
 \qquad r_3(\{1,2,3\})=1,
\]

with unspecified rewards zero.  Player 0's move from the triple to the pair
`{1,2}` gains `1/4` and kills its debt.  The target pair has debt

\[
 (0,0,0,1).
\]

Both displayed total debts equal one, but neither remaining core member is a
paid leaver.  The table has easy zero-debt behavior elsewhere and is not a
counterexample; it is an exact regression against iterating (4.2) using only
its local fields.

This regression does **not** refute the softening construction.  Along its
softened player-0 segment, the debts are

\[
 \left(\frac{1-\theta}{4},
       \frac{1-\theta}{4},
       \frac{1-\theta}{4},
       \frac14+\frac{3\theta}{4}\right),
\]

so total debt is constantly one and every coordinate remains positive for
`theta<1`.  The softened equality child therefore legitimately lowers the
sure-core rank from three to two, after which the next softening creates a
positive singleton law.

The remaining consumers are downstream: an off-minimum pure paid endpoint
still needs a charged return or regenerated descent, and the positive-
singleton minimum re-enters the existing singleton/collision chain.  The
product-law closure and softening rank remove recurrence of this particular
full-debt arm; they do not alone prove UE.

## 6. Exact local form of the off-minimum branch

The strict branch in (4.7) is sharper than generic cap switching.  By (3.3),
at the full-debt parent every cap coordinate has one unique active root
endpoint.  Hence there is `epsilon>0` such that on
`0<=theta<=epsilon` no cap branch changes.  Every debt is affine there, so

\[
 D(q^{p,\theta})=D_*+\tau_p\theta
 \qquad(0\le\theta\le\varepsilon)
\tag{6.1}
\]

for one exact coefficient `tau_p>=0`.

If `tau_p=0`, every small target is a full-debt minimum child and the core
rank decreases.  If `tau_p>0`, every positive softening is immediately
off-minimum, with the scale-exact account

\[
 \frac{D(q^{p,\theta})-D_*}
      {U_p(q^{p,\theta})-U_p(q)}
 =\frac{\tau_p}{d_p(q)}.
\tag{6.2}
\]

Thus the terminal residual is a **positive linear leakage toll**, not a
first-order remote stopping-time switch.  Deleted-law convergence and the
local polynomial cap description do not make this ratio vanish.

## 7. Exact regression for the positive linear toll

The following table shows that the cap polynomial, unique all-Continue root,
punishment normality, fixed-law minimality, and a strict affine toll can all
coexist.  It deliberately has global minimum zero, so it isolates the need
for the positive global-minimum comparison rather than refuting Fin4 UE.

Let `A={0,1}` and set every own singleton reward to `-3`.  For player 0,
for every nonempty `T subset {1,2,3}`, set

\[
 r_0(T)=1,\qquad r_0(T\cup\{0\})=0,
\]

except

\[
 r_0(\{2\})=-3,\qquad r_0(\{0,2\})=-4.
\]

For player 1 use the symmetric strict-Continue rule on subsets of
`{0,2,3}`, except

\[
 r_1(\{3\})=-3,\qquad r_1(\{1,3\})=-4.
\]

For player 2 set

\[
 r_2(A)=r_2(\{0\})=r_2(\{1\})=0,
\]

\[
 r_2(A\cup\{2\})=r_2(\{0,2\})=r_2(\{1,2\})=1,
\]

and

\[
 r_2(\{3\})=-3,qquad r_2(\{2,3\})=-4.
\]

Define player 3 symmetrically, with

\[
 r_3(A)=r_3(\{0\})=r_3(\{1\})=0,
\]

\[
 r_3(A\cup\{3\})=r_3(\{0,3\})=r_3(\{1,3\})=1,
\]

and punishment cells

\[
 r_3(\{2\})=-3,qquad r_3(\{2,3\})=-4.
\]

Set unspecified rewards to zero, subject to the displayed player-0 and
player-1 rules.

At the padded pure-pair root `A`,

\[
 U=(0,0,0,0),\qquad B=(1,1,1,1),
\qquad d=(1,1,1,1),\qquad D=4.
\tag{7.1}
\]

The singleton moat is exact: `B_i-s_i=4` and `U_i-s_i=3=D-d_i`.
The displayed exceptional cells make every player punishment normal.

Soften player 0 by putting `q_0=1-theta` and retain `q_1=1`,
`q_2=q_3=0`.  Direct endpoint evaluation gives

\[
 d(\theta)=(1-\theta,\ 1+2\theta,\ 1,\ 1),
\]

and therefore

\[
 D(\theta)=4+\theta.
\tag{7.2}
\]

Thus `tau_0=1` and the paid gain is `theta`; the leakage ratio (6.2) is
exactly one.

Against the cap

\[
 B(\theta)=(1,1-\theta,1,1),
\]

all Continue is the unique exact product root.  Players 0 and 1 strictly
prefer Continue against every opponents' root by construction.  Once they
Continue, player 2 strictly prefers Continue whether player 3 Quits or
Continues, using `-3>-4` and `1>-3`; player 3 is symmetric.

The pure-pair law also forces the displayed semantic pair, so this is a
fixed-law minimum.  Nevertheless all Never has zero debt because every own
singleton reward is negative.  The example proves that convex softening,
finite response faces, deleted-law control, unique all-Continue cap geometry,
punishment normality, and the exact singleton moat do not consume a positive
linear toll without the source's **global** positive-minimum provenance.

The remaining question is correspondingly precise: use global
cross-law minimality and source provenance to turn a positive `tau_p` into a
charged return or a renewable off-minimum descent.  No local cap-switching
argument can do it in this product-base subchamber.

## 8. Strict tolls still admit a finite paid singleton contraction

The strict branch need not stop at the first off-minimum endpoint.  At the
original full-debt minimum, all four debts are positive, every singleton
option is separated from the cap by at least `D_*`, and every active Q/C
endpoint is unique.  Hence one common root neighborhood preserves:

- positivity of every debt;
- strict inactivity of every padding-singleton option; and
- the identity of every active Q/C endpoint.

Enumerate all but one member of the sure core as

\[
 p_1,\ldots,p_{|K|-1}.
\]

Choose positive softenings `theta_j` sufficiently small that the cumulative
root remains in this common neighborhood.  Before step `j`, player `p_j` is
still a sure quitter and another sure core member remains.  Its unique best
endpoint is therefore Continue.  Softening it from one to `1-theta_j` is a
literal unilateral behavioral update with exact positive gain

\[
 \theta_j\bigl(C_{p_j}-Q_{p_j}\bigr)>0.
\tag{8.1}
\]

After at most three steps in Fin4, exactly one original core member `k`
remains sure.  At the common product root, the singleton `{k}` then has
strictly positive probability

\[
 \Pr(Q=\{k\})=
 \left(\prod_{j=1}^{|K|-1}\theta_j\right)
 \left(\prod_{h\notin K}(1-q_h)\right)>0.
\tag{8.2}
\]

This construction works whether each intermediate debt is equal to `D_*` or
strictly above it.  It retains one literal padded profile, root, and Never
tail, and its edges form an actual finite sequence of unilateral behavioral
improvements—not merely a list of counterfactual coalitions.

What it does **not** give is a return.  The endpoint is generally off the
minimum fibre, and the common Never tail need not have low debt.  Thus (8.2)
feeds a source-attached concentrated-singleton/paid-orbit interface, but the
known cap-leakage consumer may return it to the same concentrated residual.
It is a genuine producer contraction of the product-base arm, not yet a
terminal SCC elimination.

## 9. Exact additional datum needed for the positive toll

The softening path uses all consequences of its literal law interpolation:
prescribed payoffs are affine, caps are finite maxima of affine endpoints,
deleted laws are explicit, and global minimality gives `tau_p>=0`.  The
regression in Section 7 shows that these data impose no upper bound on a
positive `tau_p`.

To turn a strict toll into a charged return, one needs an additional
**cross-law orientation**, for example one of the following equivalent-in-
purpose inputs:

1. a source retraction from the softened law to the original minimum law with
   complete cap/law seam `o(theta)`;
2. an upper leakage account saying that the other-coordinate debt increase
   is at most the mover's paid decrease to first order;
3. an extension-compatible exact prefix whose absorption spends the
   off-minimum excess and returns its full semantic/law endpoint to the same
   minimum target; or
4. a finite rank on the changed law/source passport which strictly decreases
   under the paid singleton contraction.

None follows from convexity or deleted-law convergence.  Without one of
these cross-law data, repeating small softenings merely traverses one finite
horizontal path; it does not create a chronological cycle and does not
accumulate an admissible return charge.

## 10. Direct entry to the checked exact-port dichotomy

There is nevertheless a source-attached consumer available **before** taking
the strict softening endpoint.  It reduces the product-base arm to one known
terminal port.

At the full-debt minimum, the singleton-margin identity gives

\[
 U_i-s_i\ge D_*-d_i=\sum_{j\ne i}d_j>0
 \qquad(i\in I).
\tag{10.1}
\]

Punishment normality in the hard residual gives

\[
 \operatorname{Pun}_i\le s_i<U_i.
\tag{10.2}
\]

Thus the literal padded product minimum is a punishment-floor-safe profile.

Choose `p in K`.  In the padded profile, `QuitAt 1` makes `p` Quit in the
product row, while `Never` makes it Continue there.  Another sure core member
still Quits, so the exact pure-time payoff difference is

\[
 V_p(\operatorname{Never})-V_p(\operatorname{QuitAt}1)
 =C_p-Q_p=d_p>0.
\tag{10.3}
\]

The checked pure-time first-disagreement decoder therefore constructs a
`QuittingPaidFirstDisagreementRow` on the **minimum profile itself**, with no
cap transport or endpoint reprojection.  Equations (10.1)--(10.2) make it a
`QuittingPaidRowFloorSafeSource`.

Applying
`QuittingPaidRowFloorSafeSource.exists_markedExactOrbit_alternative_of_witness`
gives exactly

\[
 \boxed{\text{a uniform-equilibrium payoff}
 \quad\lor\quad
 \text{a summable-charge all-Continue semantic port}}
\tag{10.4}
\]

and, in the second arm, positive limiting reach to this same paid suffix.
This is a genuine connection to a checked consumer and makes the strict
off-minimum softening unnecessary for constructing the marked orbit.

It does not close the branch: the summable port is the known fixed-tail exact-
prefix inert residual.  Its roots are prefixed outward, so their finite
profiles do not form one forward chronology with a stable initial segment.
The positive survival of the paid product suffix is not by itself a charged
near-return.  A terminal proof still needs to consume this summable port or
produce an extension-compatible reorientation of it.

## 11. Global-minimum rigidity makes this exact port pure padding

For the attained **full-debt global minimum** used above, the right arm of
(10.4) is sharper than merely summable.  Every root selected by the exact
floor orbit is literally all Continue, and every displayed semantic pair is
the original minimum pair.

Let `z` be the terminal semantic pair of the minimum profile.  Since all four
debts are positive, choose two distinct debtors.  The checked theorem
`quittingTerminalSemantic_minimum_twoPositiveDebt_root_eq_allContinue` says
that every exact Nash root against `z.1` is all Continue.  The all-Continue
prefix fixes `z` by
`quittingTerminalSemanticPrefix_allContinue_eq_of_isZeroNash`.  Induction
along `QuittingPaidRowMarkedExactOrbit.profiles_succ` therefore gives

\[
 q_t=\mathbf C,
 \qquad
 \operatorname{Sem}(\sigma^{(t)})=z
 \qquad(t\geq0).
\tag{11.1}
\]

At the behavioral level, `sigma^(t)` is just the original minimum profile
behind `t` deterministic all-Continue rows.  Hence its time-forgetting
terminal law, unrestricted cap, prescribed payoff, every debt coordinate,
and the inherited paid-row gain are exactly constant.  The paid suffix reach
is one, while the absolute marked date increases by `t`.

This disposes of three tempting consumers.

1. **Marked-date multiplicity.**  The checked multiplicity bound concerns a
   finite set of heavy marked dates in one actual profile.  Here each sibling
   profile has only one copy of the marked row.  The family contains
   infinitely many shifted copies, but no play contains more than one.  The
   bound therefore reads `1 <= constant` separately at every depth and does
   not accumulate.
2. **The retained singleton or coalition atom.**  Its mass is constant, but
   it occurs at a date escaping to infinity.  Pointwise convergence of the
   behavioral roots sees only all Continue, while the time-forgetting laws
   remain constant.  Thus neither law tightness nor positive suffix reach
   attains the atom at one finite date in the limiting chronology.
3. **The finite product response face.**  The same two endpoint values remain
   available at the shifted product row.  Choosing the profitable endpoint
   gives one horizontal off-minimum profile (the toll branch of Sections
   6--9), not an exact predecessor root.  Shifting that response face through
   another all-Continue row creates no new charge and no renewable source
   transition.

Trying to place several copies in one chronology does not repair this.  With
two sure quitters, the first product copy absorbs surely, so all later copies
have zero reach.  Softening a sure quitter to make a later copy reachable
changes the law and creates exactly the cross-law toll whose return is still
missing.  The multiplicity bound then confirms, rather than resolves, the
need to pay for every additional heavy mark.

Thus the marked exact-port construction is an exact **full-data regression**
inside any hypothetical full-debt counterexample source: all of the global
minimum, law, atom, cap, paid-row, and punishment-floor data are retained,
yet the only compatible exact predecessor chronology is deterministic
waiting.  This is conditional on the hypothetical positive minimum source;
it is not an explicit counterexample table.  The additional datum needed is
still an extension-compatible cross-law return or finite law-passport rank,
not a stronger estimate on the existing port.

## 12. A renewable maximum-debt response chain

The pure-padding regression blocks vertical motion, but it does not prevent
an exact renewable **horizontal** construction.  The result below makes the
remaining distinction precise.

Call a behavioral profile finite-clock if there is `H` such that every
player's first-stopping law is supported on

\[
 \{0,1,\ldots,H\}\cup\{\infty\}.
\]

Every padded product profile above is finite-clock.

### Proposition 12.1 (finite-clock minimum response trichotomy)

Let `sigma_0` be an actual finite-clock profile whose terminal semantic pair
is a positive global minimum of total debt `D_*>0`.  There is a recursively
defined sequence of actual profiles with the following alternative.

1. Some step is a unilateral exact best response of gain at least `D_*/4`
   whose target has total debt strictly above `D_*`.
2. All targets remain global minima, the finite horizons stay bounded, and
   the sequence contains an exact repeated profile.  The segment between two
   repetitions is a literal horizontal best-response cycle; every edge has
   gain at least `D_*/4` and kills its mover's debt.
3. All targets remain global minima and their finite horizons are unbounded.
   After passing to record times and then to a subsequence, one fixed ordered
   pair of distinct players occurs cofinally at adjacent record deadlines:
   the responder installs a pure deadline `H+1` while one opponent has pure
   deadline `H`.  Every complete response edge still has gain at least
   `D_*/4`.

The word horizontal is essential in (2)--(3).  Neither output is asserted to
be an exact Nash--Bellman chronology.

### Proof

Suppose the current profile `sigma_n` is a global minimum.  Choose a player
`i_n` with maximum debt.  Since there are four players,

\[
 d_{i_n}(\operatorname{Sem}(\sigma_n))\ge D_*/4.
\tag{12.1}
\]

Against finite-clock opponents, the unrestricted behavioral cap is attained
by a pure stopping time.  Indeed, if the opponents have no finite stopping
mass after `H`, all pure times `t>H` give the same payoff: on opponent
absorption by `H` the outcome is already fixed, and on opponent survival the
deviator Quits alone.  Never is the only additional endpoint.  Since every
behavioral stopping law is a mixture of pure times, the cap is the maximum
of the finite list

\[
 0,1,\ldots,H,H+1,\infty.
\tag{12.2}
\]

Choose the least finite maximizing time, with Never last in the tie order,
and replace only player `i_n` by that pure response.  The mover's opponents,
and hence its complete cap, are unchanged.  Therefore the actual payoff gain
is exactly its old debt, at least `D_*/4`, and its target debt coordinate is
zero.

Carrier minimality says that the new total debt is at least `D_*`.  A strict
inequality gives alternative 1.  In the equality case the new actual profile
is another finite-clock global minimum and the construction repeats.  If
`H_n` is the largest finite time currently used, (12.2) gives

\[
 H_{n+1}\le H_n+1.
\tag{12.3}
\]

If the horizons are bounded, then each coordinate is either its unchanged
initial finite-clock strategy or one of finitely many pure times or Never.
The profile state space visited by the recursion is finite.  An infinite
equality sequence therefore repeats an exact profile, proving alternative 2.

If the horizons are unbounded, take the steps at which a new record is first
created.  Equation (12.3) makes every new record exactly `H+1`.  The responder
cannot be the unique player carrying the old record `H`: after deleting its
own old strategy, all opponent stopping mass ends earlier, so the least
maximizing late time is at most one past the opponents' smaller horizon and
cannot create `H+1`.  Hence some opponent also carries the old record `H`.
There are only twelve ordered pairs of distinct Fin4 players, so a cofinal
subsequence fixes the responder and that opponent.  This proves alternative
3.  Notice that the fixed `D_*/4` lower bound belongs to the complete response
edge; the adjacent censoring difference between deadlines `H` and `H+1` is
only known to be nonnegative, and must not be assigned that fixed bound.

### Consequence and limitation

This proposition supplies the renewable child-source ancestry which the
static reset packet itself lacks: every equality target is literally the next
source.  It also shows that an escaping response time is not arbitrary.  It
can be normalized to an adjacent record process with two recurring labels.

It still does not consume the port.  In alternative 2 the cycle consists of
whole-strategy replacements, not successive dates of one play.  In
alternative 3 the large gain can be distributed over earlier discrepancies;
the final adjacent deadline need not carry a uniform part of it.  Serializing
either family would require exactly the missing conversion of a horizontal
complete-response edge into an exact punishment-floor predecessor edge, or a
charge-relative seam estimate.  The checked static-cycle chronology barrier
applies to the same category error.

### Proposition 12.2 (the unbounded calendar has a finite strategic quotient)

Alternative 3 does not create infinitely many distinct semantic states.
After the set `P` of players which have ever been replaced stabilizes, every
player outside `P` retains one fixed finite-clock strategy and every player in
`P` uses one pure deadline or Never.  Let `F` be the finite union of the
supports of the unchanged players.  The complete semantic pair and terminal
law of the current profile depend only on

1. the weak order of the pure deadlines of players in `P`;
2. their weak order relative to the finitely many dates in `F`; and
3. which pure deadlines are Never.

Consequently the equality response chain has only finitely many distinct
joint semantic/law states.  If it is infinite and never leaves the minimum
fibre, two indices `a<b` have exactly the same prescribed payoff, complete cap
vector, and terminal law, while the intervening horizontal response edges
each have gain at least `D_*/4`.

#### Proof

For fixed pure deadlines and fixed realizations of the unchanged finite-clock
players, the terminal coalition is determined by the first occupied calendar
rank.  Its identity is unchanged by every order-preserving relabelling which
fixes `F`.  Averaging over the finitely supported unchanged clocks proves the
claim for the prescribed terminal law and payoff.

For a cap coordinate, first fix a pure stopping-time response.  Its payoff is
again determined only by its order position relative to the opponents' pure
deadlines and `F`.  There are finitely many such positions, plus Never, and
every integer deadline in the same position has the same payoff.  Taking the
maximum over these finitely many response positions shows that the complete
behavioral cap has the same finite order-type dependence.  There are only
finitely many weak orders of finitely many labels, so recurrence follows.

This is semantic recurrence with literal horizontal ancestry, not an
admissible Nash--Bellman return.  A common compression of the calendar changes
several players' strategies at once, and the positive response gains are not
absorption charges.  Thus Proposition 12.2 removes absolute deadline size as
a possible *state-space* escape, but it does not supply the missing
horizontal-to-chronological compiler.

## Sources inspected

- `notes/CODEX_SOCIAL_SOURCE__CLOSED_BEHAVIORAL_LAW_PRODUCT_BASE.md`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargePersistentBaseFiniteNashDispatch.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidRowExactPortAlternative.lean`;
- `UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`;
- `fable/MARKED_DATE_MULTIPLICITY_BOUND.md` and its checked scratch
  implementation record.
