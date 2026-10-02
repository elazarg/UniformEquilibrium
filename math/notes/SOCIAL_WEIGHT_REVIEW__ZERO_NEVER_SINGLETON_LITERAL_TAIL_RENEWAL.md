# Zero-Never singleton sources admit a literal-tail renewal split

Identity: `SOCIAL_WEIGHT_REVIEW`

Status: **ordinary-mathematics proof draft.**  The scalar factorization and
the two limiting cases below are exact.  The final child-source packaging is
a composition of reviewed source-causalization and minimum-atom results, but
has not been checked as one Lean declaration.  This is a renewable producer,
not a terminal consumer and not a well-founded descent.

Independent review:
[PAIRED_HULL_REVIEW](../feedback/SOCIAL_WEIGHT_REVIEW__ZERO_NEVER_SINGLETON_LITERAL_TAIL_RENEWAL__BY_PAIRED_HULL_REVIEW.md).
The two requested provenance repairs are incorporated in Sections 4--5; no
post-repair PASS is claimed here.

## 1. Question

Work in the Fin4 hard-residual regime with positive global minimum debt

\[
D_*>0.
\]

Suppose a retained minimum source has joint limiting point

\[
y=((U,B),\nu),\qquad D(U,B)=D_*,
\]

and, for some player \(j\) and \(\mu>0\),

\[
\nu(\mathsf{Never})=0,
\qquad
\nu(\{j\})=\mu.
\tag{1.1}
\]

The checked owner-clock compression supplies actual source profiles
\(\Sigma_n\), dates \(t_n\), and one-date targets \(\tau_n\).  The target is
obtained by changing only \(j\)'s action at \(t_n\) to sure Quit, and for a
fixed \(0<\lambda<\mu\),

\[
\Pr_{\tau_n}(\{j\}\text{ occurs at }t_n)>\lambda.
\tag{1.2}
\]

The problem is to use zero Never without replacing the actual continuation
after \(t_n\) by a newly grafted minimum reference profile.

## 2. Exact marked-row factorization

Write \(q_n\) for \(j\)'s Quit probability in the unmodified source root at
\(t_n\), and put

\[
c_n=1-q_n.
\]

Let \(L_n\) be the probability in the source that everybody reaches
\(t_n\) and every opponent of \(j\) Continues at that row.  Because the
compressed target makes \(j\) Quit surely,

\[
L_n
=\Pr_{\tau_n}(\{j\}\text{ occurs at }t_n)
>\lambda.
\tag{2.1}
\]

Let \(T_n\) be the **literal actual post-row tail** of \(\Sigma_n\), starting
at date \(t_n+1\), and let

\[
e_n=\Pr_{T_n}(\mathsf{Never}).
\]

If \(N_n=\Pr_{\Sigma_n}(\mathsf{Never})\), independence at the unique live
history gives the exact identity

\[
\boxed{N_n=L_nc_ne_n.}
\tag{2.2}

The joint laws of \(\Sigma_n\) converge to \(\nu\), hence \(N_n\to0\).
Equations (2.1)--(2.2) imply

\[
c_ne_n\le \frac{N_n}{\lambda}\longrightarrow0.
\tag{2.3}

After a subsequence, exactly one of the following alternatives is available:

1. \(c_n\to0\);
2. there is \(\varepsilon>0\) such that \(c_n\ge\varepsilon\) for every
   retained \(n\), and then \(e_n\to0\).

This is a source identity.  It uses the unmodified root probability \(c_n\)
and the literal suffix \(T_n\), not the cross-tail reference used by the
minimum-tail forced-pair normal form.

## 3. The invisible-compression arm

Assume \(c_n\to0\).  Couple \(\Sigma_n\) and \(\tau_n\) using the same
randomness everywhere except at player \(j\)'s action at \(t_n\).  The two
profiles can differ only when the old Bernoulli action of \(j\) is Continue,
an event of conditional probability \(c_n\).

This remains true uniformly after an arbitrary complete behavioral
replacement by any player \(i\ne j\): that replacement may alter the chance
of reaching the row, but cannot increase the conditional disagreement
probability of the unchanged \(j\)-coin above \(c_n\).  For \(i=j\), the
opponents are identical, so the unrestricted cap is exactly unchanged.

If every reward coordinate has absolute value at most \(M\), then

\[
d_{\mathrm{TV}}(\operatorname{Law}(\Sigma_n),
                   \operatorname{Law}(\tau_n))
\le c_n,
\tag{3.1}
\]

\[
|U_i(\Sigma_n)-U_i(\tau_n)|\le2Mc_n,
\tag{3.2}
\]

and

\[
|B_i(\Sigma_n)-B_i(\tau_n)|
\le
\begin{cases}
0,&i=j,\\
2Mc_n,&i\ne j.
\end{cases}
\tag{3.3}

Thus \(\tau_n\) converges to the same joint minimum point \(y\).  Every
\(\tau_n\) has the sure finite deadline \(t_n\) of player \(j\), so its
prescribed play absorbs by that date.

The reviewed arbitrary-clock minimum purification theorem can now be applied
to the retained sequence \((\tau_n)\).  It yields an actual off-minimum paid
port.  This use does not assert that the copied source root word remains
cap--Nash for \(\tau_n\).

## 4. The reached-tail arm

Assume \(c_n\ge\varepsilon>0\).  Then

\[
e_n\le\frac{N_n}{\lambda\varepsilon}\longrightarrow0,
\tag{4.1}

and the literal source probability of reaching \(T_n\) through the marked
row is

\[
L_nc_n\ge\lambda\varepsilon.
\tag{4.2}

Retain the actual tail \(T_n\), rather than first performing the cofinal
cross-tail graft, and jointly compactify

\[
(\operatorname{Sem}(T_n),\operatorname{Law}(T_n)).
\]

Every semantic cluster has total debt at least \(D_*\).  There are two cases.

### 4.1 Strict tail

If a selected cluster has debt greater than \(D_*\), then sufficiently late
\(T_n\) is an actual off-minimum profile.  The hard terminal-gap actual-reach
theorem supplies its paid row, with \(T_n\) itself as the port's original
profile and therefore identity replacement ancestry inside the port.  In
addition, (4.2) records that the incoming profile \(\Sigma_n\) reaches this
suffix with positive probability.  These are different provenance types:
\(\Sigma_n\to T_n\) is a reached-suffix relation, not a unilateral
behavioral-replacement ancestry.

### 4.2 Minimum tail

Suppose instead the selected joint cluster is

\[
y'=((U',B'),\nu'),
\qquad D(U',B')=D_*.
\]

Equation (4.1) gives

\[
\nu'(\mathsf{Never})=0.
\tag{4.3}

If every singleton coordinate of \(\nu'\) is zero, the reviewed closed-law
product-base theorem realizes the same semantic pair and law by an actual
finite product profile; the checked finite-clock theorem then gives an
off-minimum paid port.  This is a valid semantic-point exit, but the finite
product profile is a new realizer.  It is not one of the literal tails
\(T_n\), and no replacement ancestry from \(T_n\) to it is asserted.

Otherwise fix \(j'\) with \(\nu'(\{j'\})>0\).  The positive finite atom,
the literal realizing sequence \((T_n)\), and the retained hard residual feed
the source-faithful minimum causalization theorem.  It retains a subsequence
of these exact tails as its supplied suffix sequence, while selecting fresh
finite marks and exact cap--Nash prefixes.  The resulting complete next
`FinFourMinimumAtomProducer` is based at \(y'\) and has singleton atom
\(\{j'\}\).  By (4.2), its underlying suffix source is not an unrelated
minimum realizer: it is an actually reached later suffix of the incoming
source with a fixed reach floor on the selected transition.  The fresh child
prefix itself is not claimed to be the temporal continuation of the parent.

Hence the zero-Never positive-singleton arm has the following dispatch, with
the provenance loss in the middle arm made explicit:

\[
\boxed{
\begin{array}{c}
\text{literal-tail off-minimum paid port}\
\text{or a same-point finite-product paid port, with ancestry loss}
\end{array}
\quad\lor\quad
\text{later reached zero-Never positive-singleton minimum source}.}
\tag{4.4}

### 4.3 Every pre-existing zero debt survives the literal suffix passage

The reached-tail transition preserves more than the law support.  Let
\(R_{i,n}\) be the prescribed probability that the live history reaches the
start of \(T_n\).  For any player \(i\), copy its prescribed behavior before
that cut and, conditional on reaching the cut, use an arbitrarily good
complete response against \((T_n)_{-i}\).  Before the cut this hybrid and the
source profile are identical.  Conditional on reaching it, their payoff
difference is the corresponding tail response gain.  Taking suprema gives

\[
 d_i(\Sigma_n)\ge R_{i,n}d_i(T_n).
\tag{4.5}
\]

Here \(R_{i,n}\) is computed under the prescribed pre-cut behavior of every
player, including \(i\); the hybrid copies that behavior exactly.  In the
marked-row branch used above, the joint source reach of the tail is
\(L_nc_n\), so

\[
 R_{i,n}=L_nc_n\ge\lambda\varepsilon
 \qquad(i<4).
\tag{4.6}
\]

Consequently, if a fixed coordinate \(o\) has
\(d_o(\Sigma_n)\to0\), then

\[
 d_o(T_n)\longrightarrow0.
\tag{4.7}

Thus a reset-rigid zero-debt owner is retained at every minimum tail cluster.
The source-faithful causalization prefixes have Continue product tending to
one, so the regenerated minimum child retains the same zero coordinate in its
limit as well.  This is genuine zero-face preservation for the **reached
suffix transition**.  It does not extend across the paid behavioral response
in Section 5.2, because that response changes one of player \(o\)'s opponents
and may reactivate its cap debt.

Summing (4.5) at a minimum-to-minimum transition gives only

\[
 D_*\ge (L_nc_n)D_*+o(1),
\]

so the inequality alone supplies no strict rank.  Its useful content is the
coordinatewise preservation of all already vanishing debts, rather than a
new total-debt decrease.

## 5. Why this does not yet terminate

The second branch of (4.4) is renewable but has no proved well-founded rank.
Across successive children:

- the singleton owner may change;
- the singleton mass, hence the available \(\lambda\), may tend to zero;
- the owner Continue floor \(\varepsilon\) may tend to zero;
- the minimum joint law may change; and
- the newly causalized exact prefix is not a continuation of the old exact
  cap--Nash word.

Compactness gives two useful boundary exits but not termination.  Along an
infinite chain, if the singleton masses tend to zero, a law cluster has zero
Never and zero singleton mass and enters the product-base exit, while losing
literal-tail ancestry at the new finite product realizer.  If the compression
Continue factors tend to zero, Section 3 gives the invisible-compression
exit.  The only persistent source-faithful residual therefore has both
quantities bounded below along a cofinal subchain, and every corresponding
child tail is actually reached with a fixed positive probability.

That fixed reach is not itself absorption charge.  It does not contradict
bounded exact-block hazard capacity and does not turn the row replacement
into a Nash--Bellman edge.

### 5.1 The multiplicative telescope stops at a precise projective seam

There is nevertheless a fixed amount of **raw** hazard at every persistent
node.  Suppose its singleton mass is at least \(\mu_0>0\).  On sufficiently
late actual realizers, player \(j\)'s finite stopping probability is at least
\(\mu_0/2\), because the singleton-\(j\) terminal event is contained in the
event that \(j\) stops finitely.  Hence some finite cutoff \(H_n\) satisfies

\[
\Pr(T_j\le H_n)\ge\mu_0/4.
\tag{5.1}
\]

If \(q_{t,j}\) are the marginal live-history Quit probabilities, then

\[
\frac{\mu_0}{4}
\le 1-\prod_{t\le H_n}(1-q_{t,j})
\le \sum_{t\le H_n}q_{t,j}
\le \sum_{t\le H_n}\operatorname{Abs}(q_t).
\tag{5.2}
\]

Thus every persistent renewal source contains a finite raw block of fixed
positive hazard.  If these blocks were disjoint successive exact
Nash--Bellman blocks in one chronology, repetition would give unbounded exact
capacity and hence the existing uniform-payoff consumer.

The present construction does not give that hypothesis.  The child cut is
immediately after the first supported owner date used by clock compression,
whereas the quantile cutoff \(H_n\) in (5.1) may be arbitrarily later.  The
next child can therefore restart inside the block whose hazard was just
counted.  Adding (5.2) over children may count the same future owner mass
repeatedly.  Moreover the roots in (5.2) are the actual source roots, not
exact or uniformly approximate Nash--Bellman roots; only separately chosen
prefix words have exact cap--Nash certificates.

Equivalently, if \(A_k\) is an owner's residual finite-stop probability and
\(q_k\) its next exposed hazard, then

\[
A_k=q_k+(1-q_k)A_{k+1}.
\tag{5.3}
\]

Uniform lower bounds on \(A_k\) do not force a lower bound on \(q_k\).
The exposed hazards \(q_k\) may be summable while the unspent residual mass
is moved to later calendars at every regeneration.  A projective limit then
records boundary mass at Never rather than a charged forward block.

This locates the exact connection with the finite-deadline/projective and
bounded-capacity questions.  What is needed is not another positive atom or
another finite truncation: it is an adjacent source theorem placing a fixed
fraction of (5.2) **before** the renewed child cut, with exact or summably
approximate Nash--Bellman typing.  The current literal-tail renewal supplies
neither condition.

### 5.2 A source-attached paid response does lift from the reached tail

The checked two-cut paid-splice theorem gives more than the raw estimate
(5.2).  In Fin4, (4.3) implies that some nonempty coalition has limiting
tail-law mass at least \(1/15\).  Fix

\[
\chi=\frac1{30},
\qquad
K=(1-e^{-\chi})D_*.
\tag{5.4}
\]

The silent-padding two-cut adapter applied to the exact tail sequence
\((T_n)\) returns, after subsequence selection, either:

1. a literal later suffix with debt at least
   \(D_*+(e^\chi-1)D_*/2\); or
2. one fixed player \(p\) and a complete behavioral response in \(T_n\)
   whose payoff gain is greater than \(K/16\).

In the second arm, keep player \(p\)'s incoming strategy unchanged before
the cut into \(T_n\), and use the displayed tail response only after that
cut.  The opponents and every earlier action are literal copies.  Therefore
the whole-source payoff difference factors exactly by the prescribed joint
reach of the tail:

\[
U_p(\text{lifted response})-U_p(\Sigma_n)
=(L_nc_n)
 \bigl(U_p(\text{tail response})-U_p(T_n)\bigr).
\tag{5.5}
\]

On the persistent branch, (4.2) and (5.5) give the fixed source-attached
floor

\[
U_p(\text{lifted response})-U_p(\Sigma_n)
>\lambda\varepsilon\frac{K}{16}.
\tag{5.6}

This is an actual complete unilateral response of the incoming near-minimum
profile.  It is not merely a response contrast between two forced-prefix
plans.  Thus the zero-Never reached-tail split repairs the zero-reach defect
which prevents reattaching a paid splice behind a pure forced-pair row.

Equation (5.6) still does not close the chamber.  Because only \(p\)'s own
strategy changes, its cap is fixed and its debt falls by the displayed gain,
but the other three caps may rise by the same total amount.  If the response
target is strictly off minimum it gives the existing paid port.  If its
cluster remains on the minimum fibre, (5.6) gives a fixed conservative
cross-cap transfer and feeds the existing full-response/support-handoff
dispatch.  Support entry or debtor rotation remains possible, so no finite
rank follows merely from the positive floor.

### 5.3 Exact triangular regression for the multiplicative argument

The projective seam in Section 5.1 is real even with perfect literal suffix
matching.  Fix numbers

\[
q_k=2^{-k-2}.
\]

For each finite depth \(N\), let all players except \(j\) play Never.  Starting
at level \(k<N\), let \(j\) Quit at the current first row with probability
\(q_k\), and on Continue use the level-\(k+1\) tail.  At level \(N\), let
\(j\) Quit surely.  Then, at every finite level:

- the terminal law is exactly \(\delta_{\{j\}}\), hence has zero Never and
  singleton mass one;
- the first-row Continue factor is at least \(3/4\);
- the next node is the literal reached suffix; and
- the exposed first-row hazards through depth \(N\) sum to less than
  \(1/2\).

As \(N\to\infty\), the projective clock limit has Never probability

\[
\prod_{k=0}^{\infty}(1-q_k)>0.
\]

Thus zero Never at every finite source, a uniform singleton floor, a uniform
Continue floor, and exact tail nesting do not force divergent exposed hazard.
The missing mass may be paid by a sure deadline which recedes beyond every
fixed projective window.  This regression makes no positive-minimum or Nash
claim; it shows sharply why those additional data must enter any terminating
telescope.

## 6. The cross-tail distinction

The existing cofinal minimum-tail theorem uses the splice

\[
\operatorname{RootStack}(\eta_n;0,\ldots,t_n)
\triangleright\sigma_n,
\]

where \(\sigma_n\) is restarted from its beginning after the marked row.
That construction guarantees a minimum semantic tail, but the restarted
\(\sigma_n\) is not the original literal suffix after \(t_n\).  Therefore
the factorization (2.2) cannot be applied to that graft merely because the
upstream law has zero Never mass.

Conversely, (2.2) applies to the actual suffix \(T_n\), but before the split
in Section 4 its semantic debt is not known to be minimum.  The strict-tail
versus minimum-tail dispatch is exactly what reconciles these two facts.

This distinction is sharp.  If player \(j\) Quits surely at date zero while
all opponents Continue, the terminal law is \(\delta_{\{j\}}\) and has zero
Never mass, regardless of the continuation placed after date zero.  That
continuation may have arbitrary Never behavior and arbitrary owner-response
value.  Thus zero Never in the observed law alone says nothing about a tail
hidden behind a sure singleton row.

## 7. Exact remaining waist

The law-support contraction is therefore stronger than a bare return to the
old forced-pair node: it provides a literal later-suffix renewal unless it
already exits to the off-minimum paid port.  What is still missing is one of:

1. a bridge restoring literal source ancestry in the zero-singleton
   product-base exit, if that provenance is required downstream;
2. a well-founded rank on the renewed zero-Never singleton sources;
3. a theorem converting the fixed reached-suffix probability in the
   persistent subchain into accepted chronological charge; or
4. a terminal consumer for the actual off-minimum paid port.

Without one of these, (4.4) is a genuine source-alignment improvement but not
an elimination of the reset-rigid chamber.

## 8. Sources checked

- `formalized/FIN4_MINIMUM_SINGLETON_CLOCK_COMPRESSION.md`;
- `formalized/FIN4_WEAK_SINGLETON_TO_MINIMUM_TAIL_FORCED_PAIR.md`;
- `notes/PAIRED_HULL_REVIEW__RESET_RIGID_LAW_SUPPORT_CONTRACTION.md`;
- `formalized/ZERO_SINGLETON_BEHAVIORAL_LAW_PRODUCT_BASE_AND_SURE_CORE_DESCENT.md`;
- `formalized/PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT.md`;
- `formalized/ARBITRARY_CLOCK_MINIMUM_PURIFICATION_TO_OFF_MINIMUM_PAID_PORT.md`;
- `formalized/FIN4_MINIMUM_RETURN_SILENT_PADDING_TWO_CUT_SOURCE_ADAPTER.md`;
- `formalized/FIN4_MINIMUM_JOINT_LAW_HAS_FINITE_ATOM.md`; and
- `formalized/SOURCE_FAITHFUL_MINIMUM_ENDPOINT_CAUSALIZATION_AND_RESPONSE_MENU_TRANSPORT.md`.

The checked declarations underlying the proposed child packaging include
`exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` and, because
no incoming single date has a uniform mass floor,
`nonempty_sourceFaithfulMinimumCausalChronology`.  The stronger
`nonempty_sourceFaithfulMinimumCausalization` applies only when supplied
marks already carry such a floor.  No declaration currently packages the
whole literal-tail split (2.2)--(4.4).
