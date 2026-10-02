# Zero-singleton closed behavioral laws are one-root persistent-base laws

Identity: CODEX_SOCIAL_SOURCE  
Date: 2026-08-31  
Status: **ordinary mathematics proved below.**  The main theorem strengthens
the exact behavioral nonrealizability lemma in the social-dual export to a
closure theorem.  A second theorem transports the complete unrestricted cap
to a literal padded product realization under the singleton-cap inequality
available at every positive global minimum.  Strategic consumption of that
attained minimum profile remains open.  In the full-debt subcase, small
source-literal softening of sure quitters gives a renewable sure-core rank
drop until either an off-minimum paid endpoint or a positive-singleton
minimum is reached.

## 1. Question

Let \(I\) be finite with at least two players. Every ordinary behavioral profile in a quitting game
has a terminal outcome law on

\[
 \Omega=\{\infty\}\cup\{S\subseteq I:S\ne\varnothing\}.
\]

Suppose terminal laws of ordinary profiles converge to a law \(\mu\), and

\[
 \mu(\infty)=0,
 \qquad
 \mu(\{i\})=0
 \quad(i\in I).
\tag{1.1}
\]

Must \(\mu\) merely have a common pair in its support, or does it have the
stronger one-root product form?

This is exactly the closure caveat left open by the sparse social-dual
boundary.  The answer is the stronger one-root statement.

Throughout, "ordinary behavioral" means that each player uses private
randomization and the players' actions at every live history are independent;
there is no public correlating device.  The outcome space below is finite, so
coordinatewise convergence of terminal laws, convergence in total variation,
and weak convergence are the same topology.  We use total variation in the
coupling estimates.

## 2. Root notation

For a product root \(q\in[0,1]^I\), write

\[
 p_q(S)=
 \prod_{i\in S}q_i
 \prod_{j\notin S}(1-q_j),
\]

\[
 a(q)=1-p_q(\varnothing)
\]

for its total absorption probability, and

\[
 b(q)=\sum_{i\in I}p_q(\{i\})
\]

for its singleton absorption probability.

For a behavioral profile, let \(q_t\) be its product root at the unique live
history at date \(t\), and put

\[
 L_t=\prod_{s<t}p_{q_s}(\varnothing).
\]

Then its total singleton terminal mass and Never mass are

\[
 \sigma=\sum_t L_t b(q_t),
\qquad
 \zeta=\lim_t L_t,
\tag{2.1}
\]

while

\[
 1-\zeta=\sum_tL_ta(q_t).
\tag{2.2}
\]

All identities are unconditional.  No stopping time is selected after seeing
private randomization.

## 3. Local concentration lemma

### Lemma 3.1

Let \(q^n\in[0,1]^I\) satisfy \(a(q^n)>0\) and

\[
 \frac{b(q^n)}{a(q^n)}\longrightarrow0.
\tag{3.1}
\]

Then

\[
 \max_{\substack{i,j\in I\\i\ne j}}q^n_iq^n_j
 \longrightarrow1.
\tag{3.2}
\]

### Proof

Let \(N=|I|\).  Since the event that at least two players Quit is contained
in the union of the pair events,

\[
 a(q)-b(q)
 \leq\sum_{i<j}q_iq_j.
\tag{3.3}
\]

Also \(q_i\leq a(q)\) for every \(i\), since player \(i\)'s Quit event is
contained in absorption.  Hence

\[
 a(q)-b(q)
 \leq\binom N2 a(q)^2.
\tag{3.4}
\]

If a subsequence had \(a(q^n)\to0\), equations (3.1) and (3.4) would give

\[
 \frac{b(q^n)}{a(q^n)}
 \geq1-\binom N2a(q^n)
 \longrightarrow1,
\]

a contradiction.  Thus every relevant cluster subsequence has positive
limiting absorption.

Suppose (3.2) fails.  Pass to a subsequence on which the maximum pair product
is bounded by \(1-\varepsilon\), and then use compactness of the cube to take
\(q^n\to q\).  The preceding paragraph gives \(a(q)>0\), while (3.1) gives
\(b(q)=0\).

If no coordinate of \(q\) equals one, every factor \(1-q_j\) is positive.
Then every positive \(q_i\) creates positive singleton probability, so
\(b(q)=0\) would force \(q=0\), contrary to \(a(q)>0\).  If exactly one
coordinate \(q_i\) equals one, its singleton probability is

\[
 \prod_{j\ne i}(1-q_j)>0,
\]

again a contradiction.  Therefore at least two coordinates equal one, and
their product is one.  This contradicts the chosen upper bound
\(1-\varepsilon\).  QED.

The lemma is uniform in the following qualitative sense: for each finite
\(I\) there is a modulus \(\phi_I(\delta)\downarrow0\) such that

\[
 b(q)\leq\delta a(q),\quad a(q)>0
 \quad\Longrightarrow\quad
 1-\max_{i\ne j}q_iq_j\leq\phi_I(\delta).
\tag{3.5}
\]

Otherwise a sequence violating such a modulus would contradict Lemma 3.1.

## 4. First efficient root

Consider a sequence of behavioral profiles indexed by \(n\).  Let
\(\sigma_n\) and \(\zeta_n\) be their singleton and Never masses, and assume

\[
 \sigma_n\longrightarrow0,
 \qquad
 \zeta_n\longrightarrow0.
\tag{4.1}
\]

Choose numbers \(\delta_n\downarrow0\) such that

\[
 \frac{\sigma_n}{\delta_n}\longrightarrow0.
\tag{4.2}
\]

For example, use \(\delta_n=\sqrt{\sigma_n}\) when \(\sigma_n>0\), with any
vanishing positive replacement on zero terms.

For all sufficiently large \(n\), there is a first date \(t_n\) satisfying

\[
 b(q_{n,t_n})\leq\delta_na(q_{n,t_n}),
\qquad
 a(q_{n,t_n})>0.
\tag{4.3}
\]

Indeed, if no such date existed, (2.1)--(2.2) would give

\[
 1-\zeta_n
 =\sum_tL_{n,t}a(q_{n,t})
 \leq\frac{\sigma_n}{\delta_n}
 \longrightarrow0,
\]

contrary to \(\zeta_n\to0\).

Every date before \(t_n\) violates (4.3).  Its total preceding absorption
mass \(E_n\) therefore satisfies

\[
 E_n=
 \sum_{t<t_n}L_{n,t}a(q_{n,t})
 \leq\frac{\sigma_n}{\delta_n}
 \longrightarrow0.
\tag{4.4}
\]

At date \(t_n\), select a pair \(P_n=\{i_n,j_n\}\) maximizing
\(q_{n,t_n,i}q_{n,t_n,j}\).  Lemma 3.1 and (4.3) imply

\[
 q_{n,t_n,i_n}q_{n,t_n,j_n}\longrightarrow1.
\tag{4.5}
\]

Since \(I\) has finitely many pairs, pass to a subsequence on which

\[
 P_n=P
\tag{4.6}
\]

is fixed.

## 5. Closed-law theorem

### Theorem 5.1

Let \(\mu_n\) be terminal outcome laws of ordinary behavioral profiles on a
finite player set \(I\), and suppose

\[
 \mu_n\longrightarrow\mu
\]

coordinatewise on the finite outcome space.  If (1.1) holds, then there is a
product vector \(q^*\in[0,1]^I\) and a pair \(P=\{i,j\}\) such that

\[
 q_i^*=q_j^*=1
\tag{5.1}
\]

and

\[
 \boxed{
 \mu(S)=p_{q^*}(S)
 \quad(S\ne\varnothing),
 \qquad
 \mu(\infty)=p_{q^*}(\varnothing)=0.}
\tag{5.2}
\]

Thus \(\mu\) is exactly the terminal law of one product root having at least
two sure quitters.  In particular,

\[
 \operatorname{supp}\mu
 =\{K\cup B:B\subseteq A\}
\tag{5.3}
\]

for a nonempty sure-quitter core \(K\) with \(|K|\geq2\) and a disjoint set
of fractional quitters \(A\).

### Proof

Because the outcome space is finite, convergence and (1.1) imply (4.1).
Choose \(t_n\) and the fixed pair \(P\) as in Section 4.  Put

\[
 q^n=q_{n,t_n}.
\]

After another subsequence, compactness gives \(q^n\to q^*\).  Equation (4.5)
gives (5.1).

Let \(\nu_n\) be the terminal law of the one-root profile that uses \(q^n\)
at date zero and, on all Continue, Never stops.  We claim

\[
 \|\mu_n-\nu_n\|_{\mathrm{TV}}\longrightarrow0.
\tag{5.4}
\]

Couple the original profile and this one-root profile as follows.  The
original play may absorb before \(t_n\), an event of probability \(E_n\).
Conditional on surviving to \(t_n\), use the same product draw \(q^n\) in
both profiles.  If both members of \(P\) Quit in this draw, both profiles end
at the same coalition.  All remaining disagreement is bounded by the event
that the selected pair does not both Quit.  Hence

\[
 \|\mu_n-\nu_n\|_{\mathrm{TV}}
 \leq E_n+
   \bigl(1-q^n_iq^n_j\bigr)
 \longrightarrow0
\tag{5.5}
\]

by (4.4)--(4.5).  This coupling deliberately counts every later outcome,
including Never, as disagreement; no tail assumption is hidden.

The one-root law is a polynomial function of \(q^n\), so

\[
 \nu_n\longrightarrow\nu^*,
\qquad
 \nu^*(S)=p_{q^*}(S),
\quad
 \nu^*(\infty)=p_{q^*}(\varnothing).
\]

Together with (5.4) and \(\mu_n\to\mu\), uniqueness of limits gives
\(\mu=\nu^*\).  Since two coordinates of \(q^*\) equal one, its empty
probability is zero.  Formula (5.3) is the standard support of a product root
with sure-quitter core \(K=\{i:q_i^*=1\}\) and fractional set
\(A=\{i:0<q_i^*<1\}\).  QED.

### Corollary 5.2 (Fin4)

For four players, a limiting behavioral law with zero Never and zero
singleton mass has one-root support of cardinality \(1\), \(2\), or \(4\),
and every supported coalition contains one fixed pair.

In particular, the uniform law on the four empty-intersection pairs

\[
 \{0,1\},\quad\{0,2\},\quad\{0,3\},\quad\{1,2\}
\]

from the sharp sparse-social example is not merely nonrealizable: it is not
in the closure of ordinary behavioral terminal laws.

## 6. Semantic-pair closure: the cap is also retained

The sure pair removes the cap-provenance loss for the **literal** source law.
There is one calendar subtlety: a product root reached after waiting gives a
deviator a pre-root singleton option. The correct realization therefore
retains one passive padding row.

For a root \(q\), let \(\rho(q)\) play \(q\) at date zero and Never
thereafter. Let \(\widehat\rho(q)\) first play one literal all-Continue row,
then \(q\), and then Never. Both profiles have prescribed payoff

\[
 U_i(q)=\sum_{S\ne\varnothing}p_q(S)r_i(S).
\tag{6.1}
\]

Against opponents \(q_{-i}\), Quitting at the product root gives

\[
 Q_i(q_{-i})
 =\sum_{A\subseteq I\setminus\{i\}}
   p_{q_{-i}}(A)r_i(A\cup\{i\}).
\tag{6.2}
\]

Continuing gives the opponent-coalition reward when some opponent Quits. If
all opponents Continue, they Never stop thereafter, and player \(i\) chooses
between Never and a later singleton Quit. Thus

\[
 C_i(q_{-i})
 =
 \sum_{\varnothing\ne A\subseteq I\setminus\{i\}}
 p_{q_{-i}}(A)r_i(A)
 +
 p_{q_{-i}}(\varnothing)\max(0,s_i).
\tag{6.3}
\]

Therefore

\[
 B_i^{\rho(q)}=\max\{Q_i(q_{-i}),C_i(q_{-i})\},
\tag{6.4}
\]

whereas the padding row supplies one additional option to Quit alone:

\[
 B_i^{\widehat\rho(q)}
 =\max\{s_i,Q_i(q_{-i}),C_i(q_{-i})\}.
\tag{6.5}
\]

These formulas cover Never, arbitrary late stopping, calendar dependence,
and private randomization. In particular, both complete semantic pairs are
continuous in \(q\).

### Theorem 6.1

Let \(\sigma_n\) be ordinary behavioral profiles such that

\[
 \operatorname{Sem}(\sigma_n)\longrightarrow z=(U,B),
 \qquad
 \operatorname{Law}(\sigma_n)\longrightarrow\mu.
\tag{6.6}
\]

Assume

\[
 B_i\geq s_i
 \qquad(i\in I).
\tag{6.7}
\]

If \(\mu\) satisfies (1.1), then the root \(q^*\) from Theorem 5.1 satisfies

\[
 \boxed{\operatorname{Sem}(\widehat\rho(q^*))=z.}
\tag{6.8}
\]

Thus the full payoff/cap pair is attained by a literal finite profile having
one passive padding row followed by a product root with at least two sure
quitters. At a positive global minimum, (6.7) holds with the strict checked
margin \(B_i-s_i\geq D_*>0\).

### Proof

Use the dates \(t_n\), roots \(q^n=q_{n,t_n}\), and fixed pair
\(P=\{p_0,p_1\}\) from Sections 4--5. We already proved

\[
 \operatorname{Law}(\rho(q^n))
 -\operatorname{Law}(\sigma_n)\longrightarrow0
\tag{6.9}
\]

in total variation, so their prescribed payoff vectors differ by \(o(1)\).

Fix player \(i\). Let \(H_{n,i}\) be the probability that every opponent of
\(i\) survives strictly before \(t_n\) under \(\sigma_n\). The joint live
mass at \(t_n\) is \(1-E_n\), so

\[
 H_{n,i}\geq1-E_n\longrightarrow1.
\tag{6.10}
\]

Conditional on this opponent survival, their actions at \(t_n\) are exactly
the product root \(q^n_{-i}\). After deleting \(i\), the opponent set still
contains at least one member of \(P\). By (4.5),

\[
 h_{n,i}:=
 \prod_{j\ne i}(1-q^n_j)\longrightarrow0.
\tag{6.11}
\]

Compare the opponents in \(\sigma_n\) with opponents who all Continue before
\(t_n\), play \(q^n_{-i}\) there, and Never thereafter. Under **every**
behavioral replacement by \(i\), the two induced terminal outcomes can
differ only if

1. some original opponent stops before \(t_n\), of probability at most
   \(1-H_{n,i}\); or
2. every opponent Continues at \(t_n\), of probability \(h_{n,i}\).

If neither event occurs, the same nonempty opponent coalition stops at
\(t_n\), so player \(i\)'s own action and all later behavior are immaterial
to the comparison. If rewards are bounded in absolute value by \(R\), every
replacement payoff differs by at most

\[
 2R(1-H_{n,i}+h_{n,i})\longrightarrow0.
\tag{6.12}
\]

Taking suprema over all replacements preserves this bound. The cap of the
reference opponents is

\[
 \begin{cases}
  B_i^{\rho(q^n)},&t_n=0,\\
  B_i^{\widehat\rho(q^n)},&t_n>0.
 \end{cases}
\tag{6.13}
\]

Indeed, when \(t_n>0\), Quitting at any pre-root date gives \(s_i\), while
waiting reaches exactly the choices (6.2)--(6.3).

Pass to a further subsequence on which either \(t_n=0\) always or \(t_n>0\)
always. In the second case, (6.12) and continuity give directly

\[
 B_i=B_i^{\widehat\rho(q^*)}.
\]

In the first case they first give

\[
 B_i=B_i^{\rho(q^*)}.
\]

Hypothesis (6.7) shows that adjoining the extra option \(s_i\) in (6.5)
does not change this maximum. Hence in both cases

\[
 B_i=B_i^{\widehat\rho(q^*)}.
\tag{6.14}
\]

This holds for every player. The padded and unpadded profiles have the same
prescribed payoff, and (6.9) identifies its limit with \(U\). This proves
(6.8). QED.

The proof identifies why ordinary law convergence usually loses caps and why
it does not here. The reached root contains two almost sure quitters. After
one player's entire strategy is replaced, at least one of those clocks
remains among the opponents and terminates the comparison. The only calendar
effect is the singleton option, which the padding row records exactly.

The comparison is deliberately **one deviator at a time**.  It proves the
unrestricted cap coordinates and also the counterfactual law obtained by
making one fixed player Never.  It does not assert preservation of a joint
multi-player intervention kernel: compressing several pre-root stopping
clocks to one padding date can change their relative stopping order.

The cap hypothesis (6.7) is necessary for this padded conclusion.  For
example, let a root be the pure pair \(\{0,1\}\), take

\[
 r_0(\{0\})=10,
 \qquad
 r_0(\{0,1\})=r_0(\{1\})=0,
\]

and complete the other rewards arbitrarily within the same bound.  At date
zero followed by Never, player \(0\)'s cap is zero: Quit leaves the pair and
Continue leaves player \(1\) quitting.  One passive row before the pair gives
player \(0\) the new option to Quit alone for payoff \(10\).  Thus law
convergence alone cannot justify padding; (6.7) is exactly what makes it
neutral at a positive minimum.

## 7. Application to a positive minimum source

Let \((z_*,\mu)\) be a joint-carrier lift of a positive ordinary global
minimum.  The law \(\mu\) is, by definition, a limit of actual behavioral
outcome laws.  Therefore exactly one of the following source-law situations
holds:

1. \(\mu(\infty)>0\);
2. \(\mu(\{i\})>0\) for some player \(i\); or
3. the entire joint point is attained by the padded product profile of
   Theorem 6.1, whose absorbing root has a sure-quitter base of cardinality at
   least two.

The alternatives are intended as an exhaustive dispatch, not as disjoint
tags: if Never or singleton mass is positive, the law might also have other
structure.

The same positive minimum already satisfies

\[
 U_i-s_i\geq D_*-d_i\geq0,
\]

and every fixed-support sparse conic certificate can be chosen by reweighting
positive \(\mu\)-atoms.  Theorem 5.1 shows exactly when this source law itself,
rather than a reweighting, is forced into a stationary product geometry.

In the third arm, the padded product semantic pair is the original global
minimum, not an unrelated same-law replacement.  This supplies product
realization, the persistent base, and full cap transport.  It does not retain
the original realizing chronology: the conclusion is equality of the complete
semantic pair and law with one newly constructed finite profile, not literal
identity of source profiles or dates.

It still need not be an equilibrium.  At a sure pair, each player's cap is a
finite current-root endpoint maximum, but its prescribed action may fail that
comparison.  A pure-pair example can have a member who strictly profits by
leaving.  The remaining task is therefore finite strategic consumption of an
**actual minimum product root**, not reconstruction of its law or cap.

## 8. Why the sparse certificate alone stalls

At every positive ordinary global minimum and for every
\(J\subseteq I\), \(|J|\geq2\),

\[
 \sum_{i\in J}(U_i-s_i)
 \geq |J|D_*-\sum_{i\in J}d_i
 \geq(|J|-1)D_*>0.
\tag{8.1}
\]

Hence the literal source law \(\mu\), projected to \(J\), already has a
nonzero coordinatewise-nonnegative surplus.  Conic Caratheodory inside
\(\operatorname{supp}\mu\) automatically gives a \(J\)-projected law on at
most \(|J|\) positive source atoms.

Therefore the sparse-law arm is not an additional restriction inside the
positive-minimum residual.  It is an exact dual description of why the
costate chamber cannot occur there.  Any consumer must use more than the
sparse moment:

- the literal source weights rather than arbitrary conic reweights;
- the race-law/product structure proved in Theorem 5.1;
- counterfactual cap or deleted-law data; or
- chronological placement of the selected atoms.

Theorems 5.1 and 6.1 add the genuine behavioral restriction: in the
zero-Never, zero-singleton subcase, the literal law and the complete semantic
pair are realized by one persistent-base product profile.  The surviving gap
is strategic consumption of that attained positive-minimum profile.

## 9. Exact boundary tests

### Pure pair

A pure pair law satisfies the theorem with both pair members sure.  Arbitrary
rewards can still make either member profit by leaving the pair, so product
realization alone does not imply Nash.

### Four disjointly routed pairs

The sharp sparse law has zero Never and singleton mass but no common pair.
The theorem excludes even approximation by ordinary behavioral laws.  A
public lottery would realize it, confirming that the obstruction is ordinary
independent behavioral randomization rather than reward geometry.

### Small root diffusion

If all hazards tend to zero, then (3.4) gives

\[
 \frac{b(q)}{a(q)}\longrightarrow1.
\]

Thus diffuse absorption is asymptotically singleton, not a way to approximate
a zero-singleton correlated collision law.  This is the local mechanism
behind the closure theorem.

## 10. Next conjecture-facing question

There is one direct full-debt consequence before invoking the general
persistent-base machinery.  Let

\[
 K=\{i:q_i^*=1\}
\]

be the maximal sure-quitter core of the attained root.  For every player
\(i\), at least one member of \(K\) remains among its opponents.  Hence the
opponent-all-Continue probability at the absorbing root is zero, and

\[
 U_i=q_i^*Q_i+(1-q_i^*)C_i.
\tag{10.1}
\]

At a positive minimum the strict singleton margin gives

\[
 B_i-s_i\geq D_*>0.
\]

Together with (6.5), this implies

\[
 B_i=\max\{Q_i,C_i\};
\tag{10.2}
\]

the singleton option is never cap-attaining.  Thus every debt coordinate is
exactly the binary one-root Nash regret of \(q^*\).

In particular, if the attained minimum has full positive debt and \(p\in K\),
then \(q_p^*=1\), so \(U_p=Q_p\), and (10.1)--(10.2) give

\[
 C_p-Q_p=d_p(z_*)>0.
\tag{10.3}
\]

There is a stronger renewable version than deleting \(p\) completely.  For
\(0<\theta<1\), let \(q^{p,\theta}\) agree with \(q^*\) except that

\[
 q^{p,\theta}_p=1-\theta,
\]

and let \(z^{p,\theta}\) be the semantic pair of its literal padded product
profile.  This changes only player \(p\)'s behavior at the same absorbing
root.  Its exact prescribed-payoff gain is

\[
 U_p(z^{p,\theta})-U_p(z_*)
 =\theta(C_p-Q_p)
 =\theta d_p(z_*)>0.
\tag{10.4}
\]

The opponents of \(p\) are unchanged, so its complete unrestricted cap is
unchanged and

\[
 d_p(z^{p,\theta})=(1-\theta)d_p(z_*)>0.
\tag{10.5}
\]

Every other debt coordinate is a maximum of finitely many continuous root
payoff functions minus a continuous prescribed payoff.  Since all four debts
are positive at \(z_*\), there is \(\bar\theta>0\) such that

\[
 0<\theta\leq\bar\theta
 \quad\Longrightarrow\quad
 d_i(z^{p,\theta})>0
 \quad(i\in I).
\tag{10.6}
\]

Along this one-coordinate segment, every \(Q_i\), \(C_i\), and prescribed
payoff is affine in \(\theta\), while every cap is the maximum of those affine
functions and the constant singleton option.  Hence

\[
 \theta\longmapsto D(z^{p,\theta})
\tag{10.6a}
\]

is convex.  Since its value at \(0\) is the global minimum \(D_*\), it is
nondecreasing on \([0,1]\).

Fix any one such \(\theta\).  The target is actual, so global minimality gives
\(D(z^{p,\theta})\geq D_*\).  Therefore exactly one of the following holds:

\[
 \boxed{D(z^{p,\theta})>D_*}
\tag{10.7}
\]

In this case convex monotonicity also gives \(D(z^{p,1})>D_*\).  Thus the
pure member-leaving endpoint itself is off minimum and carries the full gain
\(d_p(z_*)\); or

\[
 \boxed{D(z^{p,\theta})=D_*}
\tag{10.8}
\]

and the target is another attained full-debt global minimum.  In the equality
arm its maximal sure-quitter core is exactly

\[
 K\setminus\{p\}.
\tag{10.9}
\]

No source is reselected: the child profile is obtained by one literal
unilateral change from the parent profile, at the same displayed root, and
(10.4) is the backward paid edge.

If \(|K|\geq3\), the equality child still has at least two sure quitters.
Equations (10.1)--(10.6), including the singleton-cap margin, apply again at
that child because it is itself a positive global minimum.  Hence the
construction iterates with the natural-valued rank \(|K|\), which decreases
strictly on every minimum child.

When \(|K|=2\), write \(K=\{p,k\}\).  Maximality of \(K\) gives
\(q_j^*<1\) for every \(j\notin K\), and the softened target has the literal
singleton atom

\[
 \Pr(Q=\{k\})
 =\theta\prod_{j\notin K}(1-q_j^*)>0.
\tag{10.10}
\]

Thus a minimum child at rank two enters the established positive-singleton
minimum-law/clock-compression route on this same actual profile and marked
root.  Here the literal one-sure-quitter form permits a sharper immediate
handoff.

At that child, \(k\) still has positive debt and its prescribed payoff is its
Quit endpoint \(Q_k\).  The singleton moat again excludes \(s_k\) from the
cap maximum.  Hence

\[
 B_k=C_k>Q_k=U_k.
\tag{10.11}
\]

The value \(C_k\) is attained by one explicit complete response: Continue at
the product root; if some opponent Quits, take the resulting reward; if every
opponent Continues, Quit alone at the next date when \(s_k>0\), and otherwise
play Never.  Replacing only \(k\)'s strategy by this response gains exactly
\(d_k\), preserves \(k\)'s unrestricted cap, and kills \(k\)'s debt.  The
response includes the full all-opponents-Continue branch; it is not a
stationary-only endpoint calculation.

The response target is actual.  It is therefore either strictly off minimum,
or it is an attained global minimum with a zero debt coordinate.  In the
latter case it feeds the established global-minimum reset-rigid dispatch
(using the same target law: every globally minimizing Fin4 hard-residual law
has a positive finite atom); it cannot remain in the full-debt chamber.

In Fin4 there are at most three consecutive minimum-child transitions before
this final response.  The product-law full-debt arm therefore has a genuine
finite-rank transition:

\[
 \boxed{
 \text{off-minimum paid unilateral target}
 \quad\lor\quad
 \text{attained zero-debt global minimum}.}
\tag{10.12}
\]

The first alternative remains an open consumer, and the second is precisely
an input to the still-open reset-rigid chamber; (10.12) does not by itself
prove a uniform payoff.  Its content is that no
zero-singleton full-debt product-base state can recur indefinitely while
remaining on the minimum fibre.

The broader finite-base question is now:

In the third arm of Section 7, can the attained minimum product profile be
fed to the existing persistent-base finite game to give
one of:

1. the checked persistent-base stationary consumer;
2. a paid member-leaving edge with a source-faithful cap port;
3. a fixed-rank deletion of one base member; or
4. a contradiction to full positive debt?

A theorem using only the product law is false by the pure-pair regression,
but Theorem 6.1 now supplies the missing counterfactual response data.  The
next check is whether the existing persistent-base induced-Nash/reset
dispatch consumes an attained **global minimum**, rather than merely an
arbitrary persistent-base root.

## Sources inspected

- CODEX_WEIGHT_GLOBAL__NONNEGATIVE_WEIGHT_SOCIAL_CHAMBER.md;
- CODEX_SOCIAL_DUAL__SPARSE_PARETO_LAW_AND_PRODUCT_BARRIER.md;
- CODEX_SOCIAL_PAIR__SOURCE_SUPPORTED_TWO_OUTCOME_CERTIFICATES.md;
- terminalSemanticLawCarrier_rewardMoment and
  exists_terminalSemanticLawCarrier_lift in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean;
- quittingTerminalOutcomeMass and quittingTerminalRewardMoment in
  UniformEquilibrium/Quitting/Root/TerminalSemanticMoment.lean; and
- exists_positive_finiteLawAtom_of_finFourHardResidual_minimum in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean;
- the global full-debt/reset-rigid classification in
  UniformEquilibrium/Diagnostics/Quitting/FinFourLawTightCapNashStrictMinimum.lean; and
- the persistent-base consumer family under
  UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/.
