# A genuine card-three maximal exact-cap ray at zero minimum

Author: `CODEX_HOPF`

## Status

This note gives an ordinary-mathematics regression, not a solution of the
Fin4 conjecture.  A fixed rational four-player quitting table and a literal
finite-clock source admit a genuinely infinite maximum-absorption exact-cap
prefix ray with:

- summable positive absorption;
- a three-player binding set;
- full current support on that binding set; and
- one uniformly nonbinding player who strictly Continues at every selected
  root.

The same table has all-Never as an exact terminal Nash profile, so its global
minimum debt is zero.  Consequently this construction does not satisfy the
positive-minimum hard residual.  Its purpose is sharper: equilibrium index,
degree, root maximality, and the card-three binding geometry alone cannot
eliminate the remaining strict-ray arm.  Any valid exclusion must use the
positive-minimum actual-source passport or another hypothesis absent here.

The finite root-game enumeration is exact.  The infinite-ray realization is
proved by an elementary invariant-neighbourhood argument.  The note is ready
for independent mathematical review; nothing in it has been checked in Lean.

A second, fixed-real completion of the spectator coordinate turns the same
orbit into a **full-binding, partial-current-support** maximal ray.  Thus the
remaining full-binding partial-support regime also exists without positive-
minimum provenance.  This variant is given in Section 7.

## Question

Can a three-player binding face in a shrinking maximal exact-cap ray be
excluded by the equilibrium-component index, or by treating its unique
omitted player as a removable spectator?

The answer to both source-free versions is no.

## Sources inspected

The bounded source set was:

- `QuittingMaximalCapSemanticPrefixRayStall` in
  `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`;
- the exact maximal-root orbit and cap-prefix identities in
  `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`;
- `normalizedSoloMatrix_eq_soloReward_sub` in
  `UniformEquilibrium/Quitting/Classification/PreemptionGateDictionary.lean`;
- `FinFourQuantitativeFullSupportHardResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`;
- the hard-principal size and finite dispatch in
  `FullSupportHardPrincipalSize.lean` and
  `FullSupportHardPrincipalDispatch.lean`; and
- `notes/CODEX_BOREL__STRICT_RAY_TAIL_NORMALIZATION.md` and the reviewed
  export `exports/STRICT_RAY_TAIL_NORMALIZED_CAP_FLOW.md`.

## 1. The active root game

Let the players be `0,1,2,3` and put

\[
 A=\{0,1,2\}.
\]

All singleton rewards are zero.  On the active coordinates use the two
zero-diagonal matrices

\[
 J=
 \begin{pmatrix}
 0&1&-2\\
 1&0&-2\\
 2/5&2/5&0
 \end{pmatrix},
 \qquad M=-cJ,
 \quad c=\frac12.
 \tag{1}
\]

First define every active player's reward coordinate on coalitions which do
not contain player `3`.  For every nonempty `S subset A` and `i in A`, put

\[
 r_i(S)=
 \sum_{j\in(S\cap A)\setminus\{i\}}M_{ij}
 +\mathbf 1_{\{i\in S\}}
  \sum_{j\in(S\cap A)\setminus\{i\}}J_{ij}.
 \tag{1a}
\]

In particular all active singleton rewards are zero.  The passive reward on
a nonempty coalition of active opponents has expectation

\[
 \sum_{j\ne i}M_{ij}x_j,
\]

while the reward increment from adding `i` has expectation

\[
 \sum_{j\ne i}J_{ij}x_j.
\]

Equation (1a) also shows directly that simultaneous active coalitions create
no unrecorded interaction term.  Rewards on coalitions containing player `3`
will be completed explicitly in Section 3.  They never enter the active root
dynamics because player `3` will be a strict Continuer.

If the continuation cap excess above the zero singleton vector is

\[
 (\delta_0,\delta_1,\delta_2),
\]

the exact Quit-minus-Continue difference at a product root `x` is

\[
 G_i(x)
 =\sum_{j\ne i}J_{ij}x_j
  -\delta_i\prod_{j\ne i}(1-x_j).
 \tag{2}
\]

The factor multiplying `delta_i` is essential.  It is the probability that
all opponents Continue; replacing it by one would only be a first-order
calculation.

For the symmetric cap vector

\[
 (\delta_0,\delta_1,\delta_2)=(a,a,b),
 \tag{3}
\]

write `z=x_2`.  If players `0` and `1` mix, their common hazard is

\[
 t(a,z)=
 \frac{a(1-z)+2z}{1+a(1-z)}.
 \tag{4}
\]

Their two-action subgame has exactly the usual three coordination branches:
both Continue, both Quit, or both mix at `t(a,z)`.  Player `2`'s exact
endpoint difference on the mixed branch is

\[
 H_{a,b}(z)
 =-b\bigl(1-t(a,z)\bigr)^2+\frac45t(a,z).
 \tag{5}
\]

For `a,b>0` sufficiently small with `b/a` in a fixed neighbourhood of one:

1. `H_(a,b)(0)<0`;
2. `H_(a,b)` is strictly increasing;
3. it has one zero `z(a,b)>0`, of order `a`; and
4. the both-Quit branch cannot be completed to a root, because player `2`
   then strictly Quits while `z=1` makes players `0` and `1` strictly
   Continue.

It follows by direct support enumeration that the active root game has
exactly three Nash roots:

\[
 (0,0,0),
 \qquad
 \left(\frac{a}{1+a},\frac{a}{1+a},0\right),
 \qquad
 (t(a,z(a,b)),t(a,z(a,b)),z(a,b)).
 \tag{6}
\]

The last root strictly dominates the pair root coordinatewise and is
therefore the unique maximum-absorption root.

At the limiting cap `a=b=0`, the complete Nash set is instead

\[
 \{(0,0,z):0\le z\le1\}.
 \tag{7}
\]

This is the topological mechanism missed by a naive degree argument.  For
positive `a,b`, all-Continue has index `+1`, the pair mixed root has index
`-1`, and the full active mixed root has index `+1`; the two new roots have
total index zero.  At the limit they merge into the inessential segment (7).
The global index remains `+1` throughout.

For comparison, if one suppresses the exact survival factor in (2), the
fully mixed root at `a=b=delta` is explicitly

\[
 \left(\frac54\delta,\frac54\delta,\frac18\delta\right),
\]

and the same three-root/index picture is already visible.  Equations
(2)--(7) show that it is not an artifact of that linearization.

## 2. Make player 3 a strict spectator without deleting it

For the omitted receiver `3`, set

\[
 r_3(T)=|T\cap A|\quad(3\notin T),
\]

put `r_3({3})=0`, and for nonempty `T subset A` set

\[
 r_3(T\cup\{3\})=|T|-1.
 \tag{8}
\]

Thus adding player `3` to a nonempty active coalition costs it exactly one,
while adding it to the empty coalition gives its zero singleton reward.  At
every positive continuation cap, Continue strictly dominates Quit for player
`3`, at every product distribution of the active opponents.  Hence player
`3` has zero hazard in every Nash root relevant below.  Its cap is nevertheless
positive because it passively values active absorption.

This also shows why the spectator cannot simply be deleted from the proof.
Its root action is fixed, but its continuation cap and passive payoff are real
semantic coordinates.  They can be changed arbitrarily without altering the
three active endpoint equations (2).

## 3. A literal pure-pair source with a paid forced-pair history

Choose a positive rational `d` which will be taken sufficiently small (for
example, `d=1/100` satisfies all the estimates below), and
put

\[
 C=\{0,3\}.
\]

Complete the active reward coordinates on the following coalitions containing
player `3` by

\[
\begin{array}{c|cc}
 &\text{Continue row}&\text{joined row}\\ \hline
i=0&r_0(\{3\})=0&r_0(\{0,3\})=d\\
i=1&r_1(C)=0&r_1(C\cup\{1\})=d\\
i=2&r_2(C)=0&r_2(C\cup\{2\})=d.
\end{array}
\tag{9}
\]

Every other still-unspecified active coordinate on a coalition containing
player `3` may be set to zero.  These values do not affect roots at which
player `3` Continues.

Let `tau_C` be the literal profile which plays the pure coalition `C` at date
zero and all-Never after the counterfactual all-Continue history.  Since
`|C|=2`, one sure quitter remains after every unilateral deviation, so the
complete unrestricted cap is read directly from the two endpoint rewards.
Equations (8)--(9) give

\[
 U(\tau_C)=(d,0,0,0),
 \qquad
 B(\tau_C)=(d,d,d,1),
 \tag{10}
\]

and therefore

\[
 d(\tau_C)=(0,d,d,1).
 \tag{10a}
\]

This source already carries the local forced-pair provenance used by the
Fin4 atlas.  Let `tau_{\{3\}}` be the otherwise identical pure-singleton
profile.  Forcing player `0` to Quit changes its date-zero payoff from
`r_0({3})=0` to `r_0(C)=d`; at the resulting pair its marked root defect is
exactly zero.  On that same pair, player `1` has the literal source-matched
joining gain

\[
 r_1(C\cup\{1\})-r_1(C)=d>0.
 \tag{10b}
\]

Player `2` supplies another gain of size `d`.  The marked pair has
unconditional mass one, all profiles have the identical post-date all-Never
tail, and every statement is against unrestricted behavioral deviations
because the pair screens the tail.

Thus the maximal ray below begins from a literal pure pair, not merely from an
abstract cap vector or an independently selected mixed source.

## 4. The exact maximum-prefix recurrence

Prefix the source recursively by its maximum-absorption exact cap root.  If
the active cap at time `k` is `(a_k,a_k,b_k)`, let

\[
 q_k=(t_k,t_k,z_k)
\]

be the third root in (6).  Because `M=-cJ` and `q_k` satisfies (2), the exact
Continue endpoint is

\[
 \boxed{
 \begin{aligned}
 a_{k+1}
   &=(1-c)a_k(1-t_k)(1-z_k),\\
 b_{k+1}
   &=(1-c)b_k(1-t_k)^2.
 \end{aligned}}
 \tag{11}
\]

There is no first-order error in (11).  The passive singleton terms contribute
`-c J q_k`; exact endpoint indifference identifies `J q_k` with the cap
excess times opponent survival, leaving the factor `1-c`.

Take the initial rational `d` sufficiently small, so that
`a_0=b_0=d`.  The following explicit estimate
gives a noncircular invariant cone:

\[
0<a_k,b_k<\varepsilon,
 \qquad
 9/10<b_k/a_k\le1.
 \tag{12}
\]

Suppose inductively that `9/10 < b_k/a_k <= 1` and `a_k<1/8`.  Then
`H_(a_k,b_k)(0)<0`, so the full root exists.  Its equality (5) gives

\[
 \frac45t_k=b_k(1-t_k)^2,
 \qquad
 0<z_k<t_k\le\frac54b_k.
 \tag{12a}
\]

The strict inequality `z_k<t_k` also follows directly from (4):

\[
 t(a,z)-z=
 \frac{a(1-z)^2+z}{1+a(1-z)}>0.
 \tag{12b}
\]

Both coordinates in (11) contract by at most `1-c=1/2`.  For
`r_k=b_k/a_k`,

\[
 \frac{r_{k+1}}{r_k}=\frac{1-t_k}{1-z_k}<1.
 \tag{12c}
\]

After decreasing `d`, (12a) makes `t_k,z_k<1/4`.  Put

\[
 u_k=\frac{t_k-z_k}{1-z_k}.
\]

Then `0<=u_k<=5b_k/3`, and (12c) is `r_(k+1)=r_k(1-u_k)`.
Moreover

\[
 b_{k+1}\le\frac12b_k,
 \qquad
 \sum_k b_k\le2b_0,
 \qquad
 \sum_k(a_k+b_k)<\infty.
\]

Starting from `r_0=1`, use `log(1-u)>=-2u` for `0<=u<=1/2`:

\[
 r_k
 \ge \exp\!\left(-2\sum_hu_h\right)
 \ge \exp\!\left(-\frac{20}{3}b_0\right).
 \tag{12d}
\]

Choose the rational `d` so small that the last expression is greater than
`9/10` and `a_0<1/8`.  Equations (12a)--(12d) then close the induction and
prove (12), without assuming in advance that the quotient remains near one.
In
particular, every `q_k` is the unique maximum-absorption root from (6), every
`q_k` has all three active hazards positive, and

\[
 \sum_k\operatorname{Abs}(q_k)<\infty,
 \qquad q_k\longrightarrow\mathbf C.
 \tag{13}
\]

Player `3` remains a strict Continuer.  Against active coalition `T`, its
Continue-minus-Quit difference is one when `T` is nonempty and is its positive
continuation cap when `T` is empty.  Thus no root with positive player-`3`
hazard competes with the active roots in (6).  Its successor cap is

\[
 b_{k+1,3}
 =\sum_{i\in A}q_{k,i}
  +\left(\prod_{i\in A}(1-q_{k,i})\right)b_{k,3}>0.
 \tag{13a}
\]

The cap limit has

\[
 \bar b_i=r_i(\{i\})=0\quad(i\in A),
 \qquad
 \bar b_3>r_3(\{3\})=0.
 \tag{14}
\]

The second assertion follows either from (13a), or just because (13) leaves a
positive infinite product of root survival probabilities while player `3`
starts with cap one.  Hence the limiting
binding set is exactly `A`, of cardinality three.

This proves the announced genuine infinite maximal-ray regression.

## 5. The table still has an exact equilibrium

Every singleton reward is zero.  At all-Never, prescribed payoff and every
behavioral best-response cap are zero.  Hence all-Never is an exact terminal
Nash profile and

\[
 D_*=0.
 \tag{15}
\]

The ray is therefore compatible with uniform equilibrium.  It cannot refute
the conjecture and does not instantiate the normalized strict-inert passport,
whose retained positive global minimum is essential.  There is a second
deliberate failure of that passport: at the limiting active cap the Nash set
is the whole inessential segment (7), rather than unique all-Continue.  The
regression therefore targets the nonconstant card-three ray geometry, not the
already-isolated unique-root endpoint.

## 6. Consequences for the remaining proof

The construction proves four precise no-gos.

1. **Equilibrium index does not exclude card three.**  The compensating
   `-1,+1` roots coalesce into an inessential boundary component while the
   maximum-absorption root shrinks.
2. **Maximality does not force full Fin4 support.**  The unique maximal root
   has full support on `A` and zero hazard on the strict fourth coordinate at
   every time.
3. **A strict omitted coordinate is not deletion data.**  The omitted
   player's passive cap can remain positive and semantically relevant even
   though it never Quits in the root chronology.
4. **The usual local forced-pair passport is not enough without its minimum
   source.**  The same literal singleton-to-pair gain, zero pair-owner defect,
   positive distinct payer, full marked mass, and common post-date tail all
   occur in this zero-minimum table.

Accordingly, a successful card-three consumer must use at least one of the
features absent from this example:

- positive global minimum provenance;
- a consequence of attaching the displayed forced-pair history to such a
  positive minimum (the local history itself is present here);
- the full normalized passport beyond its local marked-mass/gain fields; or
- the hard nonprojective principal together with a proved source alignment.

The most focused surviving question is not whether the three-face ray exists,
but whether the positive-minimum forced-pair passport can coexist with this
`(+1,-1,+1)` local root geometry.  That is the correct place to seek either a
contradiction or an executable return.

## 7. A full-binding partial-current-support variant

There is a second completion of player `3`'s reward row which keeps the whole
active orbit unchanged but makes the limiting binding set all four players.
This addresses the full-binding partial-current-support regime separately
from the card-three table above.

Fix the active orbit from Sections 1 and 4, and write

\[
 s_k=(1-t_k)^2(1-z_k),\qquad
 P_0=1,\qquad P_{k+1}=P_ks_k.
\]

By (13), `P_k` decreases to a strictly positive limit and `sum_k t_k` is
finite.  Hence

\[
 R:=\sum_{k\ge0}\frac{t_k}{P_{k+1}}
 \tag{16}
\]

is a finite positive real number.  Replace only player `3`'s reward
coordinate.  On coalitions `T subset A`, put

\[
 r_3(T)=\sum_{i\in T}m_i,
 \qquad
 (m_0,m_1,m_2)=(R,-R-1,0),
 \tag{17}
\]

and put `r_3({3})=0`.  For every nonempty `T subset A`, set

\[
 r_3(T\cup\{3\})=r_3(T)-1.
 \tag{18}
\]

In particular, at the same literal pure-pair source `C={0,3}`, player `3`'s
Continue endpoint is

\[
 r_3(\{0\})=R,
\]

whereas its prescribed Quit endpoint is `R-1`.  Thus the source cap in the
fourth coordinate is `b_(0,3)=R>0`.  The active cap is still `(d,d,d)`, since
no active reward coordinate has changed.

At any product distribution of the active players, (18) makes player `3`'s
Continue-minus-Quit difference exactly

\[
 \Pr(T\ne\varnothing)
 +\Pr(T=\varnothing)b_{k,3}>0.
 \tag{19}
\]

Consequently player `3` strictly Continues in every Nash root against the
current cap, not merely in the selected root.  The complete root enumeration
and the global maximum-absorption conclusion in (6) are therefore unchanged.

Its successor cap is the Continue endpoint

\[
 b_{k+1,3}
 =t_km_0+t_km_1+z_km_2+s_kb_{k,3}
 =s_kb_{k,3}-t_k.
 \tag{20}
\]

The choice (16)--(17) solves this recurrence explicitly:

\[
 \boxed{
 \frac{b_{k,3}}{P_k}
 =\sum_{h\ge k}\frac{t_h}{P_{h+1}}.}
 \tag{21}
\]

Indeed, (21) holds at `k=0` by definition of `R`, and subtracting its two
successive instances is exactly (20).  It follows that

\[
 b_{k,3}>0\quad\text{for every finite }k,
 \qquad b_{k,3}\longrightarrow0=r_3(\{3\}).
 \tag{22}
\]

The selected maximum roots still have support exactly `A={0,1,2}`, but now
all four limiting cap coordinates equal their singleton rewards.  Thus

\[
 \boxed{
 \text{limiting binding set}=\operatorname{Fin}4,
 \qquad
 \text{current-root support}=\{0,1,2\}.}
 \tag{23}
\]

This is also a ballistic, rather than diffuse, example in the terminology of
the tail-normalized theorem.  The decreasing ratios `b_k/a_k` converge to a
limit `r_infty in [9/10,1]`.  Equations (5) and (4) give

\[
 \frac{t_k}{a_k}\longrightarrow\frac54r_\infty,
 \qquad
 \frac{z_k}{a_k}\longrightarrow
 \frac{(5/4)r_\infty-1}{2}>0.
\]

Since `a_(k+1)/a_k -> 1/2`, the total marginal hazard
`epsilon_k=2t_k+z_k` satisfies

\[
 \frac{\varepsilon_{k+1}}{\varepsilon_k}\longrightarrow\frac12.
\]

Therefore, for `T_k=sum_(h>=k) epsilon_h`, the standard ratio lemma yields

\[
 \boxed{\rho_k=\frac{\varepsilon_k}{T_k}\longrightarrow\frac12.}
 \tag{24}
\]

This full-binding example remains a zero-minimum regression: every singleton
reward is zero, so all-Never is exact.  It does not enter the positive-minimum
strict-inert source.  It does prove that full binding plus partial current
support, ballistic scaling, maximum absorption, exact cap prefixing, and
summable nonzero motion are mutually compatible.  Any exclusion of that
remaining arm must again use the retained positive-minimum/source passport
rather than root geometry alone.
