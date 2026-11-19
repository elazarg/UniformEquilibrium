# Twenty-one singleton sign classes for four-player quitting games

Write $G_{ij}=r_i(\{j\})-r_i(\{i\})$, so $G_{ii}=0$. The following 21 sign patterns, up to a simultaneous permutation of owners and recipients, suffice for the arbitrary four-player uniform-equilibrium conjecture. Every strict sign pattern outside the list admits a uniform-equilibrium payoff for **every** completion of the higher rewards and all own singleton levels. Any counterexample on a boundary with zero singleton comparisons would persist on nearby strict patterns. Each listed pattern has a four-by-four integer matrix with entries of magnitude at most four that satisfies the degree and inverse-column tests and admits no continuous singleton path. Whether any higher-reward completion of those matrices lacks a uniform equilibrium remains open.

Encode row $i$ by the sum of $2^j$ over its positive columns $j$, with negative entries at the other off-diagonal positions. Use the lexicographically smallest four-row tuple in each relabeling orbit.

```text
(2,1,1,2) (2,1,1,4) (2,1,1,6) (2,1,8,4) (2,1,8,5) (2,1,9,6)
(2,4,1,1) (2,4,1,3) (2,4,3,1) (2,4,3,4) (2,4,3,5) (2,4,9,2)
(2,4,9,4) (2,4,9,5) (2,4,9,6) (2,5,3,4) (2,5,8,5) (2,5,8,6)
(2,5,9,2) (2,5,9,6) (2,12,9,6)
```

## Degree at a positive inverse column

A counterexample has $G$ of class $R_0$ and degree one, $\det G>0$ and a strictly positive column of $G^{-1}$. Each row has a positive entry, since the complementarity problem with positive target has a solution. Each row has a weak blocker by the full normal-core theorem. Each column has a negative entry by $R_0$, and some reciprocal pair is negative in both directions. A directed four-cycle of opposite-sign adjacent pairs with a mutually negative chord and at least one positive entry on the opposite chord already has a uniform equilibrium. We initially discard just these sign exits. A positive gap persists under small reward perturbations, so when analyzing a strict sign pattern we can also assume all principal submatrices of size at least two are nonsingular. This yields 600 labeled patterns in 31 orbits. [Strict inverse-column theorem](FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md) [Normal-core and prescribed-clock results](ZERO_SINGLETON_COLUMN_EQUIVALENCE.md) [Reciprocal-negative necessity](NO_MUTUALLY_NEGATIVE_SINGLETON_PAIR_UNIFORM_EQUILIBRIUM.md) [Four-cycle theorem](NEGATIVE_CHORD_HAMILTONIAN_UNIFORM_EQUILIBRIUM.md)

Choose $h$ with $x=G^{-1}e_h>0$. Consider $u\ge0$, $Gu\ge e_h$, $u\cdot(Gu-e_h)=0$. The full solution $x$ has index $+1$. Empty support is impossible. Every singleton column has a negative entry, excluding singletons. An invertible active block omitting $h$ has zero active target and hence zero solution. A pair containing $h$ forces $u_h=0$ by its other row equation. The only remaining solutions use a triple $S=\{h,i,j\}$ omitting $o$, and must equal $G_{SS}^{-1}e_h$ there. Their outside slack satisfies
$$
 G_{oS}G_{SS}^{-1}e_h=-\frac{\det G}{\det G_{SS}}(G^{-1})_{oh}.
$$
Thus a triple contributes exactly when its determinant is negative and all three entries of the $h$ column of its adjugate are negative. The latter condition reads
$$
 \operatorname{sgn}G_{ij}=\operatorname{sgn}G_{ji}=-\operatorname{sgn}G_{ih}=-\operatorname{sgn}G_{jh}.
$$
All entries of this adjugate column are nonzero, being signed products of off-diagonal entries. All feasible candidates have strict inactive slack. The target is therefore regular and each such triple contributes index $-1$, the sign of its active principal determinant. Consequently degree one requires **positive** determinant at every triple satisfying the displayed sign condition. Conversely, for a matrix with the stated nonsingular principal submatrices, negative column witnesses and chosen positive inverse column of positive determinant, those triple tests suffice for degree one. The index formula uses the coordinatewise minimum map, whose Jacobian has the active block and identity rows on its strict inactive coordinates. [Complementarity index convention](UNIVERSAL_REDUCED_SINGLETON_DEGREE.md)

## Exact sign screening

Scale the columns of $G$ by $x$ to obtain $H\mathbf1=e_h$. Scale each row other than $h$ by a positive factor so its positive magnitudes sum to one, as do its negative magnitudes. All principal determinant signs remain unchanged. These scalings are only used to examine the singleton matrix. Each such balanced row belongs to the convex hull of its permitted differences $e_p-e_n$, where $p$ is a positive position and $n$ a negative position. With three off-diagonal entries there are two endpoints in each row. The three balanced rows lie in $\mathbf1^\perp$, so the full determinant depends on the $h$ row only through its sum. Replace that row by a single $e_p$ at a positive position, and call the determinant $D$. Its value on the whole product of row intervals interpolates the eight vertex values. Positive determinant and positive inverse column at $h$ are simultaneously realizable exactly when one vertex has $D>0$. For sufficiency perturb that vertex into the strictly signed interiors of the three rows and take a strictly signed $h$ row of sum one. The resulting $H$ has $H^{-1}e_h=\mathbf1$. Screening all eligible $h$ leaves 591 labeled patterns in 29 orbits.

For a triple from the preceding test write $a=|H_{ij}H_{jh}|$, $b=|H_{ji}H_{ih}|$. Positive triple determinant requires $H_{hi}a+H_{hj}b<0$, since both products before the absolute values are negative. If both $h$ entries are positive this is impossible. If they have opposite signs and $h$ has only one positive entry, that entry is larger than the magnitude of either negative entry because the row sum is one. The inequality therefore requires
$$
 E=-\operatorname{sgn}(H_{hi})a-\operatorname{sgn}(H_{hj})b>0.
$$
Compute $D+E$ on the same eight vertices. The two products retain fixed signs on the closed row intervals, so $D+E$ is affine separately in each balanced row. If its largest vertex value is nonpositive there can be no matrix with $D>0$ and $E>0$. These two elementary tests eliminate seven further orbits, leaving 459 labeled patterns in 22 orbits. The accompanying checker performs these finite integer comparisons without numerical root finding. [Exact sign checker](../experiments/FIN4_SINGLETON_SIGN_CLASSES.py)

Two arbitrary-completion exclusions were previously embedded in the proportional-additive paper. Its row masks $(8,4,2,6)$ and $(8,4,9,3)$ use a different canonical ordering. They are $(2,1,3,4)$ and $(2,5,8,3)$ in the convention here. The first is among the seven degree exclusions above, and the second is the triangle orbit below. The earlier argument for the second uses a passive-row inverse criterion. The counts in this paper describe the combined matrix and path screens; they are independent of which earlier proof first resolved an individual orbit. [Earlier direct singleton exclusions](ALL_PROPORTIONAL_ADDITIVE_FOUR_PLAYER_UNIFORM_EQUILIBRIUM.md)

## The last eliminated orbit

After relabeling the extra orbit has matrix
$$
G=\begin{pmatrix}0&-a&-b&c\\-d&0&e&-f\\g&-h&0&i\\j&k&-l&0\end{pmatrix}
$$
with all displayed magnitudes positive. Its adjugate diagonal entries at 1 and 3 are $-bij-cgl$ and $-aeg-bdh$, so neither can index a positive inverse column. At index 2 the triple with labels $0,2,3$ has determinant $-bij-cgl$ and its adjugate column at 2 is $(-cl,-cj,-bj)$. The degree test excludes that index. Therefore $x=G^{-1}e_0>0$. Its first cofactor gives $\Delta=eik-fhl>0$. Its remaining equations give $hx_1=gx_0+ix_3$, $lx_2=jx_0+kx_1$ and $cx_3=1+ax_1+bx_2$, hence
$$
 c>ai/h+bki/(hl).
$$
Use the cyclic singleton order $(1,3,2)$ with phase masses proportional to $(i/h,1,f/e)$, and multiply the next tour by $\rho=fhl/(eik)\in(0,1)$. Its three active zero conditions follow upon substitution in the cyclic tail equations. Each active row stays nonnegative at intervening phases by the directed signs. In row 0, the first phase removes a negative term, the second removes a positive term and the third removes a negative term. Just after the second phase the unnormalized remaining tail is $\rho(c-ai/h)-bf/e>0$. The starting value is also positive: the value after the third phase is greater than this minimum and equals $\rho$ times the starting value. All the tail inequalities hold. The singleton-path discretization now gives a uniform equilibrium for arbitrary higher rewards. The removed orbit has 24 labeled sign patterns, leaving 435 in 21 orbits. [Continuous-path test and game consumer](GENERIC_FOUR_PLAYER_SINGLETON_PATH_CLASSIFICATION.md)

For each surviving orbit the checker verifies a particular integer matrix by the exact inverse-column and degree-at-axis criteria above. Nonzero principal determinants in sizes two, three and four and a negative witness in each column imply $R_0$. The sign graphs have no directed four-cycle. For each directed triangle, the active zero conditions determine its relative masses and scale uniquely. The checker tests those values and the outsider's three phase inequalities in rational arithmetic. Hence each orbit has a calibration that passes the named matrix conditions and fails the full continuous singleton-path test. These calibrations place no restriction on unresolved higher-reward obligations.

These calibrations also give an explicit game requiring simultaneous quitting in each of the 21 classes. Give every owner singleton level one, use the indicated matrix for centered foreign singletons, and set every centered nonsingleton reward to zero. All four players quitting on date one is an exact equilibrium: a participant and a player waiting for the complementary triple both get one. All pair joining rewards in native units equal zero, so every row satisfies the protection condition of the continuous-path converse. Its failure at these matrices forces some $\varepsilon,c>0$, depending on the game, such that every profile of original terminal regret at most $\varepsilon$ has a date with unconditional probability at least $c$ of a simultaneous first exit. This calibrates the obstruction to using only solo calendars separately on each remaining sign class. [Single-date collision consequence](GENERIC_FOUR_PLAYER_SINGLETON_PATH_CLASSIFICATION.md)

## Games with tied singleton payoffs

**Four ties suffice.** If at least four of the twelve off-diagonal comparisons satisfy $r_i(\{j\})=r_i(\{i\})$, the original game has a uniform-equilibrium payoff for every choice of its higher-coalition rewards. Two such ties in one recipient row also suffice. More generally the following is the exact count for the preceding sign screen, including its boundaries.

| Number of off-diagonal ties | Labeled patterns left | Classes up to relabeling |
| --- | ---: | ---: |
| 0 | 435 | 21 |
| 1 | 1,104 | 46 |
| 2 | 900 | 39 |
| 3 | 240 | 10 |
| 4–12 | 0 | 0 |

For a ternary sign pattern to contain a counterexample, **every** strict refinement obtained by assigning signs to its zeros must belong to the 435. Indeed one can choose the perturbations independently, holding own and nonsingleton rewards fixed. A positive terminal gap persists under sufficiently small perturbations since every prescription and every response changes by at most the largest reward change. Start with the 435 strict patterns and replace a coordinate by zero whenever both opposite signs at that coordinate occur with identical remaining entries. By induction this produces precisely the faces with every strict refinement in the list. The checker enumerates these faces and their permutation orbits. At four ties the resulting set is empty, so it is empty in every higher codimension. If a row has two ties, it has a strict refinement with all three off-diagonal entries of one sign, already excluded by the row tests.

Every one of the 95 remaining boundary classes has an integer matrix $G$ with off-diagonal magnitudes at most three, positive determinant, a strictly positive inverse column, degree one, and no nonzero homogeneous complementary vector or continuous singleton path. In the ten three-tie classes magnitudes at most two suffice. To verify this on the faces themselves, choose one row $h$ with positive sum and all other rows balanced. Then $G^{-1}e_h=\mathbf1/\sum_jG_{hj}$ whenever $\det G>0$. For the homogeneous problem the checker excludes singleton supports by a negative outsider. A pair with both active entries zero admits a positive kernel on that pair precisely when a single positive ratio satisfies its two outsider inequalities. The checker eliminates those feasible ratios. A singular triple is accepted only if one of its rows precludes a positive active kernel. Invertibility rules out full support. For the degree, enumerate supports at the regular positive target $(19,97,877,2287)$. Cramer's rule gives the sign of each positive solution and its inactive slacks. A nonzero column-replacement determinant excludes a singular block from the target. Summing the signs of the feasible active determinants gives one.

Each surviving row has at most one off-diagonal zero. In a positive-length triangle its two internal terms must cancel in each active equation, so those two entries have opposite strict signs. The strict triangle calculation above then decides every candidate, even when its outsider has a zero. For a quadrilateral the checker tests for a cyclic order with the weak switch signs and at least one strict comparison at each switch. None occurs at these calibrations. The path theorem for arbitrary hollow matrices includes exactly these possibilities together with the homogeneous case. Thus all 95 examples meet the stated matrix tests on their actual faces; existence for their arbitrary higher-reward completions remains open. [All-matrix path theorem](ALL_FOUR_PLAYER_SINGLETON_PATHS_HAVE_A_FINITE_TEST.md) · [Exact enumeration and calibrations](../experiments/FIN4_SINGLETON_SIGN_CLASSES.py)

### A quantitative bound on original terminal regret

For a strict sign pattern $S$ outside the list, order each recipient's four singleton outcomes by requiring every negatively marked outcome to precede the own singleton and every positively marked outcome to follow it. Use the reflexive and transitive closure, leaving outcomes on the same side incomparable. Write this order as $a\preceq_i b$, put $x_{ia}=r_i(\{a\})$, and define
$$
 E_i(S)=\max_{a\preceq_i b}(x_{ia}-x_{ib})_+.
$$
Then the infimum of the maximum unrestricted terminal deviation gain in the original game is at most
$$
 \min_{S\text{ outside the list}}\ \max_i E_i(S).
$$
This is a finite bound using only the sixteen original singleton payoffs. For any listed choice of $S$ in the minimum, replace $x_{ib}$ by $\max_{a\preceq_i b}x_{ia}$. The resulting singleton values satisfy all weak comparisons for $S$, and hence give a uniform-equilibrium payoff by closure of the solved strict cone. Each reward correction in row $i$, including the zero correction on every higher coalition and on perpetual play, lies in $[0,E_i(S)]$. A deviation gain thus changes by at most $E_i(S)$ on the same profile. Taking arbitrarily accurate terminal equilibria proves the claimed bound. In fact $E_i(S)$ is the least possible width of the row corrections to reach this closed sign cone. If two outcomes originally violate $x_{ia}\le x_{ib}$, the correction at $b$ must exceed the correction at $a$ by at least $x_{ia}-x_{ib}$. The construction attains that lower bound simultaneously in all rows. Exact distance to the screened union supplies an upper bound on regret even within the surviving classes.

Equivalently $E_i(S)$ is the sum of the largest positive violation at a negatively marked entry and the largest negative magnitude at a positively marked entry, using zero if a side has no violation. Clipping just these violating foreign singletons to the original own level attains the same width with **all four own levels fixed**. A quick bound dispensing with the list is twice the fourth-smallest $|G_{ij}|$ for $i\ne j$. Set those four comparisons to zero, keeping all other payoffs fixed. Their signed corrections in each row span an interval of width at most this bound, and the resulting table satisfies the four-tie theorem.

## Which inverse columns the singleton conditions force

The signs select specific owners whose inverse columns are **simultaneously strictly positive**, at arbitrary singleton magnitudes. This classification uses the existing necessary singleton conditions: $G$ is $R_0$ of degree one, $\det G>0$, it has a strictly positive inverse column, and it has no continuous singleton path. If any completion lacks a uniform-equilibrium payoff, its native singleton matrix satisfies these conditions. Failure of one of the selected columns therefore gives an original uniform-equilibrium payoff for every higher-reward completion. Positive columns alone do not decide the conjecture.

In the original labels of the 21 integer witnesses above, the selected column indices are as follows. Digits in the same entry denote distinct columns.

| Witness | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Columns | 02 | 02 | 02 | 123 | 2 | 2 | 02 | 2 | 0123 | 023 | 013 |

| Witness | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 |
|---|---|---|---|---|---|---|---|---|---|---|
| Columns | 013 | 13 | 01 | 12 | 2 | 12 | 2 | 2 | 12 | 2 |

To determine the columns directly from signs, fix a target $e_h$ and test the six orders $(i,j,o)$ of its rivals. The generic complementarity problem $x\ge0$, $Gx\ge e_h$, $x\cdot(Gx-e_h)=0$ has total index one. A support omitting $h$ would supply a nonzero homogeneous complementary solution. A singleton cannot meet its positive target and a pair cannot balance the nonpivot row. A proper support can therefore contribute positive index only on a triple $S=\{i,h,j\}$. Its pivot Schur complement is $1/x_h>0$, so the sign of $\det G_{SS}$ is that of $-G_{ij}G_{ji}$. Orient $i,j$ so that $G_{ij}>0>G_{ji}$. The two nonpivot rows require $G_{ih}<0<G_{jh}$, the pivot row needs a positive entry on the other two owners, and the outsider cannot be negative on all three.

One more case gives a continuous singleton path. Suppose $G_{hi}>0>G_{hj}$ and the outsider's signs in order $i,h,j$ run from negative to positive, allowing either sign to be absent. Write the positive triple masses normalized at $h$ as $(X,1,Z)$. The directed cycle $i,h,j$ contracts by $\rho=-G_{hj}Z/(G_{hi}X)\in(0,1)$. Rows $i,j$ balance on their two rivals, giving their active zero conditions; the definition of $\rho$ supplies the other one. The outsider's initial tail $G_{oi}X+G_{oh}+G_{oj}Z$ is nonnegative by the inactive inequality. Through the tour this unnormalized tail first rises and then falls to $\rho$ times its initial value. Thus every phase meets the outsider condition. If no order survives these tests and exclusions, a full support must supply the positive index. Its vector is $G^{-1}e_h>0$. Genericity here requires only nonvanishing principal and outside-slack determinants that are nonzero polynomials on the strict chamber. For the latter the other three rows fix a candidate and the outsider row can perturb its slack. The singleton conditions are open, including failure of a path by compactness of the path controls, so generic matrices suffice for the next argument. [Degree and regular supports](UNIVERSAL_REDUCED_SINGLETON_DEGREE.md) · [Singleton cycle criterion](ALL_FOUR_PLAYER_SINGLETON_PATHS_HAVE_A_FINITE_TEST.md)

For a surviving tied pattern take the union of the columns selected on **any** strict refinement, keeping labels fixed. A selected $y=G^{-1}e_h$ is nonnegative throughout a relative neighborhood on the face, by perturbing each of its matrices into that refinement and taking limits. It is in fact strictly positive. We have $y_h>0$ by $R_0$, and at least one other positive coordinate because the diagonal vanishes. If $y_q=0$, a perturbation of an untied entry $G_{rm}$ has derivative $-(G^{-1})_{qr}y_m$ in this coordinate. Every surviving row has at most one off-diagonal tie. When the support of $y$ has size at least three, each row therefore has an untied foreign entry in its support. If the support is $\{h,j\}$, the only possible row without such an entry is $j$, since $G_{jh}=0$ and $G_{hj}>0$. The inverse row $q$ cannot be supported on column $j$ alone: multiplying it by $G$ would give a multiple of row $j$, which has two nonzero entries. In both cases some allowed derivative is nonzero, contradicting local nonnegativity under both signs of the perturbation. This argument also removes the generic restriction on strict chambers.

| Off-diagonal ties | Exactly one selected column | Two | Three | Four |
|---|---:|---:|---:|---:|
| 0 | 7 | 9 | 4 | 1 |
| 1 | 9 | 20 | 16 | 1 |
| 2 | 3 | 15 | 18 | 3 |
| 3 | 0 | 3 | 6 | 1 |

**These lists are sharp for the stated singleton conditions on all 116 sign orbits.** For every nonselected owner the checker verifies an integer matrix on that very face, with all foreign magnitudes at most four, satisfying all the conditions while the corresponding inverse column has a strictly negative entry. Different nonselected owners may use different matrices. The strict checks use the regular positive-axis degree calculation above. On tied faces the checker uses the actual regular-target and path tests on the face itself. These matrices certify sharpness of this inference; they supply no failing game. [Exact axis enumeration and integer checks](../experiments/SIGN_SELECTED_AXES.py)

For comparison, take all relabelings of the negative-pair axis rule, the same-sign reciprocal-core rule and the previous extra columns for witnesses 1, 3 and 4. For witness 4 the earlier chain reconstruction gives owner 3 as well as the two dependent owners: the reduced right-hand side for $e_3$ is $(d/j,g/j)>0$ and the remaining two coordinates reconstruct positively. Beyond these rules the test selects owner 2 at witness 10, owners 0 and 3 at 11 and 12, owner 3 at 13 and owner 1 at 15 and 17. After taking unions over strict refinements this adds respectively 19, 13 and 2 owner indices across 15 one-tie, 11 two-tie and 2 three-tie classes. [Negative-pair rule](FIVE_NONSINGLETON_REWARDS_AND_THE_SIX_ENTRY_FRONTIER.md) · [Reciprocal cores](TWO_FREE_ROWS_FROM_A_RECIPROCAL_PAIR.md) · [Three-cycle leaf](THREE_CYCLE_WITH_A_DEPENDENT_AT_RANK_FOUR.md) · [Reciprocal-core leaf and chain reconstruction](RECIPROCAL_CORE_AT_RANK_FOUR.md)

One actual-equilibrium consequence is available at **all price scales**. In every selected row and for every rival set $T$ of two or three owners, mark independently a negative passive reward $-U_{iT}$ at $T$ and a positive participating reward $V_{iT}$ at $T+i$, with nonnegative magnitudes and at least one positive. Thus three selected columns permit 24 independent marked prices. For example the three rows 0, 1 and 3 can be marked together throughout strict chambers 11 and 12. The remaining native entries admit either sign under the all-scale theorem's bounds. Specifically let $h_*=1-(1+t)^{-3}$ and choose $t$ by $\sum_{i,T}t^{|T|-1}(U_{iT}+h_*V_{iT})=1$. Set unmarked reference magnitudes to zero and $A_i(T)=Z_i(T)+U_{iT}$, $B_i(T)=Z_i(T+i)-V_{iT}$. It suffices that $|Z_i(ij)|\le\delta(1+t)/t$ and, for $k=|T|=2,3$, $|A_i(T)-h_*B_i(T)|\le\delta t^{1-k}$ and $|B_i(T)|\le\delta(1+t)^4/t^k$. Here $\delta>0$ depends on the singleton matrix on the positive-column branch. If the singleton conditions fail, the earlier exits already supply a uniform-equilibrium payoff for every completion. [All-scale positive-column theorem](POSITIVE_GRAND_REWARDS_AT_EVERY_SCALE.md)
