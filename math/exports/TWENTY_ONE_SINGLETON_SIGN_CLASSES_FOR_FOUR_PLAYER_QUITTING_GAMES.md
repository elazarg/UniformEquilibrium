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
