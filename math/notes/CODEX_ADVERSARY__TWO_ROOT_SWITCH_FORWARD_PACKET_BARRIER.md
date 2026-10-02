# Two-root switch equations and the forward-packet barrier

**Identity:** CODEX_ADVERSARY  
**Status:** ordinary mathematics, not Lean-checked; the compiler declarations
named below are Lean-checked  
**Conclusion:** the literal minimal switch scale is an extremal boundary, and
a fixed-scale charged two-root block cannot have arbitrarily small payoff seam.
The support-approximate relaxation has a cleaner consumer: an indefinitely
iterable exact-Bellman orbit with vanishing support error and divergent charge
in one compact carrier would already be a `QuittingFiniteForwardPacket`
producer and hence contradict the terminal exploitability witness.  The
current Fin4 source does not supply the required same-orbit attachment.

This note continues
[`CODEX_ADVERSARY__QUANTITATIVE_DESCREENING_COMPLEMENTARITY_BARRIER.md`](CODEX_ADVERSARY__QUANTITATIVE_DESCREENING_COMPLEMENTARITY_BARRIER.md).

## 1. Self-contained question and conventions

Let the player set be `I=Fin 4`.  For a product root `p`, write `p_i` for
player `i`'s Quit probability.  Put

$$
w_p(S)=\prod_{i\in S}p_i\prod_{i\notin S}(1-p_i),
\qquad c(p)=\prod_i(1-p_i),
$$

and, for a tail payoff `U`,

$$
F(p,U)=\sum_{\varnothing\ne S\subseteq I}w_p(S)r(S)+c(p)U.
\tag{1.1}
$$

For player `i`, let `Q_i(p,U)` and `C_i(p,U)` be its forced-Quit and
forced-Continue endpoint payoffs against the opponents' marginals, and let

$$
G_i(p,U)=Q_i(p,U)-C_i(p,U).
\tag{1.2}
$$

All these expressions are polynomials in the quit probabilities and affine
in `U`.

Fix distinct labels `a,k` selected by the hard-source collision theorem and
write

$$
A=r_k(\{a,k\})-r_k(\{a\})\ge \gamma>0.                 \tag{1.3}
$$

The proposed first row has only `a,k` active:

$$
p_a=1-\varepsilon,\qquad p_k=t,qquad
p_j=0\quad(j\notin\{a,k\}),                              \tag{1.4}
$$

with `0<epsilon,t<1`.  The two-root block is, in actual chronological
notation,

$$
p\quad\hbox{then}\quad q\quad\hbox{then tail }U,
$$

and its Bellman vectors are

$$
X=F(q,U),\qquad V=F(p,X).                                \tag{1.5}
$$

Thus the charged-relation direction is `U -> X -> V`.  The exact desired
fields are:

1. `p` is endpoint Nash at tail `X` (or support-`delta` Nash in Section 7);
2. `q` is exact endpoint Nash at tail `U`;
3. the two equalities (1.5) hold literally;
4. `U,X,V` dominate the behavioral punishment vector `P` and lie in the
   reward box;
5. `max_i |V_i-U_i| <= zeta`, with `zeta=0` for a closed block; and
6. source usefulness is retained by a positive charge/marked-mass condition,
   not merely by `c(p)>0`.

The last distinction is essential.  On an all-normal table, `U_i=r_i({i})`
and `p=q=all-Continue` satisfy exact Nash, Bellman matching, the punishment
floor, exact payoff return, and maximal joint/deleted continuation.  They
carry zero charge and no marked collision.  Therefore “permeable” cannot mean
only positive Continue probability.

## 2. The complete finite semialgebraic system

For exact endpoint Nash, the playerwise constraints are equivalently

$$
p_iG_i(p,X)\ge0,
\qquad (1-p_i)G_i(p,X)\le0,                              \tag{2.1}
$$

and the analogous two inequalities for `(q,U)`.  Together with (1.4)--(1.5),
the cube constraints, coordinatewise box/floor inequalities, and

$$
-\zeta\le V_i-U_i\le\zeta,                              \tag{2.2}
$$

this is a finite basic semialgebraic system after choosing the finite support
stratum.  Without choosing the stratum it is still a finite semialgebraic
Boolean combination.

For support-`delta` Nash, replace (2.1) by

$$
(p_i=0\ \lor\ -\delta\le G_i(p,X)),
\qquad
(p_i=1\ \lor\ G_i(p,X)\le\delta),                       \tag{2.3}
$$

and similarly for `q` if it is also relaxed.  Notice that (2.3) is
**support-local**: a positive action of arbitrarily small probability still
pays the full endpoint inequality.  It is not the probability-weighted Nash
defect.

For a fixed numerical reward table and fixed real parameters `P,M,gamma`,
nonemptiness and its projection to any chosen parameters are therefore
semialgebraic questions.  Tarski--Seidenberg supplies a finite real-closed-
field decision theorem in principle.  This does not make the graph of the
behavioral punishment value semialgebraic when the reward table itself is
varied; here `P` is a fixed supplied vector.

## 3. Exact switch equation and the literal boundary saturation

Because `k` is interior in (1.4), exactness gives

$$
0=G_k(p,X)
=(1-\varepsilon)A+\varepsilon[r_k(\{k\})-X_k].          \tag{3.1}
$$

Hence

$$
X_k=r_k(\{k\})+\frac{1-\varepsilon}{\varepsilon}A,
\qquad
\varepsilon\ge\frac{A}{A+2M}
\ge\frac\gamma{\gamma+2M}.                             \tag{3.2}
$$

The hard source also gives `gamma<=2M`, so the universal lower scale

$$
\varepsilon_*:=\frac\gamma{\gamma+2M}                  \tag{3.3}
$$

lies in `(0,1/2]`.

### Proposition 3.1 (the universal minimal scale is extremal)

If the exact finite system is imposed at `epsilon=epsilon_*`, then necessarily

$$
A=\gamma,
\qquad r_k(\{k\})=-M,
\qquad X_k=M.                                           \tag{3.4}
$$

Consequently the system is empty if any of these three equalities fails.

### Proof

At (3.3), equation (3.1) gives

$$
X_k-r_k(\{k\})=\frac{2M}{\gamma}A\ge2M.
$$

The box gives the reverse inequality.  Equality in the box difference forces
the two endpoint extrema, and equality in `A>=gamma` forces `A=gamma`.  QED.

There is an exact support-approximate analogue.  If both actions of `k` are
played and (2.3) holds, then

$$
|G_k(p,X)|\le\delta,
\qquad
(1-\varepsilon)A\le 2M\varepsilon+\delta,               \tag{3.5}
$$

and therefore, for `delta<gamma`,

$$
\varepsilon\ge
\frac{A-\delta}{A+2M}
\ge\frac{\gamma-\delta}{\gamma+2M}.                    \tag{3.6}
$$

At the literal lower value on the right of (3.6), all inequalities again
saturate:

$$
A=\gamma,quad r_k(\{k\})=-M,quad X_k=M,quad
G_k(p,X)=\delta.                                        \tag{3.7}
$$

Thus moving to support error does not make the *minimal* switch scale generic;
one must move strictly farther into the owner-Continue direction or use a
different row.

For completeness, the other active equation is

$$
G_a(p,X)=
t[r_a(\{a,k\})-r_a(\{k\})]
 +(1-t)[r_a(\{a\})-X_a].                                \tag{3.8}
$$

Exactness requires (3.8) to vanish; support-`delta` requires its absolute
value at most `delta`.  The Fin4 collision theorem (1.3) gives no sign or
magnitude for the cross-increment in (3.8).  The two outsiders, prescribed
Continue, additionally require `G_j(p,X)<=0` in the exact system or
`G_j(p,X)<=delta` in the support system.  These are genuine unsupplied
equations, not consequences of (1.3).

## 4. Exact closed return is incompatible with the witness

Suppose `U,X,V` are exact punishment-floor states and (1.5) holds.  The
irrelevant simplex coordinate stored at the tail state can be chosen to equal
the first root `p`.  Then

$$
(U,p)\longrightarrow(X,q)\longrightarrow(V,p)           \tag{4.1}
$$

is a literal path in the full punishment-floor admissible predecessor
relation.  If `V=U`, it is a closed path.  The checked theorem
`QuittingTerminalExploitabilityWitness.admissible_cycle_chargeSum_eq_zero`
forces its total charge to be zero.  Since both stage charges are
nonnegative, both roots must be all-Continue.  In particular no genuinely
active switch row can close exactly.

The choice of the tail's stored root coordinate matters: payoff equality
alone is not state equality in the boxed relation, but that coordinate is
irrelevant to every incoming Bellman edge and may be set to `p` from the
start.

## 5. A quantitative seam floor at fixed nonperturbative scale

The exact incompatibility strengthens to an explicit positive payoff-seam
bound.  Let

$$
B=\operatorname{quittingRewardBound}(r),
\qquad C=2+7B,
$$

and suppose the first row has absorption at least `c>0`.  For example, at the
fixed scale (3.3),

$$
c=1-\varepsilon_*=\frac{2M}{\gamma+2M}\ge\frac12,       \tag{5.1}
$$

because player `a` Quits with that probability.

### Proposition 5.1 (all-behavior seam lower bound)

For every exact two-edge punishment-floor block satisfying

$$
\max_i|V_i-U_i|\le\zeta
$$

and containing an edge of absorption at least `c`, one has

$$
\boxed{
\zeta\ge
c\,\frac{(\sqrt{C^2+12\gamma}-C)^2}{72}>0.}
\tag{5.2}
$$

### Proof

If `zeta=0`, Section 4 already contradicts positive charge.  Suppose
`zeta>0` and put `e=zeta/c`.  The checked payoff-near-return theorem turns the
finite exact floor prefix into a single-seam projective lasso at error `e`:
the seam inequality is exactly `zeta=e*c`.

The lasso's checked path theorem gives a divergent root path with support
error `2e` and rationality error `2e`.  Apply the checked quantitative
support-rational path compiler with

$$
\delta=2e,qquad \text{rationalityError}=2e.
$$

It produces a terminal profile, against unrestricted behavioral deviations,
with exploitability at most

$$
6e+C\sqrt{2e}.                                           \tag{5.3}
$$

The terminal witness says every behavioral profile has exploitability at
least `gamma`; hence `gamma<=6e+C sqrt(2e)`.  Setting
`y=sqrt(2e)` and solving `3y^2+Cy-gamma>=0` gives

$$
e\ge\frac{(\sqrt{C^2+12\gamma}-C)^2}{72}.
$$

Multiplication by `c` proves (5.2).  QED.

Thus a fixed choice of `epsilon<1` cannot participate in arbitrarily accurate
two-root payoff returns.  If `epsilon` is allowed to tend to one and every
other quit probability tends to zero, this argument loses its charge floor;
that is the zero-charge all-Continue degeneration, not a retained paid row.

## 6. Exact-root permeability supplied by the hard witness

For any exact root at a boxed floor tail, the checked marginal-cap theorem
gives

$$
1-p_i\ge d:=\frac\gamma{4M}>0.                           \tag{6.1}
$$

Therefore every exact Fin4 floor root has

$$
c(p)\ge d^4,
\qquad c_{-i}(p)\ge d^3.                                \tag{6.2}
$$

This validates the required continuation denominators for exact `p,q`, but
it gives no positive absorption lower bound.  The all-Continue root satisfies
(6.1)--(6.2).  At (3.3), the separate fixed owner-Quit probability supplies
the useful charge (5.1).

## 7. The support-approximate forward-packet relaxation

The relevant checked object is not a two-root near-return.  A
`QuittingFiniteForwardPacket reward K delta R` consists of values and roots
with, on one finite prefix,

$$
U_{n+1}=F(p_n,U_n)                                      \tag{7.1}
$$

**exactly**, support-`delta` Nash at tail `U_n`, the rationality bound

$$
P_i-\delta\le U_{n,i},                                  \tag{7.2}
$$

all values in one fixed compact carrier `K`, and total raw absorption at
least the requested target `R`.

The canonical source-faithful descreening does not enter this interface.  It
has

$$
\varepsilon=\frac\gamma{8M},\qquad t=\frac12,qquad
G_k(p,X)\ge\frac\gamma2.                                \tag{7.3}
$$

Both actions of `k` are in support, so (2.3) requires

$$
\delta\ge\frac\gamma2.                                 \tag{7.4}
$$

The previously recorded probability-weighted root defect is `gamma/4`; the
forward-packet field is the stronger support-local condition, so its correct
lower bound is `gamma/2`.

### Proposition 7.1 (fixed-error capacity for exact-Bellman support orbits)

Let `K` be a fixed compact payoff carrier and put

$$
\delta_{\rm gap}:=
\frac{(\sqrt{C^2+12\gamma}-C)^2}{144}>0.                \tag{7.5}
$$

For every `0<delta<delta_gap`, there is a finite charge threshold
`T=T(K,delta)` such that no finite exact-Bellman prefix in `K` satisfying
support-`delta` Nash and (7.2) has total raw absorption at least `T`.

Consequently there is no infinite exact-Bellman forward orbit in `K`
satisfying those conditions and having divergent cumulative absorption.  In
particular, there is no indefinitely iterable orbit with infinitely many
rows whose absorption is bounded below by one fixed positive constant.

### Proof

Compact charged return supplies `T` so that any packet of charge at least `T`
contains two values within `delta` and an intervening block of raw charge at
least one.  The checked reversed-forward-block construction makes that block
a single-seam lasso:

- local support error is `delta`;
- seam error is at most `delta`;
- whole-block absorption is at least `1/2`; and
- the resulting lasso error is `2delta`.

The lasso path has support and rationality errors `4delta`.  The quantitative
support-rational path compiler would therefore give a behavioral terminal
profile with exploitability at most

$$
12\delta+2C\sqrt\delta.                                 \tag{7.6}
$$

The definition (7.5) is exactly the positive solution of
`12 delta+2C sqrt(delta)=gamma`.  For `delta<delta_gap`, (7.6) is strictly
below the witness gap, a contradiction.  Hence the requested high-charge
packet cannot exist.  A divergent infinite orbit has a finite prefix above
every finite threshold, proving the last statements.  QED.

This is stronger than asking for an approximate two-root return: no return
must be produced by hand.  Exact Bellman iteration, a common compact carrier,
small support error, rationality, and enough accumulated charge let compact
closing select the return automatically.

### Corollary 7.2 (null-error arbitrary-charge families are terminal)

Fix one compact carrier `K`.  Suppose `delta_n>0`, `delta_n -> 0`, and for
every `n` and every `R>=0` there is a finite forward packet in `K` at support
error `delta_n` and charge target `R`.  Then the game has a uniform-equilibrium
payoff.

Indeed, for any requested positive support error choose `n` with
`delta_n` below it and weaken both the support and rationality inequalities.
This produces the universal quantifiers required by
`quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets`.
Hence such a family is inconsistent with the hard residual witness.

## 8. What the actual Fin4 source does and does not supply

The following same-table fields are genuinely available.

1. `gamma>0`, a uniform terminal exploitability gap, and `gamma<=2M`.
2. All four players are punishment-normal: `P_i<=r_i({i})`.
3. For every singleton owner `a`, a distinct collider `k` satisfies (1.3).
4. Every exact floor root has the explicit Continue floor (6.1).
5. The normalized singleton packet has full support and the mass floor

   $$
   m_i\ge\frac1{1+(2M/\gamma)3}.
   $$

6. The singleton matrix lies in `ResidualHardClass`: no homogeneous simplex
   solution, standard-Q on the normal core, and not projective-Q-bar.
7. The global witness forbids exact positive floor cycles and, by Sections 5
   and 7, quantitatively limits small-error charged returns/orbits.

Only items 1--4 and 7 constrain the switch equations above.  The packet mass
and residual-LCP fields have no declared equality attaching the redesigned
mixed root to the packet's literal law or to consecutive Bellman values.
`ResidualHardClass` uses only singleton-matrix algebra; it contains no
nonsingleton switch payoff, tail, floor, or chronology field.  The packet
mass cannot honestly be multiplied by `(1-epsilon)t` without a new
same-history ancestry theorem.

The checked
`FinFourQuantitativeFullSupportHardResidual.nonempty_singletonBaseSameLawResetProducer`
does use the full residual.  It selects an exact Nash point for the three free
players and quantitative strict-superset absorption, but keeps the singleton
owner at sure Quit and localizes all positive debt to that owner.  It is a
canonical screened output, not the permeable support-small row required here.

Thus the strongest source-faithful remaining producer is:

> For arbitrarily small `delta`, construct one literal exact-Bellman forward
> orbit in a fixed compact carrier, with support-`delta` roots, rationality
> `P-delta`, and enough repetitions of switch rows whose owner Quit probability
> is bounded below (or whose marked atom has a fixed lower bound) to make raw
> charge arbitrarily large.

Proposition 7.1 is already its terminal consumer.  What is missing is the
same-orbit producer.  Current pure-pair/minimum-return rows have fixed support
error (7.4), and the independent rank rows are not successive values of one
exact Bellman recursion.

## 9. Exact declarations inspected

- `FinFourQuantitativeFullSupportHardResidual` and
  `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`,
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`;
- `FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`,
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`;
- `terminalExploitabilityGap_le_two_mul_bound`,
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalTerminalGapConstrainedStationary.lean`;
- `exactFloorRoot_quitProbability_le_one_sub_terminalGap_div_four_mul`,
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/TerminalGapExactRootMarginalCap.lean`;
- `QuittingTerminalExploitabilityWitness.admissible_cycle_chargeSum_eq_zero`,
  `UniformEquilibrium/Quitting/Bellman/Finite/TerminalExploitabilityCycleExclusion.lean`;
- `QuittingFiniteForwardPacket`,
  `exists_singleSeamProjectiveLasso_of_finiteForwardPackets`, and
  `quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets`,
  `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`;
- `exists_singleSeamProjectiveLasso_of_floorPrefix_payoffNearReturn`,
  `UniformEquilibrium/Quitting/Projective/PunishmentFloorNearReturn.lean`;
- `QuittingFiniteSingleSeamProjectiveLasso.exists_supportRationalDivergentPath`,
  `UniformEquilibrium/Quitting/Projective/SingleSeamProjectiveLasso.lean`;
- `exists_isεAsymptoticNash_of_divergentAbsorption_supportRationalPath`,
  `UniformEquilibrium/Quitting/Paths/SupportWitnessPathCompiler.lean`;
- `IsQuittingRootSupportApproxNash`,
  `UniformEquilibrium/Quitting/Boundary/Repair/SupportEnlargementAlternative.lean`;
- `FinFourQuantitativeFullSupportHardResidual.nonempty_singletonBaseSameLawResetProducer`,
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/SingletonBaseSameLawResetProducer.lean`; and
- `ResidualHardClass`,
  `UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`.

No Lean file or export was modified.
