# Uniform equilibrium when partners can join a four-date quitting cycle

In a four-player quitting game each player independently chooses a stopping date or Never. The reward is $r(S)$ for the first nonempty quitting coalition $S$, and zero for perpetual play. Put $s_i=r_i(\{i\})$ and $Z_i(S)=r_i(S)-s_i$ for nonempty $S$. Write $G_{ij}=Z_i(\{j\})$, $J_{ij}=Z_i(\{i,j\})$ for distinct $i,j$. Number players modulo four and call $m(i)=i+2$ the mate of $i$. A periodic equilibrium here compares the prescribed payoff with the payoff from every private replacement stopping law.

There is an open family on which exact absorbing four-date equilibria exist for every signed choice of the own singleton levels. The neighborhood includes a boundary where all four mates are indifferent to joining a solo phase. Its four-entry response map has local degree $-3$. At certain tables inside the neighborhood there are three distinct exact equilibrium payoffs. The incentive comparisons for each phase and the full complementarity argument are given below. A separate one-mate calculation identifies where a schedule containing just one joint phase crosses this boundary.

## Passing the upper solo threshold with one joint phase

Take the centered singleton matrix with reciprocal mate payoffs 3 and crossed payoffs −1. In forward cyclic order let the predecessor's joining reward at each solo date be strictly negative and the successor's strictly below −1. Assume all four matched joining rewards positive, with the three other than x=J₂₀ strictly below x₀=(3+√5)/2. Put J=J₀₂, a=Z₁({0,2}), b=Z₃({0,2}) and

    105D = −50+24√5−4√5 J+(9√5−20)a+(20+9√5)b.

Whenever D>0, every x in a sufficiently small interval strictly above x₀ admits an exact proper four-date periodic equilibrium. Thus each such game has a uniform-equilibrium payoff for arbitrary signed own levels. On phase 0 owners 0 and 2 mix; phases 1,2,3 retain their respective solo owners. The joint phase has entrant hazard (x−x₀)/D+O((x−x₀)²). For D<0 this same uniquely determined local mixed branch lies below the threshold and does not extend this support into its upper side. The linear test makes no conclusion at D=0.

Here is the derivative calculation. Let ρ=(3−√5)/2, h=1−ρ and B=(1+√5)/2. Use t_k for incumbent hazards and z for the extra hazard of 2 at phase 0. Write W_ik for the periodic prescribed native payoff of i at phase k; it is analytic around the base hazards, by the four affine date recursions and nonunit cycle survival. At the base all t_k=h, z=0, and W_ik is 0,−h,B,0 as i−k modulo four is 0,1,2,3. Require the four incumbent contacts W_ii=0 except W_00=zJ, and the extra contact W_20=t₀x. Because every used hazard is proper, equating prescribed and forced Quit payoffs equates the two actions. The true waiting payoff uses the same periodic continuation.

For z as curve parameter write u_k=t'_k(0) and g_ik=W'_ik(0). At fixed x=x₀ let T=(J,a,x₀,b). The first-order recursion reads g_ik=ρ g_i,k+1+E_ik, where

    E_ik=(G_ik−W_i,k+1)u_k + 1_{k=0}(ρG_i2+hT_i−W_i0).

All W on the right are the displayed base values. In particular g_ik=Σ_{l=0}³ρˡ E_i,k+l/(1−ρ⁴). The four equations g_ii=1_{i=0}J have a circulant coefficient matrix with first row

    (0, −1/2−7√5/30, (1+√5)/6, 1/6−√5/10).

Its determinant is −49/90−7√5/30. At z=0 no reward x affects the prescribed law, and the derivative of the extra contact W_20−t₀x with respect to x is −h. The analytic implicit function theorem therefore solves all five contacts uniquely for t and x in terms of z. Substitution into x'(0)=(g_20−x₀u₀)/h gives the stated D; the reproducible symbolic calculation uses only this four-by-four system. The remaining quiet constraints are strict at the base by hypothesis and persist for small z. Each rival family absorbs geometrically, so iterating the stage recursions proves the complete deadline and Never inequalities and the uniform-horizon conclusion.

Beyond Γ,J the contacts use only a,b. The only further rewards any unilateral deadline can encounter are Z₁({0,1,2}) and Z₃({0,2,3}) on phase 0. They influence the size of the interval through two quiet guards. Their coefficients in the forced offers are positive, so given upper bounds on them the interval can be chosen uniformly over all downward changes. The other 28 native rewards may vary independently without affecting that interval. For example a=0,b=1 gives D>0 throughout 0<J<x₀. The strict branch also persists at each interior upper-side point under small perturbations of all raw entries: the Jacobian in the four incumbent hazards and entrant hazard is invertible there by x'(z)≠0 and the preceding implicit calculation.

An upper-side example also fails both payoff-domain orientation tests. Take d=1/10 and directed crossed rewards −(1−d) for the predecessor and −(1+d) for the successor. Set J₀₂=J₁₃=J₃₁=1, a=300 and b=1. Put Z₀({1,2})=Z₂({0,1})=0 and Z_i({0,1,2})=Z_i({0,1,2}−i) for i=0,1,2. Set the grand column to minus the ones vector and any remaining higher coordinates to zero. All these choices have D>0. On the support {0,1,2} use odds 1/100 each. Every active forced Quit offer is strictly positive: its unnormalized numerator on row 1 is −2/100+300/100²>0, and the two other rows have positive linear sum and zero quadratic coefficient. The indifference-level Jacobian is L=J−G on that triple because the three two-rival joining increments vanish. Its determinant d²(x+J₀₂−6) is strictly negative, opposite to the required three-owner orientation. The levels on this triple are u₀=−0.019, u₁=0 and u₂=(x−3−d)/100. Put u₃=0.04. This is an interior point of the hull of the singletons and the grand column: its grand weight is (1−Σu)/5, and its singleton weights are G⁻¹u plus this grand weight in each coordinate. They are positive since G⁻¹ is positive with row sums one. It belongs also to the first-action outer set, witnessed by owner 1 alone with hazard 0.03. The respective quiet forced offers are −0.027,−0.033,0.03, and the passive lower bounds are below −0.8 since each row has minimum at most −1. These checks hold for x sufficiently close to x₀ and the determinant violation therefore occurs in both prescribed domains.

### The full interval for this support

The four-date support itself has a strict upper limit independent of the completion. Owner 2 mixes alone on phase 2, so W₂₂=W₂₃=0 and phase 1 gives W₂₁=−t₁. Its two mixed actions on phase 0 imply

    t₀ x = 3t₀−(1−t₀)t₁,     x=3−(1−t₀)t₁/t₀<3.

Phase 3 also requires t₀x=t₃/(1−t₃). This excludes every exact proper equilibrium of this specified support at x≥3.

Conversely, for **each** x between x₀ and 3 the following completion has an exact equilibrium with that support. Take directed crossed joining rewards −0.9 for the predecessor and −1.1 for the successor, and put all three nonsenior matched J equal to 1. Set

    t₁=1/2,   z=1/100,   t₀=1/(7−2x),   t₃=t₀x/(1+t₀x),
    T=95/99,   t₂=[T+t₃−(1−t₃)z]/[3+t₃−(1−t₃)z],
    U=[t₂/(1−t₂)−3t₃]/(1−t₃),           V=3t₁−(1−t₁)t₂.

Prescribe the two passive rewards at 02 by

    (a+2)t₀z=U+t₀+z,    (b+2)t₀z=t₀+z−(1−t₀)(1−z)V.

Let Z₁(012), Z₃(023) each be any real number at most −3000. All 28 other higher coordinates are unrestricted, and the signed row levels are arbitrary. The two specified passive rewards are functions of x, so this interval statement changes those two rewards as x varies.

For verification, the four phase columns of the prescribed continuation matrix, with players in row order 0,1,2,3, are

    (z, U, t₀x, 0),    (−2/99, 0, −t₁, V),
    (T, 0, 0, −t₂),    (−t₃+(1−t₃)z, t₂/(1−t₂), 0, 0).

In the last three columns the affine solo recursions and active indifferences follow by substitution. On phase 0, owner 0's forced Quit earns z and its Wait earns 3z+(1−z)(−2/99)=z. Owner 2 has the two comparisons displayed at the start of this section. The two outsider Wait equations are precisely the equations for a,b. All hazards are proper: 1/2<t₀<1, 0<t₃<3/4 and 0<t₂<1/2. For the last bound use 2T+t₃−(1−t₃)z<3.

At the solo phases the three quiet matched values are respectively V>t₁, T>t₂ and t₂/(1−t₂)>t₃. The last inequality follows from T−(1−t₃)z>(2−T)t₃. The quiet predecessors' values are −2/99,0,0 respectively and exceed −0.9 times the associated phase hazard. The quiet successors' values are at least the negative of that hazard, which exceeds −1.1 times the hazard. On phase 0 either outsider's forced offer is at most −3000t₀z<−15 since its two single-rival joining rewards are negative. The waiting values are U>−9 and zero. All quiet comparisons are therefore strict. This proves existence for suitable completions throughout the upper interval allowed by this support, with the same raw pair threshold forcing a simultaneous first exit on at least one physical date in every sufficiently accurate profile when at least one own level is positive.

## Three distinct targets beyond the threshold when one joint phase fails

Keep the same matrix and strict crossed joining inequalities as in the one-joint construction. At the corner put all four matched joining rewards equal to $x_*=(3+\sqrt5)/2$. Change $J_{m(k),k}$ by $\epsilon\ell_k$, where $m(k)=k+2$ modulo four and initially $\ell=(1,-1/10,-1/10,-1/10)$. Set the four passive rewards on matched pairs to zero. All other 28 higher rewards are arbitrary finite numbers. For every sufficiently small $\epsilon>0$ there are **three distinct exact four-phase equilibrium payoffs** for the same table, for any fixed signed own levels. Each uses two joint phases. The single-joint slope in the preceding section is strictly negative at the corner and remains negative nearby. All three constructions persist under small independent changes of the passive rewards and the direction $\ell$. The admissible interval of $\epsilon$ may depend on the other rewards.

Here is the calculation, also giving a finite strict test for other directions and passive rewards. Let $T_i$ be the payoff to quiet observer $i$ on the matched pair not containing it. In phase $k$ the incumbent has hazard $t_k$ and its mate has hazard $u_k$, which may be zero. All other owners wait. Put $\rho=(3-\sqrt5)/2$, $h=1-\rho$, and let $v^k$ be the golden base payoff, with coordinates $(0,-h,(1+\sqrt5)/2,0)$ in order $k,k+1,k+2,k+3$. To compute the four-by-four linear response matrix $H$, its column $k$ has entries at rows $k,k+1,k+2,k+3$ respectively given by the following rows times $(T_{k+1},T_{k-1},1)^\top$, all divided by $210$. Here $e=\sqrt5$.

```
  65-29e    25+11e    150-78e
  10- 4e    65-29e    150-48e
   5+  e    10- 4e    -45+57e
  25+11e     5+  e    -45+27e
```

Indeed, at any phase write $V^k$ for its periodic continuation under the actual hazards. At the base the linearized stage update is $g^k=\rho g^{k+1}+b^k$, where, for hazard variations $p_k=dt_k$, $n_k=du_k$,
\[
 b^k=(G_{\cdot k}-v^{k+1})p_k+
      (\rho G_{\cdot m(k)}+hZ(\{k,m(k)\})-v^k)n_k .
\]
Thus $g^k=\sum_{a=0}^3\rho^a b^{k+a}/(1-\rho^4)$. The incumbent's wait-minus-quit difference is $(1-u_k)V^{k+1}_k+u_k(3-J_{k,m(k)})$. Setting its differential to zero gives $g^{k+1}_k+\rho n_k=0$. The coefficient matrix on the four $p_k$ has determinant $-1127/45-56\sqrt5/5$; solving yields $p$ in terms of $n$. Its mate's wait-minus-quit difference is $(1-t_k)V^{k+1}_{m(k)}+t_k(3-J_{m(k),k})$. The resulting differential of the four mate comparisons is $Hn-h\ell\,d\epsilon$, since $v^{k+1}_{m(k)}=-h$. These recursion formulas reproduce all entries of the displayed matrix.

For any chosen entrant support $A$, solve $H_{AA}z_A=\ell_A$, setting the remaining $z$ to zero. If the submatrix is invertible, $z_A>0$ and $(Hz-\ell)_{A^c}>0$, the analytic implicit function theorem on the incumbent and active-mate contacts gives $u_A=h\epsilon z_A+O(\epsilon^2)$, with the other mate guards strictly satisfied. Both crossed guards at each phase are strict at the base and persist. The four incumbents continue to use positive proper hazards, so every rival family absorbs geometrically. Iterating the actual stage inequalities proves exact equilibrium for all unilateral deadlines and Never and gives the uniform conclusion under every signed row shift.

At $T=0$ and the displayed direction, rational enclosing intervals for the active $z$ and the quiet values $Hz-\ell$, each in increasing owner order, are as follows.

| Entrant phases | Active $z$ | Quiet $Hz-\ell$ |
| --- | --- | --- |
| $0,1$ | $(80,81),(140,141)$ | $(60,61),(61,62)$ |
| $0,2$ | $(0.54,0.55),(2.70,2.71)$ | $(0.40,0.42),(0.68,0.70)$ |
| $0,3$ | $(70,71),(45,46)$ | $(32,33),(31,32)$ |

These bounds follow by the two-by-two inverse formula with $223606797749/10^{11}<e<223606797750/10^{11}$. In particular $H_{00}=(150-78e)/210<0$, so just activating mate 2 in phase 0 gives the wrong direction. The phase-zero payoff of incumbent 0 is $u_0J_{02}$. Its three derivatives are distinct because the three intervals for $z_0$ are disjoint. Thus the targets themselves differ for all sufficiently small positive $\epsilon$.

### Persistence in all payoff directions at the four-way boundary

At the corner with all matched joining rewards x₀ and all four passive matched-pair rewards zero, **every sufficiently small perturbation of the entire original payoff table has a uniform-equilibrium payoff**. This holds at every fixed finite choice of the other 28 higher rewards and any signed own levels. The equilibrium has period four. The incumbent mixes at each phase, and its mate may also mix there. The theorem also holds at any other choice of the four passive matched-pair rewards for which the displayed response matrix H obeys

    H_ii<0,     H_ij>0,     H_ij H_ji>H_ii H_jj    (all i≠j).

To verify these hypotheses at zero passive rewards, H is circulant, with first column

    (150−78√5, 150−48√5, −45+57√5, −45+27√5)/210.

The first entry is negative, the other three are positive, and the product of the second and fourth entries and the square of the third both strictly exceed the square of the first. These are strict comparisons in the rational quadratic field.

Solve the four incumbent contacts by the analytic implicit function theorem at arbitrary small signed trial entrant hazards u and nearby raw payoff parameters R. Write F_R(u) for the vector of the mate's Wait advantage over Quit after this substitution. At the critical table R₀ its value at zero vanishes and its derivative is H. A genuine solution requires u≥0, F_R(u)≥0 and u_i F_R(u)_i=0. For y∈ℝ⁴ use the componentwise parts y₊=max(y,0), y₋=min(y,0), and consider the continuous map

    Ψ_R(y)=F_R(y₊)+y₋.

A zero gives exactly the required positive hazards and waiting inequalities, with u=y₊. Its homogeneous first-order map at R₀ is N(y)=Hy₊+y₋. If z≥0 has two positive entries i,j, it is impossible that (Hz)_i and (Hz)_j are both nonpositive: the positivity of the other off-diagonals would imply H_ij z_j≤−H_ii z_i and H_ji z_i≤−H_jj z_j. Their product contradicts the strict pair inequality. A single active entry has strictly negative diagonal. Hence N has no nonzero root, and ‖N(y)‖≥c‖y‖ for some c>0 by homogeneity and compactness.

Compute the local Brouwer degree of N with a small regular target −τ·1, τ>0. There is one preimage with all coordinates negative, with Jacobian the identity. For each singleton i there is exactly one more: its positive coordinate is −τ/H_ii, and each remaining coordinate is −τ−H_ji(−τ/H_ii)<0. Its Jacobian determinant is H_ii<0. The pair inequality excludes every larger active set, including preimages on cone boundaries. All five solutions are interior to their respective orthants and lie in any fixed ball about zero for sufficiently small τ. The degree is therefore 1−4=−3. On a sufficiently small sphere the O(‖y‖²) remainder in Ψ_R₀ gives a straight homotopy to N with no boundary zero. Uniform continuity then preserves this degree on every sufficiently small perturbation of the actual table, even across directions for which the individual one-entrant branch points below the threshold. Thus some y in the ball satisfies Ψ_R(y)=0. The four incumbents stay strictly between zero and one, all entrants stay below one, and the eight crossed waiting guards remain strict by continuity. Geometric absorption under every unilateral replacement proves the asserted original-game uniform equilibrium. This argument guarantees existence under all the perturbations; the preceding three-payoff calculation applies in its stated directions.

Only the four passive matched-pair rewards enter H among the 32 higher entries. For the full four-entrant roster there are four additional triple joining rewards in the crossed waiting guards. Their finite upper bounds suffice for a common small neighborhood because smaller values can only decrease the respective forced-Quit offers. The remaining 24 higher entries are absent from every comparison. The use of a four-phase periodic certificate is shared with earlier results. The local degree here is for four simultaneous mate-entry constraints at the boundary of the solo test.

The finite phase equations supply the payoff, unilateral and opponent-survival inputs of `isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`. The local degree calculation and the raw-table existence conclusions are ordinary mathematical results. [Periodic equilibrium compiler](../../UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean)
