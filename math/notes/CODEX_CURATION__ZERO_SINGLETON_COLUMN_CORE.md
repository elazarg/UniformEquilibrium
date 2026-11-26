# The prescribed zero singleton column

## Current best attempt

This is a standalone proof for review. It contains the prescribed-owner
carrier identity and the regret-infimum reduction for arbitrary four-player
tables. The only game-specific Lean dependencies are named below. The
carrier translation and clock completion are ordinary mathematics in this
packet and need independent review.

## Statement and model

Let \(I\) have four players. At each live date the players make independent
private Continue or Quit choices. The first nonempty quitting coalition \(S\)
absorbs and pays the reward vector on \(S\) thereafter. Live play and
perpetual continuation pay zero. A behavioral profile is described by
independent stopping laws on \(\mathbb N\cup\{\infty\}\), since before
absorption the only public history at each date is all Continue. A unilateral
deviation may replace the player's entire law. Its maximal payoff is the
supremum of the pure finite-deadline and Never offers, because arbitrary
replacement laws average those offers. Write \(U\) for the prescribed
terminal payoff vector and \(B\) for the vector of these full response caps.

For a reward table \(r\), let \(K(r)\) be the Euclidean closure of the
attainable pairs \((U,B)\), and let
\[
F(r)=\inf_{\text{all profiles}}\sum_i(B_i-U_i).
\]
Take a native table \(Z\) with \(Z_i(\{i\})=0\) for each \(i\), and write
\(r^c(S)=Z(S)-c\) for nonempty \(S\) and \(c\in\mathbb R^I\). Let
\(K_p(Z)\), \(K_{\rm abs}(Z)\), and \(K_{\rm fin}(Z)\) be the closures
with, respectively, player \(p\) stopping almost surely, at least one
player stopping almost surely, and all players stopping almost surely.
The middle condition is equivalent to almost-sure absorption by
independence. Write \(A_{Z,p}\) and \(A_Z\) for the total regret infima
on the first and second sets. Taking closures leaves these infima unchanged
by continuity. Put \(G_{ij}=Z_i(\{j\})\).

For every native \(Z\) and every prescribed \(p\), with \(g=G_{\cdot p}\),
\[
K(r^g)+(g,g)=K_p(Z),
\qquad
A_{Z,p}=A_Z=F(r^g)=\max_{c\in\mathbb R^I}F(r^c).
\]
Consequently the four-player uniform-equilibrium conjecture is equivalent
to its restriction to tables with the entire singleton column of one
prescribed player equal to zero. Each of the four such translations of
the same native kernel has a positive gap whenever any translation does.
If any row of \(G\) has a distinct weak blocker, the total regret
infimum on \(K_{\rm fin}(Z)\) also equals \(A_Z\).

## Truncation

For any fixed table, including one with a bounded nonzero payoff at Never,
couple the old and new prescribed clocks independently by owner. Suppose
clock \(i\) is changed on an event of probability at most \(\varepsilon_i\).
If all payoffs have magnitude at most \(M\), the union bound gives
\[
\|U'-U\|_\infty\le 2M\sum_i\varepsilon_i.
\]
For each pure response use the same deadline or Never in both profiles and
couple the rivals. The same bound holds uniformly over the whole response
menu and therefore holds for \(\|B'-B\|_\infty\).

In particular, one can move every finite atom later than \(T\) to Never and
send \(T\) to infinity. To retain any prescribed clock as almost surely
finite, move its late mass instead to the finite date \(T\). The sum of
the masses changed tends to zero in either construction.

## Translation for a prescribed owner

Translate every outcome of \(r^g\), including Never, by \(g\). This adds
\(g\) to both vectors and gives a terminal problem with finite rewards
\(Z\) and default \(g\). On a native profile with \(p\) finite almost surely,
the prescriptions are identical. Any deviation of another player still
faces the finite clock of \(p\). For a deviation of \(p\), the default entry
is \(g_p=Z_p(\{p\})=0\). This gives the inclusion of \(K_p(Z)\) in the
translated carrier.

For the reverse inclusion truncate a profile in the default-\(g\) problem
at \(T\), sending all its late finite atoms to Never. Replace only the
remaining Never mass of \(p\) by a uniform draw \(V\) on \(L\) consecutive
fresh dates, leaving \(T+1\) vacant. Use the native table with default zero.
Prescribed outcomes agree in value, including when the new block replaces
old joint Never by the singleton \(\{p\}\). The full cap of \(p\) agrees
because its opponents are unchanged and its default is zero.

For \(i\ne p\), the deadline offers through \(T\) agree. For any later
reply, the event of an earlier rival exit contributes the same payoff to
both problems. Conditional on every rival surviving \(T\), the two old
options are solo quit for zero and Never for \(g_i\). The new vacant date
and Never still give those offers. A finite reply at \(t\) in or after the
new block gives the conditional payoff
\[
\Pr(V<t)g_i+\Pr(V=t)Z_i(\{i,p\}).
\]
It is at most \(\max(0,g_i)+|Z_i(\{i,p\})|/L\). Thus the new cap is
between the old cap and that cap plus \(M/L\), taking \(M\) large enough
to bound the native rewards. This comparison also holds if the survival
event has probability zero, because its contribution then vanishes. Let
\(L\) and then \(T\) tend to infinity. The resulting approximations all
have \(p\) finite and give the reverse inclusion.

## Completing all clocks when the finite owner has a blocker

Suppose \(G_{pj}\le 0\) for some \(j\ne p\). We show
\(K_p(Z)=K_{\rm fin}(Z)\). By truncation, approximate a \(p\)-finite
profile with one whose finite support ends at \(T\), keeping \(p\)
certain to stop there or earlier. If \(j\) still has a Never atom,
replace it by a uniform law on \(L\) fresh dates after \(T+1\).
The prescriptions are unchanged because \(p\) stops before the new block.
The caps of players outside \(\{p,j\}\) are unchanged for the same reason,
since their replies keep \(p\)'s law fixed.
The cap of \(j\) is independent of its own prescribed law.

For \(p\), only replies after \(T\) on the old all-rivals-Never event
can change. Their old conditional value is zero. On that event the
new finite offers are convex combinations of zero and \(G_{pj}\)
with one additional collision term of probability at most \(1/L\).
Never receives \(G_{pj}\). The best old post-cutoff offer remains
accessible at the vacant date. Earlier offers are unchanged, so the
new full cap of \(p\) lies between its old cap and that cap plus \(M/L\).

There are now two clocks with bounded finite support. Place the remaining
Never atoms at a date beyond both supports. The prescriptions are unchanged.
For each respondent at least one of the two finite opponents remains, so
the whole response menu is unchanged as well. Taking the approximation
limits gives \(K_p(Z)\subseteq K_{\rm fin}(Z)\). The reverse inclusion
follows from the definitions.

## Regret infima

If every row has a distinct weak blocker, the preceding identity holds for
each \(p\). An absorbing profile has some finite owner, so the finite union
of the carriers \(K_p(Z)\) is \(K_{\rm abs}(Z)\). All of these carriers
therefore equal \(K_{\rm fin}(Z)\). The translation identity now gives
\(F(r^{G_{\cdot p}})=A_{Z,p}=A_Z\). On an all-finite profile there is
certain absorption under every unilateral replacement. Changing \(Z\) to
\(r^c\) subtracts the same constant from each player's prescription and cap.
Approximating \(A_Z\) by such profiles proves \(F(r^c)\le A_Z\) for
every \(c\).

If a row has no distinct weak blocker, every \(r^c\) has a
uniform-equilibrium payoff. Indeed, its normalized singleton matrix is
\(G\). The checked four-player normal-core theorem forces the full core on a
counterexample, and a member of the core must have a distinct nonpositive
row entry. The checked terminal debt criterion then gives \(F(r^c)=0\)
for every \(c\). The translation identity gives \(A_{Z,p}=0\) for each
\(p\), and \(0\le A_Z\le A_{Z,p}\) gives \(A_Z=0\).

If even one row \(p\) has a blocker, the local completion gives
\(K_p(Z)=K_{\rm fin}(Z)\). Its total regret infimum is \(A_{Z,p}=A_Z\)
by the scalar identity.

For the conjecture reduction, center any signed table \(r\) by its own
singleton entries on every nonempty exit. Then \(r\) is one of the
translations of that native kernel. If the original game has no uniform
equilibrium payoff, the terminal debt criterion gives \(F(r)>0\) and
maximality gives \(F(r^{G_{\cdot p}})>0\) for every \(p\). At the exit
\(\{p\}\) the translated rewards are all zero. The other direction
follows by inclusion of this class in the original class.

## Exact boundary tests

For distinct \(p,i\), let all rewards vanish except \(Z_i(\{i,p\})=1\).
Start at AllNever with default \(g=Z(\{p\})=0\). Moving \(p\)'s clock
to a uniform \(L\)-date block leaves the prescribed reward zero but gives
\(i\) cap \(1/L\), attained by quitting at any one date of the block.
This attains the error bound for the post-cutoff replacement.

Let \(Z_i(S)=1\) when \(i\notin S\) and zero otherwise. There is no weak
blocker. A sole prescribed quitter stops at a fixed finite date.
Its cap and payoff are zero. Each other player already gets
its maximal payoff one by waiting. Thus \(A_Z=0\).

When all four clocks are individually finite, each player can guarantee one
by playing Never. The sum of the four debts is then the expected number of
first quitters and is at least one. Distinct deterministic dates attain one.
The scalar equality for arbitrary kernels therefore does not give a
four-finite carrier identity without the blocker hypothesis.

## Lean handoff

- `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`)
  gives the full normal core under the four-player and nonexistence hypotheses.
- `exists_core_blocker_of_mem_normalCore`
  (`UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean`)
  supplies a distinct nonpositive entry in the core member's row.
- `normalizedSoloMatrix_eq_soloReward_sub`
  (`UniformEquilibrium/Quitting/Classification/PreemptionGateDictionary.lean`)
  identifies that entry with \(G_{ij}\) for every translation of \(Z\).
- `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`)
  identifies positive unrestricted total regret with nonexistence of a
  uniform-equilibrium payoff.

Prove the carrier translations before taking infima. For completion, state
the local blocker of the given finite owner as the input and derive the
global blocker case using independence and the full normal core. Use the
terminal debt criterion on translated games with zero reward at Never. The
nonzero default is an intermediate terminal-payoff calculation.
