# Nonnegative-singleton selection of finite quiet lifts

Ordinary mathematics, not yet implemented in Lean. The result is a source
corollary of the checked low-player existence and quiet-lift debt theorems.
It does not settle arbitrary four-player quitting games.

## Statement from finite reward data

Let I be any finite player set. A nonempty quitting coalition A pays r(A) in R^I;
infinite all-Continue pays zero. The reward table is bounded by M>=0.
Each player independently samples a stopping time in N union {Never}.
The first finite date pays its entire simultaneous quitting coalition.
Every unilateral replacement law is allowed; this is equivalent to the
complete behavioral-deviation model because the only live public history
is repeated all-Continue. There is no shared randomization.

For a profile p, let U_i(p) be its terminal payoff, B_i(p) its supremum
over all complete unilateral replacements, d_i(p)=B_i(p)-U_i(p), and
E(p)=max_i d_i(p). Put s_i=r_i({i}).

Choose a nonempty proper child S contained in I with |S|<=3, and suppose
some j in S has s_j>=0. For each outsider k in I\S, suppose there are numbers
lambda_ki>=0 satisfying, for every nonempty A contained in S,

    s_k-r_k(A) <= sum_(i in S) lambda_ki [s_i-r_i(A)],       (F)
    r_k(A union {k})-r_k(A)
      <= sum_(i in S) lambda_ki [r_i(A union {i})-r_i(A)].  (J)

All inequalities refer to the original finite table. There is no required
Never inequality s_k<=sum_i lambda_ki s_i.

**Theorem.** There are actual finite independent child laws p^n such that

    E_r(quiet(p^n)) ->0,
    Q(p^n):=product_(i in S) p_i^n(Never) ->0,              (1)

where quiet appends the deterministic law Never to every outsider. In
particular, every positive error admits a finite timing menu and an
original-game profile on that menu with full exploitability below the
error. There is one fixed uniform-equilibrium payoff, and its witnesses
may be selected from these actual quiet lifts.

The target is selected before the requested accuracy. The theorem does
not promise to extend every externally prescribed child target.

## Proof

Let g be the restricted child table. For 0<delta<=1, increase only the
coordinate g_j({j}) by delta, obtaining g^delta. Since |S|<=3, the
low-player existence theorem supplies actual independent child laws p
with unrestricted terminal exploitability at most delta^2 in g^delta.
No source profile or favorable child target is an input.

For any actual independent profile in any quitting table, a player with
positive own singleton v has full debt at least v times joint Never:

    d_i(p)>=v Q(p).                                      (2)

To prove this, retain its original finite atoms and move only its Never
atom to a deterministic date T. Its gain tends to v Q(p) as T tends to
infinity. Earlier opponent absorption is unchanged; the probability of
opponent finite absorption at or after T tends to zero; on joint Never
the new payoff is v instead of zero. Bounded rewards justify the limit.
Each finite-T replacement is legal and its gain is at most the full debt,
so the limiting gain is also bounded by that debt. No response cap or
finite-date maximizer is assumed attained.

In g^delta, player j's singleton is s_j+delta>=delta. Therefore

    Q(p)<=delta^2/(s_j+delta)<=delta.                     (3)

For every profile and every unilateral replacement, changing g to
g^delta increases player j's payoff by a number in [0,delta] and changes
no other player's payoff. Returning the SAME laws to g consequently gives

    E_g(p)<=delta+delta^2,     Q(p)<=delta.                (4)

Neither (F) nor (J) is used for the perturbed table. We now apply them
only to the original game and the laws selected in (4).

Set rho_k=max(s_k-sum_i lambda_ki s_i,0). For every actual child law,
the original-table full-debt comparison is

    d_k(quiet(p)) <= sum_i lambda_ki d_i(p)+rho_k Q(p),
    d_i(quiet(p)) = d_i(p) for i in S.                    (5)

For completeness, fix an outsider pure deadline t and couple its gain
with the separate child replacements T_i -> min(T_i,t). Before the
deadline all gains vanish. At a first coalition A exactly at t, (J)
bounds its join gain by the weighted child gains. At a first finite
coalition after t, (F) gives the same bound. On child joint Never the
possible residual is rho_k. An outsider Never action has zero gain.
Integrating and bounding each child replacement by its full debt proves
(5), then taking the outsider supremum covers every replacement law.
This is a coupling of separate counterfactual experiments, not public
correlation in the played profile.

Put C=max(1,max_k sum_i lambda_ki) and R=max_k rho_k. By (4)-(5),

    E_r(quiet(p)) <= C(delta+delta^2)+R delta.             (6)

To make the selected laws finite, move their finite mass after a large
cutoff to Never. Choose the cutoff so that the sum tau of moved marginal
masses is at most delta^2. A product coupling bounds the change of each
prescribed payoff and each fixed unilateral-deviation payoff by
2M tau. Taking the full response supremum therefore increases regret by
at most 4M tau. The product Never probability increases by at most tau.
The resulting actual finite law p^delta satisfies

    E_r(quiet(p^delta))
        <=(C+R)delta+(C+4M)delta^2,
    Q(p^delta)<=delta+delta^2.                            (7)

Taking delta to zero proves (1). Every outsider remains literally Never.
The constants are computed from original rewards and the finite weights;
no estimate uniform in the finite deadline is assumed.

Terminal payoff vectors lie in a compact finite-dimensional reward cube.
A convergent subsequence of these actual profiles selects one fixed
target. The terminal-to-uniform family theorem retains members of the
same family as witnesses, each controlling all sufficiently long horizons
and all behavioral deviations. This proves the uniform conclusion with
the stated quantifier order.

## Five-kind withdrawal extension

Replace (F)-(J) by any of the original finite F/J certificates in
`WithdrawalFutureJoinRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`.
Each outsider may independently use patient, deadline, evaluated-security,
terminal-security, or cancellation withdrawal. The literal definitions
`debtWeight` and `neverExcess` produce fixed nonnegative coefficients
c_ki and residuals rho_k from original rewards and weights.

The exact theorem
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`
gives (5) with c_ki replacing lambda_ki for EVERY actual original child
profile. Patient and cancellation use summed operation weights; the other
three kinds use their maximum. The patient residual includes its original
Never bonus. Use C=max(1,max_k sum_i c_ki) in (6)-(7).

No perturbed F/J inequality or perturbed security floor is needed. The
finite-law conclusion and the existential fixed-target conclusion are
identical for every finite parent and child of cardinality at most three.
In particular this changes the strictly positive child-singleton
hypothesis of the Fin4 existence wrapper to a nonnegative one. It does
not strengthen its separate specified-child-target extension statement.

For a canonical own-singleton vector (1,0,0,0), the child {1,2,3}
automatically meets the nonnegative sign condition. Whenever its omitted
pivot has one of the original F/J certificates, (7) selects the three
finite opponent marginals required by the small pivot-repair source:
the quiet pivot is already a full-regret competitor, and minimizing the
actual pivot LP can only decrease that value.

## Source boundary and checks

The exact named inputs, inspected under their source imports, are:

- `QuittingThreePlayerStrategyClass.of_card_le_three` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazardAllSigns.lean`,
  with the actual terminal strategy-class definition in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazard.lean`;
- the original raw definitions and slack theorem cited above;
- `quittingTerminalExploitability_censored_le` in
  `UniformEquilibrium/Quitting/Paths/LateFiniteStoppingLawCensor.lean`;
- `quittingGame_uniformPayoffWitnesses_of_terminalNash_tendsto` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `exists_pivotRepairMass_objective_le_finiteMenu_exploitability` in
  `UniformEquilibrium/Quitting/Terminal/PivotRepairSmallValueSource.lean`.

The existing strict Fin4 consumer is
`quittingGame_exists_uniformEquilibriumPayoff_of_finFour_withdrawalFutureJoinFamily`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`.
Its existence conclusion also extends to this sign boundary by reward
perturbation and closure of equilibrium existence. The proof above records
an explicit original-law selection with both vanishing regret and
vanishing joint Never, and retains actual finite quiet witnesses without
perturbing any original reward certificate.

The positive residual cannot be deleted for arbitrary supplied child
profiles. In the one-child zero-reward example, an all-Never child has
Q=1 and debt zero, while an outsider with constant terminal reward one
has debt one. The theorem selects a different child law, such as sure
Quit, which has Q=0 and still has zero original child debt.

The nonnegative sign cannot be omitted from a universal quiet-source
theorem. Take one child with reward -1 on every nonempty coalition and
an outsider with constant terminal reward one. Zero weights satisfy
(F)-(J). If the outsider prescribes Never, child debt equals its finite
quit probability and outsider debt equals the child's Never probability.
Every quiet lift has full regret at least 1/2. The parent itself has an
equilibrium with the outsider quitting; this is a sharp failure of the
quiet-source sign extension, not a game without equilibrium.
The same test has four players by adding two further outsiders, also
with constant terminal reward one, and retaining the one-player child.

## Why a prescribed child target cannot be retained

Take child S={1,2} with rewards

    g({1})=(0,1),  g({2})=(1,0),  g({1,2})=(0,0).

All-Never is an exact child equilibrium with target (0,0). Add outsider
0 with reward one at every nonempty parent coalition, and set both child
rewards to zero on coalitions containing 0. Zero weights satisfy (F)-(J).

For any child laws let f_i be its probability of a finite quit, and u_i
its prescribed payoff. The Never deviations give B_1>=f_2 and B_2>=f_1.
Thus original quiet profiles whose regrets tend to zero and child payoffs
tend to (0,0) would have f_1,f_2->0. Their child joint-Never probability
would tend to one. But the outsider has cap one and prescribed payoff
1-Q, hence debt exactly Q. This contradicts vanishing parent regret.
The terminal/uniform bridge gives the same obstruction for quiet uniform
witnesses at a target extending (0,0).

Exact quiet equilibria nevertheless exist: player 1 Quit0 and player 2
Never gives child payoff (0,1), and the reversed choice gives (1,0).
This distinguishes selecting a child target from preserving an arbitrary
one. For a literal Fin4 version add a second outsider 3 with reward zero
everywhere, retain outsider 0's constant reward one, and set child rewards
to zero on every coalition containing 0 or 3. Both outsiders have valid
zero-weight F/J certificates and the same argument applies.

## Lean handoff

The new producer should first select an actual child family from
`QuittingThreePlayerStrategyClass.of_card_le_three` after increasing one
nonnegative own singleton by delta. Its output, evaluated in the ORIGINAL
child game, is the pair of bounds (4). The late-Never replacement proves
the scalar estimate (2); existing positive-singleton Never bounds may be
reused under the perturbed rewards. No child target is supplied to this
producer.

The parent adapter applies
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` with the
ORIGINAL reward table, certificate, and selected laws. Finite maxima of
the original coefficients yield (6). The independent-law censor theorem
then yields the actual finite family (7), still with quiet outsiders.
Finally use compact payoff selection and
`quittingGame_uniformPayoffWitnesses_of_terminalNash_tendsto` to retain
that family at one fixed parent target. The target's child coordinates
are those selected by the family, not arbitrary input data.

For canonical Fin4 pivot deletion, pass the resulting finite nonpivot
marginals through
`exists_pivotRepairMass_objective_le_finiteMenu_exploitability`. The quiet
pivot is the explicit low-regret competitor, so this source adapter needs
no extra optimal-pivot compatibility hypothesis.

No claim is made that every four-player table has these F/J certificates,
or that the resulting class is disjoint from other previously solved
classes.
