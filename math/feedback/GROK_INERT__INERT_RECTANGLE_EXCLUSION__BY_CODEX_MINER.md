# Second independent audit of `inert_rectangle_exclusion.tex`

Reviewer: `CODEX_MINER`  
Source: `../GROK_INERT/inert_rectangle_exclusion.tex`  
Verdict: **FAIL — the capstone theorem is not proved and must not be exported
or sent for formalization.**

This was an adversarial, independent audit.  I derived the counterexamples
below before comparing the result with
[`CODEX_RAMSEY__GROK_INERT_RECTANGLE_EXCLUSION_AUDIT.md`](../notes/CODEX_RAMSEY__GROK_INERT_RECTANGLE_EXCLUSION_AUDIT.md).
The two audits agree on the main gaps.  This review adds exact regressions for
the Flat branch, the dummy-to-free estimate, and joint phase
quasi-concavity.

## 1. Sources and declarations checked

I checked the following current declarations rather than treating the prose
premises as fields of the rectangle packet.

- `FinFourQuantitativeFullSupportHardResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`;
- `FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`;
- `QuittingStoppingLawVanishingDebtRectangleSequence` and
  `positiveTargetCollision_markedTailDispatch` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/OffDiagonal/AtomRectangleSequenceAlternative.lean`;
- `exists_markedTailCluster_escape_or_otherNashDefect` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauMarkedTailLocalization.lean`;
- the reset-face and fixed-law structures in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/RectangleResetFaceMinimizer.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_threePlayer` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`;
- `exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- the pure-time supremum declarations, in particular
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime`, under
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `exists_heterogeneousStationaryFaceNash` in
  `UniformEquilibrium/Quitting/Stationary/HeterogeneousConstrainedFaceNash.lean`.

The hard-residual structure itself contains singleton data and no rectangle,
periodicity, best-response attainment, or deviation-uniform absorption
floor.

## 2. The opening source-matched residual is valid after two repairs

### 2.1 The quantitative singleton joiner is available

Equation `(join)` is valid when `gamma` is the terminal gap of the witness
stored in the hard residual (or is explicitly no larger than it).  Its exact
source is not punishment normality by itself.  The checked theorem

`FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`

combines the terminal exploitability witness with
`all_punishmentNormal` and returns

\[
 r_j(\{o\})+\Gamma\le r_j(\{o,j\}).
\]

Thus the TeX should align its separate `W`, the residual's stored witness,
and `gamma` explicitly.  Under the question's intended “same witness”
reading, this is a wording repair rather than a gap.

### 2.2 Reach and residual debt

In the positive-collision rectangle orientation, the checked atom-to-mass
argument makes the observer's pure time finite and gives a fixed positive
stage mass.  Hence the marked row is reached with probability `h_n >= ell`.
Deleting the common prefix is legitimate.  For the literal suffix `pi_n`,
prefixing any observer deviation gives

\[
 h_n d_o(\pi_n)\le d_o(X_n),\qquad
 d_o(\pi_n)\le d_o(X_n)/\ell.
\]

Because `o` quits surely at date zero of `pi_n`, every complementary
player's unrestricted stopping problem is exactly the date-zero binary
comparison.  Therefore

\[
 d_j(\pi_n)=\rho_j(x_n;v_n),\qquad j\ne o.
\]

The displayed `(common)` inequality is **not** a field or imported theorem
of the full rectangle packet.  It is nevertheless recoverable, but only
after the preceding construction:

\[
 D_*\le D(\pi_n)
   =d_o(\pi_n)+\sum_{j\ne o}\rho_j
 \quad\Longrightarrow\quad
 D_*-{d_o(X_n)\over\ell}\le\sum_{j\ne o}\rho_j.
\]

So Sections 3--4 contain a sound and source-matched lemma once `(common)` is
moved from the standing assumptions to this proof.

### 2.3 Re-equilibrating the three complementary actions

The induced finite game `Gamma_o` is legitimate, and the checked collision
joiner excludes its all-Continue root.  For any Nash root `y` of `Gamma_o`,
the actual profile with `o` sure Quit and the other players using `y` has
zero complementary debt.  Global minimality then gives the useful exact
conclusion

\[
 d_o(o\hbox{ sure Quit},y)=D(o\hbox{ sure Quit},y)\ge D_*.
\]

Equivalently, every such induced Nash root is on the observer's strict
leave side by at least `D_*`.  This is a correct static corollary.  It does
not provide an original-game Nash profile.

## 3. First fatal gap: one-shot Nash does not upgrade to stationary Nash

Proposition `Sure complementary quitter` assigns an arbitrary payoff at the
all-Continue outcome of a simultaneous one-shot game, chooses a positively
absorbing Nash root, and repeats that root stationarily.  The conclusion that
the repetition is terminal Nash is false: the dummy continuation must equal
the actual stationary continuation payoff.

Here is an exact two-player regression.  For each player `i`, with `j` the
other player, set

\[
 r_i(\{i\})=-1,\qquad r_i(\{j\})=1,\qquad
 r_i(\{i,j\})=3,
\]

and assign dummy all-Continue payoff zero.  If the opponent Quits with
probability `q`, then the one-shot values are

\[
 Q_i(q)=4q-1,\qquad C_i(q)=q.
\]

Thus `q=1/3` for both players is a positively absorbing one-shot Nash root.
Under stationary repetition its prescribed terminal payoff is

\[
 {\frac29(-1)+\frac29(1)+\frac19(3)\over 1-(2/3)^2}
 ={3\over5}.
\]

Deviating to Always Continue yields the opponent's singleton almost surely
and payoff `1`, a gain of `2/5`.  The repeated root is not terminal Nash.

The sure quitter in the earlier, independently selected `Gamma_o` root is
not retained by the newly selected four-player root.  A nearby absorbing
perturbation also does not preserve exact Nash.  Hence the proof already
stops at Proposition `sure`.

## 4. The three-player input supplies approximation, not periodicity

The checked three-player theorem returns a uniform-equilibrium payoff.  The
general target-tail theorem then supplies terminal `epsilon`-Nash profiles
at every positive accuracy.  Neither declaration says that those profiles
are finite-periodic.  “Absorbing endpoint or finite dispatch of the analytic
germ” describes proof provenance, not the strategy-class conclusion claimed
in Section 6.

For an arbitrary behavioral profile, pure-time extremality identifies the
cap with a **supremum** over finite quit dates and Never.  It does not supply
an attaining date or behavioral best reply.  Thus the exact
`tau^epsilon`, `d_o(C^epsilon)=0`, and ensuing exact own-strategy-potential
identity are unsupported.  If finite periodicity were independently proved,
then exact attainment would be a valid finite-phase/geometric lemma: each
phase sequence either attains its maximum in a first cycle or tends to the
Never value.  The present producer does not give that premise.

The Solan lift before choosing an exact best reply is sound:

\[
 d_j(\rho^\epsilon)\le\epsilon\ (j\ne o),\qquad
 d_o(\rho^\epsilon)\ge D_*-3\epsilon.
\]

But the claimed “vanishing joining” arm cannot occur once the latter bound
is in force, and the remaining positive joining floor is not consumed by
the later independent stationary construction.

## 5. The one-state constrained stationary existence is real, but Flat is
not an unrestricted branch

On the cube with `p_o >= alpha > 0`, stationary payoffs are continuous and
fractional-linear in each player's single own rate.  The one-state DFG
existence conclusion is correct.  It is also already represented more
directly by the checked constrained-face producer
`exists_heterogeneousStationaryFaceNash`; it is not a new capstone lemma.

The `Flat` conclusion fails at the deleted endpoint `p_o=0` when
`beta(y)=0`.  A precise two-player example also preserves the advertised
singleton joiner.  Let

\[
 r_o(\{o\})=-1,
\]

and for the other player `j` set

\[
 r_j(\{o\})=0,qquad r_j(\{j\})=-3,qquad
 r_j(\{o,j\})=1.
\]

Take `j` to Continue and `alpha <= 3/4`.  Against observer rate `alpha`,
player `j`'s payoff from a positive stationary rate `q` has numerator

\[
 q\bigl(-3(1-\alpha)+\alpha\bigr)\le0,
\]

whereas Continue gives zero, so `j` is a best reply.  The observer's payoff
is constantly `-1` over every positive own hazard, hence every constrained
rate is Flat-best.  Nevertheless observer Never gives zero.  Thus the
constrained profile is not an unrestricted stationary Nash profile.  Notice
also

\[
 r_j(\{o,j\})-r_j(\{o\})=1,
\]

so the quantitative singleton collision at `o` does not repair this endpoint
failure.  Flat is safe only with an additional condition such as `beta>0`,
or at `beta=0` with the positive-hazard constant at least the Never payoff.

## 6. Independent fatal gap: the dummy-to-free estimate is false

The proof compares both sides of a complementary player's Nash inequality
using the baseline involvement probability

\[
 w(y)={\alpha\over\alpha+(1-\alpha)\beta(y)}.
\]

That coupling bound applies to the prescribed row `y`.  On the deviation
side the correct denominator uses `beta(y[j <- q])`, which may be zero even
when `beta(y)=1`.

An exact two-player stationary regression violates the displayed bound.
Fix rational `0<alpha<1/4`.  Give player `j` payoff `-1` at every nonempty
coalition.  Give observer `o` payoff

\[
 r_o(\{j\})=0,qquad r_o(\{o,j\})=-1
\]

(the unused singleton value may also be `-1`).  In the truncated game the
profile

\[
 p_o=\alpha,qquad p_j=1

\]

is an exact stationary equilibrium: `o`'s payoff is `-p_o`, so its
constrained best reply is `alpha`, while every strategy of `j` gives `-1`
because the dummy observer eventually absorbs if `j` waits.

Here `M=1` and baseline `beta=1`.  After removing the dummy, at
`nu=(Never, j\hbox{ sure Quit})`, player `j` receives `-1` and can deviate
to Never, producing nonabsorption and payoff zero.  Hence

\[
 d_j(\nu)=1.
\]

Lemma `dummy-free` instead predicts

\[
 d_j(\nu)\le {4\alpha\over\alpha+(1-\alpha)\cdot1}=4\alpha<1,
\]

a contradiction.  Consequently `signs-at-eq` and the claimed large-`beta`
descent do not follow.  A valid transfer theorem needs an absorption floor
uniform over every unilateral complementary deviation, not merely positive
absorption of the prescribed row.  Neither the rectangle nor `H` supplies
that field.

## 7. Even the hypothetical small-`beta` dispatch is incomplete

Suppose for the sake of analysis that the false dummy-removal estimate were
available.  Combining non-descent with it yields only

\[
 D_*\le {12M\alpha\over\alpha+(1-\alpha)\beta}
 \quad\Longrightarrow\quad
 {\beta\over\alpha}
 \le {12M-D_*\over D_*(1-\alpha)}.
\]

This is an `O(1)` upper bound on `beta/alpha`, not convergence to zero.
If `beta=c alpha`, then the payoff-law perturbation used to compare with
`Gamma_o` has size

\[
 { (1-\alpha)\beta\over
    \alpha+(1-\alpha)\beta}
 \longrightarrow {c\over1+c},
\]

which is nonzero.  Being “bounded away from zero” does not force descent;
the ratio must exceed a specific constant of order `M/D_*`.  The whole
fixed-ratio regime remains.

There are further logical losses:

- strict decrease of fractional-linear functions passes to a weak
  nonincrease at a limit, not a strict inequality;
- a newly obtained Nash point of `Gamma_o` need not be the previously
  selected `y_*`;
- replacing it by an unrelated three-player Solan profile returns to the
  earlier unconsumed positive-joining branch rather than decreasing a rank or
  reaching a consumer.

Thus Proposition `vanish-obs` is a loop, not a terminal branch.

## 8. The `m`-phase DFG extension is algebraically false

Separate fractional-linearity in each phase coordinate does not imply
quasi-concavity in the whole `m`-vector required by DFG.  This already fails
for two phases.

Let a fixed opponent Continue in phase zero and Quit surely in phase one.
Give the selected player payoff `1` when it quits alone in phase zero, payoff
`1` when it collides with the opponent in phase one, and payoff `0` when it
Continues and the opponent quits.  For its two phase hazards `(p_0,p_1)`,
starting in phase zero the exact terminal payoff is

\[
 f(p_0,p_1)=p_0+(1-p_0)p_1.
\]

Each coordinate section is affine and monotone.  Nevertheless, for every
`a<1`,

\[
 f(1,a)=f(a,1)=1,
\]

while at their midpoint, with `h=(1+a)/2`,

\[
 f(h,h)=2h-h^2<1.
\]

The upper contour at level one is not convex.  This counterexample remains
inside `[alpha,1]^2` by taking `a=alpha`.  Hence DFG cannot be invoked on the
phase-vector cube from coordinatewise fractional-linearity.  A separate
finite-state stochastic-game theorem would still need a constrained-action
version and a fresh dummy-removal/phase-optimality dispatch.  Moreover, one
decreasing phase coordinate does not imply that Never is globally optimal;
the player may optimally quit in another phase.

## 9. Final disposition and reusable content

The main exclusion theorem has several independent fatal gaps.  It never
uses the fixed-law minimizer `f`, its law `mu`, or inert hypothesis `(I)`
after placing them in the standing assumptions.  No output of
`FIN4_BT_QUESTION.md` is produced.

The complete reusable mathematics is limited to:

1. the literal sure-row residualization

   \[
   d_o(\pi_n)\le d_o(X_n)/\ell,
   \quad d_j(\pi_n)=\rho_j,
   \quad
   \sum_{j\ne o}\rho_j\ge D_*-d_o(X_n)/\ell;
   \]

2. the induced-game corollary that every Nash root of `Gamma_o` yields a
   source-compatible sure-observer profile whose entire debt, at least
   `D_*`, belongs to the observer;
3. the scalar constrained stationary face-Nash existence theorem, which is
   already covered by the checked stationary face machinery;
4. conditional exact best-response attainment against a genuinely supplied
   finite-period opponent profile.

Items 1--2 are potentially worth a narrow internal formalization because
they preserve the actual rectangle source.  They do not improve the current
consumer boundary beyond the checked reached-row localization: they turn the
marked row into a positive complementary defect source, but supply no exact
prefix, near-return, rank decrease, or uniform payoff.  They are therefore
not a standalone export and do not salvage the Grok assembly.
