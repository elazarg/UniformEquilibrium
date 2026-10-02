# Simon normalized-motion stationary-prefix producer

Authors: `CODEX_NOETHER` (Proposition 44); packet assembled by `CODEX_MINER`

Independent reviews:
[CODEX_GAUSS, Round 16](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_GAUSS__ROUND_16.md),
[CODEX_CEDAR, Round 12](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_CEDAR__ROUND_12.md)

## Exact statement

Let \(I\) be a nonempty finite set of players and let

\[
  v:\{S\subseteq I:S\ne\varnothing\}\longrightarrow \mathbb R^I
\]

be a finite quitting-game reward table. At every live stage, each player
independently chooses Quit or Continue. The first nonempty coalition \(S\) of
quitters absorbs and pays \(v(S)\); eternal continuation pays \(0\).

For a product row \(p=(p_i)_{i\in I}\in[0,1]^I\), put

\[
 q(p)=1-\prod_{i\in I}(1-p_i)
\]

and let \(f(r,p)\) be the one-stage expected payoff when the all-Continue
outcome has continuation vector \(r\). Write

\[
 \chi_i=\inf_{\tau_{-i}}\sup_{\sigma_i}
   U_i(\sigma_i,\tau_{-i})
\]

for player \(i\)'s quitting punishment value, where both the infimum and the
supremum range over unrestricted behavioral strategies.

A vector \(r\in\mathbb R^I\) is **\(\gamma\)-rational** if

\[
 r_i\ge \chi_i-\gamma\qquad(i\in I).
\]

For player \(i\), let \(A_i(p)\) be the one-stage payoff obtained by forcing
\(i\) to Quit against \(p_{-i}\), and let \(B_i(r,p)\) be the payoff obtained
by forcing \(i\) to Continue, using \(r_i\) if all opponents also Continue.
The row \(p\) is **support-locally \(\gamma\)-optimal at \(r\)** if, for every
\(i\),

\[
\begin{aligned}
 p_i>0&\Longrightarrow A_i(p)\ge B_i(r,p)-\gamma,\\
 p_i<1&\Longrightarrow B_i(r,p)\ge A_i(p)-\gamma.
\end{aligned}
\]

Use the maximum norm
\(\lVert x\rVert_\infty=\max_{i\in I}|x_i|\).

**Normalized-motion producer.** Assume that the game does not have instant
approximate equilibria in the following sense: it is not true that, for every
\(a>0\), there are a player \(j\), a first-stage product row with \(j\) quitting
surely, and an \(a\)-punishment of \(j\), whose splice is an \(a\)-equilibrium
against all unilateral behavioral deviations.

Suppose there are sequences

\[
 \gamma_k>0,\qquad \gamma_k\longrightarrow0,\qquad
 r_k\in\mathbb R^I,\qquad p_k\in[0,1]^I
\]

such that, for every \(k\),

1. \(r_k\) is \(\gamma_k\)-rational;
2. \(p_k\) is support-locally \(\gamma_k\)-optimal at \(r_k\);
3. \(q_k:=q(p_k)>0\); and
4. with \(y_k=f(r_k,p_k)\),

   \[
     \lVert y_k-r_k\rVert_\infty<\gamma_kq_k.
   \]

Then the game has stationarily generated approximate equilibria, with the
punishment and equilibrium errors quantified independently: for every
\(\delta>0\) and \(\varepsilon>0\), there are a row \(p\), a natural number
\(M\) with \(1<M\), a player \(j\), and a punishment profile \(P\) such that

1. every unrestricted behavioral response of \(j\) against \(P_{-j}\) pays at
   most \(\chi_j+\delta\); and
2. the profile which plays \(p\) at every stage \(t\le M\) and, if still live,
   plays \(P\) from stage \(M+1\) onward is an
   \((\varepsilon+\delta)\)-equilibrium against every unilateral behavioral
   deviation.

The theorem has the following unconditional contrapositive form, which is the
normalized-motion clause used by the corrected Simon compact alternative.

**Fixed normalized-motion lower bound.** If a finite quitting game has neither
instant approximate equilibria nor stationarily generated approximate
equilibria, then there is \(\rho\) with \(0<\rho<1\) such that every
\(\rho\)-rational vector \(r\) and every support-locally
\(\rho\)-optimal row \(p\) satisfy

\[
 \rho q(p)\le \lVert f(r,p)-r\rVert_\infty.       \tag{1}
\]

No feasibility or compactness assumption on \(r\) is needed for this clause.
In particular, it applies to the smaller near-feasible carrier occurring in
Simon (2012), Lemma 2.1.

## Conjecture-facing change

The maintained Simon compact-alternatives frontier names the
**normalized-motion producer** as missing. The near-total-absorption rounding
branch is checked, while the implication from vanishing normalized motion to
the stationarily generated branch was previously only a two-sentence paper
sketch and an ordinary-mathematics note. The producer above supplies that
implication with an explicit horizon and full behavioral-deviation bounds.
Equivalently, (1) proves the normalized-motion lower-bound clause under the
two branch exclusions.

This strictly narrows the frontier recorded in
[`docs/FRONTIER.md`](../../../docs/FRONTIER.md) and
[`docs/TOOLKIT.md`](../../../docs/TOOLKIT.md): after formalization, the words
“normalized-motion producer ... remain[s] supplied” can be removed. The
conference question inventory already records that this reviewed proof exists
but that its production adapter is missing; see
[`questions/README.md`](../questions/README.md).

What remains of the corrected compact lemma is separate: the
near-total-absorption clause must be combined at one common scale, and the
positive-solo/sign-pattern clause remains outside this packet. Nothing here
produces a finite orbit or proves the full Simon route.

## Definitions and assumptions

### Probability, stopping, and payoff mode

At a live stage the players' Bernoulli actions are conditionally independent.
Absorption occurs at the first stage at which at least one player Quits. The
terminal payoff is the expectation of \(v(S)\) at that first absorbing
coalition; the payoff on the event of Never absorbing is \(0\). Thus this is
the production terminal-payoff semantics, not a discounted or Cesàro payoff.

Choose

\[
 B=\max\bigl(1,\max_{S\ne\varnothing,\,i\in I}|v(S)_i|\bigr).
\]

Every prescribed or deviating terminal payoff, and every payoff conditional
on absorption in a product row, lies in \([-B,B]\).

### Observation and behavioral agency

Strategies may depend on the complete observed finite history and may
randomize freshly at every stage. A unilateral deviator replaces their entire
behavioral strategy; they are not restricted to a stationary row, a one-shot
deviation, a deterministic controller, or bounded memory. Along the unique
live history of a quitting game, such a deviation induces an arbitrary
time-indexed sequence of Quit hazards. Conversely every such hazard sequence
is induced by a behavioral strategy. The exact production pure-time theorem
then identifies the supremum over all of these deviations with the supremum
over deterministic quit dates together with Never.

No public correlation device or correlation between different players'
stage randomizations is assumed. The product row is the same independent
root used by the production quitting-game model.

### Instant and stationary-prefix branches

An \(a\)-punishment of \(j\) is a behavior profile of the other players for
which every behavioral response of \(j\) is bounded above by \(\chi_j+a\).
An instant witness uses a row with one sure quitter on the first stage and
then such a punishment. A stationary-prefix witness uses one product row at
the inclusive dates \(0,1,\ldots,M\), followed at date \(M+1\) by a shifted
punishment profile. These are respectively the production predicates
`QuittingInstantPunishmentεEquilibriumExistence` and
`QuittingStationarilyGeneratedApproximateEquilibria`, up to harmless
rescaling of the single error in the instant predicate.

The explicit \(\gamma_k\)-rationality hypothesis is essential. “Rational”
does not mean rational-number coordinates and does not mean exact individual
rationality. It means the scale-indexed inequalities
\(r_{k,i}\ge\chi_i-\gamma_k\).

## Source correspondence

### Original paper

[Simon, *A Topological Approach to Quitting Games* (2012)](../../../literature/SIMON_2012__A_TOPOLOGICAL_APPROACH_TO_QUITTING_GAMES.pdf),
Section 2.3, Lemma 2.1, p. 185, states that failure of the normalized-motion
bound along errors tending to zero gives stationarily generated approximate
equilibria. Its proof sketch says to take a convergent subsequence and, if
necessary, punish at an advanced stage a player who has largest quitting
probability. The paper does not display the pure-time recursion, the exposure
window, or a bound uniform in the ratio
\(\max_i p_{k,i}/\gamma_k\).

Accordingly, the theorem-level implication is not claimed as novel over
Simon. The new formalization-worthy content is the complete quantitative
proof, the explicit error ledger, the zero-denominator repair, and the exact
unrestricted-deviation bridge needed to turn the source sketch into a checked
production theorem.

### Current literature transcription

[`Literature/Simon2007.lean`](../../../Literature/Simon2007.lean) contains the
source-shaped definitions `QuitProbability`, `QuittingOneStagePayoff`,
`ForcedQuitPayoff`, `ForcedContinuePayoff`, `EpsilonRow`, `IsRational`,
`StationaryPrefixThenPunish`, `IsPunishmentWithin`, and
`HasStationarilyGeneratedApproximateEquilibria`. It also contains the checked
local compiler `instantProfile_isQuitEpsilonEquilibrium` and the scale
exclusion `exists_scale_without_sure_quitter_of_not_instant` in that notation.

The capstone `lemma5_corrected_2012` in that file is a `sorry` theorem in a
non-production literature transcription. It must not be used to formalize
this packet. The proof below supplies only its normalized-motion component.

### Current production correspondence

The exact production notions already exist:

- `quittingRootAbsorptionMass`, `quittingRootSuccessorPayoff`,
  `quittingRootQuitPayoff`, `quittingRootContinuePayoff`, and
  `quittingRootEndpointDifference` express \\(q,f,A,B,A-B\\);
- `QuittingSimonRationalPayoffAt` is the \\(\\gamma\\)-rationality floor;
- `IsQuittingRootSupportApproxNash` is exactly the two support-local endpoint
  conditions;
- `quittingStationaryPrefixThenRoots`,
  `IsQuittingRootSequencePunishmentWithin`, and
  `QuittingStationarilyGeneratedApproximateEquilibria` are the target syntax
  and semantics; and
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` gives exact
  unrestricted behavioral pure-time extremality.

The relevant checked files are
[`SuppliedCorrespondence.lean`](../../../UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/SuppliedCorrespondence.lean),
[`SupportEnlargementAlternative.lean`](../../../UniformEquilibrium/Quitting/Boundary/Repair/SupportEnlargementAlternative.lean),
[`StationarilyGeneratedBranch.lean`](../../../UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedBranch.lean),
[`BehaviorPureTimeExtremality.lean`](../../../UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean), and
[`Stationary/Payoff.lean`](../../../UniformEquilibrium/Quitting/Stationary/Payoff.lean).

[`CompactQuantitativeAlternatives.lean`](../../../UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/CompactQuantitativeAlternatives.lean)
checks the other, near-total-absorption rounding branch and explicitly says
that the normalized-motion producer remains isolated. Its
`exists_oneStagePunishedProfile_of_rational_support_sureQuitter` is also the
narrow checked ingredient needed below to derive a no-sure-quitter scale from
failure of the instant branch.

[`PositiveAbsorptionStationarySplice.lean`](../../../UniformEquilibrium/Quitting/Classification/Existence/PositiveAbsorptionStationarySplice.lean)
is not a duplicate. It starts from a full stationary approximate equilibrium.
The rows in this packet are only support-locally optimal at a nearby carrier;
the selected largest-hazard player need not have a uniformly small stationary
Never gain. The exposure-window argument below is precisely what repairs that
missing global stationary bound.

## Proof

Fix \(\delta>0\) and \(\varepsilon>0\). We prove the producer first.

### 1. Excluding sure quitters at one fixed scale

Failure of the instant branch implies that there is \(\sigma>0\) such that no
\(\sigma\)-rational, support-locally \(\sigma\)-optimal row has a sure quitter.

Indeed, if no such \(\sigma\) existed, then for every \(a>0\) there would be
an \(a/4\)-rational, support-locally \(a/4\)-optimal row with a sure quitter.
Choose an actual \(a/4\)-punishment of that quitter. The one-stage endpoint
compiler gives a \(2(a/4)+a/4=3a/4\)-equilibrium. Relaxing both its punishment
cap and equilibrium error to \(a\) gives an instant witness at every positive
\(a\), a contradiction.

For all sufficiently large \(k\), \(\gamma_k\le\sigma\). Rationality and
support-local optimality are monotone in their error parameter, so every such
\(p_k\) has \(p_{k,i}<1\) for every \(i\).

### 2. Conditional stationary payoff and normalized motion

Fix one such \(k\), and abbreviate

\[
 \gamma=\gamma_k,\quad p=p_k,\quad q=q(p),\quad r=r_k,
 \quad y=f(r,p).
\]

Let \(w_i(p)\) be the expected one-stage terminal reward contribution, with
the all-Continue outcome contributing zero, and define

\[
 h_i=\frac{w_i(p)}q.
\]

Since \(q>0\), \(h\) is the payoff of the absorbing stationary profile \(p\).
The affine one-stage equation gives the exact identities

\[
 f(h,p)=h,
 \qquad f(r,p)-r=q(h-r).
\]

Consequently

\[
 d:=\lVert h-r\rVert_\infty<\gamma.                 \tag{2}
\]

For each \(i\), put

\[
 c_i=\prod_{\ell\ne i}(1-p_\ell),\qquad
 g_i=A_i(p)-B_i(h,p),\qquad
 \zeta=\gamma+d<2\gamma.
\]

Only player \(i\)'s continuation coordinate changes between
\(B_i(r,p)\) and \(B_i(h,p)\), and its coefficient is \(c_i\le1\). The two
support conditions, together with \(p_i<1\), therefore give

\[
 g_i\le\zeta,                                        \tag{3}
\]

and, whenever \(p_i>0\),

\[
 -g_i\le\zeta.                                      \tag{4}
\]

The stationary fixed-point equation, separated according to player \(i\)'s
own Bernoulli action, is

\[
 h_i=p_iA_i(p)+(1-p_i)B_i(h,p),
 \qquad B_i(h,p)-h_i=-p_ig_i.                       \tag{5}
\]

### 3. Exact deterministic quit-time values

Against stationary opponents, let \(V_{i,t}\) be the payoff when \(i\)
Continues at dates \(0,\ldots,t-1\) and Quits at date \(t\). Iterating the
affine forced-Continue map gives, for every finite \(t\),

\[
 V_{i,t}-h_i
   =c_i^t(1-p_i)g_i-p_ig_i\sum_{s<t}c_i^s.          \tag{6}
\]

This finite-sum form is valid also at \(c_i=1\). If \(c_i<1\), the Never
value is obtained by dropping the first term and replacing the finite sum by
\(1/(1-c_i)\). If \(c_i=1\), the stationary Never payoff is \(0\) and is not
asserted to be that limit; the only occurrence that matters below is handled
separately.

Choose \(j\) with largest marginal

\[
 m=p_j=\max_i p_i.
\]

Because \(q>0\), \(m>0\). For \(i\ne j\), player \(j\) is an opponent, hence

\[
 1-c_i\ge m,\qquad p_i\le m.                        \tag{7}
\]

If \(g_i\ge0\), (6) bounds every deterministic quit-time gain by
\(g_i\le\zeta\). If \(g_i<0\), its positive part is at most

\[
 \frac{p_i(-g_i)}{1-c_i}\le\zeta.                  \tag{8}
\]

When \(p_i=0\), the numerator in (8) is exactly zero, so (4) has not been
used outside its support hypothesis. Thus every finite quit date and Never
for every \(i\ne j\) gains at most \(\zeta\) against the infinite stationary
profile.

For \(j\), a Quit before date \(L\) gains at most \(\zeta\) if \(g_j\ge0\),
and at most

\[
 Lm\zeta                                                \tag{9}
\]

if \(g_j<0\). This uses the finite sum in (6), not division by
\(1-c_j\). If \(c_j=1\), all opponents Continue surely. Equation (5), together
with \(p_j=m>0\), then forces \(g_j=0\), so there is no hidden zero-denominator
case.

### 4. Punishment splice

By the definition of \(\chi_j\) and boundedness of terminal payoffs, there is
an actual punishment profile \(P\) such that every behavioral response of
\(j\) against \(P_{-j}\) pays at most \(\chi_j+\delta\). Rationality and (2)
give

\[
 \chi_j+\delta-h_j\le\delta+\gamma+d.               \tag{10}
\]

If a pure-time response of \(j\) Continues through all \(L\) stationary
dates, let \(T_j\le\chi_j+\delta\) be its conditional payoff in the punishment
tail. Iterating the forced-Continue map gives

\[
 B_j^L(T_j)-h_j
 =c_j^L(T_j-h_j)-p_jg_j\sum_{s<L}c_j^s.
\]

Equations (4), (9), and (10) imply that every such response, including Never,
pays at most

\[
 h_j+Lm\zeta+\delta+\gamma+d.                       \tag{11}
\]

The same bound covers Quit dates before the splice because the window chosen
below has \(Lm>1\).

The prescribed prefix profile differs from the infinite stationary profile
only if all players Continue for the first \(L\) dates. Therefore its payoff
differs coordinatewise from \(h\) by at most

\[
 2B(1-q)^L\le2B(1-m)^L.                             \tag{12}
\]

For \(i\ne j\), replacing the stationary continuation after date \(L-1\) by
the punishment tail changes any fixed pure-time deviation payoff by at most
another \(2B(1-m)^L\): independently of \(i\)'s behavior, the fixed opponent
\(j\) must Continue at each of the \(L\) prefix dates. Combining (8) and (12),
the regret of every nonselected player is at most

\[
 \zeta+4B(1-m)^L.                                   \tag{13}
\]

For the selected player, (11) and the prescribed-payoff half of (12) bound
regret by

\[
 \delta+Lm\zeta+\gamma+d+2B(1-m)^L.                \tag{14}
\]

### 5. Exposure window and arbitrary deviations

Take \(\gamma<1/4\), put

\[
 R=\gamma^{-1/2},\qquad L=\left\lceil\frac Rm\right\rceil.
\]

Then \(L\ge3\), \(R\le Lm<R+1\), and

\[
 (1-m)^L\le e^{-Lm}\le e^{-R},
 \qquad Lm\zeta<2\sqrt\gamma+2\gamma.               \tag{15}
\]

The right sides of (13) and of (14) after subtracting \(\delta\) tend to zero
as \(k\to\infty\), regardless of the rate of \(m/\gamma\). Choose \(k\) so
large that

\[
 \zeta+4Be^{-R}<\varepsilon
\]

and

\[
 Lm\zeta+\gamma+d+2Be^{-R}<\varepsilon.
\]

Set \(M=L-1\). Since the prefix convention is inclusive, this gives exactly
\(L\) stationary dates, and \(L\ge3\) gives \(1<M\).

Equations (13)--(15) bound every deterministic quit date and Never. Exact
pure-time extremality now upgrades these pointwise bounds to the supremum over
every unilateral behavioral strategy. The spliced profile is therefore an
\((\varepsilon+\delta)\)-equilibrium with the required \(\delta\)-punishment.
This proves the normalized-motion producer.

### 6. Fixed lower bound by contrapositive

Assume now that neither the instant branch nor the stationarily generated
branch exists. If (1) failed for every \(0<\rho<1\), choose, for
\(\gamma_k=1/(k+2)\), a \(\gamma_k\)-rational vector and a support-locally
\(\gamma_k\)-optimal row satisfying

\[
 \lVert f(r_k,p_k)-r_k\rVert_\infty
   <\gamma_kq(p_k).
\]

The strict inequality forces \(q(p_k)>0\). The producer would then give the
stationarily generated branch, a contradiction. Hence one fixed
\(0<\rho<1\) satisfies (1). This proves the corollary. ∎

## Boundary tests

1. **Exact zero table.** If every terminal reward is \(0\), take \(r=0\) and
   any row with \(q(p)>0\). Then \(f(r,p)=h=0\), all endpoint differences are
   zero, and every displayed identity and regret bound is exact. Such a game
   also has instant equilibria, so it tests the algebra while confirming that
   the no-instant hypothesis is a branch exclusion rather than a hidden
   algebraic premise.

2. **Inactive nonselected player.** If \(p_i=0\), the potentially positive
   term for \(g_i<0\) is
   \(p_i(-g_i)/(1-c_i)=0\). This is the exact boundary at which the reverse
   support inequality (4) is unavailable; the proof never invokes it.

3. **No opponent hazard for the selected player.** This includes the
   one-player game. Then \(c_j=1\), and (5) with \(p_j>0\) gives \(g_j=0\).
   The proof neither divides by \(1-c_j\) nor identifies stationary Never with
   a false geometric limit.

4. **Arbitrarily small largest marginal.** The attempted rate falsifier
   \(\gamma_k=k^{-2}\), \(m_k=\gamma_k^2=k^{-4}\) makes
   \(m_k/\gamma_k\to0\). Nevertheless \(R_k=k\) and one may take
   \(L_k=k^5\), so \(L_km_k=k\) and
   \(L_km_k\zeta_k<2/k\). Only exposure \(Lm\), not calendar length, enters
   the incentive error.

5. **All-Continue row.** If \(q(p)=0\), \(h=w/q\) is undefined and no largest
   positive marginal exists. The producer excludes this case explicitly. In
   the contrapositive lower bound, however, (1) is automatic at \(q=0\), so no
   source case is lost.

6. **Sure quitter.** A sure-quitter row can make \(p_i<1\) false and remove the
   Continue-support estimate (3). The no-instant assumption is used exactly
   once to rule out such rows at a fixed small scale; the checked one-stage
   compiler shows that failure of this exclusion would itself produce the
   instant branch.

7. **Rationality repair.** Without
   \(r_j\ge\chi_j-\gamma\), normalized motion controls \(h-r\) but gives no
   upper bound on \(\chi_j-h_j\). The punishment-tail estimate (10) can then
   fail by an arbitrary amount. This is why scale-indexed
   \(\gamma_k\)-rationality is an explicit hypothesis, rather than the
   ambiguous phrase “rational vectors.”

8. **Inclusive horizon.** The constructed profile has \(L\) copies of the row
   at dates \(0,\ldots,L-1\). The production argument must pass
   `horizon = L - 1`; passing \\(L\\) would insert one extra stationary date.

The two independent reviews explicitly tried the dangerous cases
\(p_i=0\), \(c_j=1\), Never, \(m/\gamma\to0\), arbitrary post-splice behavior,
and the inclusive horizon. `CODEX_CEDAR` found the missing scale-indexed
rationality hypothesis in an earlier version; it is present in the current
source statement and throughout this packet. `CODEX_GAUSS` found that the
stationary-Never limit sentence had to be restricted to \(c_i<1\); that repair
is present in Step 3. Both reviewers then reported no remaining mathematical
objection. These constitute two independent falsification audits of the
unrestricted strategy-class conclusion.

## Adapter and consumer

### Actual-data adapter

The input is not a hypothetical certificate type. Failure of a uniform
normalized-motion lower bound supplies it directly: choose any positive
\\(\\gamma_k\\to0\\), and at each scale choose the actual rational support row
that violates
\\(\\gamma_kq(p)\\le\\lVert f(r,p)-r\\rVert_\\infty\\). Strict failure automatically
gives positive absorption. Step 6 is the resulting arbitrary-game
contrapositive and is the precise narrowing of the named live obligation.

In production notation the data are
`QuittingSimonRationalPayoffAt reward γ tail`,
`IsQuittingRootSupportApproxNash reward tail γ root`, and the strict
normalized displacement inequality for
`quittingRootSuccessorPayoff` and `quittingRootAbsorptionMass`. No finite
orbit, path, or supplied semantic witness is assumed.

### Checked downstream consumer

The output lands exactly in
`QuittingStationarilyGeneratedApproximateEquilibria`. The checked theorem
`quittingApproximateEquilibriumExistence_of_stationarilyGenerated` turns it
into behavioral approximate-equilibrium existence. The checked theorem
`quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence`
then yields a terminal uniform-equilibrium payoff. Both are in
[`StationarilyGeneratedBranch.lean`](../../../UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedBranch.lean).

These consumers are already checked Lean. The normalized-motion producer and
the notation bridge described here are ordinary mathematics until an external
formalizer implements them.

## Lean handoff

The narrowest implementation belongs beside the near-total branch in
`UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/CompactQuantitativeAlternatives.lean`
or in one new sibling imported there. It should not use
`Literature.Simon2007.lemma5_corrected_2012`.

A useful theorem decomposition is:

1. `exists_noSure_support_scale_of_not_instant`: from
   `¬QuittingInstantPunishmentεEquilibriumExistence reward`, obtain a positive
   scale at which rational support-local rows have no sure quitter. Prove it
   from `exists_oneStagePunishedProfile_of_rational_support_sureQuitter` and
   error monotonicity.
2. Define the stationary conditional payoff as
   `fun who => quittingTerminalPayoff reward
   (quittingStationaryProfile reward root) who`. Use
   `quittingTerminalPayoff_stationary_eq_absorbingContribution_div` and
   `quittingRootExpectedPayoff_eq_absorbingContribution_add` for the identities
   in Step 2; do not introduce division when absorption is zero.
3. Prove the scalar forced-Continue recursion (6), preferably first with
   `Finset.sum (Finset.range t) (fun s => c ^ s)`. Split \\(c<1\\) only for the
   infinite stationary Never formula.
4. Package the largest-marginal inequalities (7)--(9) as small scalar lemmas.
   Preserve the support guard on the estimate for (-g_i).
5. Use `exists_stationaryRoot_cap_lt_punishmentValue_add` to choose a constant
   punishment row, turn it into a constant root sequence, and discharge
   `IsQuittingRootSequencePunishmentWithin` with the existing stationary-cap
   theorem.
6. State the main producer directly with conclusion
   `QuittingStationarilyGeneratedApproximateEquilibria reward`. Its source
   predicate, if named, should quantify actual `tail` and `root` data at every
   positive threshold rather than carry the desired conclusion as a field.
7. State the fixed-\\(\\rho\\) corollary separately by classical
   contraposition. This is the declaration the compact-alternatives frontier
   can cite.

Likely reusable checked declarations include:

- `QuittingSimonRationalPayoffAt.mono` and
  `IsQuittingRootSupportApproxNash.mono`;
- `quittingRootSuccessorPayoff_eq_endpointMix`,
  `quittingRootQuitPayoff_sub_successorPayoff`, and
  `quittingRootContinuePayoff_sub_successorPayoff`;
- `quittingTerminalPayoff_stationary_eq_absorbingContribution_div`;
- `quittingJointSurvivalWeight_const` and
  `quittingOpponentSurvivalWeight_const_le_pow_continue`;
- `isQuittingRootSequencePunishmentWithin_iff_bestReplyValue`;
- `isεQuittingRootSequenceNash_iff_isεAsymptoticNash`; and
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime`.

The smallest useful finite tests are `ι = Fin 1` for \\(c_j=1\\), `ι = Fin 2`
with one inactive nonselected marginal, a row with one sure quitter for the
scale-exclusion lemma, and an abstract arithmetic test with
\\(\\gamma=k^{-2},m=k^{-4},L=k^5\\). The final theorem must quantify over
arbitrary hazard sequences or behavioral strategies; a bounded-controller
test is not an adequate substitute.

## Scope and nonclaims

- This packet contains Proposition 44 only, together with its direct
  contrapositive. It does not export Proposition 45 or any later proposition
  from the source notebook.
- It does not prove that arbitrary game data produce a vanishing-motion
  sequence. It proves the exact alternative: such a sequence produces the
  stationary-prefix branch, and exclusion of that branch gives one uniform
  normalized-motion lower bound.
- It does not prove the positive-solo/sign-pattern clause, the common-
  \\(\\rho\\) conjunction with the absorption cap, corrected Lemma 2.1 in full,
  Simon's finite-orbit equivalence, or the finite-quitting uniform-equilibrium
  conjecture.
- It does not assert a stationary approximate equilibrium. The output is the
  corrected, weaker stationary-prefix-then-punishment shape.
- It does not restrict deviations to stationary, Markov, deterministic,
  finite-state, or bounded-memory strategies.
- It is proved in Lean by the declarations listed below. The result remains a
  normalized-motion alternative; it does not supply rational support-local
  rows, near-feasibility, or the positive-solo clause.

## Checked Lean realization

The production implementation is
`UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/NormalizedMotionStationaryPrefixProducer.lean`.
Its principal declarations are:

- `HasArbitrarilySmallQuittingNormalizedMotionRows`, the actual row source;
- `exists_stationaryPrefix_punishment_nash_of_normalizedMotionRow`, the
  quantitative one-row producer;
- `stationarilyGenerated_of_arbitrarilySmallNormalizedMotionRows`, the full
  source-to-stationary-prefix theorem;
- `HasQuittingNormalizedMotionLowerBoundAt`, whose definition deliberately
  contains no feasibility or existence assertion;
- `exists_normalizedMotionLowerBound_of_not_branches`, the fixed positive
  scale contrapositive; and
- `instant_or_stationarilyGenerated_or_normalizedMotionLowerBound`, the
  reader-facing trichotomy.

Evidence seals: **M**, **L**, **A**, and **C**. The source rows retain the
literal rationality, support-locality, positive absorption, and normalized
motion data; the output is the production stationary-prefix punishment
object with Nash inequalities against arbitrary behavioral hazards. The
fixed-scale branch has no **A** seal by design: it is a universal obstruction
and does not claim the quantified row class is inhabited.
