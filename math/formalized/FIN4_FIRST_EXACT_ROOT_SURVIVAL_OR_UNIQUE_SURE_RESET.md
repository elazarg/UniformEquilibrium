# First exact-root debt descent leaves a delayed paid fork or a unique-sure reset

Authors: CODEX_NEGATIVE_CERTIFICATE

Independent reviews:
[CODEX_SPINOZA](../feedback/CODEX_NEGATIVE_CERTIFICATE__FIRST_EXACT_ROOT_SURVIVAL_AND_UNIQUE_SURE_RESET__BY_CODEX_SPINOZA.md)
and
[CODEX_HAHN](../feedback/CODEX_NEGATIVE_CERTIFICATE__FIRST_EXACT_ROOT_SURVIVAL_AND_UNIQUE_SURE_RESET__BY_CODEX_HAHN.md).

## Exact statement

Let \(I=\operatorname{Fin}4\), let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a bounded quitting reward table, and let Never pay zero. Suppose the game
has no uniform-equilibrium payoff. Let \(\mathcal C(r)\) be the compact
terminal-semantic carrier, let

\[
 X=(u,B),\qquad d_i(X)=B_i-u_i,\qquad D(X)=\sum_i d_i(X),
\]

and suppose

\[
 D_*:=\min_{X\in\mathcal C(r)}D(X)>0.                         \tag{1}
\]

Assume the actual-data adapter supplies stationary behavioral profiles
\(\tau_n\), one fixed player \(b\), and one fixed \(\gamma>0\). Write

\[
 X_n=(u_n,B_n)=\operatorname{Sem}(\tau_n),\qquad
 d_{n,i}=d_i(X_n),\qquad s_b=r_b(\{b\}).
\]

For all sufficiently large \(n\), literal Quit at date zero is an attained
complete behavioral cap for \(b\) at \(\tau_n\), with

\[
 d_{n,b}\ge\gamma,\qquad B_{n,b}\longrightarrow s_b.          \tag{2}
\]

Choose \(M>0\) such that every reward coordinate and every \(u_{n,i}\) has
absolute value at most \(M\), and put

\[
 \delta_b=\min\{\gamma/2,\gamma^2/(16M)\}>0,\qquad
 a=\min\{1,\gamma/(16M)\}>0.                                 \tag{3}
\]

At each sufficiently late \(n\), choose an arbitrary exact independent
product Nash root \(q_n\) of the one-stage quitting game whose all-Continue
payoff is \(u_n\). Define the literal root-and-tail profile and its semantic
pair by

\[
 \rho_n=q_n::\tau_n,\qquad
 Y_n=\operatorname{Sem}(\rho_n)
     =\operatorname{Prefix}(q_n,X_n),
\]

and write

\[
 c_n=\prod_i(1-q_{n,i}).
\]

Every such root satisfies, uniformly over its selection,

\[
 \operatorname{Abs}(q_n)=1-c_n\ge a,                         \tag{4}
\]

\[
 d_{n,b}-d_b(Y_n)\ge\delta_b,\qquad
 D_*\le D(Y_n)\le D(X_n)-\delta_b.                            \tag{5}
\]

After passage to a subsequence, exactly one of the following alternatives
holds.

### A. Positive-survival delayed paid fork

There is \(\eta>0\) such that

\[
 \eta\le c_n\le1-a.                                           \tag{6}
\]

Player \(b\) has an actual unilateral behavioral response from \(\rho_n\)
which copies \(q_{n,b}\) at the new date zero and, after joint Continue,
uses the old literal Quit0 cap response in \(\tau_n\). Its first changed
source row is the shifted row at date one, reached with probability
\(c_n\ge\eta\), and its exact total payoff gain is

\[
 c_nd_{n,b}\ge\eta\gamma.                                    \tag{7}
\]

Consequently \(d_b(Y_n)\ge\eta\gamma\). This response need not attain the
whole cap of \(Y_n\), and \(Y_n\) need not be stationary.

### B. Vanishing-survival unique-sure reset

One has \(c_n\to0\). After a further subsequence, \(q_n\to q\), where there
is a unique player \(k\) with

\[
 q_k=1,\qquad q_j<1\quad(j\ne k),\qquad
 O_k:=\prod_{j\ne k}(1-q_j)>0.                               \tag{8}
\]

At the finite prefixed sources,

\[
 d_i(Y_n)\longrightarrow0\quad(i\ne k),\qquad
 d_k(Y_n)\ge D_*/2                                           \tag{9}
\]

for every sufficiently large \(n\). The exact complete cap of \(k\) at
\(\rho_n\) forces Continue in the new root and then uses an exact cap
response in the unchanged stationary opponent tail \(\tau_n\). Its gain is
\(d_k(Y_n)\), and it enters that opponent tail with probability converging to
\(O_k\), hence eventually at least \(O_k/2\). After a two-valued
subsequence, the tail cap is always one literal stationary endpoint, Quit0
or Never.

Let \(\widehat q\) be the behavioral profile which repeats \(q\) at every
date. It is an actual stationary profile with exactly one debtor, \(k\).
There is a fixed terminal exploitability gap \(\Gamma>0\), and literal Never
is \(k\)'s exact cap over every unilateral behavioral deviation, with gain

\[
 U_k(\widehat q[k\leftarrow\operatorname{Never}])
 -U_k(\widehat q)\ge\Gamma.                                  \tag{10}
\]

The Never child need not be Nash, floor-safe, a returned minimum source, or
a regenerated instance of the hypotheses.

## Conjecture-facing change

The structured tropical paid-port construction previously stopped before
classifying arbitrary exact payoff-tail roots at its actual stationary
source. This theorem consumes that ambiguity uniformly: every exact root
spends one fixed amount of the same named complete behavioral debt
coordinate, and every selected sequence has only the two survivor arms above.

Thus an exact root cannot leave an unclassified low-absorption cloud. Positive
joint survival preserves an actual shifted paid response with fixed reach and
gain. Vanishing joint survival has neither a mixed no-sure limit nor a
two-sure tail-screened limit; it lands at a literal stationary unique-sure
Never reset.

Relative to
[FIN4_QUANTITATIVE_PAID_PORT_CONSUMER.md](../questions/FIN4_QUANTITATIVE_PAID_PORT_CONSUMER.md),
the remaining obligation is narrower but nonempty. The delayed fork does not
regenerate the cap pin, while the Never child can reactivate another player.
The theorem proves no source return, renewable rank, or uniform equilibrium.

## Definitions and assumptions

For a product root \(q\), a player \(i\), and a semantic pair \(X=(u,B)\),
write

\[
 s_i(q)=\prod_{j\ne i}(1-q_j)
\]

for opponent Continue mass, and

\[
 e_i(q;u)
 =[Q_i(q_{-i})-C_i(q_{-i};u_i)]_+
\]

for the positive Quit exercise premium. At an exact product Nash root, the
complete terminal-semantic debt action is

\[
 d_i(\operatorname{Prefix}(q,X))
 =[s_i(q)d_i(X)-e_i(q;u)]_+.                                 \tag{11}
\]

In particular,

\[
 0\le d_i(\operatorname{Prefix}(q,X))
 \le s_i(q)d_i(X)\le d_i(X).                                 \tag{12}
\]

The second coordinate \(B\) is the supremum over every unilateral behavioral
strategy. It includes randomized stopping, arbitrarily late stopping, and
literal Never. Prefixing uses \(B_i\), rather than \(u_i\), after joint
Continue when computing the new cap.

The root is an ordinary independent mixed-strategy profile. There is no
private correlated recommendation. The root Nash condition concerns the
current Quit/Continue choice against the literal continuation payoff \(u\).
The complete attached-tail strategy class remains unrestricted.

For stationary opponents, behavioral pure-time extremality makes the cap the
better of Quit0 and Never when opponent Continue mass is below one. If that
mass equals one, every finite Quit time has the Quit0 value and Never pays
zero, so the same two-endpoint statement holds directly.

## Source correspondence

The actual stationary sources, fixed final mover, positive Quit0 gain, cap
cluster identity, positive global debt floor, and literal source ancestry are
the frozen reviewed export
[FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md](FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md),
SHA-256
52c87dac80db59733cf4f3bbdb26bcdf9a915060d94a94acc5bc29df5a51a027.

The uniform first coordinate drop is the twice-reviewed theorem
[CODEX_HAHN__FIXED_CAP_PIN_COORDINATE_DEBT_DROP.md](../notes/CODEX_HAHN__FIXED_CAP_PIN_COORDINATE_DEBT_DROP.md),
frozen SHA-256
a4b9e7cf7b60a2566c07eeb47a942549a5bd68715c42d8a197d1c84705198a75.
Its reviews are
[CODEX_NEGATIVE_CERTIFICATE](../feedback/CODEX_HAHN__FIXED_CAP_PIN_COORDINATE_DEBT_DROP__BY_CODEX_NEGATIVE_CERTIFICATE.md)
and
[CODEX_SPINOZA](../feedback/CODEX_HAHN__FIXED_CAP_PIN_COORDINATE_DEBT_DROP__BY_CODEX_SPINOZA.md).
That theorem uses neither Fin4, \(D_*\), nor a separately supplied absorption
floor. The absorption floor (4) is derived below from its scalar case split.

The theorem packet reviewed before this standalone assembly is
[CODEX_NEGATIVE_CERTIFICATE__FIRST_EXACT_ROOT_SURVIVAL_AND_UNIQUE_SURE_RESET.md](../notes/CODEX_NEGATIVE_CERTIFICATE__FIRST_EXACT_ROOT_SURVIVAL_AND_UNIQUE_SURE_RESET.md),
frozen SHA-256
e24671f378ca5cbb1395a5601f903112b86907e6c8f866dfbd12f9c2546873d5.

Named checked Lean declarations supporting the semantic interfaces are:

- quittingTerminalSemanticDebt_prefix_eq_blockAct and
  quittingTerminalSemanticPrefix_mem_carrier in
  UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean;
- continuous_quittingTerminalSemanticPrefixSimplex in
  UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedSemanticCarrier.lean;
- continuous_quittingRootCoordinateNashDefect_simplex in
  UniformEquilibrium/Quitting/Root/NashDefectContinuity.lean;
- quittingTerminalSemanticPrefix_congr_of_twoSureQuitters in
  UniformEquilibrium/Diagnostics/Quitting/TwoSureProductRootTailScreen.lean;
- quittingTerminalPayoff_update_rootThenContinuation_eq in
  UniformEquilibrium/Quitting/Root/NearSureProfile.lean;
- sSup_range_quittingTerminalPayoff_update_eq_pureTime in
  UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean;
- exists_quitNow_or_never_terminalPayoff_eq_unilateralCap in
  UniformEquilibrium/Quitting/Stationary/BestResponse.lean; and
- not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap in
  UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean.

No checked declaration combines the structured source, arbitrary exact-root
selection, survival split, finite owner cap-tail response, and limiting
stationary Never reset.

## Proof

### Uniform coordinate drop and absorption floor

For a late \(X_n\), cap convergence gives

\[
 |B_{n,b}-s_b|\le\gamma/4.
\]

Let

\[
 \alpha_b(q)=1-\prod_{j\ne b}(1-q_j)
\]

be the probability that at least one opponent of \(b\) Quits in the root.
The fixed-cap-pin theorem gives (5), including the \(b\)-coordinate drop.
Its proof has two exhaustive cases. If

\[
 \alpha_b(q)\ge\gamma/(16M),
\]

then total root absorption is at least \(\alpha_b(q)\), and hence at least
\(a\). Otherwise the Quit-minus-Continue endpoint gap for \(b\) exceeds
\(\gamma/2\). Exact Nash complementarity forces \(q_b=1\), so total root
absorption equals one. This proves (4) uniformly for every late exact root.

Equation (12) makes every other coordinate debt nonincreasing. Since every
literal prefix is an actual semantic carrier point, (1) and the named
\(b\)-coordinate drop prove (5).

### Compact survival split

The semantic carrier and product-root simplex are compact. Pass to a
subsequence such that

\[
 X_n\to X,\qquad q_n\to q,\qquad c_n\to c_\infty.
\]

Equation (4) gives \(c_\infty\le1-a\). If \(c_\infty>0\), take
\(\eta=c_\infty/2\), obtaining (6). It remains to construct (7).

Every marginal Continue probability is then positive on a tail. At an exact
root, if \(b\) mixes it is indifferent; if it plays pure Continue, Quit is
not better. Thus its positive exercise premium in (11) vanishes, and

\[
 d_b(Y_n)=s_b(q_n)d_{n,b}
 \ge c_nd_{n,b}\ge\eta\gamma.                                \tag{13}
\]

For the literal response, player \(b\) copies its root randomization at the
new date zero. Root-absorbing outcomes are therefore identical under source
and response. Conditional on joint Continue, it replaces only its stationary
tail strategy by the old attained Quit0 cap response. The tail payoff
difference is \(d_{n,b}\), and the exact entry probability is \(c_n\).
This proves (7), including the row reach and unrestricted agency.

### A vanishing-survival limit has exactly one sure quitter

Suppose \(c_\infty=0\). Continuity gives
\(\prod_i(1-q_i)=0\), so at least one player Quits surely. Joint continuity
of root Nash defects in the prescribed payoff and root shows that \(q\) is
an exact root against \(u=X.1\).

If two distinct players were sure quitters, every unilateral replacement
would leave another sure quitter. The complete semantic tail would be
screened for every player. Equivalently, every opponent-survival factor in
(11) would be zero. The limiting prefix
\(\operatorname{Prefix}(q,X)\) would be diagonal. Joint prefix continuity
would imply

\[
 D(Y_n)\longrightarrow0,
\]

contradicting the carrier floor \(D(Y_n)\ge D_*>0\). Hence the sure quitter
is unique; call it \(k\). This proves (8).

For \(i\ne k\), the survival factor \(s_i(q_n)\) contains
\(1-q_{n,k}\to0\). Carrier compactness bounds the source debts, so (12) gives
\(d_i(Y_n)\to0\). The total floor then gives \(d_k(Y_n)\ge D_*/2\) on a
tail, proving (9).

### The finite source cap follows the old tail

For large \(n\), \(q_{n,k}>0\). Let \(U'_{n,k}\) and \(B'_{n,k}\) be the
prescribed payoff and complete cap at \(Y_n\). Exact root Nash makes forced
Quit a maximizing prescribed-payoff endpoint, so its value equals
\(U'_{n,k}\). The complete cap is

\[
 B'_{n,k}
 =\max\{Q_k(q_{n,-k}),C_k(q_{n,-k};B_{n,k})\}.                \tag{14}
\]

The Continue endpoint is monotone in its tail coordinate because
\(B_{n,k}\ge u_{n,k}\). If the maximum in (14) were the Quit endpoint, then
\(B'_{n,k}=U'_{n,k}\), contradicting (9). Thus the
Continue-with-old-cap branch is strictly maximal.

An exact cap response therefore forces \(k\) to Continue at the new root and,
when all opponents Continue, uses a cap-attaining response in the stationary
tail \(\tau_n\). Its opponent-tail entry probability is

\[
 \prod_{j\ne k}(1-q_{n,j})\longrightarrow O_k>0.
\]

Its gain is exactly \(d_k(Y_n)\). Stationary pure-time extremality selects
Quit0 or Never as the tail cap; a subsequence fixes the two-valued choice.
The response changes \(k\)'s tail strategy, so it preserves the opponent
tail but does not regenerate the complete source.

### The limiting stationary profile is a unique-sure Never reset

Repeat \(q\) at every date to form \(\widehat q\). Since \(q_k=1\), this
profile absorbs at date zero. Every outsider \(i\ne k\) remains screened by
\(k\) after an arbitrary behavioral deviation. The limiting exact-root
inequality therefore gives

\[
 B_i(\widehat q)=U_i(\widehat q)\quad(i\ne k).                 \tag{15}
\]

For \(k\), Quit0 equals its prescribed payoff. Against stationary opponents,
pure-time extremality gives

\[
 B_k(\widehat q)
 =\max\{U_k(\widehat q),
         U_k(\widehat q[k\leftarrow\operatorname{Never}])\}.  \tag{16}
\]

When the opponents' one-row Continue mass is one, every finite Quit time has
the Quit0 value and Never pays zero, so (16) still holds.

No uniform-equilibrium payoff yields a fixed \(\Gamma>0\) such that every
actual behavioral profile has a unilateral terminal gain at least
\(\Gamma\). Apply this gap to \(\widehat q\). Equation (15) rules out every
outsider. Equations (15)--(16) force player \(k\)'s Never gain to be at
least \(\Gamma\). This proves (10) and the theorem.

## Boundary tests

### Positive survival does not regenerate the cap pin

The response in (7) is copied through the root, but another root-date
deviation may attain the whole cap of \(Y_n\). Thus its new \(b\)-cap need
not approach \(s_b\), even though the shifted old paid row has fixed reach.
The fixed-cap-pin theorem cannot automatically be iterated.

### Two sure quitters genuinely screen the complete tail

With two sure quitters, every unilateral deviation leaves a sure quitter at
date zero. Prescribed and deviating tails, including the complete behavioral
cap, are unreachable. This is why the zero-debt contradiction in the proof
is complete rather than stationary-only.

### Exact reactivation after the Never reset

Pad the following three-player table by a fourth player whose rewards are
identically zero and who always Continues. Name the active players \(k,a,b\).
Every unspecified reward is zero. Put

\[
 r_a(\{a\})=\tfrac12,
\]

\[
 r_k(\{k\})=0,\qquad
 r_k(S)=\tfrac43\ \text{if }k\in S,\ S\ne\{k\},\qquad
 r_k(S)=\tfrac65\ \text{if }k\notin S.
\]

On coalitions containing \(k\), set

\[
\begin{array}{c|rrrr}
S&\{k\}&\{k,a\}&\{k,b\}&\{k,a,b\}\\ \hline
r_a(S)&1&0&0&1\\
r_b(S)&0&1&1&0.
\end{array}                                                    \tag{17}
\]

Let \(q_k=1\) and \(q_a=q_b=1/2\). The outsiders play exact matching
pennies, so each forced endpoint pays \(1/2\). Player \(k\)'s Quit0 payoff is
\(1\), whereas literal Never pays \(6/5\). Thus the stationary profile is a
unique-debtor source and Never is \(k\)'s exact cap with gain \(1/5\).

After the Never update, the terminal coalitions
\(\{a\},\{b\},\{a,b\}\) each have probability \(1/3\). Player \(a\)'s
prescribed payoff is \(1/6\), but Quit0 yields \(1/4\), a strict gain
\(1/12\). The Never child is therefore not necessarily terminal Nash or a
renewed unique-sure source.

This table is an interface regression, not a positive-gap counterexample. It
may admit another equilibrium. Its role is precisely to falsify the local
renewal implication omitted from the theorem.

## Adapter and consumer

The actual-data adapter is the frozen tropical two-Never-to-paid-port export.
Its stationary last-edge sources give (1)--(2), with one fixed final mover and
complete unrestricted caps. The twice-reviewed fixed-cap-pin theorem gives
the root-uniform coordinate drop, and its own scalar proof gives the
absorption floor (4).

The output narrows the debt-transition and inert modes of the quantitative
paid-port question to two literal source-attached objects: a positive-reach
shifted paid fork, or a stationary unique-sure Never reset. The positive arm
retains the old source after joint Continue; the zero-survival arm retains an
exact finite cap-tail response and a separate literal stationary reset at the
root limit.

Neither arm reaches a presently checked terminal consumer. The positive arm
lacks a regenerated cap pin. The zero-survival Never child may reactivate an
outsider, as (17) shows. A downstream proof must attach one of these objects
to a source-matched Nash--Bellman return, a strictly decreasing rank on
regenerated complete sources, or a terminal approximate-equilibrium compiler.

## Lean handoff

A narrow formalization should separate four declarations.

1. Derive the uniform absorption floor from the fixed-cap-pin scalar
   dichotomy: macroscopic opponent absorption, or a sure Quit by \(b\).
2. Prove the positive-survival transport identity: copying the current root
   action and changing only the attached tail response multiplies its payoff
   difference by the joint-Continue mass.
3. Prove the compact Fin4 classification: positive carrier debt rules out two
   limiting sure quitters, and a unique sure \(k\) kills every other prefix
   debt while leaving \(d_k\ge D_*/2\).
4. Prove the stationary unique-sure theorem: exact screened outsider
   coordinates plus the terminal gap force literal Never to be the unique
   owner's unrestricted cap.

The finite owner cap step should use (14) directly. Once its finite prefix
debt is positive, exact root Nash excludes the Quit branch. The boundary
where all stationary opponents Continue surely must remain a separate simple
case rather than be fed to the strict-contraction endpoint theorem.

No structure field should assume that the positive-survival response attains
the new whole cap, that the finite tail-changing response equals the limiting
stationary profile, or that the Never child is renewable.

## Scope and nonclaims

- The theorem is reviewed ordinary mathematics, not yet Lean-checked.
- Root selection is arbitrary and uniform, but the final dichotomy is
  subsequential.
- The roots are independent product Nash roots against the literal prescribed
  payoff, not roots against the cap vector.
- All cap statements cover unrestricted unilateral behavioral deviations.
- Alternative A gives one executable response, not necessarily the whole cap,
  and its prefixed source is nonstationary.
- Alternative B distinguishes the finite prefixed source, its tail-changing
  cap response, and the stationary profile constructed from the limiting
  root.
- The stationary Never child may reactivate an outsider, violate punishment
  floors, lose the paid label, or revisit an earlier support.
- No renewal, source return, well-founded rank, uniform-equilibrium payoff, or
  all-behavior counterexample is proved.
