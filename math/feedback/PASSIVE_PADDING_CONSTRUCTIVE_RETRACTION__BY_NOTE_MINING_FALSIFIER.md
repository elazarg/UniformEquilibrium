# Falsification review: passive-padding constructive retraction

**Reviewer:** CODEX_GATE_FALSIFIER

**Sources reviewed:**

- [constructive retraction note](../notes/CODEX_ROOT__PASSIVE_PADDING_CONSTRUCTIVE_RETRACTION.md);
- [independent source audit](PASSIVE_PADDING_CONSTRUCTIVE_RETRACTION__BY_NOTE_MINING_SOURCE_AUDIT.md);
- [earlier Ramsey review](CODEX_ROOT__PASSIVE_PADDING_CONSTRUCTIVE_RETRACTION__BY_CODEX_RAMSEY.md).

**Final verdict: PASS.**  I found no counterexample for positive penalty.
The quantitative reverse projection, same-target uniform-payoff retraction,
forced-zero fresh coordinates, exact target-set equality, profilewise
exploitability inequality, and two-sided infimum comparison are all correct
for the canonical padding.  They cover arbitrary unilateral behavioral
deviations.

One boundary should be strengthened before final packaging: at penalty zero
the target retraction itself can fail, not merely its displayed quantitative
factor.  An exact counterexample is given below.  This strengthens the stated
boundary and does not alter the positive-penalty theorem.

## Required final statement

Let $I$ and $J$ be finite nonempty player types.  Let $r$ be a quitting reward
table on $I$.  For each old player $i$, define

\[
 H_i=\max\bigl(0,\{r_i(S):S\ne\varnothing\}\bigr),\qquad
 L_i=\min\bigl(0,\{r_i(S):S\ne\varnothing\}\bigr),
\]

and

\[
 \Omega=\max_i(H_i-L_i).
\]

Let $A>0$, let $m=|J|$ as a real number, and put

\[
 f=\frac{A}{A+m\Omega}>0.
\]

Let $r^+$ be the canonical reward on $I\sqcup J$:

- if a nonempty terminal coalition contains an old player, delete all fresh
  labels for the old coordinates and pay every fresh coordinate zero;
- if it contains only fresh players, pay old player $i$ the value $H_i$,
  pay each participating fresh player $-A$, and pay every other fresh player
  zero.

For a padded behavioral profile $\sigma^+$, let
$P\sigma^+$ be the old behavioral profile obtained by retaining the actual
old live-root hazard at every date.

The final package may state all of the following.

### Quantitative terminal projection

If $\epsilon\ge0$ and $\sigma^+$ is a terminal
$\epsilon$-Nash profile of $r^+$ against every unilateral behavioral
deviation, then $P\sigma^+$ is a terminal $(\epsilon/f)$-Nash profile of $r$.

If additionally

\[
 |U_i^+(\sigma^+)-v_i^+|\le\epsilon
 \qquad(i\in I),
\]

then, for $v_i=v^+_{\operatorname{inl}i}$,

\[
 |U_i(P\sigma^+)-v_i|\le\epsilon/f
 \qquad(i\in I).
\]

### Target retraction and exact target set

If $v^+$ is a uniform-equilibrium payoff of $r^+$, then its old restriction
$v$ is a uniform-equilibrium payoff of $r$, and every fresh coordinate of
$v^+$ is zero.

Conversely, if $v$ is a uniform-equilibrium payoff of $r$, then its canonical
extension $(v,0)$ is a uniform-equilibrium payoff of $r^+$.  Hence

\[
 \operatorname{UEPayoffs}(r^+)
 =
 \{(v,0):v\in\operatorname{UEPayoffs}(r)\}.
\]

### Numerical exploitability

For maximum terminal exploitability $E$ and its literal behavioral-profile
infimum $\eta$,

\[
 f\,E_r(P\sigma^+)\le E_{r^+}(\sigma^+)
\]

for every padded behavioral profile, and

\[
 f\,\eta(r)\le\eta(r^+)\le\eta(r).
\]

The target-set theorem is the main new result.  The numerical statements
also discharge the existing passive-padding revisit item.

## 1. Fresh-only mass estimate

Let $s$ be the total infinite-horizon probability that first absorption is by
a nonempty fresh-only coalition.  For each fresh player $j$, changing its
entire strategy to Never gives terminal payoff zero.  Terminal
$\epsilon$-Nash therefore implies

\[
 -U_j^+(\sigma^+)\le\epsilon.
\]

The checked aggregate payoff inequality says

\[
 \sum_{j\in J}U_j^+(\sigma^+)\le -As.
\]

Thus

\[
 As\le\sum_j(-U_j^+)\le m\epsilon,
\qquad
 s\le\frac{m\epsilon}{A}. \tag{1}
\]

All signs are correct.  A fresh-only collision with $k$ participating fresh
players contributes $-kA$ to the sum, so the aggregate inequality remains
valid.  Old/fresh ties are not in $s$ and pay every fresh coordinate zero.
No best-response attainment is used.

The estimate works also at $\epsilon=0$, where it forces $s=0$.  The explicit
assumption $\epsilon\ge0$ is necessary for the standalone quantitative
theorem.

## 2. Projection against arbitrary old deviations

The canonical interval coupling gives, for every old player $i$,

\[
 0\le U_i^+(\sigma^+)-U_i(P\sigma^+)
 \le \Omega s. \tag{2}
\]

Fix an arbitrary old behavioral strategy $\tau_i$.  Its padded lift copies
its entire live-history hazard sequence, not merely a stationary or pure-time
strategy.  The checked deviation comparison gives

\[
 U_i((P\sigma^+)[i\leftarrow\tau_i])
 \le
 U_i^+(\sigma^+[\operatorname{inl}i\leftarrow\widetilde\tau_i]). \tag{3}
\]

Subtracting the baselines in (2), applying padded
$\epsilon$-Nash, and then using (1), gives

\[
\begin{aligned}
 U_i((P\sigma^+)[i\leftarrow\tau_i])-U_i(P\sigma^+)
 &\le\epsilon+\Omega s\\
 &\le\epsilon\left(1+\frac{m\Omega}{A}\right)
 =\frac{\epsilon}{f}.
\end{aligned}
\]

Because $\tau_i$ was arbitrary, this is the full behavioral terminal-Nash
claim.  The same bound and the triangle inequality give the old target error.

I tried to break (3) using a deviation which quits only after an arbitrarily
late fresh clock and using one with a Never atom.  Both are still literal
behavioral hazards in the checked lift.  Fresh-only preemption pays the old
upper endpoint and cannot lower the padded deviating value; old-containing
absorption agrees after deletion.  No counterexample results.

## 3. Uniform and finite-horizon quantifiers

The argument does not claim a same-horizon projection theorem for arbitrary
finite-horizon average equilibria.  It uses the exact terminal waist, and
that use is valid.

Starting from the fixed padded uniform target $v^+$, the checked target
acceptance theorem supplies, for every terminal accuracy
$\epsilon>0$, one padded terminal $\epsilon$-Nash profile whose terminal
payoff is within $\epsilon$ of that same $v^+$.  Given an old requested
accuracy $\eta>0$, choose $\epsilon=f\eta$.  The quantitative projection
produces one old terminal $\eta$-Nash profile within $\eta$ of the fixed
restriction $v$.  The checked fixed-target terminal compiler then supplies
the uniform finite-horizon quantifiers:

\[
 \forall\eta>0\ \exists\sigma_\eta,N_\eta\
 \forall N\ge N_\eta
\]

with the same declared target $v$ and all unilateral behavioral deviations
controlled.

Thus neither the profile nor the horizon threshold is required to be uniform
in $\eta$, while the payoff target is fixed before $\eta$.  No target is
selected by compactness during the reverse construction.

## 4. Fresh coordinates of every padded target

For every padded profile and every fresh player $j$,

\[
 U_j^+\le0
\]

because every terminal reward in that coordinate is either $0$ or $-A$.
For a terminal $\epsilon$-Nash profile, Never gives
$U_j^+\ge-\epsilon$.

Apply the fixed-target acceptance certificate for a padded target $v^+$.
Together with $|U_j^+-v_j^+|<\epsilon$, these inequalities give, for every
$\epsilon>0$,

\[
 -2\epsilon<v_j^+<\epsilon.
\]

Therefore $v_j^+=0$.  This is valid coordinatewise for every fresh player and
does not assume convergence of a preselected profile sequence.

## 5. Quiet lift and exact all-behavior semantics

Given an old terminal approximate equilibrium, copy every old strategy and
make every fresh player Never.  Old prescribed payoffs and arbitrary old
unilateral deviations agree exactly with the old game.

If one fresh player $j$ changes its complete behavioral strategy while all
other fresh players remain Never, then:

- strict preemption of old absorption by $j$ yields fresh-only singleton
  $\{j\}$ and payoff $-A$;
- a tie with an old quitter yields an old-containing terminal and payoff zero;
- old preemption and nonabsorption also yield zero.

Hence the exact deviating payoff is

\[
 -A\Pr(j\text{ strictly preempts old absorption})\le0.
\]

Never attains zero, so the fresh cap and debt are exactly zero.  This proves
the quiet terminal lift against the complete behavioral class and, through
the target compiler, sends $v$ to exactly $(v,0)$.

The generic all-behavior lift is already checked through block
dispensability.  The new content is the canonical sum-type adapter and the
closed form of the fresh target coordinates, not a new generic deletion
principle.

## 6. Pointwise and infimum inequalities

Let $E_{r^+}(\sigma^+)$ be maximum terminal exploitability.  It is nonnegative,
and by definition $\sigma^+$ is a terminal
$E_{r^+}(\sigma^+)$-Nash profile.  Applying the quantitative theorem with
this exact error gives

\[
 E_r(P\sigma^+)\le E_{r^+}(\sigma^+)/f,
\]

which is the pointwise inequality.

For every padded profile,

\[
 \eta(r)\le E_r(P\sigma^+).
\]

Multiplying by $f>0$, applying the pointwise inequality, and taking the
infimum over padded profiles gives

\[
 f\,\eta(r)\le\eta(r^+).
\]

For every old profile, the quiet lift has exactly the same old debts and zero
fresh debt, so its padded exploitability equals the old exploitability.
Taking infima gives

\[
 \eta(r^+)\le\eta(r).
\]

All profile sets are nonempty and the exploitability ranges are bounded below
by zero, so no improper-infimum case is hidden.

## 7. Positive and zero penalty boundaries

### Positive penalty

For $A>0$, $\Omega\ge0$, and nonempty $J$,

\[
 A+m\Omega>0,\qquad f>0.
\]

If $\Omega=0$, then $f=1$ and (2) has zero old baseline error.  There is no
singularity.

### Zero penalty: exact failure of target retraction

Let the old game have two players $1,2$ and rewards

\[
 r(\{1\})=(1,0),\qquad
 r(\{2\})=(0,1),\qquad
 r(\{1,2\})=(0,0).
\]

Its canonical upper endpoint is $H=(1,1)$.  The vector $(1,1)$ is not even a
possible old terminal payoff: every terminal outcome, including Never, lies
in the convex hull of

\[
 (1,0),\ (0,1),\ (0,0),
\]

whose coordinate sum is at most one.  The fixed-target terminal
characterization therefore rules out $(1,1)$ as an old uniform-equilibrium
payoff.

Now add one fresh player with penalty $A=0$.  Let the fresh player Quit at
date zero and both old players Never quit.  The new-only terminal pays
$(1,1,0)$.  An old player who joins at date zero receives its old singleton
reward $1$, and no later deviation changes the already absorbed outcome.
The fresh player receives zero under every unilateral strategy.  Thus this
is an exact terminal Nash profile and $(1,1,0)$ is a padded
uniform-equilibrium payoff, but its old restriction $(1,1)$ is not an old
uniform-equilibrium payoff.

Strict positivity of $A$ is therefore essential to the qualitative
retraction, not only to the factor $f$.

### Other boundaries

- Empty $J$ is the identity case and should be stated separately.
- Empty $I$ is excluded because the canonical extrema require an old player.
- The theorem is false for arbitrary extensions of a reward table.  It uses
  the exact canonical upper endpoint on fresh-only absorption, deletion of
  fresh labels on old-containing absorption, zero fresh reward there, and
  the negative participating-fresh penalty.

## 8. Source and novelty check

The required primitives are checked in
UniformEquilibrium/Quitting/Terminal/PassivePlayerPadding.lean:

- the live-root projector;
- the old baseline comparison;
- the arbitrary old-deviation lift;
- the aggregate fresh-player penalty;
- the exact fresh Never payoff.

The canonical interval data are checked in
PassivePlayerPaddingCanonical.lean.  The fixed-target uniform/terminal
equivalence is checked in
Terminal/TargetTail/TerminalTargetSemantics.lean.

The current formalized passive-padding packet proves only upward terminal-gap
and nonexistence transport and explicitly lists the converse as absent.  The
pointwise and infimum claims remain in
revisit/TERMINAL_EXPLOITABILITY_PASSIVE_PLAYER_PADDING_POINTWISE_INFIMUM.md.
The generic forward lift is already checked in Classification/BlockDeletion.lean.

I found no checked declaration or current export proving the positive-penalty
reverse profile estimate, restriction of the same padded target, forced-zero
fresh coordinates, or exact target-set equality.  The package is therefore
fresh in precisely those claims.

## 9. Export requirements

The final export should:

1. state $\epsilon\ge0$, $A>0$, and finite nonempty $I,J$ explicitly;
2. define the canonical reward and live-root projection rather than referring
   only to source names;
3. make the target-set equality the headline;
4. include the exact $A=0$ counterexample above;
5. distinguish terminal quantitative projection from the compiled uniform
   finite-horizon conclusion;
6. present the generic block-dispensable forward lift as existing input;
7. include the pointwise and infimum corollaries, or clearly leave them for a
   second formalization milestone without weakening their mathematical
   status; and
8. retain the nonclaim that no arbitrary $(k+1)$-player game is reduced.

With that exact scope, this is ready for the export gate.
