# A recentered paid tail either renews an anchored cap ray or creates a cap-cross rectangle

Author: CODEX_HAHN

## Status

**Exact ordinary mathematics; source-to-source/rectangle reduction, not
Lean-checked and not a terminal consumer.**  The actual old tail in the
vanishing live-word recentering theorem carries more than a cap pin: one
distinct player is prescribed to Quit surely by a finite deadline and has
zero complete debt.  The fixed-gain tail update cannot alter that player's
prescribed clock, because the paid mover has positive source debt and is
therefore a different player.

If the update leaves the finite-clock player's debt below half the terminal
gap, that clock is still strong enough to restart the exact shifted-cap ray.
Exact-prefix debt monotonicity prevents the anchor itself from becoming the
unique-sure debtor at a later zero-survival root.  If instead the update gives
the anchor a fixed debt, the same update creates a fixed positive
source-matched response rectangle: the anchor had no profitable response
before the update and has one afterward.

The second arm is a cap cross-effect, not an accepted chronology.  The first
arm renews an exact cap-clock source but does not restore the stronger Quit0
singleton pin or close the horizontal return seam.

## 1. Self-contained input

Let \(I=\operatorname{Fin}4\).  Fix a bounded quitting reward table and a
terminal exploitability gap \(\Gamma>0\):

\[
 \max_i d_i(P)\ge\Gamma
 \quad\text{for every actual behavioral profile }P.
\tag{1}
\]

Assume also the no-uniform-payoff consequence that every bounded exact
Nash--Bellman prefix ray has finite total marginal hazard.

For every \(n\), let \(X_n\) be an actual source and let \(a\) be one fixed
player such that:

1. player \(a\)'s prescribed strategy Quits surely by a finite date \(H_n\);
2. \(d_a(X_n)=0\).

Let

\[
 Z_n=X_n[k\leftarrow\zeta_{n,k}]
\tag{2}
\]

be a literal one-player replacement, for one fixed \(k\), satisfying

\[
 U_k(Z_n)-U_k(X_n)\ge g_0>0,
 \qquad d_k(Z_n)\longrightarrow0.
\tag{3}
\]

Own-cap invariance gives \(d_k(X_n)\ge g_0\).  Hence

\[
 k\ne a.
\tag{4}
\]

Consequently the prescribed finite clock of \(a\) is literally unchanged in
\(Z_n\): player \(a\) still Quits surely by \(H_n\), although its debt need
not remain zero.

These are the fields in the maintained application.  There \(X_n\) is the
actual high reset child, \(a\) is its old zero-debt finite-deadline owner, and
the recentered live-word theorem supplies (2)--(3) with
\(g_0=D_*/4\).

## 2. Exact dichotomy

After passing to a subsequence, exactly one of the following alternatives
holds.

### A. Subcritical anchored target

\[
 d_a(Z_n)<\Gamma/2
\quad\text{for every retained }n.
\tag{5}
\]

For every such \(Z_n\), every recursively chosen exact product-root prefix
ray has the following exhaustive output:

1. some root has two sure quitters, and the corresponding actual prefix is
   an unrestricted terminal Nash profile; or
2. after the last zero-survival root, one fixed player
   \(\ell_n\ne a\) has a positive attained finite-time-or-Never cap whose
   deterministic clock shifts through every later positive-survival exact
   root, with debt bounded below by a positive constant along that ray.

Thus \(Z_n\) is an actual source for the exact shifted-cap-clock
construction.  The initial attained response and its positive lower bound may
depend on \(n\).

### B. Fixed cap-cross rectangle

\[
 d_a(Z_n)\ge\Gamma/2
\quad\text{for every retained }n.
\tag{6}
\]

Choose a deterministic finite-time-or-Never response \(\beta_{n,a}\) whose
payoff at \(Z_n\) is within \(\Gamma/4\) of \(a\)'s complete cap.  Then

\[
\begin{aligned}
 U_a(Z_n[a\leftarrow\beta_{n,a}])-U_a(Z_n)
   &>\Gamma/4,\\
 U_a(X_n[a\leftarrow\beta_{n,a}])-U_a(X_n)
   &\le0.
\end{aligned}
\tag{7}
\]

Since \(a\ne k\), the four actual profiles

\[
\begin{array}{ccc}
 X_n &\xrightarrow{\ k\ }& Z_n\\
 {\scriptstyle a}\downarrow &&\downarrow{\scriptstyle a}\\
 X_n[a\leftarrow\beta_{n,a}]
   &\xrightarrow{\ k\ }&
 Z_n[a\leftarrow\beta_{n,a}]
\end{array}
\tag{8}
\]

form a literal commuting strategy rectangle.  Its \(a\)-payoff
cross-difference satisfies

\[
\begin{aligned}
 &\bigl(U_a(Z_n[a\leftarrow\beta_{n,a}])-U_a(Z_n)\bigr)\\
 &\quad-
 \bigl(U_a(X_n[a\leftarrow\beta_{n,a}])-U_a(X_n)\bigr)
 >\Gamma/4.
\end{aligned}
\tag{9}
\]

The top \(k\)-edge retains its gain \(g_0\).  Equation (9) is therefore a
fixed two-player cap cross-effect attached to the literal renewed source,
not a comparison between independently compactified profiles.

## 3. Proof of the anchored-ray alternative

Fix \(n\) satisfying (5), abbreviate \(Z=Z_n\), and recursively choose any
exact independent product root \(q^m\) Nash against the prescribed payoff of
the current actual source:

\[
 P^0=Z,\qquad P^{m+1}=q^m::P^m.
\tag{10}
\]

The finite-deadline strategy of \(a\) remains prescribed in every \(P^m\)
and surely Quits by date \(H_n+m\).  Exact-prefix coordinatewise debt
monotonicity gives

\[
 d_a(P^{m+1})\le d_a(P^m)\le d_a(Z)<\Gamma/2.
\tag{11}
\]

Finite exact-block hazard capacity implies

\[
 \sum_m\sum_i q^m_i<\infty.
\tag{12}
\]

Every zero-survival root contains a sure quitter and therefore contributes
at least one to (12).  There are only finitely many zero-survival roots.

If one such root has two sure quitters, any unilateral deviation leaves a
sure opponent quitter at the current date.  The tail is completely screened,
and exact root Nash proves that the literal prefixed profile is a terminal
Nash profile against unrestricted behavioral deviations.

Otherwise every zero-survival root has a unique sure quitter.  At the child
of such a root, every debt coordinate except that of the sure quitter is
zero.  By (1), its sure quitter \(\ell\) has debt at least \(\Gamma\).
Equation (11) shows that \(\ell\ne a\).

Because \(a\ne\ell\) is prescribed to Quit surely by a finite deadline, the
complete response problem of \(\ell\) at the preceding tail is attained by a
deterministic finite quit time or Never.  At the unique-sure child, the
current Quit endpoint equals the prescribed payoff, whereas its debt is
positive.  Hence its cap is attained by Continuing through the sure root and
then using that tail cap.

If no zero-survival root occurs, apply (1) already at \(P^0=Z\).  The selected
debtor \(\ell\) cannot be \(a\) by (5), and its cap is again attained by a
finite time or Never because the distinct prescribed clock \(a\) surely
terminates.

In either nonterminal case, start after the last zero-survival root (or at
zero if there is none).  Every subsequent root has positive joint survival.
If \(A\) attains \(\ell\)'s tail cap, exact root Nash and positive Continue
support imply that Continue-then-\(A\) attains the new cap and

\[
 d_\ell(P^{m+1})
 =s_{m,\ell}d_\ell(P^m),
 \qquad
 s_{m,\ell}:=\prod_{i\ne\ell}(1-q^m_i)>0.
\tag{13}
\]

The deterministic cap time shifts by one date at each prefix; Never remains
Never.  From (12),

\[
 \prod_{m\ge m_0}s_{m,\ell}>0.
\tag{14}
\]

Since the initial debt is at least \(\Gamma\), equations (13)--(14) give a
strictly positive debt floor along the whole shifted ray.  This proves
Alternative A.

## 4. Proof of the cap-cross alternative

Fix \(n\) satisfying (6).  Pure-time extremality of the unrestricted
behavioral cap gives a deterministic finite quit time or Never
\(\beta_{n,a}\) with payoff strictly larger than
\(B_a(Z_n)-\Gamma/4\).  Therefore

\[
 U_a(Z_n[a\leftarrow\beta_{n,a}])-U_a(Z_n)
 >d_a(Z_n)-\Gamma/4\ge\Gamma/4.
\tag{15}
\]

At \(X_n\), zero \(a\)-debt means that no complete behavioral replacement can
improve \(a\)'s payoff.  In particular,

\[
 U_a(X_n[a\leftarrow\beta_{n,a}])-U_a(X_n)\le0.
\tag{16}
\]

Replacements of distinct players commute literally, proving (8), and
subtracting (16) from (15) proves (9).

## 5. Relation to the maintained source

The high reset child \(X_n\) retains two different roles:

- the old owner \(a\), whose prescribed strategy is a sure finite clock and
  whose debt is zero; and
- the pinned reset observer, whose Quit0 cap and positive singleton-wall debt
  seed the later capacity construction.

The recentered mover \(k\) has fixed positive debt at \(X_n\), so it cannot be
the old zero-debt owner \(a\).  This is the only label separation needed for
the theorem.

Alternative A does not prove that the pinned observer's Quit0 cap remains
optimal at \(Z_n\).  It proves something weaker but executable: some debtor
distinct from the still-sure anchor has an attained cap and generates a
literal exact shifted-cap ray.

Alternative B records precisely how preservation can fail at a macroscopic
scale.  The \(k\)-update creates a fixed profitable response for a player
whose every response was nonprofitable at the source.  This is a
source-attached response rectangle, not merely a change in a displayed cap
coordinate.

## Sources inspected

- `notes/CODEX_HAHN__LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE.md`;
- `notes/CODEX_HAHN__RECENTERED_TAIL_EDGE_AT_A_RENEWED_CAP_CLOCK_SOURCE.md`;
- `notes/CODEX_HAHN__VANISHING_LIVE_WORD_REPROJECTS_PAID_EDGE_TO_LITERAL_SOURCE_TAIL.md`;
- `notes/CODEX_SPINOZA__UNIQUE_SURE_ACTUAL_CHILD_TO_LITERAL_SHIFTED_CAP_RAY.md`;
- `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`;
- `UniformEquilibrium/Quitting/Root/LiteralPrefixDeviationTransport.lean`;
- `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `UniformEquilibrium/Quitting/Bellman/Finite/UnboundedExactBlockHazardCapacity.lean`; and
- `UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`.

## Boundary and nonclaims

- The sure finite clock need not have zero debt after the \(k\)-update.
  Alternative A only requires its debt to stay strictly below the global
  terminal gap.
- The finite deadline \(H_n\), the selected debtor, its response time, and
  its eventual positive debt floor may depend on \(n\).  No common diagonal
  ray is asserted.
- The shifted-cap ray does not regain the source's Quit0 singleton pin.
- The cap-cross rectangle in Alternative B need not give a Nash--Bellman
  edge, a response cycle, or a chronological charge.  Generic local
  rectangles do not have such a consumer.
- No source return, renewable finite rank across horizontal cap
  installations, terminal approximate Nash profile, or uniform-equilibrium
  payoff is proved.

## Exact remaining question

Can the fixed source-attached rectangle in Alternative B be combined with
the off-minimum collar and the exact \(k\)-gain to force a minimum chord,
accepted charged return, or finite law/support rank?  If not, the surviving
obstruction is an actual two-player cap cross-effect at a source which already
carries a finite anchor and a fixed paid edge.
