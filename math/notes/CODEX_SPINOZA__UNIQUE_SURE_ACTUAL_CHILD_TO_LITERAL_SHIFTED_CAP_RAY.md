# A unique-sure actual child enters a literal shifted-cap exact ray

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics; theorem-level reduction, not Lean-checked and
not a terminal consumer.** A finite unique-sure root does not require
stationary repetition to recover an actual cap source. If its literal tail
has one fixed finite-horizon zero-debt anchor, then the unique debtor at the
prefixed child is distinct from that anchor and has an attained pure-time (or
Never) complete cap at the child itself.

Iterating arbitrary exact prescribed-payoff roots from that child preserves
the same finite-horizon zero-debt anchor. Under the Fin4 counterexample-side
bounded exact-block capacity, only finitely many of those roots can have zero
joint survival. If there is no zero-survival root, the global terminal gap at
the initial anchored source already supplies a distinct positive debtor with
an attained finite/Never cap. Otherwise, after the last such root, its unique
sure quitter supplies that debtor and cap. In either case one fixed positive
debtor and one attained cap shift through every later positive-survival exact
prefix. Thus the zero-survival finite-source seam enters the
eventual-shifted-cap branch on one literal actual genealogy, without a compact
limiting root or a stationary-profile replacement.

This still does not give a forward infinite Nash--Bellman spine. The finite
exact blocks are nested by adding roots at the front, so their chronological
orders reverse the construction order; the fixed anchor and profitable cap
escape to the far end of the calendar. The remaining obstruction is
projective timing, not cap attainment or source provenance.

## Question

Suppose a late-reset source is prefixed by an exact root of zero joint
survival and exactly one sure quitter. Can the resulting finite actual child
itself seed the cap-clock construction, or must one first replace it by the
stationary repetition of a limiting root?

## Sources inspected

- notes/CODEX_HAHN__LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE.md,
  reviewed at SHA256
  c38983e9a73e14005838181d46f51602dafc02763df71a369920e58e1da2d2bb;
- notes/CODEX_NEGATIVE_CERTIFICATE__FIRST_EXACT_ROOT_SURVIVAL_AND_UNIQUE_SURE_RESET.md;
- exports/FIN4_UNIQUE_SURE_ROOT_SAME_PROFILE_SINGLETON_HANDOFF.md;
- notes/CODEX_SPINOZA__RECURSIVE_LITERAL_U_ROOT_PREFIX_LEDGER_AND_STALL.md;
- UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean, especially
  quittingTerminalSemanticDebt_prefix_eq_blockAct and
  quittingTerminalSemanticDebt_prefix_le;
- UniformEquilibrium/Diagnostics/Quitting/TwoSureProductRootTailScreen.lean;
  and
- UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean,
  especially
  finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff.

The narrow search also found the general horizontal recharge ledger in
notes/PAIRED_HULL_REVIEW__PAID_PORT_RECHARGE_LEDGER_AND_INERT_REFUSAL.md.
The present result does not claim that repeated horizontal cap installation
has a new scalar budget; it avoids that seam only for the finite
zero-survival child by staying on its literal vertical prefix genealogy.

## 1. Arbitrary-source anchored setup

Let \(I=\operatorname{Fin}4\). Fix a bounded quitting reward table and a
terminal exploitability witness with gap \(\Gamma>0\): every actual behavior
profile has some complete unilateral behavioral gain at least \(\Gamma\).

Let \(\sigma^0\) be an actual behavior profile and fix a player \(b\) such
that:

1. under the prescribed strategy of \(b\), player \(b\) Quits surely by one
   finite date \(H\), independently of the other players' strategies; and
2. \(b\)'s complete terminal-semantic debt at \(\sigma^0\) is zero:

   \[
   d_b(\sigma^0)=0.                                         \tag{1}
   \]

The literal late-reset cap children have exactly these fields: the old owner
is prescribed to use a finite deterministic deadline, and installing its
complete cap makes its debt zero.

Recursively choose any exact independent product root \(q^n\) Nash against
the actual prescribed payoff of \(\sigma^n\), and put

\[
 \sigma^{n+1}=q^n::\sigma^n.                                \tag{2}
\]

Write

\[
 h_{n,i}=q_i^n,\qquad
 c_n=\prod_i(1-h_{n,i}),\qquad
 s_{n,i}=\prod_{\ell\ne i}(1-h_{n,\ell}).                  \tag{3}
\]

Every \(\sigma^n\) is actual. Player \(b\)'s prescribed strategy still Quits
surely by date \(H+n\): at each added root it either Quits there or, after
Continue, uses its old surely terminating strategy. Exact semantic prefixing
and (1) give

\[
 d_b(\sigma^n)=0\qquad(n\ge0),                              \tag{4}
\]

because nonnegative debt cannot increase under an exact prefix.

## 2. Exact unique-sure backprojection

Fix a depth \(n\) with \(c_n=0\).

If two distinct players Quit surely in \(q^n\), then
\(\sigma^{n+1}\) is a terminal Nash profile against every unilateral
behavioral deviation. Any one deviator leaves another sure quitter at the
new date zero, so the old tail is screened; exact root Nash covers the only
remaining Boolean action comparison.

Suppose instead that \(k\) is the unique sure quitter:

\[
 h_{n,k}=1,\qquad h_{n,i}<1\quad(i\ne k).                   \tag{5}
\]

For every \(i\ne k\), the opponents-Continue factor at this root is zero.
The exact debt action therefore gives

\[
 d_i(\sigma^{n+1})=0\qquad(i\ne k).                         \tag{6}
\]

The terminal gap at the actual child forces

\[
 d_k(\sigma^{n+1})\ge\Gamma.                               \tag{7}
\]

In particular \(k\ne b\), by (4) and (6).

Let

\[
 E_{n,k}
 =Q_k((q^n)_{-k})-C_k((q^n)_{-k};U_k(\sigma^n)).
\]

Since \(k\) is prescribed to Quit surely and \(q^n\) is exact root Nash,

\[
 E_{n,k}\ge0.                                               \tag{8}
\]

Unique sureness gives \(s_{n,k}>0\). The exact debt action and (7) show that
the positive-part bracket is active:

\[
\begin{aligned}
 d_k(\sigma^{n+1})
 &=s_{n,k}d_k(\sigma^n)-E_{n,k},\\
 d_k(\sigma^n)
 &=\frac{d_k(\sigma^{n+1})+E_{n,k}}{s_{n,k}}
 \ge d_k(\sigma^{n+1})
 \ge\Gamma.                                                 \tag{9}
\end{aligned}
\]

The complete cap at the child cannot be the current Quit endpoint, because
the prescribed payoff is that same endpoint while (7) is positive.
Consequently it is exactly:

> force \(k\) to Continue at the new root and, after opponents Continue, use
> an attained complete cap against the old tail \(\sigma^n\).

Such a tail cap is attained by a pure time in

\[
 \{0,\ldots,H+n,\operatorname{Never}\}.                    \tag{10}
\]

Indeed the fixed player \(b\ne k\) still Quits surely by \(H+n\), even after
an arbitrary deviation by \(k\); behavior after that deadline is
outcome-irrelevant, and the unilateral payoff is affine in the stopping-time
law. Thus the child cap is the literal pure time \(T+1\), or Never when the
tail cap is Never.

This proves the first main point:

\[
\boxed{
\begin{array}{c}
\text{unique-sure exact actual child}\\
\text{with a distinct finite-horizon zero-debt anchor}
\end{array}
\Longrightarrow
\begin{array}{c}
\text{same literal child has one fixed debtor }k,\\
d_k\ge\Gamma,\text{ and an attained finite/Never cap.}
\end{array}}                                                \tag{11}
\]

No stationary repetition or limiting-root profile occurs in (11).

## 3. Positive-survival transport for an arbitrary attained cap

The cap-transport calculation does not require the initial cap to be Quit0.
Let an actual terminal-semantic pair \(X=(u,B)\) have
\(d_k(X)>0\), and suppose a literal strategy \(A\) attains \(B_k\). Let \(q\)
be exact root Nash against \(u\) with positive joint survival.

Then \(q_k<1\), \(s_k(q)>0\), and exact root Nash says that Continue is a
maximizing prescribed-payoff endpoint whenever it has positive support.
Changing the tail coordinate from \(u_k\) to \(B_k=u_k+d_k(X)\) raises that
Continue endpoint by exactly \(s_k(q)d_k(X)>0\). Therefore the complete cap
at \(q::X\) is uniquely on the Continue branch and is attained by
Continue-then-\(A\). Moreover,

\[
 d_k(q::X)=s_k(q)d_k(X).                                   \tag{12}
\]

If \(A\) is pure time \(T\), the new cap is pure time \(T+1\); if \(A\) is
Never, it remains Never. This is the arbitrary-cap version of the escaping
clock calculation.

## 4. Bounded capacity makes the last zero-survival child finite

Assume now that the Fin4 game has no uniform-equilibrium payoff. The checked
bounded finite exact-block capacity gives one \(K<\infty\) such that every
finite chronological exact Nash--Bellman block in the canonical payoff box
has total marginal hazard at most \(K\).

For every \(N\), read (2) in its true chronological order:

\[
 q^{N-1},q^{N-2},\ldots,q^0,\sigma^0.                      \tag{13}
\]

More precisely, the nonterminal boxed annotations carry payoffs
\(U(\sigma^N),\ldots,U(\sigma^1)\) and roots
\(q^{N-1},\ldots,q^0\); the terminal annotation carries
\(U(\sigma^0)\) and may be decorated by the all-Continue simplex root. This
is a literal finite exact Nash--Bellman block in the canonical payoff box.
Hence

\[
 \sum_{n<N}\sum_i h_{n,i}\le K
 \qquad(N\ge1),                                             \tag{14}
\]

and therefore

\[
 \sum_n\sum_i h_{n,i}<\infty.                              \tag{15}
\]

Every zero-survival root has at least one sure coordinate and contributes at
least one to the left side of (14). Thus there are only finitely many such
roots.

There are two possible ways to initialize the eventual positive-survival
ray.

- If there is no zero-survival root, the terminal gap at the actual profile
  \(\sigma^0\), together with \(d_b(\sigma^0)=0\), gives some
  \(k\ne b\) with

  \[
  d_k(\sigma^0)\ge\Gamma.
  \]

  This complete cap is attained by a pure time in
  \(\{0,\ldots,H,\operatorname{Never}\}\): the distinct player \(b\)
  surely stops by \(H\), even after an arbitrary deviation by \(k\).
  Put \(m=0\).

- If zero-survival roots exist and one has two sure quitters, the terminal
  Nash conclusion of Section 2 already applies. Otherwise let \(L\) be the
  last zero-survival index. Its unique sure quitter \(k\) gives, at the actual
  child \(\sigma^{L+1}\), the debt and attained cap in (7)--(11). Put
  \(m=L+1\).

In either nonterminal case, \(d_k(\sigma^m)\ge\Gamma\), the cap is attained
by a finite pure time or Never, and every root \(q^n\) with \(n\ge m\) has
positive joint survival. Iterating (12) yields

\[
 d_k(\sigma^N)
 =d_k(\sigma^m)
   \prod_{n=m}^{N-1}s_{n,k}
 \qquad(N>m).                                               \tag{16}
\]

Since \(s_{n,k}\ge c_n\) and the marginal hazards are summable, the infinite
product is positive. Consequently there is one constant \(\gamma_k>0\)
such that

\[
 d_k(\sigma^N)\ge\gamma_k>0
 \qquad(N\ge m).                                             \tag{17}
\]

The same attained finite/Never cap shifts by one date at every later prefix.
Meanwhile the fixed anchor \(b\) continues to stop surely by \(H+N\) and
continues to have zero debt.

Therefore an infinite exact prefix construction has the exhaustive output

\[
\boxed{
\begin{array}{ll}
\text{(i)}&\text{some zero-survival root has two sure quitters, giving an}\\
&\text{unrestricted terminal Nash profile;}\\[2pt]
\text{(ii)}&\text{there is no zero-survival root, and from }\sigma^0
\text{ one fixed}\\
&k\ne b\text{ carries a uniformly positive attained cap through every}\\
&\text{positive-survival exact prefix;}\\[2pt]
\text{(iii)}&\text{zero-survival roots exist and are all unique-sure; from the}\\
&\text{actual child after the last one, its fixed }k\ne b\text{ carries the}\\
&\text{uniformly positive attained cap through every later root.}
\end{array}}                                                \tag{18}
\]

In both (ii) and (iii), the cap shifts by one date at each later prefix (or
remains Never), while \(b\) remains the fixed finite-horizon zero-debt
anchor.

This is a literal source theorem. When zero-survival roots occur, the source
of the eventual shifted ray is the finite actual child
\(\sigma^{L+1}\), not the stationary repetition of a limit root. When none
occurs, it is the given actual anchored source \(\sigma^0\).

## 5. Exact relation to the late-reset renewal packet

At a sufficiently late reset child from
CODEX_HAHN__LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE, take that actual
child as \(\sigma^0\). Its old cap owner \(b\) is prescribed to use a finite
deadline and has zero debt. Hahn's singleton-wall theorem says that every
first exact root has fixed absorption and fixed debt expenditure.

If the first root has positive survival, Hahn's renewed cap-clock ray starts.
If it has zero survival, Sections 2--4 above apply directly. Thus the
zero-survival exception does not require the compact stationary
singleton-handoff bridge. It either gives a two-sure terminal Nash profile or
enters an arbitrary finite/Never cap ray on the same literal genealogy.

The cap after the last unique-sure root need not be Quit0 and need not be
close to the singleton reward. Therefore the fixed singleton-wall
debt/absorption expenditure is not regenerated there. What is regenerated is
the exact cap clock and its positive complete debt.

## 6. Repeated renewal and the remaining horizontal budget

The result above removes the finite zero-survival source-entry seam. It does
not by itself concatenate separate late-reset renewal rays. For completeness,
the uniform constants imply the following exact global account.

Suppose an infinite sequence of renewal phases has actual cap-pinned sources
\(S_m\). Let \(F_m\) be the front actual profile reached from \(S_m\) by its
finite exact prefix block, before installing the old owner's complete cap.
Let the resulting horizontal cap child be the next source \(S_{m+1}\). Put

\[
 V_m=D(S_m)-D(F_m),\qquad
 H_m=D(S_{m+1})-D(F_m).                                    \tag{19}
\]

The fixed first-root theorem gives \(V_m\ge c_0>0\), uniformly in \(m\), and
the literal identity is

\[
 D(S_{m+1})-D(S_m)=H_m-V_m.                                \tag{20}
\]

Since total debt is bounded and nonnegative, infinitely many phases satisfy

\[
 H_m\ge c_0/2.                                              \tag{21}
\]

Otherwise (20) would eventually decrease total debt by at least \(c_0/2\)
per phase.

Let \(b_m\) be the cap owner installed from \(F_m\) to \(S_{m+1}\), and let
\(g_m=d_{b_m}(F_m)\) be its exact payoff gain. Its own cap is invariant under
the best-response replacement and its new debt is zero. Therefore

\[
 H_m=-g_m+
 \sum_{i\ne b_m}
   \bigl(d_i(S_{m+1})-d_i(F_m)\bigr).                       \tag{22}
\]

At every index satisfying (21), some outsider \(i\ne b_m\) has

\[
 d_i(S_{m+1})-d_i(F_m)\ge c_0/6.                            \tag{23}
\]

By Fin4 pigeonhole, one ordered pair \((b,i)\), \(b\ne i\), realizes (23)
infinitely often.

This is a fixed spectator-debt recharge, not a contradiction. Exact
best-response cycles can repeatedly remove one player's debt and create
another's, and the general recharge identity was already known. Neither
bounded exact-block capacity nor finiteness of the owner label charges the
horizontal cap updates. The new literal theorem is (18); equations
(19)--(23) state sharply why repeating distinct renewed rays still stops.

## Boundary tests

### The distinct anchor is essential for finite cap attainment

If the sole finite-horizon quitter is the deviating player itself, replacing
its strategy can expose an unbounded opponent tail. A complete cap can then
be approached only by clocks tending to infinity. In (11), the zero-debt
anchor \(b\) is distinct from the unique debtor \(k\), so this failure is
excluded rather than assumed away.

### Zero survival is not stationary

Nothing above repeats a root. The actual child is
\(q^n::\sigma^n\), its continuation is the literal \(\sigma^n\), and its cap
uses that same tail. A stationary repetition can have different
unrestricted caps and is unnecessary for (11)--(18).

### The literal unique-sure child cannot be a Quit0-pinned source

This is an exact obstruction, not a missing compactness argument. At a
unique-sure child owned by \(k\), the prescribed payoff is its current Quit
endpoint:

\[
 U_k(q^n::\sigma^n)=Q_k((q^n)_{-k}).
\]

But (7) says its complete cap is strictly larger by at least \(\Gamma\).
Therefore Quit0 does not attain that cap. The cap is necessarily the
Continue-then-tail-cap strategy identified above. Repeating the same root
stationarily can create a different profile with a Never cap and can enter
the checked singleton-base handoff, but it changes the continuation law and
is not a literal descendant of this finite child. Hence the stationary
same-marginal bridge cannot upgrade (11) to an actual Quit0-pinned renewal
without exactly the ancestry substitution that the present theorem avoids.

### Finitely many zero roots uses capacity, not pointwise compactness

The conclusion is not that a convergent sequence of roots eventually has
positive survival. It follows from the additive exact-block bound (14):
each zero-survival row spends at least one unit of marginal hazard in the
same nested finite block family.

### The front limit still loses the clocks

Even with (17), every fixed front window of the reversed blocks can converge
to all Continue while the anchor and the profitable pure time move to
infinity. Thus compact convergence of the front roots does not produce a
terminal equilibrium or preserve the attained cap at a finite date.

## Scope and nonclaims

This note proves an arbitrary-source, actual-profile cap-attainment and
eventual-shift theorem for the zero-survival finite child (and the initial
anchored source when no zero root occurs). It preserves all
behavioral caps, including Never and arbitrarily late deviations, because the
fixed distinct anchor makes the relevant response problem finite.

It does not prove a fixed singleton-wall margin after the last zero root, a
renewable debt-expenditure constant on the eventual shifted ray, a forward
infinite chronology, a projective timing compiler, or a uniform-equilibrium
payoff. Repeated owner-to-owner renewal still contains horizontal cap-child
seams with the spectator recharge (23).

## Next exact question

Can the literal exact ray in (18), carrying a fixed finite-horizon zero-debt
anchor \(b\) and a fixed positive-debt shifted cap \(k\ne b\), be converted
into terminal approximate Nash profiles without passing to the all-Continue
front limit? Equivalently, does the two-cap projective family admit a
finite-deadline compatibility selection, or can one build an exact reward
table where the two clocks escape and the terminal gap stays uniformly on
the shifted-cap owner?
