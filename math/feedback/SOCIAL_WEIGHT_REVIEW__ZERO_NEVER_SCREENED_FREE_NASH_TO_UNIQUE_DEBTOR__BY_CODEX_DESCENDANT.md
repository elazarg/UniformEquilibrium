# Review of zero-Never screened free Nash contraction

Reviewer: `CODEX_DESCENDANT`

Verdict: **PASS as ordinary mathematics, with one terminology qualification.**

The construction genuinely contracts a minimum-realizing family whose joint
Never mass tends to zero to either an actual off-minimum paid port or a joint
minimum cluster with exactly one positive debt coordinate.  The late-time
estimate controls the complete behavioral response class.  I found no timing
counterexample to the argument.

The qualification is that “source-attached” means the literal
profile-by-profile ancestry and the unchanged stopping law of the selected
player.  The proof does not by itself reconstruct a complete minimum-atom
producer, a positive marked atom, or a Nash--Bellman chronology at the new
minimum cluster.  The note mostly says this already; the boxed conclusion
should not be read more strongly.

## 1. Fixed label and cutoff

For independent marginal stopping laws,

\[
 \Pr(\mathsf{Never})=\prod_{i<4}\zeta_{i,n}.
\]

At every index some factor is at most the fourth root of the product.  A
finite pigeonhole subsequence fixes one label (k), and its marginal Never
mass tends to zero.  This is exact.  The argument needs only discard finitely
many indices before using the displayed strict inequality
(zeta_{k,n}<\varepsilon_n); the proposed formula for \(\varepsilon_n\)
has that property once \(\zeta_{k,n}<1\), including the case
\(\zeta_{k,n}=0\).

Since

\[
 \Pr(T_k>H)\downarrow \Pr(T_k=\infty)=\zeta_{k,n}
\]

for each fixed (n), a finite (H_n) satisfying the required tail bound
exists.  No common cutoff is asserted or needed.

## 2. Finite game and behavioral realization

Holding player (k)'s literal stopping law fixed leaves a finite normal-form
game for the other three players with action set

\[
 \{0,\ldots,H_n\}\cup\{\infty\}.
\]

A mixed Nash equilibrium exists.  Nash mixing is independent across players,
and every probability law on this finite subset of
(\mathbb N\cup\{\infty\}) has the canonical behavioral-hazard realization
along the unique live history.  Thus the selected point is an actual quitting
profile, not a correlated timing law.

Changing the three free strategies simultaneously can be written as three
literal unilateral complete-strategy replacements in any fixed order.  This
is ancestry only, exactly as the note states.

## 3. Late time versus Never

Fix a free player (i) and (s>H_n).  Couple the response QuitAt (s) with
Never while leaving all opponents' clocks fixed.

* If another free opponent has a finite clock, it is at most (H_n), so both
  responses produce the same earlier outcome.
* Otherwise both other free opponents are Never.  The two outcomes can differ
  only if (T_k>H_n).  This includes (T_k=s), (T_k>s), and
  (T_k=\infty).

Therefore the payoff difference is at most

\[
 2M\Pr(T_k>H_n)\le2M\varepsilon_n.
\]

This bound is sharp in its probability mode.  A minimal test has (H_n=0),
the two other free players Never, and player (k) Quit at date zero except on
an event of mass \(\varepsilon_n\); reward rows differing by (2M) make the
late-versus-Never payoff difference equal to the bound.  The example confirms
rather than falsifies the coupling.

Finite-game Nash controls every response time through (H_n) and Never.
The coupling controls every later finite time.  Finally, any complete
behavioral response induces a probability law on pure stopping times, and its
payoff is the corresponding expectation.  Taking the supremum therefore
gives

\[
 d_i(\rho_n)\le2M\varepsilon_n
 \quad(i\ne k)
\]

against the unrestricted behavioral class.  No finite-horizon cap is being
substituted.

## 4. Compact dispatch

The semantic/law carrier is compact.  At a selected cluster (y), the three
free debts vanish.  If (D(y)=D_*>0), nonnegativity and additivity of debt
force

\[
 d_k(y)=D_*,\qquad d_i(y)=0\ (i\ne k).
\]

The joint Never mass is at most the unchanged marginal Never mass of (k),
so it tends to zero.  More strongly, each realizing profile retains the
literal (k)-strategy selected from the incoming family.

If (D(y)>D_*), sufficiently late targets are genuinely off minimum.  The
actual-reach paid-row theorem used in
`formalized/ARBITRARY_CLOCK_MINIMUM_PURIFICATION_TO_OFF_MINIMUM_PAID_PORT.md`
applies to one such actual target and supplies the outgoing paid port; the
three-replacement ancestry attaches it to the corresponding incoming
profile.  No fixed lower bound on the amount of off-minimum excess is needed.

## 5. Exact consequence and remaining boundary

The valid reduction is

\[
 \text{joint Never mass tending to zero at a positive minimum}
 \Longrightarrow
 \begin{cases}
 \text{actual off-minimum paid port},\\
 \text{minimum cluster with unique debtor }k,
 \end{cases}
\]

where in the second arm the three other players have zero unrestricted debt
and the realizing sequence preserves (k)'s marginal stopping law with
Never mass tending to zero.

This is a genuine chamber contraction.  It is not yet a consumer of the
unique-debtor output.  In particular it does not show that the debtor's best
reply preserves the other three zeros, nor does it turn the three replacement
ancestry into temporal Nash--Bellman edges.  Subject to that explicit
boundary, I found no mathematical gate blocker.
