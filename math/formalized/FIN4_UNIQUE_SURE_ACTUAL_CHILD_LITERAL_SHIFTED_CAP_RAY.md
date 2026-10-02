# A unique-sure actual child enters a literal shifted-cap exact ray

Author: CODEX_SPINOZA

Independent reviews:
[CODEX_GROMOV](../feedback/CODEX_SPINOZA__UNIQUE_SURE_ACTUAL_CHILD_TO_LITERAL_SHIFTED_CAP_RAY__BY_CODEX_GROMOV.md)
and
[CODEX_HAHN](../feedback/CODEX_SPINOZA__UNIQUE_SURE_ACTUAL_CHILD_TO_LITERAL_SHIFTED_CAP_RAY__BY_CODEX_HAHN.md).

The reviewed source note is frozen at SHA-256
`dd1da90ccc9fafb7fbc994799d708148470e641d843849aaec0aab65f785133d`.
Both reviews record a PASS on that exact revision.

## Exact statement

Let \(I=\operatorname{Fin}4\), let \(r\) be a bounded quitting reward table,
and suppose that the game has no uniform-equilibrium payoff. Assume moreover
that one fixed \(\Gamma>0\) satisfies

\[
 \max_i d_i(\sigma)\ge\Gamma
\]

for every actual behavioral profile \(\sigma\), where \(d_i\) is complete
terminal-semantic debt against all unilateral behavioral deviations.

Let \(\sigma^0\) be an actual profile with a player \(b\) such that:

1. under \(b\)'s prescribed strategy, \(b\) Quits surely by a finite date
   \(H\), independently of the other players' strategies; and
2. \(d_b(\sigma^0)=0\).

Recursively choose any exact independent product root \(q^n\) Nash against
the prescribed payoff of \(\sigma^n\), and put

\[
 \sigma^{n+1}=q^n::\sigma^n.
\]

Write \(h_{n,i}\) for player \(i\)'s Quit probability in \(q^n\),

\[
 c_n=\prod_i(1-h_{n,i}),\qquad
 s_{n,i}=\prod_{\ell\ne i}(1-h_{n,\ell}).
\]

Then exactly one of the following exhaustive alternatives occurs.

1. Some zero-survival root \(q^n\), meaning \(c_n=0\), has at least two
   sure quitters. Then the literal child \(\sigma^{n+1}\) is a terminal Nash
   profile against every unilateral behavioral deviation.

2. No zero-survival root occurs. There is a fixed \(k\ne b\), selected at
   \(\sigma^0\), whose complete cap is attained by a finite pure time or
   Never and whose debt is at least \(\Gamma\). The same cap shifts by one
   date through every prefix (or remains Never), and there is
   \(\gamma_k>0\) such that

   \[
   d_k(\sigma^N)\ge\gamma_k\qquad(N\ge0).
   \]

3. Zero-survival roots occur, and each of them has a unique sure quitter.
   There are only finitely many such roots. If \(L\) is the last
   zero-survival index and \(k\) its unique sure quitter, then \(k\ne b\),
   the literal actual child \(\sigma^{L+1}\) has

   \[
   d_k(\sigma^{L+1})\ge\Gamma,
   \]

   and its complete cap is attained by a finite pure time or Never. The same
   cap shifts by one date through every later prefix (or remains Never), and
   there is \(\gamma_k>0\) such that

   \[
   d_k(\sigma^N)\ge\gamma_k\qquad(N\ge L+1).
   \]

In alternatives 2 and 3, \(b\) remains a prescribed sure quitter by date
\(H+N\) and satisfies \(d_b(\sigma^N)=0\) at every depth. The source of the
shifted ray is respectively the given actual profile \(\sigma^0\) or the
finite actual child \(\sigma^{L+1}\). No stationary repetition or limiting
profile is substituted.

## Conjecture-facing change

The reviewed late-reset recursion previously left a zero-joint-survival
first root as a finite-source exception. A compact-limit argument could pass
from such roots to a stationary unique-sure profile, but that changed the
literal tail and lost source ancestry.

This packet eliminates that finite-source exception. The persistent distinct
finite-horizon anchor makes the unique debtor's unrestricted cap attain its
maximum at a finite pure time or Never on the actual child itself. Bounded
exact-block capacity makes zero-survival roots finite in number; thereafter
the attained cap and a positive debt floor move through one literal exact
prefix genealogy.

This is a strict source reduction, not a terminal consumer. The surviving
cap and anchor move to the far end of the reversed finite blocks, and their
projective timing is not controlled by local convergence of the front roots.

## Definitions and assumptions

Players randomize independently at every date conditional on the unique
public all-Continue history. A unilateral deviator may replace their complete
behavioral strategy, including by any randomized finite or unbounded stopping
law or literal Never.

For an actual profile \(\sigma\), let \(U_i(\sigma)\) be prescribed terminal
payoff and \(B_i(\sigma)\) the supremum over all such unilateral deviations.
Then

\[
 d_i(\sigma)=B_i(\sigma)-U_i(\sigma)\ge0.
\]

An exact product root is a mixed Nash profile of the one-stage Boolean
Quit/Continue game with the displayed tail payoff on the all-Continue
outcome. Prefixing is literal: after all players Continue at the new root,
play uses the old behavioral profile.

The hypothesis that \(b\) Quits surely by \(H\) independently of the other
players means that this same stopping guarantee survives every unilateral
replacement by a distinct player. It is stronger than prescribed play merely
being terminal by \(H\), and it is exactly what makes the distinct player's
complete response problem finite up to the Never class.

## Source correspondence

The actual anchored sources are supplied by the reviewed packet
[FIN4_LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE.md](FIN4_LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE.md):
after installing an attained finite clock, the old owner is a finite-horizon
sure quitter with zero debt.

The reviewed source theorem is
[CODEX_SPINOZA__UNIQUE_SURE_ACTUAL_CHILD_TO_LITERAL_SHIFTED_CAP_RAY.md](../notes/CODEX_SPINOZA__UNIQUE_SURE_ACTUAL_CHILD_TO_LITERAL_SHIFTED_CAP_RAY.md),
frozen at the SHA displayed above.

The exact semantic prefix debt formula and monotonicity are
`quittingTerminalSemanticDebt_prefix_eq_blockAct` and
`quittingTerminalSemanticDebt_prefix_le` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
Two-sure screening is in
`UniformEquilibrium/Diagnostics/Quitting/TwoSureProductRootTailScreen.lean`.

The counterexample-side capacity theorem is
`finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
in
`UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`.
It bounds finite exact Nash--Bellman blocks in the full canonical payoff box;
it has no terminal-boundary or punishment-floor premise.

The new ordinary mathematics is the actual-child cap-attainment argument,
the arbitrary attained-cap transport identity, and their combination with
the exact-block capacity theorem on the literal nested genealogy.

## Proof

### The anchor persists

At every added root, \(b\) either Quits there or, after Continue, uses its old
surely terminating strategy. Thus \(b\) Quits surely by \(H+n\) at
\(\sigma^n\). Exact prefixing cannot increase any complete debt. Since debts
are nonnegative and \(d_b(\sigma^0)=0\),

\[
 d_b(\sigma^n)=0\qquad(n\ge0).
\]

### Classify a zero-survival root

Fix \(n\) with \(c_n=0\). If two players Quit surely in \(q^n\), every
unilateral deviator leaves another sure quitter at the new date zero. The old
tail is screened, and exact root Nash covers the remaining Boolean action
comparison. Hence \(\sigma^{n+1}\) is terminal Nash against the unrestricted
behavioral class.

Suppose instead that \(k\) is the unique sure quitter. For every \(i\ne k\),
the opponents-Continue factor is zero, so the exact prefix debt formula gives

\[
 d_i(\sigma^{n+1})=0.
\]

The global gap therefore forces

\[
 d_k(\sigma^{n+1})\ge\Gamma,
\]

and the persistent zero-debt anchor gives \(k\ne b\).

Let \(E_{n,k}\) be the one-stage advantage of Quit over Continue for \(k\)
against the prescribed tail payoff. Exact root Nash and \(h_{n,k}=1\) give
\(E_{n,k}\ge0\). Unique sureness gives \(s_{n,k}>0\). Since the child debt is
positive, the positive-part debt formula is active and yields

\[
 d_k(\sigma^{n+1})
 =s_{n,k}d_k(\sigma^n)-E_{n,k},
\]

so \(d_k(\sigma^n)\ge d_k(\sigma^{n+1})\ge\Gamma\).

At the child, \(k\)'s prescribed payoff is exactly its current Quit endpoint.
Because its complete debt is positive, current Quit cannot attain its cap.
The cap is Continue at the new root followed by a cap against the old tail.
The distinct player \(b\) still Quits surely by \(H+n\) after an arbitrary
deviation by \(k\). Hence all finite times after \(H+n\) are outcome-equivalent
to Never, and the cap is attained by one pure time in

\[
 \{0,\ldots,H+n,\operatorname{Never}\}.
\]

The cap at the child is this time shifted by one, or Never.

### Transport any attained positive cap

Let an actual semantic pair \(X=(u,B)\) have \(d_k(X)>0\), and let a literal
strategy \(A\) attain \(B_k\). Let \(q\) be exact root Nash against \(u\) and
have positive joint survival. Then \(k\) has positive Continue support, so
its prescribed Continue endpoint is root-optimal. Replacing only the tail
coordinate \(u_k\) by \(B_k=u_k+d_k(X)\) raises that endpoint by exactly
\(s_k(q)d_k(X)>0\), while the current Quit endpoint is unchanged. Therefore
the complete cap at \(q::X\) is uniquely on the Continue branch, is attained
by Continue-then-\(A\), and

\[
 d_k(q::X)=s_k(q)d_k(X).
\]

A finite pure time shifts by one; Never remains Never.

### Capacity leaves a final positive-survival tail

For every \(N\ge1\), form a canonical boxed finite exact Nash--Bellman block
whose nonterminal payoffs and roots, in chronological order, are

\[
 (U(\sigma^N),q^{N-1}),\ldots,(U(\sigma^1),q^0),
\]

and whose terminal payoff is \(U(\sigma^0)\), decorated by the all-Continue
simplex root. The checked capacity theorem gives one \(K<\infty\) with

\[
 \sum_{n<N}\sum_i h_{n,i}\le K
\]

for every \(N\). Thus all marginal hazards are summable. Every
zero-survival root has a sure coordinate and contributes at least one, so
there are only finitely many zero-survival roots.

If none occurs, the global gap at \(\sigma^0\) and \(d_b(\sigma^0)=0\) choose
\(k\ne b\) with \(d_k(\sigma^0)\ge\Gamma\). The distinct sure anchor makes
this cap attained by a finite pure time or Never. Set \(m=0\).

If zero-survival roots occur, the two-sure case has already terminated.
Otherwise let \(L\) be the last such index and set \(m=L+1\). The
unique-sure argument supplies \(k\ne b\), debt at least \(\Gamma\), and an
attained finite/Never cap at \(\sigma^m\).

Every root \(q^n\) with \(n\ge m\) has positive survival. Repeated cap
transport gives

\[
 d_k(\sigma^N)=d_k(\sigma^m)
   \prod_{n=m}^{N-1}s_{n,k}\qquad(N>m).
\]

Since \(s_{n,k}\ge c_n\), all factors are positive, and the marginal hazards
are summable, the infinite product is positive. This proves a uniform
positive debt floor and the literal cap shift in alternatives 2 and 3.

## Boundary tests

### The distinct sure anchor is essential

If the only finite-horizon quitter is the deviator, replacing that strategy
can expose an unbounded opponent tail. A complete cap may then be approached
only by clocks tending to infinity. Here \(b\ne k\), so the opponent stopping
guarantee survives \(k\)'s deviation and gives actual finite/Never
attainment.

### The literal unique-sure child is not Quit0-pinned

At that child, the unique sure quitter's prescribed payoff equals its current
Quit endpoint, while its complete debt is at least \(\Gamma\). Thus Quit0
cannot attain the cap. The cap necessarily lies on the Continue branch.
Repeating the root stationarily may create a different profile with a Never
cap, but it changes the tail law and is not a literal descendant. This is why
the theorem yields an arbitrary shifted cap, not a renewed singleton-wall
Quit0 source.

### All-Continue prefixes expose the projective obstruction

An exact all-Continue root has positive joint survival and zero hazard. It
can shift both the sure anchor and the profitable cap without spending any
exact-block capacity. Therefore finite cap attainment and positive debt do
not by themselves make the clock visible in a fixed front window. The proof
claims only a far-end shifted ray.

## Adapter and consumer

At a late reset child in
[FIN4_LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE.md](FIN4_LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE.md),
the old owner \(b\) has installed a finite deterministic cap, hence is a
finite-horizon sure quitter with zero debt. This supplies the exact source
hypotheses.

The positive-survival first-root branch is already the reviewed renewed
escaping-cap-clock source. The present packet consumes its zero-survival
exception: a two-sure root is terminal Nash; a unique-sure root enters the
literal shifted-cap ray; and if no zero root occurs, that ray starts at the
given source.

No named existing consumer accepts the remaining shifted-cap ray. Its fixed
anchor and profitable response occur at the far end of reverse-nested exact
blocks. A downstream theorem must temporalize this projective two-clock
object, or charge a horizontal cap installation, without replacing the
actual source by a stationary law.

## Lean handoff

Suggested declarations are:

```
uniqueSurePrefix_fixedAnchor_attains_shiftedCap

positiveSurvivalPrefix_transports_attainedCap

finite_zeroSurvival_indices_of_boundedExactBlockCapacity

anchoredExactPrefixSequence_terminal_or_eventualShiftedCap
```

The first should combine the exact terminal-semantic prefix debt formula,
two-sure screening, the terminal gap, and finite pure-time extremality under
a distinct sure opponent. The second is a direct specialization of the
exact prefix cap/debt formula. The third should build the reversed finite
block with an explicit all-Continue terminal decoration. The final theorem
should state the three alternatives separately so the no-zero-root case does
not rely on a nonexistent last index.

Useful finite tests are: two sure coordinates; one unique sure coordinate;
no zero-survival root; an attained finite cap; and an attained Never cap.

## Scope and nonclaims

This packet proves ordinary mathematics and assigns no Lean seal to the new
theorem.

It does not prove that the shifted cap is Quit0, that the literal child is a
singleton-wall source, that later prefixes spend a fixed positive amount of
hazard or debt, or that the reverse-nested blocks define a forward infinite
Nash--Bellman chronology. It does not charge the horizontal installation of
the cap, bound the resulting cross-player debt recharge, produce a terminal
approximate Nash family, or prove a uniform-equilibrium payoff.
