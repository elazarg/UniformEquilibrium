# Independent falsification of `OPPONENT_TIGHT_POSITIVE_MINIMUM_REALIZATION`

**Reviewer:** `CODEX_EULER`  
**Date:** 2026-08-26  
**Verdict:** **PASS as ordinary mathematics; two mandatory statement repairs
before export/formalization packaging.**

I independently reconstructed the weak-law argument and attempted to break
both the uniform behavioral-cap passage and the one-proper minimum argument.
I found no mathematical counterexample.  The theorem genuinely realizes an
opponent-tight semantic limit against unrestricted behavioral deviations and
gives the claimed sharp negative-singleton classification when exactly one
limiting clock is proper.

The current note already incorporates the first review's important
subsequence and late-or-Never repairs.  Before it is treated as an exact
formalization packet, it must additionally state the nontrivial finite player
hypothesis and type its weak convergence through the one-point compact
stopping-law space.  These are statement/type repairs, not changes to the
proof or conclusion.

## 1. Exact claim reviewed

For a sequence of actual behavioral profiles whose terminal semantic pairs
converge to `z`, pass to a fixed subsequence on which all players' complete
stopping laws converge weakly on

\[
K=\mathbb N\cup\{\infty\}.
\]

The note claims:

1. if every player faces a uniformly tight opponent stopping clock, then the
   profile reconstructed from the limiting laws realizes the whole semantic
   point `z`, including unrestricted behavioral caps;
2. two proper limiting clocks imply this opponent-tightness condition;
3. hence every law-limit subsequence of a nonattained point has at most one
   proper clock and has a fixed common opponent late-or-Never event;
4. at a nonattained global debt minimizer with exactly one proper clock `k`,
   only cap coordinate `k` can jump, Never is its unique excess endpoint, and

   \[
   r_k(\{k\})<0,
   \qquad
   0<\widehat b_k-b_k
      \le-q_{-k}r_k(\{k\});
   \]
5. therefore every selected compactified realizing subsequence of a
   nonattained minimum is either all-nonproper or is in this one-proper
   negative-singleton arm.

## 2. One-point topology and compactification: PASS with a typing repair

The correct space is

```text
Math.Probability.CompactStoppingTime = WithTop Nat
```

with its one-point compactification topology, not `Option Nat` equipped with
its ordinary discrete topology.  Under this topology:

* each finite singleton `{t}` is clopen;
* each finite-prefix complement
  `{H+1,H+2,...,infinity}` is clopen; and
* `{infinity}` is closed but not open, so its mass is not a continuous
  coordinate.

Thus weak convergence passes every finite-date mass and every fixed cutoff
tail mass, exactly the coordinates used in the proof.  It does not pass the
Never atom itself, and the note correctly makes no such inference for the
approximating laws.

Probability laws on this compact metrizable space are compact in the weak
topology.  Since the player set is finite, a single subsequence makes every
marginal converge.  `CompactStoppingLaw.toPMF` and
`CompactStoppingLaw.ofPMF` identify those probability measures with the
project's stopping-law PMFs, and
`quittingStoppingLawBehaviorStrategy` realizes every limiting PMF by a
literal behavioral strategy.  Independence of players' private
randomizations makes the reconstructed joint law the product of the limiting
marginals.

### Mandatory statement repair 1

The theorem must explicitly say:

> Fix a finite player type `I` with at least two players, a quitting reward
> table on `I`, and a finite reward bound `R`.

The notation `M_{-i}=min_{j ne i}T_j` and the prescribed-payoff proof's choice
of an opponent set require this nontriviality assumption.  In Lean-facing
language, use `[Fintype I] [DecidableEq I] [Nontrivial I]` (or an equivalent
cardinality hypothesis).

### Mandatory statement repair 2

Type the convergent laws as `CompactStoppingLaw` on `WithTop Nat` and only
then use `toPMF` for hazard reconstruction.  Writing merely “PMFs on
`Option Nat` converge weakly” is ambiguous because the default discrete
topology would make the compactness assertion false.

## 3. Opponent-tight prescribed payoff convergence: PASS

For fixed `H`, absorption by time `H` is determined by finitely many clopen
cylinder coordinates, so its payoff moment converges.  The discarded part is
bounded by

\[
R\Pr(\min_iT_i^n>H)
 \le R\Pr(M_{-i_0}^n>H)
\]

for any fixed player `i_0`.  Opponent tightness makes this error uniformly
small.  Fixed-tail clopen convergence transfers the same estimate to the
limiting product profile.  Hence the prescribed payoff vector converges to
that of the reconstructed profile.

No continuity at the joint all-Never point is silently assumed; opponent
tightness is exactly what removes its possible contribution.

## 4. Uniform convergence of unrestricted caps: PASS

For player `i`, write `v_{i,n}(t)` for the payoff from deterministic Quit time
`t`, including Never.  Every fixed finite `t` is continuous in the opponents'
weak laws.  If `s,t>H`, the two deviations coincide on the event that an
opponent stops by `H`; bounded rewards therefore give

\[
|v_{i,n}(s)-v_{i,n}(t)|
 \le 2R\Pr(M_{-i}^n>H).
\]

Compare every late `t` to `H+1`.  For fixed `H`, the corresponding limiting
opponent-tail probability is the limit of the approximating clopen-tail
probabilities, and is bounded by their `limsup`.  Opponent tightness therefore
makes both tail oscillation terms small.  The finitely many times through
`H+1` converge uniformly simply because the set is finite.  This proves

\[
\sup_{t\in K}|v_{i,n}(t)-v_{i,\infty}(t)|\longrightarrow0.
\]

The checked theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` identifies the supremum
over this menu with the supremum over all unilateral behavioral strategies.
Consequently every unrestricted behavioral cap converges.  This is not a
stationary, finite-horizon, or supplied-deviation-only argument.

The standard escaping-clock regression—both players deterministically Quit
at date `n`—does not falsify the theorem: every relevant opponent-tail
probability is one for fixed `H` and large `n`, so opponent tightness fails
maximally.

## 5. Two-proper criterion and subsequence quantifiers: PASS

If limiting law `mu_j` is proper, its fixed cutoff tail masses tend to zero as
`H` tends to infinity.  Weak convergence of the clopen tails then gives

\[
\limsup_n\Pr(T_j^n>H)=\mu_j((H,\infty]).
\]

With two distinct proper players, every player has a proper opponent, so
opponent tightness holds.

For a nonattained point, a fixed compactified law-limit subsequence can
therefore have at most one proper coordinate.  If exactly `i` is proper,
choose that `i`; if none is proper, choose any `i`.  All opponents of the
chosen player have positive limiting Never mass, so

\[
q_{-i}=\prod_{j\ne i}\mu_j(\{\infty\})>0.
\]

For every fixed `H`, independence and clopen-tail convergence actually give
a limit, stronger than the displayed `limsup`, bounded below by `q_{-i}`.
Thus any `0<kappa<=q_{-i}` works.  The current note correctly makes `i` and
`kappa` depend on the selected compactified subsequence and correctly calls
the finite-`n` event late-or-Never rather than literal Never.

## 6. One-proper global-minimum branch: PASS

Let `k` be the unique proper player.  Its clock makes total absorption tight,
so prescribed payoffs converge to those of the reconstructed actual profile:

\[
U(\widehat\sigma)=u.
\]

For each `j ne k`, player `k` is a proper opponent, so the coordinatewise cap
argument gives `B_j(\widehat\sigma)=b_j`.  Writing
`widehat b_k=B_k(\widehat\sigma)`, actual carrier membership and global
minimality yield

\[
D(\operatorname{Sem}(\widehat\sigma))
 =D(z)+\widehat b_k-b_k\ge D(z),
\]

hence `widehat b_k>=b_k`.

For every fixed finite `t`, convergence and the approximating cap inequality
give `v_k(t)<=b_k`.  Therefore the supremum of all finite pure times is at
most `b_k`.  If `widehat b_k=b_k`, every semantic coordinate agrees with
`z`, contradicting nonattainment.  Thus

\[
\widehat b_k>b_k\ge\sup_{t<\infty}v_k(t).
\]

Pure-time extremality leaves only the Never point of the menu to attain the
larger cap, so `widehat b_k=v_k(infinity)`.

Finally, dominated convergence gives the exact late-finite identity

\[
v_k(t)\longrightarrow
v_k(\infty)+q_{-k}r_k(\{k\}).
\]

On the event that some opponent stops finitely, sufficiently late Quit and
Never induce the same terminal coalition.  On the all-opponents-Never event,
finite Quit pays the singleton reward while Never pays zero.  Since the
left-hand limit is bounded by `b_k`, the claimed inequalities and strict
negative singleton sign follow.  The factor `q_{-k}` and the inequality
orientation are both sharp.

The proof in fact uses global minimality rather than the numerical positivity
of `D_*` at this algebraic step.  Keeping `D_*>0` is appropriate for the named
frontier application and causes no defect.

## 7. Novelty and overlap

The late-finite/Never formula and the qualitative negative-singleton boundary
overlap with Proposition 2 and Proposition 3 of
`CODEX_CEDAR__STOPPING_TIME_COMPACT_GAME`.  That earlier ordinary-mathematics
note does not prove uniform cap convergence under opponent tightness, the
two-proper realization criterion, or the global-minimum quantitative jump
bound.

The checked `PositiveDebtTerminalSemanticNonattainment.lean` supplies an
all-nonproper escaping-clock regression whose global minimum is zero.  It
does not subsume this theorem.  The strategically precompact watchdog results
use proper approximation to build auxiliary Nash profiles; they do not
realize arbitrary terminal-semantic limits.  Existing minimum-fiber theorems
remain on the closed semantic carrier and likewise do not identify a literal
profile.

The genuinely new content is therefore:

* opponent-tight convergence of the full unrestricted semantic pair;
* the two-proper-clock attainment criterion; and
* the per-subsequence reduction of one-proper nonattainment to the sharp
  negative-singleton Never jump.

## 8. Formalization and export recommendation

After the two exact statement repairs above, the result is mathematically
ready for a narrow formalization packet.  The likely checked dependencies are:

* `CompactStoppingLaw`, `CompactStoppingLaw.toPMF`, and
  `CompactStoppingLaw.ofPMF` in
  `MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`;
* `quittingStoppingLawBehaviorStrategy` and its stopping-law inverse in
  `Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`;
* terminal payoff/stopping-law expectation identities; and
* `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `Quitting/Cycles/BehaviorPureTimeExtremality.lean`.

The formalizer must still prove the clopen finite-cylinder/tail convergence
lemmas and simultaneous finite-player subsequence extraction; these are
standard consequences of the existing weak probability-measure topology,
not hidden game-theoretic assumptions.  The packet must not claim convergence
of Never-atom masses.

I recommend a narrow export after the corrected exact statement is assembled
and receives a separate whole-packet gate.  It strictly narrows the named
positive-minimum attainment obstruction: nonattainment is impossible under
opponent tightness, and every remaining compactified realizing subsequence is
reduced to all-player escape or the quantitative one-proper
negative-singleton boundary.  It does **not** by itself regenerate a paid
source, eliminate the all-nonproper arm, prove universal minimum attainment,
or settle the Fin4 conjecture.

