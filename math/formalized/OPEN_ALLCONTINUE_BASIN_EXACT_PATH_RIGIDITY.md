# Exact-path rigidity of an open all-Continue basin

Author: `CODEX_RAMSEY`

Independent review:
[CODEX_EULER](../feedback/CODEX_RAMSEY__OPEN_ALLCONTINUE_BASIN_NO_REENTRY__BY_CODEX_EULER.md)

Whole-packet gate:
[CODEX_EULER](../feedback/OPEN_ALLCONTINUE_BASIN_EXACT_PATH_RIGIDITY__BY_CODEX_EULER__PACKET_GATE.md)

## Exact statement

Let `I` be a finite player type, let

```text
reward : {S : Finset I // S.Nonempty} -> Payoff I
```

be a quitting reward table, and let `N` be a set of payoff vectors with the
following property:

```text
for every V in N, every exact endpoint-Nash product root against V
is the all-Continue root.                                      (H)
```

Use the repository's Nash--Bellman orientation: an edge from a continuation
tail `v_(t+1)` to its predecessor head `v_t` consists of a product root `q_t`
such that

```text
q_t is exact endpoint Nash against v_(t+1),
v_t = Succ(v_(t+1),q_t).                                      (1)
```

Then the following hold.

### Theorem A: finite backward rigidity

For every natural number `L`, every family of payoff vectors
`v_0,...,v_L`, and every family of roots `q_0,...,q_(L-1)` satisfying (1), if
`v_L=V` for some `V in N`, then

```text
v_t=V                    for every 0<=t<=L,
q_t=all-Continue         for every 0<=t<L.                       (2)
```

Consequently every edge in the path has zero absorption charge.

### Corollary B: no exact charged return or re-entry

No `V in N` admits an `IsQuittingCyclicContinuation reward V`: every anchored
finite exact block returning to `V` is the constant all-Continue block and
therefore fails the required positive-absorption clause.

More generally, in the displayed index orientation, if a later tail node
`v_k` lies in `N`, every earlier predecessor `v_0,...,v_k` equals `v_k`.
Thus an exact path segment cannot have an earlier outside node and then a
later tail node in `N`.  This is one-sided: a head in `N` need not force its
tail to lie in `N`.

### Corollary C: a fixed terminal-seam floor

Suppose `U in N`, `N` is open, and `r>0` is such that the open payoff ball
`B(U,r)` is contained in `N`.  Every finite exact Nash--Bellman block with at
least one positive-absorption root and terminal tail `V` satisfies

```text
dist(V,U) >= r.                                                (3)
```

The origin payoff is arbitrary.  Hence there is no sequence of charged exact
finite blocks, even with varying origins, whose terminal tails converge to
`U`.

### Corollary D: exact infinite convergence rigidity

Let `(v_t,q_t)_(t>=0)` be an infinite exact Nash--Bellman path satisfying
(1) for every `t`.  If `N` is open, `U in N`, and `v_t -> U`, then

```text
v_t=U and q_t=all-Continue for every t.                         (4)
```

### Finite-four-player application

For the plateau `(U,B)` supplied by
[`FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md`](FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md),
the reviewed source theorem gives an open neighborhood `N` satisfying (H),
indeed an open tube around the whole segment

```text
H(t)=B-t(B-U),  0<=t<=1.
```

Theorems A--D therefore apply at every anchor in that tube.  In particular,
the remaining four-player exact construction cannot be a charged finite
return with terminal seam tending to the plateau, nor an exact infinite path
whose payoff values converge to it.

## Conjecture-facing change

The prior plateau-isolation packet proved only an edge-local fact: an exact
edge whose continuation tail is in the open tube is the zero-charge identity.
The present theorem closes the corresponding finite- and infinite-path
shortcuts.  Backward propagation makes every finite block ending in the tube
constant, produces a positive terminal-seam floor for every charged block,
and makes every exact path converging to an interior plateau point constant
from time zero.

Thus a conjecture-facing exact connector must use genuinely nonlocal terminal
tails and cannot hide the excursion in a long exact path that merely returns
closer and closer to the plateau.  Approximate-root or approximate-seam
architectures remain open.

## Definitions and semantic audit

An exact endpoint-Nash product root is a profile of independent Boolean
mixed actions satisfying both pure endpoint inequalities for every player
against the supplied continuation payoff.  `Succ(V,q)` is the one-row
expected payoff: terminal rewards on absorption and `V` on joint Continue.
The absorption charge is the probability that at least one player Quits at
that row.

The theorem is entirely about exact one-row roots and their Bellman
composition.  It introduces no public randomization, no correlated action,
and no stopping-law approximation.  The roots are exact against both pure
actions, hence against every mixed one-row deviation.  The result does not
upgrade that local root notion to an unrestricted behavioral equilibrium;
the Fin4 source obtains its all-behavior meaning separately through the
terminal-semantic carrier and exploitability-witness reduction.

## Proof

### 1. Finite paths

Start from `v_L=V in N`.  By (H), the exact root `q_(L-1)` against `v_L` is
all-Continue.  Its absorption charge is zero and its successor map is the
identity, so (1) gives `v_(L-1)=V`.

Repeat the same argument at `L-2,L-3,...,0`.  Descending induction proves
(2), including the root and charge assertions.  No floor, compactness,
carrier, or debt hypothesis is used.

An exact cyclic continuation block anchored at `V` is one such finite path
with terminal value `V` and with at least one positive-absorption stage.
Theorem A makes every stage all-Continue, contradicting the latter clause.
Applying the same induction to any prefix ending at a later tail node in `N`
proves the stated one-sided no-re-entry conclusion.

### 2. Seam floor

If a charged exact block had terminal tail `V` with `dist(V,U)<r`, then
`V in B(U,r) subset N`.  Theorem A would make the block zero-charge, a
contradiction.  This proves (3).  If terminal tails of charged blocks
converged to `U`, they would eventually enter `B(U,r)` and yield the same
contradiction.  The proof never uses their origins.

### 3. Infinite paths

If `v_t -> U` and `N` is open, then `v_t in N` for every sufficiently large
`t`.  For all sufficiently large edges, the tail `v_(t+1)` lies in `N`; (H)
makes `q_t` all-Continue and (1) makes `v_t=v_(t+1)`.  The value sequence is
therefore eventually constant, and its limit identifies that constant as
`U`.  Applying the finite descending argument to the remaining initial
segment propagates `U` and all-Continue to time zero, proving (4).

## Source correspondence and novelty

The orientation and finite-path data are checked in

```text
UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean
UniformEquilibrium/Quitting/Cycles/CycleMismatchContraction.lean
UniformEquilibrium/Quitting/Debt/Dynamic/CyclePinnedDebt.lean.
```

The relevant declarations are `IsQuittingNashBellmanEdge`,
`quittingAnchoredPathValue_eq_successor`,
`quittingAnchoredPathRoots_isZeroEndpointNash`,
`quittingAnchoredPathValue_at_cutoff`, and
`IsQuittingCyclicContinuationBlock`.

The source-specific hypothesis (H) for the maintained Fin4 residual is the
reviewed result exported in `FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md`.  The
new ordinary mathematics is the propagation from tail-local root uniqueness
to finite backward rigidity, the origin-independent seam floor, and infinite
convergence rigidity.  A narrow search found no checked declaration packaging
these consequences.  No external literature result is used.

## Boundary tests

1. **Positive one-player test.**  For one player with singleton payoff
   `s=0`, every tail `V>0` has all-Continue as its unique exact root.  Thus
   `N=(0,infinity)` satisfies (H), and the theorem correctly makes every
   finite path ending at a positive tail constant.

2. **Root uniqueness is load-bearing.**  In the two-player table with both
   singleton payoff vectors zero, joint-quitting payoff vector `(1,1)`, and
   tail `(1/4,1/4)`, all-Continue is exact but is not unique.  The symmetric
   root with Quit probability `1/5` for each player is also exact, since each
   player's Quit and Continue payoffs both equal `1/5`.  Merely knowing that
   all-Continue is one exact root does not imply path rigidity.

3. **The orientation is one-sided.**  The proof starts from a tail in `N`.
   The definition `head=Succ(tail,root)` supplies no converse implication
   from `head in N` to `tail in N`; the packet therefore preserves nonlocal
   incoming edges rather than silently excluding them.

4. **Exactness is load-bearing.**  An approximately exact root in `N` may
   carry small positive absorption.  Repeating such rows is not covered by
   (H), so the theorem gives neither a uniform lower seam nor constancy for
   approximate Bellman paths.

## Adapter and consumer

The generic theorem consumes the supplied root-uniqueness set (H).  Its
actual-data adapter in the live Fin4 residual is the same-table no-uniform
reduction and open-tube theorem in
`FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md`; no desired path or root is assumed
as source data.

The output is a strict no-go for the exact-return architecture in the
maintained four-player question.  It is not a terminal-equilibrium consumer:
the surviving routes must either construct approximate terminal Nash
profiles, use a nonlocal exact tail that does not converge to the plateau, or
derive a contradiction before return.  The downstream positive endpoint
remains `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`.

## Lean handoff

Formalize the generic theorem first, without importing terminal-semantic
machinery.  A narrow statement can use a finite list of values and roots, or
`QuittingFiniteNashBellmanPath`, together with the three anchored-path
declarations named above.  Prove the result by descending induction from the
cutoff.  The cyclic corollary should eliminate the positive-absorption field
of `IsQuittingCyclicContinuationBlock`.

Then add the metric seam and sequence corollaries for an open set `N`.  The
Fin4 adapter should consume the unique-root tube theorem from the plateau
packet rather than restating its proof or storing root uniqueness as a new
source structure field.  Useful regressions are the one-player positive
half-line and the two-player `1/5` root above.

## Scope and nonclaims

- The packet proves no uniform-equilibrium payoff and constructs no terminal
  approximate Nash profile.
- It excludes only exact product-root Nash--Bellman paths.  It says nothing
  quantitative about approximate roots or approximate Bellman seams.
- It does not exclude a nonlocal incoming edge whose head lies in `N` and
  whose continuation tail lies outside `N`.
- It does not exclude exact paths remaining outside `N` and accumulating only
  on the boundary of `N`.
- The generic theorem does not produce (H); the actual Fin4 adapter is the
  separately reviewed minimum-plateau isolation theorem.
- No claim is made for arbitrary stochastic games or arbitrary player counts
  beyond the conditional generic path statement.
