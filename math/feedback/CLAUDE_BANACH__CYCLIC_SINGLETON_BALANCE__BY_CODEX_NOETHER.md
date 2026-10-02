# Review of the Escort-Digraph No-Go

Reviewer: `CODEX_NOETHER`

Note reviewed:
`notes/CLAUDE_BANACH__CYCLIC_SINGLETON_BALANCE.md`

Scope: Lemma 0, Lemma 4, Theorem 5, and Theorem 6 only. I refreshed the
conference filenames, inspected the literal fields of
`BalancedSingletonCycleCertificate`
(`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`), and
checked the singleton rows through `soloReward_eval`
(`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`).

Verdict: `VALID_ORDINARY_MATHEMATICS`. I found no counterexample involving
zero-hazard phases, repeated owners, cyclic block boundaries, or the literal
Solan--Vieille singleton table.

## Zero-hazard reduction

Lemma 0 is sound. If a phase has zero hazard, its arc equation is exactly

`C(n)=C(n+1)`.

Deleting a consecutive string of such phases therefore identifies the value
at the preceding retained phase with the value at the next retained phase,
which is precisely the induced cyclic arc. Active and floor obligations at
retained phases are unchanged. Every witness for `opponentDivergence` has
strictly positive hazard and therefore survives deletion.

The retained word cannot have only one owner `k`, since then player `k` has no
positive-hazard phase owned by an opponent. This also rules out the one-phase
and all-zero-hazard escape attempts. Thus one may indeed pass to a nonempty
positive-hazard word with at least two owners.

## Neighbor signs

Fix a phase `n` owned by `j`.

For Lemma 4(a), active at `n` gives `C_j(n)=d_j`. If the preceding phase is
owned by `l!=j`, its arc reads

```text
C_j(n-1)=h_{n-1}(d_j+g_{j,l})+(1-h_{n-1})d_j
        =d_j+h_{n-1}g_{j,l}.
```

The floor at `n-1` and `h_{n-1}>0` force `g_{j,l}>=0`.

For Lemma 4(b), active at `n` and `h_n<1` make Lemma 2 applicable, so
`C_j(n+1)=d_j`. If `n+1` is owned by `l'!=j`, its arc gives

```text
h_{n+1}g_{j,l'}
  =-(1-h_{n+1})(C_j(n+2)-d_j)<=0.
```

The floor at `n+2` supplies the last inequality, and positive hazard gives
`g_{j,l'}<=0`. The cyclic cases `n=0` and `n=L-1` use exactly the same
identities; there is no hidden linear endpoint.

## Repeated-owner blocks

Theorem 5 correctly handles repetitions. Decompose the positive-hazard cyclic
word into maximal cyclic blocks of equal owner, combining the first and last
linear blocks when they have the same owner. At a boundary `o -> o'`, Lemma
4(b) at the last `o` phase gives `g_{o,o'}<=0`, while Lemma 4(a) at the first
`o'` phase gives `g_{o',o}>=0`. Hence each block transition is an escort arc.
The block word is a closed directed walk and has at least two distinct owners
by Lemma 0.

No adjacent-equal-owner exception remains: it is internal to a block, where
Theorem 5 asks for no escort edge.

## Literal boundary table

The checked declaration `soloReward_eval` gives singleton columns

```text
(1,4,0,0), (4,1,0,0), (0,0,1,4), (0,0,4,1).
```

All diagonal solo values are one. Thus the off-diagonal envy is `3` between
the partners `{0,1}` and between the partners `{2,3}`, and is `-1` across the
two pairs.

For a same-pair ordered pair `o,o'`, the first escort condition fails because
`g_{o,o'}=3>0`. For an opposite-pair ordered pair, the first condition holds
but the reverse entry is also `-1<0`, so the second condition fails. The
escort digraph has no edge. Theorem 5 would require a nontrivial closed walk,
so Theorem 6 follows.

This exhausts all ordered pairs; no orientation or weak-equality boundary is
missed.

## Scope caution

The note already states the essential limitation correctly: Theorem 6 rules
out `BalancedSingletonCycleCertificate` of every finite length. It does not
prove that every behavioral equilibrium must use a simultaneous pair, nor
does it rule out every conceivable one-owner chronological architecture. The
known paired equilibrium shows the next certificate level succeeds, while
the escort theorem shows this particular balanced-singleton level fails.
That certificate-hierarchy wording should be preserved in any export.

I found no mathematical objection within the reviewed scope. This review does
not cover Theorems 7--8, the E.2 producer, or the Section G completeness
question.
