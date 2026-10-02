# All-suffix survival, persistent labels, and actual-packet charges

## Current best attempt

**External proposal, awaiting incremental review.**  The two-label theorem is
already independently reviewed and exported in
[`../exports/PERSISTENT_DELETED_CLOCK_TWO_LABEL_REDUCTION.md`](../exports/PERSISTENT_DELETED_CLOCK_TWO_LABEL_REDUCTION.md).
This note proposes three additions:

1. the exact rule for an arbitrary deleted player set `A`;
2. an equivalent packet-boundary criterion using absorption charges of the
   actual executed roots; and
3. direct Lean closures of the all-suffix opponent-clock equivalence and joint
   domination implication.

Author: `CHATGPT_EXTERNAL` (submitted through the conference orchestrator)

Status: `UNREVIEWED INCREMENTAL EXTENSION`

## 1. Scalar all-suffix product criterion

For `a_t in [0,1]`,

```text
forall m, product_(t=m)^(m+N-1) (1-a_t) -> 0
  iff
sum_t a_t = infinity.
```

The forward implication uses a late suffix with total mass below `1/2` and
the finite product union bound.  The reverse implication uses
`product(1-a_t) <= exp(-sum a_t)`.  Requiring every suffix removes the isolated
sure-Quit pathology.

## 2. Arbitrary deleted sets

For actual product roots, write `p(t,j)` for player `j`'s Quit marginal.  For a
deleted set `A`, define

```text
h(-A,t)=1-product_(j notin A)(1-p(t,j)),
J(-A,m,N)=product_(t=m)^(m+N-1)(1-h(-A,t)).
```

Let

```text
P={j | sum_t p(t,j)=infinity}.
```

The proposal claims the complete finite-player rule

```text
forall m, J(-A,m,N)->0   iff   P\A is nonempty.       (2.1)
```

Indeed, for every `j notin A`,

```text
p(t,j) <= h(-A,t) <= sum_(k notin A) p(t,k),
```

and finiteness turns divergence of the middle series into persistence of some
nondeleted label.  Joint survival corresponds to `A=empty`; all one-player-
deleted survivals correspond exactly to `|P|>=2`.  For a nonempty player set,
joint survival is redundant once all one-player-deleted survivals vanish.

## 3. Literal four-player regression

On players `{0,1,2,3}`, give players `0,1` Quit hazard

```text
a_t=1/(t+2)
```

and let `2,3` Continue surely.  Then

```text
R(m,N)=product_(t=m)^(m+N-1)(1-a_t)=(m+1)/(m+N+1),
J(m,N)=R(m,N)^2,
J(-0,m,N)=J(-1,m,N)=R(m,N),
J(-2,m,N)=J(-3,m,N)=R(m,N)^2.
```

All required joint and one-player-deleted suffix clocks vanish, while deleting
both active players leaves survival one.  Taking the literal tail profile
`sigma^m` that executes root `q_(m+s)` at relative time `s` gives exact
all-Continue residual identity `Residual(sigma^m)=sigma^(m+1)` and exact
semantic Prefix recursion.  This is a regression for source-matched clock
semantics, not a small-debt or equilibrium producer.

## 4. Packet-boundary criterion

Let `0=N_0<N_1<...` be finite packet boundaries and define the actual
player-`i`-deleted absorption probability of packet `k` by

```text
delta(k,-i)=1-product_(t=N_k)^(N_(k+1)-1)
                    product_(j!=i)(1-p(t,j)).
```

The proposal claims

```text
forall i,m, J(-i,m,N)->0
  iff
forall i, sum_k delta(k,-i)=infinity.                (4.1)
```

At packet boundaries this is the scalar product criterion; starting inside a
finite packet removes only one finite partial block.  Packet widths need not be
uniformly bounded.  Hence if `sum lambda_k=infinity` and eventually

```text
delta(k,-i)>=kappa*lambda_k
```

for every player `i` and some fixed `kappa>0`, all deleted and joint suffix
clocks vanish.  The charges must be measured on actual executed roots, not on
frozen proposal packets.

## 5. Proposed Lean closure

The suggested core equivalence is

```lean
theorem allTail_opponentSurvival_iff_not_summable_charge
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    (∀ start,
        Tendsto
          (quittingOpponentSurvivalWeight roots who start)
          atTop (nhds 0)) ↔
      ¬ Summable (quittingOpponentClockCharge roots who) := by
  constructor
  · intro hzero hsummable
    obtain ⟨start, hhalf⟩ :=
      exists_suffix_half_le_quittingOpponentSurvivalWeight_of_summable
        roots who hsummable
    have hcontra : (1 / 2 : ℝ) ≤ 0 :=
      ge_of_tendsto' (hzero start) hhalf
    norm_num at hcontra
  · intro hdiverges start
    apply
      tendsto_zero_quittingOpponentSurvivalWeight_of_not_summable_charge
    intro hsuffix
    apply hdiverges
    have hshift :
        Summable
          (fun offset =>
            quittingOpponentClockCharge roots who (offset + start)) := by
      simpa [Nat.add_comm] using hsuffix
    exact (summable_nat_add_iff start).1 hshift
```

The proposed joint consequence is

```lean
theorem tendsto_zero_quittingJointSurvivalWeight_of_opponent
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    (hzero :
      Tendsto
        (quittingOpponentSurvivalWeight roots who start)
        atTop (nhds 0)) :
    Tendsto
      (quittingJointSurvivalWeight roots start)
      atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun fuel =>
      quittingJointSurvivalWeight_nonneg roots start fuel
  · exact fun fuel =>
      quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
        roots who start fuel
  · exact hzero
```

Exact declaration names, shifted-summability orientation, and `ge_of_tendsto'`
usage must be checked in source/Lean before accepting these bodies.

## Scope and open objections

- The survival analysis does not produce persistent hazards from atom/reset
  data and does not prove small initial debt.
- Pair-deleted survival is deliberately not claimed.
- Confirm (4.1) with isolated probability-one packet charges and unbounded but
  finite packet widths.
- Determine whether the general deleted-set and packet forms are useful enough
  to extend the existing export or should remain implementation notes.
