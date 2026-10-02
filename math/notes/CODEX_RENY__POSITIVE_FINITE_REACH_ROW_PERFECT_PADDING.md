# Exact row-perfect padding with positive reach at every finite date

Ordinary mathematical corollary recorded by CODEX_RENY. The
[source-correspondence review](../feedback/REDUCTION__SOURCE_CORRESPONDENCE_BY_CODEX_RENY.md)
compares it with the existing one-dummy hardness construction. This note
proves only the additional source property, not the general hardness theorem
or the reverse implication from row perfection to equilibrium existence.

## Data and exact row-perfection convention

Let I be a nonempty finite player set. An old quitting game has reward
r(S)∈ℝ^I for each nonempty S⊆I and Never payoff z∈ℝ^I. Players use
independent behavioral randomization on the unique live all-Continue
history. Define

```text
H_i=max({z_i}∪{r_i(S):∅≠S⊆I}).
```

Add one player d and choose K>0. On the enlarged player set J=I∪{d},
keep old Never coordinates z_i and give d Never payoff zero. Define the
entire enlarged reward table r̂ by old-quitter priority:

- If A⊆J is nonempty and S=A∩I is nonempty, set r̂_i(A)=r_i(S) for
  every old player i and r̂_d(A)=0, even if d belongs to A.
- The remaining coalition is A={d}; set r̂_i({d})=H_i for every old
  player and r̂_d({d})=−K.

For any independent root q∈[0,1]^J and continuation value v∈ℝ^J, let
p_q^{−i}(S) be the probability that exactly S⊆J\{i} of player i's
opponents Quit at that root. Define the literal endpoints and mixed value

```text
Q_i(q)=∑[S⊆J\{i}] p_q^{−i}(S) r̂_i(S∪{i}),
C_i(q,v)=∑[∅≠S⊆J\{i}] p_q^{−i}(S) r̂_i(S)
           +p_q^{−i}(∅)v_i,
V_i(q,v)=q_i Q_i(q)+(1−q_i)C_i(q,v).
```

A root is exactly row-perfect against v when, for every i,

```text
Q_i≤V_i,       C_i≤V_i,
q_i>0 ⇒ Q_i≥V_i,       q_i<1 ⇒ C_i≥V_i.
```

For a root sequence, the continuation at date n is the **actual terminal
payoff** of the prescribed sequence restarted at n+1, including the
enlarged Never payoff if that restarted sequence never absorbs. No free
Bellman annotation or full-response equilibrium assumption is involved.

## Corollary

For every fixed α∈(0,1], the stationary sequence

```text
q_i=0   (i∈I),             q_d=α
```

is exactly row-perfect at every date against its actual restarted payoff,
and it terminates almost surely after every restart. If α<1, it has
positive survival through every finite date. In fact, from a restart at m
through the rows m,…,N−1,

```text
a_{m,N}=(1−α)^(N−m)        (m≤N).
```

The same sequence therefore witnesses every positive row-error tolerance.
Its only nonzero Quit probability may be made arbitrarily small by choosing
α small and positive.

## Proof

After every restart the dummy eventually quits alone with probability one,
because (1−α)^n→0. The actual restarted payoff vector is consequently

```text
γ_i=H_i  (i∈I),             γ_d=−K.
```

Fix an old player i. If it Quits in the current row, then either the dummy
Continues and the coalition is {i}, or the dummy Quits and the coalition
is {i,d}. Old-quitter priority makes its payoff r_i({i}) in both cases.
Thus Q_i=r_i({i})≤H_i. If it Continues, the dummy either terminates the
game now at H_i or Continues into the actual restarted value H_i. Hence
C_i=αH_i+(1−α)H_i=H_i=V_i. This proves all four clauses for i.

For the dummy, Quit gives −K and Continue gives the actual next value
−K, because every old player Continues. Therefore Q_d=C_d=V_d=−K,
including when both actions are supported. All row-perfect clauses hold.

The finite survival formula follows by multiplying the independent
per-date Continue probability 1−α. It is positive at every finite N for
α<1 and tends to zero as N→∞. The empty product at N=m is one; when
α=1 every nonempty prefix has survival zero. This proves the corollary.

The prescribed source itself is not terminal Nash: the dummy receives
−K but its complete deviation Never yields zero. Positive finite reach
does not remove this difference between a one-row comparison against the
prescribed continuation and an unrestricted change of the whole strategy.
