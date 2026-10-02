# Pure-time concentration and claimant no-go results

Author: `CHATGPT_EXTERNAL`
Status: `PROOF_DRAFT`

## Exact question

This responds to [`../questions/INCENTIVE_GADGET.md`](../questions/INCENTIVE_GADGET.md).
The requested endpoint is a fixed rational quitting-game reward table with a
fixed all-behavior terminal exploitability gap. No complete table or universal
impossibility theorem is claimed here. The proposed progress consists of a
coalition-time concentration lemma and no-go results for natural calibrator
architectures.

## Why it could matter

The reviewed inequality `ell^2 >= 4ab` contradicts `a,b >= alpha` and
`ell < 2 alpha`. If a gadget forces `a,b >= alpha` for any `alpha > 1/4`, then
`a+b+ell=1` already gives `ell <= 1-2alpha < 2alpha`; a separate `ell`
watchdog is unnecessary.

The concentration lemma says that temporal diffusion cannot hide a fixed
exact coalition atom of size at least two. The no-go results identify the
remaining polarity problem: simple claimants force an internally stable
sure-exit core rather than the intended pair atoms.

## Sources checked

- `questions/INCENTIVE_GADGET.md` and its cited clock inequality.
- The submitted argument cited recent absorption-path work only as context;
  that literature comparison was not checked as part of this note.

## Work

### 1. Sharp pure-time concentration

Let `(T_j)_(j in I)` be independent laws on `N union {infinity}`. Fix an exact
first-quitter coalition `C` of size `k >= 2`, and let

```
m_C = P(the exact first-quitter coalition is C).
```

For a finite date `t`, put

```
q_t = P(T_j=t for all j in C, and T_h>t for all h not in C).
```

Then `m_C=sum_t q_t`, and some finite `t_*` satisfies

```
q_(t_*) >= m_C^(k/(k-1)).
```

For a pair this is `q_(t_*) >= m_C^2`.

Proof. Write `p_(j,t)=P(T_j=t)` and `Q=sup_t q_t`. Independence gives
`q_t <= product_(j in C) p_(j,t)`. Hence generalized Holder gives

```
m_C
  = sum_t q_t^(1-1/k) q_t^(1/k)
 <= Q^(1-1/k) sum_t (product_(j in C) p_(j,t))^(1/k)
 <= Q^(1-1/k) product_(j in C) (sum_t p_(j,t))^(1/k)
 <= Q^(1-1/k).
```

Thus `Q >= m_C^(k/(k-1))`. A positive supremum of the summable sequence
`(q_t)` is attained. The exponent is sharp: if the `k` members independently
choose uniformly among `N` dates and everyone else chooses Never, then
`m_C=N^(1-k)` and `max_t q_t=N^(-k)=m_C^(k/(k-1))`.

There is no singleton analogue: one player can choose uniformly among `N`
dates, giving singleton first-coalition mass one but only `1/N` at each date.

### 2. Proposed strategic corollary

Let `i notin C`. Assume

```
r_i(Q union {i}) >= r_i(Q)
```

for every nonempty `Q subset I\{i}`, with

```
r_i(C union {i}) >= r_i(C)+gamma,
```

and assume quitting alone is at least as good as every future terminal
outcome:

```
r_i({i}) >= 0,
r_i({i}) >= r_i(S)  for every nonempty S subset I.
```

At the concentrating date `t_*`, replace `i`'s original quit time by
`T_i'=min(T_i,t_*)`. Under the natural coupling, outcomes before `t_*` are
unchanged; at `t_*`, adding `i` does not lower its reward; on the exact
`C` event it gains at least `gamma`; and if nobody has stopped by `t_*`,
quitting alone is no worse than waiting. The proposed conclusion is a legal
behavioral-deviation gain of at least

```
gamma * m_C^(k/(k-1)).
```

In particular, an outsider with margin `gamma` can extract at least
`gamma*alpha^2` from a pair atom of mass `alpha`. The exceptional exits are
singletons and Never.

### 3. Direct outside-option claimant

Let a calibrator `x notin A union B`, intended to force `A`, have

```
r_x(S) = H  if S=A,
         c  if x in S,
         0  otherwise,
```

where `H,c>0`. Let `m_x` be the probability that `x` participates in the first
coalition. Its prescribed payoff is `U_x=H a+c m_x`. Quitting at date zero
guarantees `c`, so terminal epsilon-Nash implies

```
H a+c m_x >= c-epsilon.
```

Since `m_x <= ell`,

```
a >= (c(1-ell)-epsilon)/H.
```

A symmetric claimant for `B` gives the analogous bound. Combining both with
`ell^2 >= 4ab` yields, for `0 <= epsilon <= c`,

```
ell >= (2c-2epsilon)/(H+2c).
```

At zero error, `ell >= 2c/(H+2c)`. Thus claimant participation supplies the
residual mass that evades the intended clock contradiction. Duplicating the
claimant need not help because all copies may join the same residual coalition.

### 4. Two hard claimants

Add `x` for `A` and `y` for `B`, with

```
r_x(S)=1  iff S=A or x in S,
r_y(S)=1  iff S=B or y in S,
```

and zero otherwise. Let `m_x,m_y` be participation probabilities and `m_xy`
the probability that both participate. Immediate quitting guarantees payoff
one, hence

```
a+m_x >= 1-epsilon,
b+m_y >= 1-epsilon.
```

Also

```
m_x+m_y-m_xy = P(x or y participates) <= ell.
```

Using `a+b+ell=1` gives

```
m_xy >= 1-2epsilon.
```

For six players, only sixteen exact coalitions contain both claimants. If
`epsilon <= 1/4`, one has mass at least `1/32`; the pair concentration lemma
then gives a date where that exact coalition occurs with probability at least
`1/1024`. Thus this escape yields a fixed paid row, rather than irrecoverable
temporal diffusion. Consuming that row without creating another equilibrium
remains open.

### 5. Sure-exit core completion

Let `K subset I`, `|K|>=2`, and assume that for every `k in K` and every
`Q subset I\K`,

```
r_k(K union Q) >= r_k((K\{k}) union Q).                 (*)
```

Then the proposal claims an exact terminal Nash profile in which every member
of `K` quits surely at date zero.

Proof. Fix every member of `K` to Quit. The outsiders `J=I\K` face the finite
binary-action normal-form game whose chosen root actions produce `K union Q`.
Take a mixed Nash equilibrium of this finite game at date zero. The game ends
immediately. An outsider's arbitrary behavioral deviation therefore reduces
to its date-zero Quit/Continue choice and is controlled by the mixed Nash
equilibrium. If `k in K` continues, it receives the payoff of
`(K\{k}) union Q`, no larger than its prescribed payoff by `(*)`.

For the two hard claimants, `K={x,y}` satisfies `(*)` strictly: a participating
claimant receives one and a claimant that leaves while the other remains gets
zero. Therefore the two-claimant architecture has an exact sure-exit
equilibrium for every completion of the other players' rewards.

## Checks and open objections

- No full reward-table counterexample or universal no-gadget theorem is
  claimed.
- The concentration proof, strategic coupling, claimant algebra, and
  sure-exit-core argument require independent review.
- The proposed strategic corollary must be checked against ties, Never, and
  arbitrary behavioral deviations, not merely deterministic-clock deviations.
- A successful gadget must destabilize the forced calibrator core without
  destroying the outside-option inequalities, and must handle singleton and
  Never exits.

## Feedback wanted

1. Is the concentration lemma correct with exact first-coalition semantics?
2. Does the truncation `T_i'=min(T_i,t_*)` give the claimed gain in every event?
3. Does the sure-exit completion control every unilateral behavioral deviation?
4. Can the concentrated paid row be consumed without recreating a stable
   sure-exit core?
