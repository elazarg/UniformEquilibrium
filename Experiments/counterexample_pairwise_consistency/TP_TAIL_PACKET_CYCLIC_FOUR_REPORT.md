# T × P: cyclic four-player exact-equation regression

## Status

**Consistent for the exposed T × P equations; full optimized-minimizer/projective and packet-from-tail provenance remains open.**

There is one rational four-player reward table on which:

- a genuinely nonstationary, positive-hazard tail satisfies every displayed
  phantom-tail, Bellman, exact dynamic-debt, conservation, honest-payoff, and
  owner-clock equation; and
- every normalized packet satisfying (15), not merely one chosen packet, has
  a refusal gap of at least the same positive number `1/52`.

This proves same-table compatibility of the exposed equations.  It does not
prove that the tail is the projective limit of the optimized finite minimizers
used in the counterexample extraction.  Nor is the packet mass an occupation
law of this tail: the tail occupation is a pure atom and fails funding.  Thus
the construction is deliberately a regression for the missing interface, not
a counterexample to Question 172.

The exact scalar proof is
`TailPacketCyclicFourWitness.lean`.  The full-table finite-date audit is
`tail_packet_cyclic_four_exact.py`.

## 1. One common reward table

Let `I = {0,1,2,3}`, with indices read modulo four.  Singleton rewards are

```text
                 singleton quitter j
payoff row i       0   1   2   3
             0     1   0   0   4
             1     4   1   0   0
             2     0   4   1   0
             3     0   0   4   1
```

Equivalently,

```text
r_i({j}) = 1  if i = j,
           4  if i = j+1 mod 4,
           0  otherwise.
```

For every coalition `S` with at least two quitters, put

```text
r_i(S) = -4
```

for every player `i`.  Thus `M = 4` and every positive singleton cap is
`K_i = 1`.

For later use, `chi_i <= 1`: opponents can all Continue forever, against
which player `i` can obtain at most `1` and can obtain `1` by eventually
quitting.  Only the upper bound is needed below.

## 2. The entire normalized packet family

For a probability vector `lambda`, the singleton mixtures are

```text
m_0 = lambda_0 + 4 lambda_3,
m_1 = lambda_1 + 4 lambda_0,
m_2 = lambda_2 + 4 lambda_1,
m_3 = lambda_3 + 4 lambda_2.
```

Take any pair `(lambda,z)` satisfying every clause of (15).  The solo floor
and funding clauses imply

```text
1 <= z_i <= m_i
```

for every `i`, hence `m_i >= 1` for all four rows.  These inequalities force a
quantitative full-support bound.

Fix `i`.  If `lambda_i >= 1/4`, then certainly `lambda_i >= 1/13`.  Otherwise,
the row for `i+1` and the row for `i` give

```text
lambda_(i+1) >= 1 - 4 lambda_i,
lambda_(i-1) >= (1 - lambda_i)/4.
```

Using nonnegativity of the fourth coordinate and `sum_i lambda_i = 1` gives

```text
1 >= lambda_i + (1 - 4 lambda_i) + (1 - lambda_i)/4,
```

so again `lambda_i >= 1/13`.  Consequently

```text
1/13 <= lambda_i <= 10/13
```

for every player.  In particular, every coordinate is positive and the
complementarity clause in (15) pins the whole target:

```text
z_i = r_i({i}) = 1.
```

Put `h_i = m_i-1`.  Every `h_i` is nonnegative, while cyclic summation gives

```text
sum_i h_i = 5 sum_i lambda_i - 4 = 1.
```

Some owner therefore has `h_i >= 1/4`.  Its refusal value is

```text
R_i(lambda) = 4 lambda_(i-1)/(1-lambda_i),
```

and exact algebra gives

```text
R_i(lambda) - m_i(lambda)
  = [lambda_i/(1-lambda_i)] [m_i(lambda)-1]
  >= (1/13)(1/4)
  = 1/52.                                                   (P*)
```

The selected owner also has `0 < lambda_i < 1`, and `z_i=1<m_i` because its
surplus is at least `1/4`.  Thus (16) holds for the *entire* normalized packet
family with the table-wide rational margin

```text
delta = 1/52.
```

This family is nonempty.  For example, `lambda_i=1/4` and `z_i=1` gives
`m_i=5/4` and `R_i=4/3` for every `i`; the punishment clause follows from
`chi_i<=1`.  Notice that the universal proof did not assume this symmetric
packet or reduce the quantifier to it.

The Lean theorem `cyclic_packet_uniform_refusal` proves the full-support
bounds and (P*) over arbitrary real masses satisfying the four funding
inequalities.

## 3. A nonstationary rational phantom tail

Distinguish player `0`.  At date `t`, only player `0` has positive Quit
probability:

```text
p_t       = 1/(2^(t+2)-1),
a_(0,t)   = p_t,
a_(i,t)   = 0                         for i != 0.
```

Define

```text
A_t = 1/2^(t+1),
P_t = 1-A_t,

v_t = (1, 1+3 A_t, P_t, P_t),
d_t = (1, 0, 0, 0).
```

All rewards, hazards, annotations, and debts displayed here are rational.
Letting `s=2^(t+1)`, one has

```text
p_t = 1/(2s-1),
P_t = 1-1/s,
P_(t+1) = 1-1/(2s),
P_t = (1-p_t) P_(t+1).                                    (T1)
```

Therefore the survival products telescope.  Starting at date `t`, the
probability of never absorbing is `P_t`, and the honest absorption probability
is exactly `A_t`.

### Charge and convergence

Here `q(a_t)=p_t>0` at every date, so this is not an all-Continue plateau.
Moreover,

```text
p_t <= 1/2^(t+1),
sum_t q(a_t) <= 1,
a_t -> 0.
```

Thus the tail is summably absorbing and approaches all-Continue.

### Exact Bellman--Nash equations

For player `0`, both pure endpoints equal `1`, so mixing with probability
`p_t` gives the prescribed value `v_t(0)=1` exactly.

For every nonowner, quitting now has endpoint

```text
Q_i(t) = (1-p_t) r_i({i}) + p_t r_i({0,i}) = 1-5p_t.        (T2)
```

Player `1`'s Continue endpoint is

```text
4p_t + (1-p_t)(1+3A_(t+1)) = 1+3A_t = v_t(1),
```

and players `2,3` have Continue endpoint

```text
0p_t + (1-p_t)P_(t+1) = P_t = v_t(i).
```

Since `A_t=1/s <= 5/(2s-1)=5p_t`, (T2) is at most `P_t`, and it is plainly at
most player `1`'s value.  Continue is therefore optimal for every nonowner.
The stage payoff is affine in a unilateral Quit probability, so these two
endpoint comparisons prove exact one-stage Nash against every mixed
alternative, not only the two pure alternatives.

### Exact dynamic debt and conservation

Use the exact update

```text
D_i(t) = max(Q_i(t), C_i(t)+c_i(a_t)d_(t+1)(i)) - v_t(i),
```

where `c_i(a_t)` is the probability that all opponents of `i` Continue.
For owner `0`, `c_0=1`, `Q_0=C_0=1`, and hence

```text
D_0(t) = max(1,1+1)-1 = 1 = d_t(0).
```

For a nonowner the successor debt is zero, its Continue endpoint equals the
current value, and its Quit endpoint is no larger.  Hence `D_i(t)=0=d_t(i)`.
Every consecutive pair is therefore an exact dynamic-debt edge, not merely a
coarse conservation edge.

The question's conservation equation also holds literally.  Since
`c(a_t)=1-p_t`,

```text
d_t(0) = (1-p_t)d_(t+1)(0) + p_t d_t(0) = 1,
```

and all nonowner equations are zero identities.  Equivalently, the owner's
opponent-survival multiplier is one.

### Phantom payoff and the common margin

The honest suffix payoff is

```text
U_i(a^(t)) = A_t r_i({0}) -> 0.
```

In particular,

```text
v_t(0) = d_t(0) = 1,
v_t(0)-U_0(a^(t)) = 1-A_t -> 1.
```

Choose the same number used for the packet margin:

```text
eta = delta = 1/52.
```

Then `eta <= d_t(0) <= K_0=1` for every date and the prescribed owner limit is
`V=1>=eta`.  No opponent of player `0` ever quits, so every finite owner-clock
sum in (12) is exactly zero and is bounded by `log(52)`.  All annotations lie
in `[-4,4]^4` and all debts lie between zero and their singleton caps.

The Lean theorems `rational_tail_step` and
`rational_tail_bellman_values` prove the telescoping, deterrence, summability
majorant, and Bellman scalar identities.  The Python probe expands the common
reward table and checks all four players' exact Bellman, Nash-endpoint,
dynamic-debt, conservation, and honest-payoff formulas over 256 dates using
only exact fractions.  The finite loop is an audit; the arbitrary-real Lean
lemmas and the displayed algebra carry the proofs.

## 4. The corrected occupation/refusal branch split

The normalized hazard occupation of this tail is not the symmetric packet.
Only player `0` ever carries hazard, so every normalized occupation vector is

```text
lambda^tail = e_0.
```

Meanwhile `v_t -> z^tail=(1,1,1,1)`.  Its singleton mixture is column zero:

```text
m(lambda^tail) = (1,4,0,0).
```

Thus the ghost pair fails packet funding for players `2` and `3`:

```text
z^tail_i = 1 > 0 = m_i(lambda^tail),       i=2,3.
```

In this example `chi<=z^tail`, the positive debt owner is aligned with the
active atom, and complementarity holds at that atom.  Funding alone fails.
The table-wide funded packet exists elsewhere on the same reward table, but
there is no equation identifying it with tail occupation.

This exactly respects the corrected branch split in `172-Answer-CP`:
phase/occupation limits need not fund the target, while refusal-shaped limits
only enter the packet theorem after funding (and, generally, the punishment
floor and owner alignment) have separately been proved.  This report does not
smuggle any of those bridges into the witness.

## 5. What this establishes, and what remains open

### Established exactly

- one finite player set and one reward table are shared;
- the positive margin is shared: `eta=delta=1/52`;
- the tail has positive hazard at every date and finite total charge;
- every consecutive tail edge is exact Bellman--Nash and exact dynamic debt;
- annotation and honest terminal payoff are kept distinct;
- the full table-level packet family, including arbitrary targets satisfying
  (15), has the uniform refusal margin;
- no packet mass is identified with a tail occupation mass.

### Not established

- The tail is not proved to arise as a projective subsequential limit of the
  optimized finite min-max dynamic-debt chains with the extraction's terminal
  boundary.  Its finite prefixes are coherently exact and extendable, but that
  is weaker than optimized-minimizer provenance.
- The displayed packet is not canonically derived from the tail, and the
  tail-derived occupation is unfunded.
- The table is not shown to satisfy uniform terminal instability (A) or the
  universal exact-chain charge bound (B).  It is not a counterexample.
- Nothing here proves cardinal-minimality.  Cardinal-minimality is a property
  of a hypothetical counterexample; this same-table regression does not claim
  to be one.
- Arbitrarily adjoining dummy players does not preserve the packet proof.
  A cyclic construction can be redesigned in other cardinalities, but this
  report proves only the four-player instance and claims no automatic player
  extension theorem.

### Residual compatibility system

To upgrade exposed-equation consistency to full selected-tail consistency,
one must add at least the following provenance/interface data:

1. finite optimized chains with the prescribed terminal boundary whose
   projective limit is the displayed kind of positive exact-D tail; and
2. a tail-derived mass `lambda*` and target `z*` for which funding
   `z*_i <= m_i(lambda*)` and the punishment floor `chi_i<=z*_i` are proved,
   with the positive-debt/refusal owner aligned when that owner is used.

The witness shows why item 2 is substantive: exact debt conservation,
summable charge, positive phantom value, and even a separate table-wide
packet theorem do not force funding of the tail occupation.  Consequently no
T × P contradiction follows from the exposed equations alone.
