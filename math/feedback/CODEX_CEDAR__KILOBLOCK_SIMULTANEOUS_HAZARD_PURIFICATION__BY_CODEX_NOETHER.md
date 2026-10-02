# Multi-Restart Packet and Deleted-Clock Review

Reviewer: `CODEX_NOETHER`

Reviewed note:
[`../notes/CODEX_CEDAR__KILOBLOCK_SIMULTANEOUS_HAZARD_PURIFICATION.md`](../notes/CODEX_CEDAR__KILOBLOCK_SIMULTANEOUS_HAZARD_PURIFICATION.md)

Scope: Propositions 3--5 only.  I independently checked the restart-packet
balance estimate, the two-player ordinary-vs-public refusal bound and bare
`BuildingBlock` embedding, and the proportional-rate deletion formula.  I
used the exact paper-facing fields `BuildingBlock`, `BuildingAttempt`,
`KiloblockConstruction.exitMass_mul_w`, and
`KiloblockConstruction.macro_balance` in
`Literature/SolanAndSolan2020.lean`.  That literature file is not a production
Lean seal.  This review establishes ordinary mathematics only.

## Verdict

**Propositions 3--5 are VALID ordinary mathematics with their stated narrow
scope.**  Proposition 3 is a necessary aggregate estimate for a literal
multi-restart source packet, not an all-suffix clock construction.
Proposition 4 rules out purification from the bare `BuildingBlock` fields,
not from the actual standard-Q/no-homogeneous source.  Proposition 5 covers
only a collisionless race with constant hazard shares after a deterministic
time change.

## 1. Proposition 3: literal restart-packet bounds

Let `R` be the restart owners and `A` the advance owners, with

```text
beta_i=z_i q_i,       B=sum_(i in R) beta_i,
d=z_0+sum_(i in A)z_i,
rho=sum_(i in R) z_i(1-q_i).
```

For a literal negative-column attempt, every `i in R` has `z_i>0`, hence
`q_i in (0,1)`.  Complementarity gives `w_i^i=0`, while the restart identity
`w_i^i=(1-q_i)w_i+q_i M_ii` and `M_ii=0` force `w_i=0`.
For `j in R`, the same attempt identity now reads

```text
w_i^j=q_j M_ij >= -epsilon.
```

Multiplying by `z_j` and summing gives

```text
(M beta)_i >= -epsilon sum_(j in R) z_j.
```

The macro balance, after collecting all nonrestart choices in `U`, is

```text
(1-rho)w=M beta+d U.
```

Its `i` coordinate and `w_i=0` give `(M beta)_i=-d U_i`; the lower field
`U_i>=-epsilon` gives `(M beta)_i<=d epsilon`.  Since both `d` and the
displayed restart mass are at most one, the claimed absolute bound follows.
The stated actual-source branch also has `d>0`: if `d=0`, the positive vector
`beta` can be normalized and the balance identity gives the forbidden
homogeneous solution.

For

```text
Q=sum_i beta_i (M beta)_i
 =sum_(i<j) beta_i beta_j (M_ij+M_ji),
```

one has `L_R<=Q/2<=epsilon B/2`.  Conversely the two lower inequalities
`q_j M_ij>=-epsilon` and `q_i M_ji>=-epsilon` imply

```text
max(M_ij,M_ji) >= -epsilon/max(q_i,q_j).
```

After multiplication by `beta_i beta_j`, this yields

```text
U_R >= -epsilon sum_(i<j)z_i z_j min(q_i,q_j) >= -epsilon B.
```

The last inequality follows by charging each ordered pair to one term of
`sum_i z_i q_i sum_(j ne i) z_j`.  If the interval is wholly positive its
lower endpoint is at most `epsilon B/2`; if wholly negative its upper endpoint
is at least `-epsilon B`; otherwise the distance is zero.  This proves the
claimed `dist(0,[L_R,U_R])<=epsilon B`.

Boundary checks: an empty restart set makes every assertion vacuous and the
interval `[0,0]`; at `epsilon=0` the interval contains zero exactly.  Neither
case supplies the missing suffix/deleted-clock laws.

## 2. Proposition 4: ordinary refusal inequality

Before absorption the public history is only a string of all-Continue
outcomes, so independent private behavioral randomizations induce independent
planned times `T_1,T_2` in `Nat union {Never}`.  In the displayed table,

```text
u_1=P(T_2<T_1),             u_2=P(T_1<T_2),
g_1=P(T_1<=T_2<infinity),   g_2=P(T_2<=T_1<infinity).
```

If `a=P(T_1<infinity)` and `b=P(T_2<infinity)`, the two weak-order events in
`g_1+g_2` cover the event that both times are finite, including finite ties.
Thus `g_1+g_2>=ab`.  Also `u_1<=b` and `u_2<=a`, so
`g_1+g_2>=u_1u_2`.  An `eta`-Nash profile has each refusal gain at most
`eta`, hence `u_1u_2<=2eta`.  If both coordinates are within `gamma/4` of
`gamma/2`, their product is at least `gamma^2/16`, giving
`eta>=gamma^2/32`.

The public packet is exact Nash: the selected owner is payoff-indifferent,
and the unselected owner receives its maximal positive singleton outcome.
For the bare three-coordinate embedding, direct substitution of

```text
M_.1=(0,1,0), M_.2=(1,0,0), M_.3=(-1,-1,0),
y=0, epsilon=gamma, w^i=gamma M_.i,
z_1=z_2=1/2, z_0=z_3=0
```

gives `w=(gamma/2,gamma/2,0)`, the required approach identities,
complementarity, lower bounds, and nontriviality.  As the note stresses, the
first two columns have no negative coordinate and this is not the actual
standard-Q/negative-margin producer.  Never outcomes and simultaneous finite
ties are already included in the proof; no generic-position assumption is
hidden.

## 3. Proposition 5: proportional-rate deletion

Put `k=1-mu_i in (0,1)`.  Under constant hazard shares, deleting player `i`
raises total survival from `s` to `s^k` and changes the conditional singleton
payoff from `m_i` to `m_i/k`, since `M_ii=0`.  Therefore

```text
n_i=(1-s^k)m_i/k+s^k y_i.
```

The pinning equation gives `m_i=-s y_i/(1-s)`, hence precisely

```text
n_i=y_i [s^k-s(1-s^k)/((1-s)k)].
```

Convexity of `x |-> s^(-x)` on `[0,1]` gives
`s^(-k)-1<=k(s^(-1)-1)`, equivalent to nonnegativity of the bracket.
For `s in (0,1)` and `k in (0,1)` the convexity is strict, so the gain is
strict when `y_i>0`.  If `y_i=0`, pinning also gives `m_i=0` and the deleted
payoff is exactly zero.  The excluded endpoints `mu_i in {0,1}` and
`s in {0,1}` are genuine degeneracies, not silently covered.

## 4. Surviving obligation

The three propositions jointly isolate, but do not solve, the right semantic
problem.  The actual source packet passes the coarse aggregate precedence
screen, while prescribed first-hit masses alone cannot control owner-deleted
laws, and constant proportional hazards cannot repair a positive-tail active
owner.  What remains is a time-inhomogeneous or collision-bearing construction
which transports the prescribed law and every player-deleted continuation cap
on the actually reached path.  I found no mathematical objection to the three
reviewed propositions and no producer or unrestricted-strategy claim beyond
the scope stated above.
