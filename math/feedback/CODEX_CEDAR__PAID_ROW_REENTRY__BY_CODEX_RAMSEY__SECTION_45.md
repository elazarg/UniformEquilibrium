# Review of Section 45 of `CODEX_CEDAR__PAID_ROW_REENTRY`

Reviewer: `CODEX_RAMSEY`

Status: `REPAIR REQUIRED IN GENERAL STATEMENT; VALID AFTER ADDING THE CANONICAL-BOX UPPER BOUND; RATIONAL REPAIR VALID`

## Post-review correction

The punishment-floor state is also a subtype of the canonical payoff box.
The original hypothesis `H_k(z)>=P_k` does not imply `H_k(z)<=M`: when
`O(z)` is small, `(Q_k(z)-K_k(z))/O(z)` can exceed the reward bound even
though `Q_k` and `K_k` are bounded.  Exactness of the original sure root gives
only the lower bound `H_k>=U_k>=P_k`.  The general Proposition 45 must
therefore also assume `H_k(z)<=M` (equivalently, that the constructed `V`
belongs to the canonical admissible box).  The proof below is valid with that
additional hypothesis.  The concrete Section 44/45 rational repair has
`H_k=11/15` and is unaffected.

## General compiler

Fixing the owner's interior Quit probability `s` and the outsiders' own tail
coordinates `W_i` defines an ordinary finite binary-action game among the
outsiders.  A mixed Nash profile `z` therefore exists.  Outsider endpoint
optimality in the combined quitting root is exactly its Nash condition in
that finite game; no continuation coordinate other than `W_i` enters player
`i`'s forced-Continue endpoint.

For the owner, forced Quit is tail-independent and forced Continue has the
form

```text
K_k(z)+O(z)V_k,
O(z)=product_(i != k)(1-z_i).
```

When `O(z)>0`, choosing

```text
V_k=H_k(z)=(Q_k(z)-K_k(z))/O(z)
```

makes the owner indifferent.  The side condition `H_k(z)>=P_k` and the
assumed outsider floors make `V` floor-safe.  The exact predecessor-floor
bound then applies to the successor.  Joint Continue probability is
`(1-s)O(z)`, so the absorption charge is at least `s`.

At the boundary `O(z)=0`, the owner's gap is independent of the tail.  An
interior owner mixture is possible exactly when `Q_k(z)=K_k(z)`.  The note's
zero-survival qualification is therefore exact.

## Section 44 support-change repair

At zero outsider tails, direct evaluation of the modified Section 44 table
gives, for `s>1/2`,

```text
Delta_a=2*s*z_b-1,
Delta_b=(1+s)/2-(1+3*s)*z_a/2.
```

For `s=3/4`, the unique fully mixed solution is

```text
z_a=7/13,
z_b=2/3.
```

Its outsider Continue product is

```text
O=(6/13)(1/3)=2/13.
```

For the owner,

```text
Q_k=(4/3)(11/13)=44/39,
K_k=(6/5)(11/13)=66/65,
H_k=(Q_k-K_k)/O=11/15.
```

The tail `(11/15,0,0)` is above the zero floor.  Since owner Continue mass is
`1/4`, the charge is

```text
1-(1/4)(2/13)=25/26.
```

The owner is indifferent at payoff `44/39`; the exact mixed outsider values
are `1/4` and `21/52`.  Hence the successor is exactly

```text
(44/39,1/4,21/52).
```

## Verdict and scope

After adding the canonical-box upper bound above, I found no missing Nash
condition, floor issue, survival boundary, charge factor, or rational
arithmetic error.  Proposition 45 is then a complete conditional exact
root-changing compiler and Section 44 lies on its positive side after the
displayed support change.

The scalar side condition `H_k(z)>=P_k` and a source that reaches the selected
outsider completion are still hypotheses.  The successor remains a fixed
positive payoff distance from the tail, so the result is not a payoff return
and not an actual paid-source adapter.  The note states these limitations
correctly.
