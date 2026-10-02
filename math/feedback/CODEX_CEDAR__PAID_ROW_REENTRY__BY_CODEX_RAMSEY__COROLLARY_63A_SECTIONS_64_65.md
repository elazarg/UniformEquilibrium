# Review of Corollary 63A and Sections 64--65

Reviewer: `CODEX_RAMSEY`

## Verdict

**PASS.**  The tolerance-dependent reached update, four-player monotone-ray
regression, and three-player local Nashification no-go are exact in their
stated scopes.  None supplies an exact paid-return producer or a positive-
minimum counterexample.

## Corollary 63A

Replacing the endpoint error by `0<eta<=c/8` keeps the raw-carrier parameter
sum within its valid budget:

```text
c/4+c/8+eta <= c/2 < c.
```

At sufficiently late ranks the endpoint debt is at least `3c/8`.  The
receiving strategy therefore gives

```text
U_o(R_r)-U_o(F_r)
  >= B_o(F_r)-eta-U_o(F_r)
  >= 3c/8-c/8 = c/4.
```

Updating only player `o` does not change its opponents' strategies, and the
unrestricted behavioral cap is a function of that opponent environment.
Thus `B_o(R_r)=B_o(F_r)`, while the same receiving inequality gives

```text
debt_o(R_r)=B_o(R_r)-U_o(R_r)<=eta.
```

The rank threshold may depend on `eta`, exactly as stated.  This is one
literal unilateral behavioral port; it imposes no simultaneous root Nash
conditions.

## Section 64

I independently enumerated every pure stopping region.  For observer `o`,
Quit at date zero pays `1-2lambda`, while waiting past date one pays
`(1-s)(1-lambda)`; all other relevant pure times pay zero.  For `m` and `p`,
immediate Quit attains cap one.  For `h`, immediate Quit has value

```text
2(1-s)lambda+3s lambda=2lambda+s lambda,
```

and all later choices have value zero.  Since the opponents absorb only at
dates zero and one, arbitrary behavioral strategies are convex combinations
of these stopping regions; the displayed values are the unrestricted caps,
not a restricted menu.

The debts at `s=0` are

```text
(1-lambda,1,1-lambda,2lambda)
```

and sum to three.  Since `lambda<=1/4` lies before the crossing
`lambda/(1-lambda)`, the normalized change from `s=0` to `s=lambda` is exactly

```text
(-(1-lambda),-1,2(1-lambda),lambda),
```

whose sum is zero.  At `s=1` the debt vector and total are exactly

```text
(1-2lambda,0,3(1-lambda),3lambda),
4-2lambda.
```

Summing the four debt formulas before and after the unique crossing gives

```text
D(s)=3                                      before,
D(s)=3-lambda+s(1-lambda)                  after.
```

The observer debt falls monotonically from `1-lambda` to `1-2lambda`, so its
total downward variation over every monotone subdivision is exactly at most
`lambda`.  The limiting base, flat direction, zero inactive tangent, full-
endpoint excess, and curvature values quoted in the note follow from these
same exact vectors.

The scope qualification is necessary and correct: this table proves only a
selected-ray amplification failure.  It neither proves the limiting pair is
a global minimum of the semantic carrier nor supplies compatible rays for the
other active movers.

## Section 65

At `F`, player 1 terminates alone and receives `-1`; players 2 and 3 receive
zero.  At `R`, players 2 and 3 quit together first, and the coalition `{2,3}`
has payoff vector zero.  Hence the prescribed gain is one and `U(R)=0`.
Player 1's opponent environment is unchanged; waiting past `{2,3}` is worth
zero and every joining action is worth `-1`, so its cap is zero and
`debt_1(R)=0`.  (Players 2 and 3 do have positive debt at `R`; the proposition
does not claim otherwise.)  The punishment floor is exactly the zero vector:
Never guarantees each player a nonnegative `b_i` payoff against any absorbing
opponent coalition, and the displayed opponent punishments attain cap zero.

At a one-stage root with tail zero, for every player and every realized
opponent Quit set `A`, including the empty set,

```text
Continue payoff = b_i(A),
Quit payoff     = b_i(A)-1.
```

Quit is therefore strictly dominated under every product law.  All-Continue
is the unique exact endpoint-Nash root, has zero charge, and maps tail zero to
current payoff zero.  Iterating in the stated tail-to-current orientation
proves that every finite exact floor-admissible path starting at zero has only
zero-charge edges.

This is an exact local obstruction to converting the Corollary 63A-style
reached recovery into a positive exact edge at the reached payoff.  It reuses
the Section 27 table and does not instantiate the positive-minimum tangent
frontier or rule out nonlocal excursions.
