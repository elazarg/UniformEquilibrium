# Review of normal-floor collapse and reset exit

Reviewer: `CODEX_HAHN`

Reviewed file:
`notes/CODEX_GROMOV__SUMMABLE_WAIST_NORMAL_FLOOR_AND_RESET_EXIT.md`

Reviewed SHA-256:
`13ec5a9b0fdcde5d3fff28a156642fab4bb26618f9404d0506c933b459b4de05`

## Verdict

**REVISE.** The normal-floor collapse and the game-independent exact-root
debt-expenditure lemma are correct. The singleton-wall conclusion in Section
2 is also recoverable from the supplied reset data, but its displayed proof
has a reversed inequality and does not establish it as written. Section 4
becomes valid after replacing that step by the direct reset-endpoint limit
argument below.

## Normal-floor collapse: PASS

Summable joint absorption makes the Bellman increments summable, hence the
bounded displayed values converge. Every marginal root hazard is bounded by
joint absorption, so the exact roots converge to all Continue. Closedness of
root Nash then gives `r_i({i}) <= v_infinity(i)`.

The checked violation theorem propagates a strict floor violation forward
and makes that coordinate nonincreasing. Its limit would therefore remain
strictly below the punishment floor. For a normal player the floor is at most
the singleton payoff, contradicting the preceding all-Continue inequality.
Thus an all-normal bounded summable exact tail is floor-safe at every date.

## Section 2: the stated derivation fails, but a direct repair works

Equations (5) and (6) in the reviewed note say

```
Delta_j^n <= -delta/2,
r_j({j}) <= U_j^infinity.
```

These do **not** imply

```
W_j^n <= r_j({j}) - delta/4.
```

The inequality on `U_j^infinity` has the wrong orientation for that
inference. `U_j^infinity` may lie arbitrarily far above the singleton payoff.

The desired wall crossing nevertheless follows directly at reset indices.
There the note already has

```
bar E_n = Q_j(bar q^n_-j) - C_j(bar q^n_-j; W_j^n) >= delta.
```

Summable hazards give `bar q^n -> all Continue`. Therefore the Quit endpoint
tends to `r_j({j})`, the absorbing part of the Continue endpoint tends to
zero, and its continuation coefficient tends to one. Consequently

```
r_j({j}) - W_j^n >= delta - o(1)
```

along reset indices. In particular the stated `delta/4` wall separation is
valid at every sufficiently late reset. This proof does not need the
holonomy inequality (5), although the holonomy theorem is what identifies
the source of the reset seam.

## Exact-root debt expenditure: PASS after the repair

For an actual pair with `d_j >= d0` and payoff at least `epsilon` below the
singleton wall, the exact coordinate identity

```
d'_j = [s_j d_j - max(E_j,0)]_+
```

gives the two cases in the note. If opponent absorption is at least
`epsilon/(8M)`, survival alone spends at least
`epsilon*d0/(8M)`. Otherwise endpoint stability keeps the Quit advantage
above `epsilon/2`, spending at least `min(d0,epsilon/2)`. Every other debt
coordinate weakly decreases under an exact prefix, so this is also a total
debt drop.

Using the directly repaired wall separation at the reset child therefore
gives the uniform exact-prefix drop claimed in Section 4, and global
minimality places every sufficiently late reset child a fixed distance above
the minimum fibre.

## Scope

The repaired result is a genuine one-step exact Nash--Bellman exit, not a
renewable rank. The descendant is not shown to retain the nested cap-child
passport. The eventual shifted-cap arm remains untouched.

There are also stray control characters before two occurrences of
`varepsilon` in the reviewed bytes; these are editorial but should be removed
before any export candidate is frozen.

## Repaired delta audit

I checked the repaired note at SHA-256
`cb2982590e3cbfe5e6f3472642ec61d8d8d295208dc14a5ffe902e29f9f4639f`.
The wall crossing is now derived directly from the reset equation
`bar E_n >= delta` and convergence of the barred roots to all Continue. This
correctly gives `W_j^infinity <= r_j({j})-delta`, hence the eventual
`delta/2` finite-depth wall. The exact-root lemma is then applied with the
correct constants
`min(delta,delta/4,delta^2/(16M))`. The control characters are removed.
No other claim was strengthened. **PASS** at the repaired SHA.

## Exact delta audit: absorption-floor strengthening

I checked the subsequently strengthened note at SHA-256
`b1425eead9f69f695bef8a1e1b69d02327bc010de7cd06760aba66c0047948ab`.
The only mathematical addition is the uniform joint-absorption floor in the
game-independent singleton-wall lemma and its specialization to the reset
child.

The proof is correct.  In the large-opponent-absorption case, joint
absorption dominates opponent absorption, so it is at least
`epsilon/(8M)`.  In the complementary case, endpoint stability leaves a
strictly positive Quit-minus-Continue gap for the named player; exact product
root Nash therefore forces that player to Quit surely, making joint
absorption one.  This gives
`min(1, epsilon/(8M))`, and substituting `epsilon = delta/2` gives the stated
reset constant `min(1, delta/(16M))`.  The debt-drop constants and the
all-normal floor-elimination argument are unchanged and remain valid.

The strengthening still makes only a literal one-step claim and explicitly
does not claim renewal across the cap-child seam.  **PASS** at the exact SHA
above.
