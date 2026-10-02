# Round 5 Feedback on Toggle Potentials

Reviewer: `CODEX_NOETHER`

Reviewed note: `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`

Scope: Proposition 21 only, the fixed Quit-now/Never coalitionwise
calibration escape. The proposed future reward gadget and any Nash or
counterexample conclusion are outside this review.

Status: `VALID_ORDINARY_MATHEMATICS`

## Claim reconstructed

Let `I` be finite and nonempty and fix `theta_i` with `0<theta_i<1`. Assume

```text
r({i})_i >= 0
```

for every `i`, and, for every nonempty `T` not containing `i`,

```text
(1-theta_i) r(T)_i + theta_i r(T union {i})_i >= 0.       (CE)
```

Proposition 21 claims that the stationary product profile with live-stage
Quit probabilities `theta_i` absorbs almost surely and has nonnegative
terminal payoff in every coordinate. It does not claim that this profile is
Nash.

I find the claim and its stated scope correct.

## Product-law and absorption check

At one live stage put

```text
w(S) = product_(j in S) theta_j * product_(j notin S)(1-theta_j).
```

The one-stage all-Continue probability is

```text
c = w(empty) = product_j (1-theta_j).
```

Because `I` is nonempty and every `theta_j` is strictly positive,
`0<=c<1`. Independent repetition at the unique live history gives survival
probability `c^N` through `N` dates, which tends to zero. Thus absorption is
almost sure, including the countable-time `Never` outcome.

For every nonempty coalition `S`, the probability that `S` is the first
quitting coalition is

```text
sum_(n>=0) c^n w(S) = w(S)/(1-c).
```

Hence the prescribed payoff is exactly the conditional one-stage product law
given a nonempty coalition, not an approximation and not a finite-horizon
claim.

## Pairing check

Fix `i`. The nonempty coalitions partition into the singleton `{i}` and the
pairs

```text
T, T union {i}
```

indexed by nonempty `T subseteq I\{i}`. The empty set must not be included in
this index: its partner is precisely the separately handled singleton `{i}`.

For every indexed `T`, strict positivity of `1-theta_i` gives

```text
w(T union {i}) = w(T) * theta_i/(1-theta_i).
```

Therefore the unnormalized pair contribution to player `i` is

```text
w(T) r(T)_i + w(T union {i}) r(T union {i})_i
 = w(T)/(1-theta_i)
     * ((1-theta_i) r(T)_i + theta_i r(T union {i})_i)
 >= 0.
```

The remaining singleton contribution is
`w({i}) r({i})_i>=0`. Summing and dividing by `1-c>0` proves the
coordinatewise payoff conclusion. The displayed weights in the note have the
correct orientation.

## Boundary and falsification tests

- For one player there is no nonempty `T` excluding `i`; the theorem reduces
  correctly to the solo hypothesis. The stationary profile terminates
  geometrically and pays `r({i})_i>=0`.
- For two players, `theta_0=3/10`, `r({1})_0=-3`, and
  `r({0,1})_0=7` make player 0's paired expression exactly zero:
  `(7/10)(-3)+(3/10)7=0`. The two product weights cancel exactly as the proof
  predicts; no symmetry or `theta=1/2` is being used.
- The solo hypothesis is necessary at the unpaired boundary. In the
  one-player game, a negative solo payoff falsifies the conclusion while all
  `(CE)` hypotheses are vacuous.
- Each nonempty-`T` instance of `(CE)` is likewise necessary for this
  coalitionwise proof: making one paired expression negative and all other
  reward entries zero makes that pair's contribution negative in player
  `i`'s payoff.
- The open restrictions `0<theta_i<1` justify both the geometric absorption
  and the division by `1-theta_i`. The theorem does not silently assert an
  endpoint extension to `theta_i=0` or `1`.

## Behavioral and scope audit

The constructed strategy is a legitimate behavioral profile on the unique
live history: at each public date every player uses a fresh private Bernoulli
coin, and the players' coins are independent. No public correlation is
introduced. Simultaneous quitting is retained by the full coalition law
`w(S)`.

The result is deliberately not a Nash statement. It evaluates one feasible
product profile and therefore does not control a player's pure quit time,
history-dependent behavioral replacement, or an interior-time deviation.
Accordingly it rules out only a negative argument whose claimed contradiction
comes from the displayed fixed coalitionwise Quit-now/Never floor inequalities.
It does not rule out schedule-adapted incentive gadgets and does not itself
produce or refute a quitting-game equilibrium.

## Verdict

Proposition 21 is valid ordinary mathematics at its narrow stated scope. The
singleton/empty boundary, exact product weights, almost-sure absorption,
simultaneous coalitions, and behavioral interpretation all check. I found no
mathematical objection or wording correction.
