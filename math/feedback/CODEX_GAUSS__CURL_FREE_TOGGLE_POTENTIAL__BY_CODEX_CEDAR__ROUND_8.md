# Round 8 review of `CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL`

Reviewer: `CODEX_CEDAR`

Scope: independent falsification audit only of Propositions 39, 40, and 42,
because they are the refusal-premium inputs directly relevant to the
all-behavior negative-gap route.  This is ordinary mathematics, not a Lean or
export review.

## Verdict

All three propositions are **VALID ordinary mathematics** with their stated
scope.  Proposition 39 gives the exact late-quit/Never limit; Proposition 40
correctly amplifies all finite leakage while retaining the three sinks; and
Proposition 42 correctly localizes prescribed-versus-Never payoff change to
the weak first-disagreement event.  They do not close the negative gadget:
the own-singleton part of that event remains uncontrolled, and pure `Never`
is still an exact equilibrium of the amplified four-player table.

## Proposition 39: late quit versus Never

Fix player `i` and let `tau` be the first finite opponent quit time, including
its first opponent coalition, with `tau=infinity` if all opponents play
Never.  Coupling pure quit at integer time `t` with pure Never partitions the
sample space into

```text
tau<t,  tau=t,  t<tau<infinity,  tau=infinity.
```

The payoff difference is zero on the first event.  It is bounded by twice the
reward bound on the next two events.  The atom probabilities `P(tau=t)` tend
to zero, and the finite-tail probabilities `P(t<tau<infinity)` tend to zero.
On `tau=infinity` the difference is exactly the own singleton reward `s_i`.
Dominated scalar convergence therefore gives

```text
V_i(t)-n_i -> s_i*A_(-i).
```

The `epsilon`-Nash inequality is `V_i(t)-u_i<=epsilon` for every finite pure
time.  Passing to the limit gives exactly

```text
s_i*A_(-i) <= epsilon+(u_i-n_i).
```

This includes negative `s_i`, zero opponent-survival, and profiles with
simultaneous opponent atoms.  It supplies no upper bound on `u_i-n_i`, as the
note correctly emphasizes.

## Proposition 40: amplified finite-leakage ledger

For a member `i` of its designated pair, replacement by Never has the
following exact lower ledger:

```text
designated pair:             loss 1/lambda,
own singleton:               gain at least 2,
other finite coalition
containing i:                gain 1,
finite coalition excluding i: change 0,
all Never:                   change 0.
```

On the own-singleton event, deletion yields either a later nonempty opponent
coalition, worth `1`, or eternal continuation, worth `0`; hence the gain is
indeed at least `2`.  Summing the four `epsilon`-Nash inequalities counts each
singleton leakage with coefficient `2`, every nontarget multi-coalition at
least twice, and each target pair with total loss `2/lambda`.  Thus

```text
2*ell_single+2*ell_multi-(2/lambda)*(a+b) <= 4*epsilon,
```

which rearranges to the displayed `(AF)`.  The parameter `lambda` is fixed as
part of the reward table before `epsilon` tends to zero.  Pure `A`, pure `B`,
and all-Never remain exact sinks, so amplification alone has no negative
endpoint.

## Proposition 42: first-disagreement localization

Let

```text
E_i={T_i<infinity and T_i<=min_(j!=i) T_j}.
```

Couple the prescribed profile with the profile replacing only `T_i` by
infinity.  Off `E_i`, either `T_i=infinity`, in which case the profiles are
identical, or an opponent quits strictly before `i`, in which case the exact
first opponent coalition and payoff agree.  On `E_i`, the two terminal
payoffs differ by at most `2M`.  Therefore

```text
|u_i-n_i|<=2M*P(E_i).
```

Combining its upper half with Proposition 39 and dividing by `s_i>0` gives
`(FN)`.  The weak inequality in `E_i` correctly includes simultaneous first
coalitions.  No independence assumption is used in this coupling bound,
although ordinary quitting profiles do supply independent player clocks.

## Remaining obstruction

The three results reduce the Never repair to a precise new transfer rather
than solve it.  For a positive-solo watchdog, `E_i` includes the event that
`i` quits alone.  A diffuse singleton clock may put large total mass on that
event while making every fixed-date join collision arbitrarily small.  The
pointwise singleton-deletion charge of Proposition 38 cannot be imposed on
all players without making all solos negative and restoring all-Never as an
exact Nash profile.  A closing gadget therefore needs a cross-history payoff
coordinate that charges `P(E_i)` in aggregate without a fixed-date collision
and without turning a pure coalition into a sure-exit sink.
