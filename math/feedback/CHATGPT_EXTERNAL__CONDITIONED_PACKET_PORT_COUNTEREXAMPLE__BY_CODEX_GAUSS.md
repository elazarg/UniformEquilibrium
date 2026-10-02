# Review of Conditioned-Packet Residual-Port Counterexample by `CODEX_GAUSS`

Reviewed note:
[`CHATGPT_EXTERNAL__CONDITIONED_PACKET_PORT_COUNTEREXAMPLE.md`](../notes/CHATGPT_EXTERNAL__CONDITIONED_PACKET_PORT_COUNTEREXAMPLE.md).

## Verdict

**The three-player posterior calculation is valid as a nonidentifiability
example for one preselected residual port, not as a negative answer to the
conditioned-packet question.**  The positive-denominator `Omega_L` estimate is
valid under the stated common-component model.  Small reset mesh and equality
of terminal semantic **pairs** do not determine the clock obtained by
conditioning the preceding complete law.  But the question asks to construct
an actual packet at the reached semantic source; it does not formally require
using that particular conditional port.  On this degenerate table one may
restart the two branch laws with entrance weight `lambda`, recovering the
frozen clock and atom while keeping the same reached semantic pair.  The
phrase "profile provenance" does not specify a fixed latent-port identity
strong enough to forbid this restart.

The example also does not instantiate `QuittingVanishingDebtAtomAccess`, whose
frontier, tangent-family, eventual-rank, and positive-support data are not
supplied.  It therefore falsifies only a proposed theorem asserting continuity
of a **given conditioned port** from mesh and semantic-pair distance; it does
not show that every allowed reprojection loses a clock or violates the
carrier.

The replacement theorem needs three qualifications.

1. Every compared suffix must have positive mixed survival under both entrance
   weights; at a zero denominator the Bayes port is undefined and cannot be
   recovered from terminal semantics.
2. The charge-halving constant `(7.2)` is correct for the prescribed atom arm.
   For the rectangle arm, the same worst-case two-profile comparison requires
   `Omega_L <= q/(16*K*R)`, not `q/(8*K*R)`.
3. The argument proves a sufficient posterior-conditioned modulus, not the
   proposed repair's maximality.  Summability gives vanishing **tail** error
   and transports a separately supplied divergent block clock; it does not by
   itself supply small debt, semantic seams, or divergence.

I did not run Lean.  The conclusions here are exact ordinary probability and
payoff calculations, not a checked source adapter.

## Bayes arithmetic and behavioral realization

Let the initial weight of branch `B` be `lambda=1/N`.  At the preceding date,
branch `A` survives with probability `lambda^2`, while `B` survives surely.
Conditioning on survival gives

```text
P(B | survive)
 = lambda / ((1-lambda)*lambda^2+lambda)
 = N^2/(N^2+N-1).
```

Both complete branches eventually terminate at `{a}` when `m,o` never Quit:
branch `A` either Quits at the preceding date or, conditional on survival,
at the packet date; branch `B` Quits one date after the packet.  Hence before
the reset all mixtures have terminal outcome law `delta_{ {a} }` and semantic
pair zero.

At the packet date, branch `A` Quits and `B` Continues.  Therefore the frozen
and reached Continue probabilities of `a` are `lambda` and `hatLambda`.
For `N>=17`,

```text
hatLambda-lambda
 = N^2/(N^2+N-1)-1/N > 1/2.
```

The inequality in fact has considerable slack.  The conditioning convention
and the complete stopping-law realization are consistent.

With `m` Quitting now with probability `delta=1/N` and `o` continuing, player
`o` receives `-1` exactly on the event that `m` Quits, irrespective of `a`'s
action.  Never/Continue is optimal for `o`; every own Quit yields `-1`.  Thus

```text
U_o=B_o=-delta,
```

and the other two coordinates are zero.  The frozen and reached terminal
semantic pairs are indeed both

```text
((0,0,-delta),(0,0,-delta)).
```

Their terminal **outcome laws at this reset root are not equal**: the masses
of `{a,m}` and `{m}` depend on the branch weight.  This should be called
semantic-pair equality, not semantic-law equality; the atom switch uses
exactly that hidden law difference.

Literal reached semantic tails have zero one-step prescribed/direct defects
under the exact-data construction.  This observation does not identify them
with a positive-minimum frontier packet.

## Atom and deleted-clock calculations

For the source where `m` never Quits and the endpoint where `m` Quits surely
at the packet date, terminal `{a,m}` has source mass zero and endpoint mass
`1-w`.  Since its observer reward is `-1`, the project's orientation

```text
(source mass - endpoint mass) * reward
```

gives atom `1-w`.  There are `1+(2^3-1)=8` terminal outcomes including Never.
At `w=lambda`, `8(1-lambda)>=1/2`; after conditioning,

```text
1-hatLambda=(N-1)/(N^2+N-1),
8(1-hatLambda)<1/2
```

for `N>=17`.  The charge-one label `{a,m}` therefore fails after conditioning,
while `{m}` carries atom `hatLambda` and becomes the large label.  Source and
endpoint observer debts are both zero.  These data instantiate the prescribed
arm of one local
`HasQuittingStoppingLawVanishingDebtAtomAlternative`; they do not by
themselves instantiate the frontier-level `QuittingVanishingDebtAtomAccess`.

Deleting player `m` from the packet root leaves only `a,o`, with `o`
continuing surely.  The deleted-`m` one-row survival is therefore exactly
`a`'s Continue probability, namely `lambda` versus `hatLambda`.  Their
distance exceeds `1/2`, and the triangle inequality gives the stated `>1/4`
lower bound for approximation by one common clock.  Thus semantic-pair
distance zero and reset parameter `delta->0` do not control this residual
port.

They also exhibit the missing universal quantifier in the proposed negative
answer.  At the reached semantic pair, discard the posterior port and start a
new literal continuation which mixes the same two branches with weight
`lambda`.  The packet-date root, deleted clock, and `{a,m}` atom return to the
frozen values, while the semantic pair remains `x_delta`.  Unless "profile
provenance" is strengthened to mean conditional continuation of one fixed
preceding behavioral law, this is an admissible construction rather than a
violation.  The read-only question contains no such formal fixed-port clause.

## Posterior modulus

For common component laws with survivals `S(s),T(s)`, direct algebra gives,
whenever both mixed denominators are positive,

```text
F_s(a)-F_s(b)
 = S(s)T(s)(a-b)/(M_s(a)M_s(b)).
```

Conditioning independent player laws on joint survival factorizes by player.
At suffix `s`, couple the two profiles by first coupling each player's latent
component labels.  The disagreement probability for player `i` is at most
`|F_i,s(a_i)-F_i,s(b_i)|`; a union bound gives at most `Omega_L`.  Conditional
on equal labels, use the same residual component law.  Hence every event of
the complete conditional future law differs by at most `Omega_L`.  In
particular this controls joint survival and, after omitting any selected
player, every one-player-deleted survival for every remaining finite horizon.
Equivalently, one may telescope the corresponding products.

This proof requires that the frozen and reached ports use the **same two
component laws** and differ only in entrance weights.  It also requires
`M_i,s(a_i),M_i,s(b_i)>0` at every suffix being compared.  If a mixed survival
is zero, that suffix is null and Bayes conditioning supplies no canonical
off-path port.  A separate convention or direct literal-root hypothesis is
then necessary.

If all denominators are at least `rho`, survivals are at most one, so

```text
Omega_L <= rho^(-2) * sum_i |a_i-b_i|.
```

The posterior update identity

```text
|a_i-b_i|
 = b_i(1-b_i)|T_i-S_i|/M_i(b_i)
```

is exact, and the preceding survival floor `rho_0` gives `(6.5)`.  In the
example `M_pre(lambda)` is of order `lambda`, while the numerator is also of
order `lambda`; the posterior displacement stays order one.  Thus some
conditioning-sensitive datum—denominator control, direct posterior TV, or an
equivalent port field—is genuinely necessary for a vanishing modulus based
on this parametrization.  This does not prove that the displayed condition
number is the unique or maximal possible repair.

## Semantic, best-response, and atom stability

The coupling bound gives payoff expectation difference at most
`2R*Omega_L`.  For best response, compare the payoff of the same arbitrary
behavioral deviation under both opponent ports; the same coupling bound is
uniform in that deviation, and
`|sup f-sup g|<=sup|f-g|`.  Thus the two semantic-pair bounds in `(7.1)` are
valid, and the debt bound `4R*Omega_L` follows by subtraction.  This is full
behavioral best response, not pure-time-only control.

For a signed terminal atom comparing two profiles, perturbing each profile's
outcome law costs at most `Omega_L`; the signed atom changes by at most
`2R*Omega_L`.  In the prescribed arm, an old bound `K A>=q/2` remains valid
for charge `q/2`, whose threshold is `q/4`, under

```text
Omega_L <= q/(8KR).
```

In the rectangle arm the old threshold is `q/4` and the charge-halved
threshold is `q/8`.  The same worst-case calculation instead needs

```text
Omega_L <= q/(16KR).
```

unless a one-sided/common-profile coupling improves the factor two.  Argmax
label stability additionally needs a genuine gap; the suggested
`4R*Omega_L<g` is the safe two-label comparison.

## Concatenation and scope

For block `n`, the `s=0` case controls its whole-block joint/deleted survival
factor.  If nominal block survival products vanish through a divergent clock
budget and `sum_n Omega_(L_n)<infinity`, summable perturbation transports that
divergence to the actual block factors.  The same summability makes comparison
errors from sufficiently late packet tails arbitrarily small.

Finite total error is not automatically an `eta`-small certificate from date
zero; one starts sufficiently late or imposes a preassigned total budget.
Nor does `(7.3)` create a divergent clock, small initial debt, or summable
semantic seam mismatch.  The result is therefore a useful port-stability
condition and a valid warning that semantic pairs do not identify a chosen
conditional port.  It is not a counterexample to the existential
conditioned-packet producer, not a complete producer, and not a proof of
maximality.
