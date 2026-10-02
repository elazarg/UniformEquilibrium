# Conditioned-packet residual-port non-identifiability and posterior stability

## Corrected status and retraction

**Internal regression and sufficient conditional stability lemma.**
Terminal-semantic source data and residual stopping-law ports are different.
The rational example below has exactly matching frozen and reached
terminal-semantic laws, zero prescribed and direct-debt defects, and
arbitrarily fine reset mesh, but conditioning changes one deleted-player clock
by more than `1/2` and switches the charged terminal atom.

The example proves non-identifiability of an arbitrarily preselected residual
port from its semantic pair.  It does **not** refute the existential producer
in `questions/CONDITIONED_PACKET_REPROJECTION.md`: that producer may choose the
preceding packet, retain the complete port as recursive state, or construct a
third compatible realization.  The example is not derived from a
positive-minimum tangent family and does not show that every compatible
executable chronology fails.

The earlier claims that there were “only two possibilities,” that this was an
acceptable negative answer, that the conditional-port formulation was
maximal, and that the producer was false are retracted.  The surviving
positive result is only sufficient: for a finite packet, the quantity
`Omega_L` below controls every joint and one-player-deleted suffix clock under
its explicit port hypotheses.  Without survival denominators or a branch gap,
clock and branch-label stability of a preselected realization are false.

Author: `CHATGPT_EXTERNAL` (submitted through the conference orchestrator)

Status: `CORRECTED INTERNAL REGRESSION; CONDITIONAL LEMMA UNREVIEWED`

Review targets: the exact behavioral realization and Bayes conditioning; the
claimed `QuittingVanishingDebtAtomAccess` instance; deleted-clock labels; the
uniform payoff/best-response comparison; and whether the replacement controls
all suffix laws claimed.

## 1. Claim being tested and exact logical scope

The historical statement tested by this note asked mesh and
terminal-semantic source closeness to control a preselected attached packet's
fixed orientation, prescribed/direct defects, and every joint and
one-player-deleted suffix clock while retaining profile provenance.  The
current
[`CONDITIONED_PACKET_REPROJECTION.md`](CONDITIONED_PACKET_REPROJECTION.md)
instead carries an actual reached port and asks for an existentially selected
source-matched kernel; the example below does not refute that formulation.

The proposal distinguishes

```text
terminal-semantic source (u,b)
residual stopping-law port.
```

Conditioning may leave the first unchanged and alter the second by order one.
This rules out semantic-state-only reconstruction of an arbitrarily selected
port.  It does not rule out existential construction of a compatible port.

## 2. Rational three-player game

Let `I={a,m,o}`.  For every nonempty terminal coalition `S`, put

```text
r_a(S)=r_m(S)=0,
r_o(S)=-1  if m in S or o in S,
r_o(S)=0   otherwise.
```

Fix `N>=17` and `lambda=delta=1/N`.  Player `a` has two labelled complete
stopping-law branches:

- `A`: at the preceding date survive with probability `lambda^2`, then Quit
  surely at the packet date;
- `B`: Continue at the preceding and packet dates, then Quit surely one date
  later.

Both branches eventually terminate at `{a}` when `m,o` Continue.  Hence every
mixture has prescribed payoff, best-response value, and terminal outcome law

```text
U=B=(0,0,0),      law=delta_{ {a} }.
```

Initially give branch `B` weight `lambda`.  Conditioning on survival of the
preceding date changes its posterior weight to

```text
hatLambda
  = lambda / ((1-lambda)*lambda^2+lambda)
  = N^2/(N^2+N-1).
```

At the packet date branch `A` Quits and branch `B` Continues, so `a`'s frozen
and reached Continue probabilities are respectively `lambda` and `hatLambda`.
For `lambda<=1/4`,

```text
hatLambda-lambda > 1/2.
```

## 3. Fine reset packet and unchanged semantic source

At the packet date, let `m` Continue forever with weight `1-delta` and Quit
now with weight `delta`; let `o` Continue.  The frozen and reached product-root
Continue vectors are

```text
(lambda,    1-delta, 1),
(hatLambda, 1-delta, 1).
```

The mesh is `delta -> 0`.  If the root continues, `a` later absorbs alone at
payoff zero.  At the root, `o` gets `-1` exactly when `m` Quits, so

```text
U_o=-delta,
Quit_o=-1,
Continue_o=-delta,
B_o=-delta,
D_o=B_o-U_o=0.
```

The other coordinates are zero.  Thus the frozen and reached first semantic
pair is exactly

```text
x_delta=((0,0,-delta),(0,0,-delta)),
```

and the displayed prescribed and direct-debt defects are zero.

## 4. Fixed atom orientation switches

At the underlying source let `m` Continue forever; at the full reset endpoint
let `m` Quit surely at the packet date.  For terminal label `C={a,m}`, source
mass is zero and endpoint mass is `1-w` when branch `B` has weight `w`.  Since
`r_o(C)=-1`, the prescribed-payoff atom is

```text
A_C(w)=1-w.
```

At the frozen source `A_C(lambda)=1-lambda`.  With eight terminal outcomes
including Never and charge `q=1`,

```text
q/2 <= 8*A_C(lambda).
```

The source and endpoint observer debts are zero: at the source `o` optimally
Continues for zero, while at the endpoint every action gives `-1`.

After conditioning,

```text
A_C(hatLambda)=1-hatLambda=(N-1)/(N^2+N-1),
8*A_C(hatLambda)<1/2       for N>=17.
```

Thus the fixed orientation `{a,m}` loses the charge-one atom; the atom moves
to `{m}`.  The claim that this is a literal instance of the project's local
vanishing-debt atom interface is a specific review obligation, not yet an
established fact.

## 5. Deleted-clock separation

Delete `m` from the packet root.  Since `o` Continues surely, the deleted-`m`
one-row survival is exactly `a`'s Continue probability:

```text
D_m_frozen=lambda,
D_m_conditioned=hatLambda.
```

Their distance is greater than `1/2`.  Any proposed common reprojected clock
`d` satisfies

```text
max(|d-lambda|,|d-hatLambda|)
  >= (hatLambda-lambda)/2 > 1/4.
```

Restarting the next packet at `lambda` preserves the semantic carrier but
discards temporal provenance; retaining the unfinished preceding stopping law
forces `hatLambda` and loses the frozen clock.  Hence no modulus depending only
on mesh and semantic-source tolerance can track both of these **preselected**
realizations.  This is a port non-identifiability regression, not a
counterexample to the existential local producer, uniform equilibrium, or the
positive-minimum frontier.

## 6. Sufficient conditional-port stability estimate

For one player's two component laws, let `S(s),T(s)` be their survivals from
packet entrance to suffix start `s`.  For entrance weight `w`, set

```text
M_s(w)=(1-w)*S(s)+w*T(s),
F_s(w)=w*T(s)/M_s(w).
```

For positive denominators and entrance weights `a,b`, direct cancellation
gives

```text
F_s(a)-F_s(b)
  = S(s)*T(s)*(a-b)/(M_s(a)*M_s(b)).                 (6.1)
```

For a finite packet of length `L`, define

```text
Omega_L(a,b)=max_(0<=s<=L) sum_i
  S_i(s)*T_i(s)*|a_i-b_i|/(M_i,s(a_i)*M_i,s(b_i)).  (6.2)
```

The proposal claims that for every suffix start and remaining finite length,
the frozen/reached joint survival and every one-player-deleted survival differ
by at most `Omega_L`.  The proof couples each player's component-mixture law
using (6.1), then telescopes finite products.

If every displayed mixed survival is at least `rho>0`,

```text
Omega_L(a,b) <= rho^(-2)*sum_i |a_i-b_i|.            (6.3)
```

If `a_i` is the posterior formed by conditioning prior `b_i` through a
preceding prefix with component survivals `S_i_pre,T_i_pre`, then

```text
|a_i-b_i|
 = b_i*(1-b_i)*|T_i_pre-S_i_pre|/M_i_pre(b_i).       (6.4)
```

With preceding survival floor `rho_0>0` and

```text
delta=max_i b_i*(1-b_i)*|T_i_pre-S_i_pre|,
```

one obtains

```text
Omega_L <= |I|*delta/(rho_0*rho^2).                  (6.5)
```

The denominator factors are claimed necessary; in the example
`rho_0` is comparable to `lambda`, so `delta/rho_0` stays order one.

## 7. Semantic and branch-label estimates

If all reward coordinates have absolute value at most `R`, the same coupling
is claimed to yield, at every packet suffix,

```text
||U^a-U^b||_infty <= 2*R*Omega_L,
||B^a-B^b||_infty <= 2*R*Omega_L,
||D^a-D^b||_infty <= 4*R*Omega_L.                   (7.1)
```

The best-response estimate requires uniform control for every fixed deviation
before taking the supremum.  Literal conditioned semantic tails then have zero
one-step prescribed/direct defects, while (7.1) compares them to frozen data.

For a frozen atom of charge `q`, outcome count `K`, and fixed terminal label,
the same label is claimed to remain valid at charge `q/2` if

```text
Omega_L <= q/(8*K*R).                                (7.2)
```

A literal argmax branch label additionally needs a positive gap `g`, for
example `4*R*Omega_L<g`; without a gap, argmax-label stability is false.

Successive packets compare to their frozen versions with vanishing tail error
when

```text
sum_n Omega_(L_n) < infinity.                        (7.3)
```

Conditioning itself is associative, so profile provenance is exact; (7.3) is
used for frozen-packet comparison.  Divergent absorption is separate.

## 8. Sufficient interface and remaining producer

One sufficient conditional interface is

```text
port-matched vanishing-debt atom access
  + summable posterior condition numbers Omega
  -> concatenable conditioned packets.
```

This is not claimed necessary or maximal.  A successful producer could instead
choose its preceding packet so the desired port is reached, carry complete
literal root/flux data recursively, or prove a frontier-specific realization
theorem producing another continuation with the desired semantics and clocks.

For retention of a fixed signed atom, an explicit strict margin is sufficient.
If

```text
A_S = r_i(S)*(mu(S)-nu(S)) >= gamma > 0,
|r_i(S)| <= M,
||muHat-mu||_1 <= xi,
||nuHat-nu||_1 <= xi,
```

then

```text
|Ahat_S-A_S| <= 2*M*xi,
Ahat_S >= gamma-2*M*xi.
```

Thus the same orientation survives when `2*M*xi<gamma`.  A branch label
defined by finitely many strict inequalities similarly survives under a port
perturbation smaller than its minimum strict margin divided by the relevant
Lipschitz constant.  Production of these closeness and margin hypotheses from
the actual positive-minimum frontier remains open.

The existing executable germ and diffuse-clock bridge retain literal profile
windows but do not visibly bound (6.2) or (6.5).  Exact-prefix stacks may make
some survival probabilities tend to one, but no all-suffix,
every-player-deleted denominator theorem is claimed here.

## Checks and open objections

1. Verify the complete stopping-law mixture and conditioning convention against
   the exact project definitions.
2. Verify that the source/endpoint data satisfy the literal local atom-access
   fields and that the outcome-count normalization is correct.
3. Check that `Omega_L` controls full terminal laws, not merely one-row survival,
   before accepting (7.1).
4. Check zero denominators, sure-Quit atoms, suffix indexing, deleted-player
   labels, and arbitrary finite packet length.
5. Determine whether a weaker existing port/provenance field already excludes
   the example.
6. Do not infer a negative result for the existential producer from this
   preselected-port non-identifiability regression.
