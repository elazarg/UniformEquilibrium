# Exact Transport of Completed Pure-Time Response Graphs

## 1. Setup

Let `I` be a finite player set and let `r_i(S)` be the terminal reward for a
nonempty quitting coalition `S`.  A behavioral profile has one live public
history at every date, so it may be represented by a sequence of product
roots

```text
x_t = (x_t,i)_(i in I),   t = 0,1,2,... .
```

Fix a profile `sigma` and player `i`.  For

```text
T = Nat union {infinity},
```

write `V_i^sigma(d)` for the terminal payoff obtained when player `i` quits
at the deterministic date `d`, with `d = infinity` meaning Never, against
the prescribed opponents `sigma_-i`.

The project has checked the two facts used below:

* every behavioral deviation payoff is the expectation of these pure-time
  values under its stopping law; and
* the unrestricted behavioral cap is their supremum.

The relevant declarations are listed in `OVERLAP_AND_SOURCES.md`.

Assume `|r_i(S)| <= M` for all `i,S`.

## 2. The completed response graph

Equip `T` with its one-point compact topology and define

```text
Gamma_i(sigma)
  = closure { (d, V_i^sigma(d)) : d in T }
```

inside the compact space `T x [-M,M]`.

This graph is nonempty and compact.  Its maximum height is exactly the full
behavioral cap:

```text
B_i(sigma) = max { y : exists d, (d,y) in Gamma_i(sigma) }.       (2.1)
```

Indeed, taking a closure does not change the supremum of the bounded second
coordinate, and compactness turns the supremum into a maximum.  Pure-time
extremality identifies this supremum with the unrestricted behavioral cap.

This makes the cap a continuous projection on the hyperspace of nonempty
compact subsets: the maximum-height functional is Lipschitz for the Hausdorff
metric induced by the product metric.

## 3. What lives over infinity

Let `lambda_j` be opponent `j`'s stopping law and let

```text
a_i = product_(j != i) lambda_j({infinity}).
```

For a fixed actual profile, bounded convergence gives the exact late-deadline
limit

```text
lim_(n -> infinity) V_i^sigma(n)
  = V_i^sigma(infinity) + a_i r_i({i}).                           (3.1)
```

For each realized opponent-clock vector, a sufficiently late finite deadline
either comes after the first finite opponent clock, reproducing Never's
payoff, or every opponent is Never, in which case the player obtains the solo
reward.  The simultaneous-at-`n` events vanish in the limit.

Thus an actual graph has at most two heights over infinity:

```text
the literal-Never value V_i(infinity),
the escaping-deadline value V_i(infinity) + a_i r_i({i}).
```

Limits of actual graphs can have a larger vertical fibre.  For example, let
one opponent quit uniformly on dates `1,...,N`, let

```text
r_i({i}) = 1,   r_i({opponent}) = r_i({i,opponent}) = 0.
```

For deadlines `t_N` with `t_N/N -> alpha`, the payoff tends to `1-alpha`.
The Hausdorff limit has the whole vertical interval `[0,1]` over infinity.
This interval records relative escape scales that pointwise finite-date
values and the literal Never value do not record.

## 4. Exact prefix law

Let `x` be a product root prefixed before `sigma`.  For player `i`, let

```text
p_-i(T) = probability that exactly the opponent coalition T quits at x,
m_i(x)  = p_-i(empty),

Q_i(x)  = sum_(T subset I\{i}) p_-i(T) r_i(T union {i}),
A_i(x)  = sum_(nonempty T subset I\{i}) p_-i(T) r_i(T).
```

Here `Q_i(x)` is the value of quitting immediately and `A_i(x)` is the
unconditional reward contribution when `i` Continues and some opponent quits
immediately.

The pure-time values satisfy

```text
V_i^(x*sigma)(0)       = Q_i(x),                                  (4.1)
V_i^(x*sigma)(d + 1)   = A_i(x) + m_i(x) V_i^sigma(d),             (4.2)
V_i^(x*sigma)(infinity)= A_i(x) + m_i(x) V_i^sigma(infinity).      (4.3)
```

Let `shift(infinity)=infinity` and `shift(d)=d+1` at finite dates.  The map

```text
Phi_(x,i)(d,y) = (shift(d), A_i(x) + m_i(x)y)
```

is continuous.  Equations (4.1)--(4.3), followed by taking closures, give

```text
Gamma_i(x*sigma)
  = {(0,Q_i(x))} union Phi_(x,i)(Gamma_i(sigma)).                  (4.4)
```

This is the exact continuation-game edge suggested by the motivating idea.
It transports finite deadlines, Never, and all escaping-scale fibres at
infinity in one formula.

Taking maximum heights in (4.4) gives

```text
B_i(x*sigma)
  = max(Q_i(x), A_i(x) + m_i(x) B_i(sigma)),                      (4.5)
```

which is precisely the cap coordinate of `quittingTerminalSemanticPrefix`.
Thus the response graph strictly refines the semantic cap while projecting
to the existing exact prefix map.

## 5. Prescribed payoff and terminal-law transport

Let `p_x(S)` be the root coalition mass and let `c(x)=p_x(empty)`.  If
`nu_sigma` is the law on nonempty terminal coalitions plus Never, then

```text
nu_(x*sigma)(S)     = p_x(S) + c(x) nu_sigma(S),   S nonempty,     (5.1)
nu_(x*sigma)(Never) = c(x) nu_sigma(Never).                        (5.2)
```

Consequently

```text
U_i(x*sigma)
  = sum_(nonempty S) p_x(S) r_i(S) + c(x) U_i(sigma).              (5.3)
```

All formulas are affine and continuous in the root and the stored compact
coordinates.

## 6. Positive-survival prefixing is reversible on the graph state

Suppose the root has positive joint all-Continue probability `c(x)>0`.  Then
every player's opponent-Continue mass `m_i(x)` is also positive.  The tail
state can be recovered from the current state and the known root.

For the response graph, delete its unique date-zero slice and apply

```text
(d+1,y) -> (d,(y-A_i(x))/m_i(x)),
infinity -> infinity.                                             (6.1)
```

Equation (4.4) says the result is exactly `Gamma_i(sigma)`.  For the terminal
law, equations (5.1)--(5.2) invert as

```text
nu_sigma(S)     = (nu_current(S)-p_x(S))/c(x),
nu_sigma(Never) = nu_current(Never)/c(x).                          (6.2)
```

If individual stopping laws are stored, player `i`'s tail law is likewise
obtained by deleting the current date-zero atom, shifting back, and dividing
by the root Continue probability.

Therefore positive-survival prefixing is an injective continuous map on the
joint response-graph carrier.  Since the carrier is compact Hausdorff, it is a
homeomorphism onto its image.

This is strictly stronger than the `(U,B)` prefix.  When immediate Quit
dominates, the maximum in the cap formula can hide the tail cap and make the
finite semantic prefix noninjective.  The full response graph retains the
dominated shifted menu and hence the exact second-day state.

## 7. A compact joint carrier

Let `H(T x [-M,M])` denote the hyperspace of nonempty compact subsets.  Map
every actual profile to

```text
State(sigma) =
  (nu_sigma, U_sigma, (Gamma_i(sigma))_(i in I)).                  (6.1)
```

Take the closure of this joint image, rather than the product of its separate
coordinate closures.  The resulting carrier is compact metrizable and every
boundary point has one common realizing sequence for all displayed
coordinates.

Equations (4.4) and (5.1)--(5.3) define a continuous prefix self-map of this
carrier and agree with literal profile prefixing on actual states.

One may add the vector of compact stopping laws to (6.1).  That preserves an
actual profile quotient and makes exact horizontal replacement computable on
actual points.  It does not make horizontal replacement continuous at the
boundary; see `HORIZONTAL_REPLACEMENT_NO_GO.md`.

## 8. Lean-facing mathematical package

A future formalization could separate four declarations:

```text
quittingPureTimeValue_tendsto_never_add_opponentNeverMass_mul_solo

quittingCompletedResponseGraph_cap_eq_maxHeight

quittingCompletedResponseGraph_prefix_eq_insert_affineShift

quittingResponseGraphState_prefix_continuous

quittingResponseGraphState_prefix_embedding_of_continueMass_pos
```

No Lean implementation is claimed here.
