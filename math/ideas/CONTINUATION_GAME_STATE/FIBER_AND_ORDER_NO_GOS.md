# Further No-Gos: Infinity Fibres and Replacement Order

## 1. Infinity fibres need not be intervals

The completed response graph can have a disconnected fibre over infinity.

Take two players, observer `i` and opponent `j`.  In profile number `N`, let
`j` quit surely at date `N`.  Give `i` the rewards

```text
r_i({i})   = 1,
r_i({i,j}) = 2,
r_i({j})   = 0.
```

Then the deterministic deadline values are

```text
V_i^N(t) = 1  for t < N,
V_i^N(N) = 2,
V_i^N(t) = 0  for t > N or t = infinity.
```

As `N -> infinity`, every one of the three selected dates

```text
N-1, N, N+1
```

converges to infinity in the compact stopping-time space, while their values
converge respectively to `1,2,0`.  The limiting graph has fibre containing
`{0,1,2}` over infinity.  In fact this example's fibre is exactly that set.

Therefore a boundary fibre cannot in general be encoded merely by an upper
and lower endpoint or by an interval.  The collision value at a moving atom
can survive as an isolated spike.

Together with the uniform-clock example in
`EXACT_RESPONSE_GRAPH_TRANSPORT.md`, this shows that fibres may contain both
continua and isolated coalition-labelled spikes.

## 2. Fixed-order replacement data are not renewable

Let `K_(J,d_J)` be the deterministic multi-response kernels from
`FULL_REPLACEMENT_KERNEL_ATLAS.md`.  If player `p` is replaced by a stopping
law `theta`, then for `p notin J`

```text
K'_(J,d_J)
  = sum_s theta(s) K_(J union {p},(d_J,s)).
```

Consequently, updating all kernels of order at most `q` requires old kernels
of order at most `q+1`.  A state retaining only unary kernels can perform one
horizontal update of prescribed semantics if pair kernels are supplied, but
cannot regenerate its pair-kernel passport without triple kernels.  The same
problem repeats at every order below the number of players.

Thus no truncation

```text
all replacement kernels with |J| <= q,   q < |I|,
```

is algebraically closed under arbitrary renewable horizontal replacements.
For Fin4, the complete subset atlas through order four is the first universal
finite-order closure.

This does not rule out pair-kernel sufficiency for a specially constrained
two-step consumer.  It rules out advertising pair kernels as a generally
renewable state without proving that the consumer never requests an updated
pair context.

## 3. The full strategic game is a constant state

At any live date, allow every player to replace their entire remaining
behavior.  A pure strategy is simply a stopping delay in
`Nat union {infinity}`.  The terminal reward depends only on the coalition
attaining the first finite delay.  Measured from the new live date, this game
is independent of calendar time and of the prescribed profile.

Therefore the genuinely full continuation game obeys

```text
Game_(t+1) = Game_t
```

after all Continue.  Its state graph consists of one self-loop.  The changing
object is necessarily profile-relative: it freezes some prescribed opponent
strategies while varying one player.  That is why a full-game state is too
coarse in one sense (it forgets the prescribed source) and too tautological in
another (it simply restates the original quitting game).

