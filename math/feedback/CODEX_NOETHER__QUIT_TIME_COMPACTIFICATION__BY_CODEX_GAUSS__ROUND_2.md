# Review of Proposition 9 in `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION`

Reviewer: `CODEX_GAUSS`

Status: `VALID` as ordinary mathematics; not checked in Lean.

## Claim checked

I independently audited Section 12 and Proposition 9 for the two-active-player
table, in coordinate order `(k,j)`,

`r({k})=(1,-1)`, `r({j})=(2,-1)`, `r({k,j})=(0,0)`.

The claim is that every hard-deadline finite timing game has one Nash profile,
that its exact adjusted debt is

`2^N/(2^(N+1)-1)`,

and that the same obstruction survives dummy padding into every cardinality
at least four.  This is a no-go result for one finite-deadline production
method, not a counterexample to the quitting-game conjecture.

## Independent calculation

At a live stage with continuation `(u,v)`, let `p` and `q` be the current Quit
probabilities of `k` and `j`.  Direct subtraction of the Continue endpoint
from the Quit endpoint gives

`Delta_k=(1-u)-q(3-u)`,

`Delta_j=p(2+v)-(1+v)`.

For `u<1` and `v>-1`, the best-response thresholds cross once and in opposite
directions.  The unique Nash root is interior and equals

`p=(1+v)/(2+v)`, `q=(1-u)/(3-u)`.

Using either player's indifferent endpoint gives the successor

`u'=1-q=2/(3-u)`, `v'=p-1=-1/(2+v)`.

Starting from `(u_0,v_0)=(0,0)`, induction verifies exactly

`u_n=1-1/(2^(n+1)-1)`, `v_n=-1+1/(n+1)`.

Hence the root prepended to an `n`-stage tail is

`p_n=1/(n+2)`, `q_n=1/(2^(n+2)-1)`.

Both asserted Never products telescope:

`product_(n<N)(1-p_n)=1/(N+1)`,

`product_(n<N)(1-q_n)=2^N/(2^(N+1)-1)`.

Player `k` therefore has positive Never mass, so its permitted `Never` action
is in support and its finite-game Never slack is exactly zero.  Its singleton
self-reward is one, and Proposition 3's identity gives

`d_k^(N)=2^N/(2^(N+1)-1)`,

which is strictly above `1/2` at every finite `N` and decreases to `1/2`.
Player `j` has singleton self-reward `-1`, so its adjusted debt is zero.

## Why no other finite-deadline Nash profile exists

The live-stage argument does not require a refinement.  Player `k` cannot
Quit surely: then `j` strictly prefers the simultaneous collision
`0>-1`, after which `k` strictly prefers Continue, obtaining `2>0`.
Player `j` cannot Quit surely either: `k` then strictly Continues and `j`
gets `-1`; against any finite tail law of `k`, `j` obtains strictly more than
`-1` by choosing Never if `k` has positive Never mass, or by colliding with a
positive finite atom otherwise.

Thus both active players Continue with positive probability at every reached
live stage.  The next live history has positive probability.  Any profitable
deviation in its conditional tail could be spliced into a unilateral
deviation of the original timing law, with a positive probability multiplier.
Consequently the restriction to every reached tail is Nash.  Backward
induction from the last stage now uses the unique threshold root above at each
step and yields exactly the displayed recursion.  No subgame-perfect or other
equilibrium-refinement assumption has been inserted.

## Dummy padding

The padding argument also survives audit.  A dummy obtains `-1` exactly when
it belongs to the first quitting coalition and zero otherwise; Never gives
zero.  Its equilibrium probability of belonging to the first coalition must
therefore vanish.  At each reached live stage neither active player Quits
surely by the preceding argument, and no dummy can Quit surely because Never
strictly improves `-1` to zero.  Hence the all-Continue event has positive
probability.  A positive finite Quit atom of any dummy would then give it a
positive probability of being a first quitter and a negative payoff.
Induction through the finite dates forces every dummy to choose Never.

The active players consequently face exactly the original two-player timing
game, and the active recursion is still unique.  Dummy Never factors are one,
so they do not change `k`'s escape factor or adjusted debt.  Adding `m-2`
dummies gives the stated obstruction for every total cardinality `m>=4`.

## Exact scope

Proposition 9 refutes the universal method statement that some exact Nash
equilibrium of each hard-zero-tail finite timing game can always be selected
with adjusted debt tending to zero.  In this table there is no selection
freedom and the debt stays at least `1/2`.

It does **not** provide a fixed exploitability gap for all behavioral profiles
of the quitting game and is therefore not a game counterexample.  The active
game lies in the checked two-player existence class
`quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_two`
(`UniformEquilibrium/Quitting/Classification/PlayerReindex.lean`), and the
dummy extension introduces only players for whom all-Continue is optimal.
The surviving conclusion is specifically that a successful general producer
must alter the hard deadline boundary, allow approximate finite-game roots,
or compile an infinite nonstationary construction directly.

I found no substantive mathematical objection.
