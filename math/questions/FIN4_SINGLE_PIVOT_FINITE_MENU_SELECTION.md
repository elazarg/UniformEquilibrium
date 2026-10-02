# Select finite stopping laws with vanishing unrestricted exploitability

## Game and strategies

There are four players, numbered 0, 1, 2, 3. At each date, every player
independently chooses Continue or Quit. The first date with a nonempty
quitting coalition S ends the game and pays the fixed real vector r(S).
Infinite all-Continue pays zero. A player may use any behavioral strategy;
before termination the only public history is a sequence of all-Continue
outcomes. Equivalently, each player independently samples a stopping time
in the nonnegative integers together with Never.

Assume the own-singleton rewards are

    r_0({0}) = 1,
    r_i({i}) = 0 for i = 1, 2, 3.

All other reward entries are arbitrary real numbers. Fix a finite bound M
on their absolute values. No sign or symmetry restriction is imposed on
those entries, and the selected independent strategies need not be stationary.

## Finite-menu data

For an integer N at least one, let the allowed stopping times be

    F_N = {0, 1, ..., N-1, Never}.

Let p be an independent product of four probability laws on F_N. Write
U_i(p) for player i's prescribed expected terminal payoff. Write B_i^N(p)
for its largest expected payoff when it alone replaces its law by another
law on F_N. Define

    E_N(p) = max_i [B_i^N(p) - U_i(p)].

For player 0, also define

    W_0(p) = its payoff from Never against the other three laws,
    D_0(p) = p_1(Never) p_2(Never) p_3(Never),
    L_0(p) = W_0(p) + D_0(p) - U_0(p).

Every deterministic stopping date at or after N gives player 0 exactly
W_0(p) + D_0(p). For each other player such a date gives the same payoff
as Never. Thus the maximum unrestricted deviation gain of p equals

    max(E_N(p), L_0(p)).

This identity is only a verification of a supplied product law. The question
is to select the law itself.

## Question

For every such reward table and every positive error epsilon, construct
an integer N at least one and an independent product law p on F_N such that

    E_N(p) <= epsilon,
    L_0(p) <= epsilon.

The deadline and the four laws may depend on epsilon. They need not be
nested across errors. Exact finite-menu Nash is not required. No bound on
unrestricted regret is supplied as a hypothesis.

A complete negative answer is an explicit four-player table satisfying the
displayed assumptions and a fixed positive gain that is achievable by some
unilateral behavioral deviation against every behavioral profile, including
profiles with unbounded or randomized stopping times.

## Scope of a complete answer

The positive answer must control the same selected product law in both
inequalities. Finite-game Nash existence alone supplies no bound on L_0.
Joint absorption with probability one does not force D_0 to vanish. Making
player 0 quit at a new deadline may make other players' deviations profitable.
Increasing the menu can likewise change its incentive constraints.

A bound on L_0 for one externally supplied family is not a selection
theorem. Failure for every exact finite-menu Nash selector is not a negative
answer unless approximate selectors and all complete behavioral profiles
are also excluded.
