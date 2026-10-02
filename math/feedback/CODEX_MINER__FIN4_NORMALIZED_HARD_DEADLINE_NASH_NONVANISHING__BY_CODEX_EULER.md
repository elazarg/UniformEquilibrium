# Review of `CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING`

Reviewer: `CODEX_EULER`

## Verdict

**PASS.**  I independently re-derived the finite-deadline Nash recursion, the
Never masses, the unrestricted late-time debt, and the diffuse non-Nash
comparison.  The note gives a valid normalized rational Fin4 no-go for the
proposal “add finitely many hard dates, select an exact timing-game Nash, and
let the deadline grow.”  It is not a quitting-game counterexample, and the
note states that boundary correctly.

The result is compatible with the separate sharp two-date theorem in
[`CODEX_EULER__TWO_DATE_NASH_UNRESTRICTED_DEBT_HALF_BOUND.md`](../notes/CODEX_EULER__TWO_DATE_NASH_UNRESTRICTED_DEBT_HALF_BOUND.md):
at `N=2` the present regression has debt `2/7<1/2`.  The two-date theorem is a
strict finite-step improvement; this regression proves that exact
hard-tail Nashification is not a recursive vanishing-error scheme.

## 1. Table and dummy elimination

The table is complete and normalized.  For a dummy `d`, Never gives zero
against every opponents' timing profile, whereas every finite quit action
gives `-1` on the event that `d` belongs to the first quitting coalition and
never improves elsewhere.  In particular finite actions are strictly
dominated at any reached current date, so both dummies are Never throughout
every timing-game equilibrium.

For the active pair, if `k` quits surely at a current date, `j` strictly
prefers to collide (`0` rather than `-1`), after which `k` strictly prefers to
Continue (`1` rather than `0`).  If `j` quits surely, `k` uniquely Continues.
Then `j` can improve over `-1`: Never is strict if `k` has positive Never
mass, while colliding with any positive finite atom of `k` is strict if that
Never mass is zero.  Hence both current hazards are strictly below one.
The current all-Continue history consequently has positive reach, and any
profitable deviation in its conditional tail splices into a profitable
deviation of the whole timing game.  This validates the ordinary-Nash
backward induction; no subgame-perfect hypothesis is being smuggled in.

## 2. Exact recursion

With active continuation payoff `(u,v)`, direct subtraction gives

\[
 \Delta_k=(1/2-u)-q(3/2-u),\qquad
 \Delta_j=p(2+v)-(1+v).
\]

On `u<1/2`, `v>-1`, the unique local Nash root is interior and equals

\[
 p={1+v\over2+v},\qquad q={1/2-u\over3/2-u}.
\]

Indifference then gives

\[
 u'={1\over3-2u},\qquad v'={-1\over2+v}.
\]

Starting from `(0,0)`, substitution verifies

\[
 u_n={1\over2}\left(1-{1\over2^{n+1}-1}\right),
 \qquad v_n=-1+{1\over n+1},
\]

and therefore `p_n=1/(n+2)`, `q_n=1/(2^(n+2)-1)`.  Both invariant strict
ranges persist.  The products telescope exactly:

\[
 a_k^{(N)}={1\over N+1},\qquad
 a_j^{(N)}={2^N\over2^{N+1}-1}.
\]

This also confirms uniqueness of the full finite timing-game Nash, including
equilibrium selection.

## 3. Unrestricted debt

The finite timing Nash controls every supported deadline action and Never.
All pure quit times after the finite support have one common value.  Relative
to Never, that value adds exactly the singleton reward on the event that all
opponents selected Never.  Pure-time extremality therefore gives the full
behavioral cap, rather than only a bounded-controller cap.

Player `k` uses Never with positive mass, so its finite-game Never slack is
zero.  Since `s_k=1/2` and the dummies are surely Never,

\[
 d_k={1\over2}a_j^{(N)}
 ={2^{N-1}\over2^{N+1}-1}>{1\over4}.
\]

Player `j` and the dummies have singleton reward `-1`, so their after-support
action cannot improve on Never and their debts are zero.  The displayed
quantity is thus the exact total exploitability, not merely a lower bound.

## 4. Diffuse comparison

In the comparison profile, `j` quits surely at date zero, `k` conditionally
uses the uniform clock on `{1,...,L}`, and both dummies Never.  The prescribed
payoff is `(1,-1,0,0)`.  Player `k` and the dummies cannot improve.  If `j`
refuses, every pure time yields `-1` except for its single collision atom with
`k`, which changes the payoff to zero.  The exact best gain is therefore
`1/L`; times after the support and Never both give `-1`.  Pure-time
extremality again covers arbitrary behavioral deviations.  Hence `eta(r)=0`
is proved and the table is correctly excluded from counterexample status.

## 5. Scope and disposition

This is a substantive architecture no-go: it eliminates exact Nash selection
in growing hard-zero-tail timing games as a complete approximation method,
even though the actual finite-clock class remains expressive enough on the
same table.  A narrow export is mathematically justified after the ordinary
packet gate, provided it retains:

- the exact normalized Fin4 table;
- uniqueness at every deadline;
- the explicit `eta(r)=0` comparison; and
- the nonclaim about soft tails, approximate timing roots, and deliberately
  non-Nash finite-clock profiles.

No mathematical repair is required.
