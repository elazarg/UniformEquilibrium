# Two-clock renewal does not supply an aligned exact cross-share tail

Author: `CODEX_HAHN`

## Status

**Exact interface obstruction with an explicit rational regression; not
Lean-checked.**  The conditioned cross-share rigidity theorem needs the
two-clock law and exact Nash--Bellman roots on one profile.  A cap-clock
renewal supplies them on opposite sides of its horizontal seam: the original
prefix profile has exact roots, while the cap child has the two installed
sure clocks.  Installing the cap can destroy exactness of an outsider at the
very first retained root.

The regression below realizes this loss inside the exact move-to-front cycle
at global minimum debt zero.  It does not exclude a hard-residual theorem
repairing the seam, but proves that finite complete semantics alone cannot
provide the missing conditioned-tail adapter.

## Question

Can the two sure clocks accumulated by late-reset renewal instantiate the
checked two-clock conditioned cross-share contradiction?

## 1. The exact datum required by cross-share rigidity

For fixed distinct players `p,q`, one needs a **single** one-sided exact
Nash--Bellman tail `(v_t,x_t)` with all of the following properties:

1. `v_t` converges to a boundary `v_infinity` pinned by

   \[
   v_\infty(p)=r_p(\{p\}),\qquad
   v_\infty(q)=r_q(\{q\});
   \]

2. eventually only `p,q` have positive Quit hazards;
3. the eventual absorption probability `A_t` is positive and the conditioned
   mesh `(one-stage absorption)/A_t` tends to zero;
4. at cofinally many `p`-active dates, the future terminal law conditioned on
   absorption assigns at least one fixed `eta>0` to singleton `{q}`; and
5. symmetrically, at cofinally many `q`-active dates it assigns at least
   `eta` to singleton `{p}`.

Under those hypotheses, the conditioned active-support identity forces both
reciprocal normalized solo entries to vanish, contradicting a card-two Fin4
hard principal.

The word **single** is load-bearing.  Singleton `{p}` mass in one cap child
and singleton `{q}` mass in another source do not give the two aligned
conditional inequalities.

## 2. The renewal profiles have the wrong incidence

Write `tau^N` for a literal exact prefix profile before installing an attained
cap, and `zeta^N` for the horizontal child obtained by replacing the cap
owner's full strategy.

- The roots of `tau^N`, in reverse construction order, form an exact finite
  Nash--Bellman block.  The new owner clock has not been installed there.
- The child `zeta^N` contains the new owner clock and the retained old owner
  clock, so its complete unilateral semantics is finite.  But changing one
  player's full strategy changes the one-stage games seen by every outsider.
  Its retained roots are not asserted to remain exact Nash.

Thus neither profile supplies the joint input above.  Passing between them is
exactly the horizontal cap seam which the renewal/recharge ledger leaves
uncharged.

There is a second, independent alignment failure.  In the cap child the new
owner clock is strictly earlier than the retained old owner clock.  On the
event that the earlier prefix survives, the old owner's deterministic clock
is screened.  A positive singleton atom for the newest owner therefore does
not imply a positive singleton atom for the retained owner in the same
conditioned future law.  Earlier stochastic roots may create such mass, but
the two-clock theorem gives no lower bound for it.

## 3. Exact outsider-Nash regression

Use the rational reward table and profiles in
`CODEX_HAHN__MOVE_TO_FRONT_EXACT_PREFIX_CAP_CYCLE_REGRESSION`.
At its profile `B`,

\[
 U(B)=(1/2,1/2,0,0),
\]

and the root `qB`, at which player 2 Quits with probability `1/2` and every
other player Continues, is exact Nash against `U(B)`.  In particular, player
1's Continue and Quit endpoints are respectively

\[
 \tfrac58\quad\text{and}\quad\tfrac12.
\tag{1}
\]

Install player 0's shifted Quit0 cap through that root.  The resulting actual
child `A_0` has two sure clocks: player 0 at the first tail date and player 1
one date later.  Its literal continuation after `qB` now terminates at
singleton `{0}`, so player 1's Continue endpoint at the retained root becomes

\[
 \tfrac12 r_1(\{2\})+\tfrac12 r_1(\{0\})=\tfrac38,
\]

while its Quit endpoint is still `1/2`.  Therefore player 1 has a strict
one-stage gain `1/8` and the retained root is **not** Nash against the cap
child's literal continuation.

The original exact root and the two-clock law are both literal, but they
cannot be combined into one exact tail.  This is precisely the missing
interface, not a compactness or cap-attainment issue.

The same child also shows why cross-share does not follow just from two
clocks.  Its prescribed terminal law is

\[
 \tfrac12\delta_{\{2\}}+\tfrac12\delta_{\{0\}}.
\]

The retained player-1 clock is always screened by the earlier player-0 clock
after survival of the stochastic root, so singleton `{1}` has zero mass.

## 4. Strongest surviving route

To use conditioned cross-share rigidity, a new source theorem must do more
than retain two clocks.  It must output either:

1. one exact Nash--Bellman tail after the cap installation, with both aligned
   cross-singleton shares bounded below; or
2. a charged exact repair path from the non-Nash cap child back to such a
   tail, preserving the two singleton shares and the boundary pins.

Replacing every nonexact retained root by a newly selected exact root does
not prove either conclusion: it changes the continuation law and can erase
one of the cross shares.  Sending the resulting positive atom through the
generic Fin4 entrance merely returns to the existing forced-pair/off-minimum
paid-port component and gives no smaller rank.

## Source correspondence and nonclaims

The conditional cross-share theorem is
`GATE_STRENGTHENER__TWO_CLOCK_CROSS_SHARE_RIGIDITY`.  The finite semantic
adapter is
`CODEX_HAHN__TWO_RENEWED_SURE_CLOCKS_GIVE_FINITE_COMPLETE_SEMANTICS`.
The renewal and horizontal-recharge sources are
`CODEX_HAHN__LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE` and
`CODEX_HAHN__RENEWED_OWNER_CYCLE_CAPACITY_RECHARGE_LEDGER`.

This note does not show that the aligned cross-share adapter is impossible
under positive global minimum debt.  It does not produce a counterexample,
an exact infinite tail, a chronological return, or a uniform-equilibrium
payoff.

## Next exact question

Can the positive-minimum cap collar control the outsider Nash loss across the
horizontal installation strongly enough to repair the retained roots while
preserving both conditioned singleton shares on the same literal tail?
