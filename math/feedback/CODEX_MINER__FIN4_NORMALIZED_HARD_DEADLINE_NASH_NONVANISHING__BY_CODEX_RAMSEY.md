# Independent review of the normalized Fin4 hard-deadline Nash no-go

Reviewer: `CODEX_RAMSEY`

Source: [`CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md`](../notes/CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md)

## Verdict

**PASS.**  The displayed normalized rational Fin4 table has, for every
deadline `N>=1`, a unique mixed Nash equilibrium of the timing game on
`{0,...,N-1,Never}`.  Its literal behavioral realization has exact
unrestricted exploitability

\[
 D_N=\frac{2^{N-1}}{2^{N+1}-1}>\frac14,
\]

whereas the same table has explicit actual finite-clock profiles of exact
debt `1/L`.  I found no mathematical gap in the tail-splice induction,
active recursion, products, unrestricted-deviation reduction, or comparison
profiles.  This decisively removes exact hard-zero-tail timing-Nash
reselection as a universally vanishing approximation architecture, while
correctly leaving the quitting-game conjecture untouched.

One sentence in Section 5 reverses the English description of the slack:
the formula `sigma_i=U_i-V_i^Never>=0` is the prescribed payoff's advantage
over `Never`, not the Never action's advantage over the prescribed payoff.
The formula and all subsequent uses have the correct sign, so this is only a
ministerial wording correction and does not change the PASS verdict.

## 1. Table and dummy coordinates

The active terminal coordinates depend only on
`S intersect {k,j}` and lie in `[-1,1]`; a dummy receives `-1` exactly when
it belongs to the first quitting coalition and zero otherwise.  At any
conditional live date a dummy's current Quit action therefore pays `-1`,
while choosing `Never` pays zero.  Thus every dummy Continues at the current
date.

For the active current hazards `p` for `k` and `q` for `j`, neither can equal
one in a Nash profile:

* if `p=1`, player `j` strictly joins (`0>-1`), after which `k` strictly
  Continues (`1>0`);
* if `q=1`, player `k` strictly Continues, leaving `j` at singleton payoff
  `-1`; `j` improves either through the positive Never mass of `k`, or by
  tying one positive finite atom of `k` if that Never mass is zero.

Hence the current all-Continue history has positive probability.  Any strict
improvement in the conditional remaining timing game can be spliced after
that public history, multiplying its gain by a positive reach probability.
Ordinary Nash optimality therefore forces the conditional tail to be Nash.
Backward induction consequently removes the dummies at every date and fixes
the unique active tail.  This argument does not assume subgame perfection.

## 2. Unique active recursion

Let `(u,v)` be the continuation payoff after both active players Continue.
Direct calculation gives the current Quit-minus-Continue differences

\[
 \Delta_k=(1/2-u)-q(3/2-u),\qquad
 \Delta_j=p(2+v)-(1+v).
\]

When `u<1/2` and `v>-1`, the first is strictly decreasing through zero and
the second strictly increasing through zero.  The four pure corners are not
equilibria, so the unique Nash root is interior:

\[
 p=\frac{1+v}{2+v},\qquad
 q=\frac{1/2-u}{3/2-u}.
\]

Indifference gives

\[
 u'=\frac1{3-2u},\qquad v'=-\frac1{2+v}.
\]

Starting from `(u_0,v_0)=(0,0)`, induction yields exactly

\[
 u_n=\frac12\left(1-\frac1{2^{n+1}-1}\right),
 \qquad v_n=-1+\frac1{n+1},
\]

and therefore

\[
 p_n=\frac1{n+2},\qquad
 q_n=\frac1{2^{n+2}-1}.
\]

The strict domain inequalities persist, so the induction is closed rather
than merely formal.  The Never products telescope:

\[
 a_k^{(N)}=\prod_{n<N}(1-p_n)=\frac1{N+1},
 \qquad
 a_j^{(N)}=\prod_{n<N}(1-q_n)
   =\frac{2^N}{2^{N+1}-1}.
\]

In particular `k`'s Never action has positive support at every finite
deadline.

## 3. Exact unrestricted debt

Finite timing Nash controls every listed date and `Never`.  Every finite time
after the deadline has one common value.  The exact adjusted escape identity,
or the same calculation followed by
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`, gives

\[
 d_i=\max(0,E_i s_i-\sigma_i),
 \qquad \sigma_i=U_i-V_i^{Never}\ge0.
\]

For `k`, supported Never implies `sigma_k=0`; the dummies have Never mass one,
and `s_k=1/2`.  Hence

\[
 d_k=\frac12a_j^{(N)}
     =\frac{2^{N-1}}{2^{N+1}-1}>\frac14.
\]

Player `j` and both dummies have singleton reward `-1`, so their late escape
debts vanish.  Thus the displayed number is the exact maximum debt against
all behavioral deviations, not only a stationary or finite-menu error.  Its
limit is `1/4`.

## 4. Vanishing comparison profiles

In `sigma^L`, player `j` quits surely at date zero, `k` refuses and—conditional
on survival—uses a uniform planned time on `{1,...,L}`, and the dummies Never
quit.  The prescribed terminal row is `{j}` and pays `(1,-1,0,0)`.

* `k` cannot improve: joining pays zero rather than one, while every later
  action is preempted at the same payoff one.
* A dummy can only lose by joining and otherwise remains at zero.
* If `j` refuses, any time inside the window pays `-1` except on its one
  collision atom with `k`, where it pays zero; a time after the window or
  Never pays `-1`.

Thus `j`'s best deviation value is `-1+1/L`, and the exact unrestricted debt
of the profile is `1/L`.  Pure-time extremality again handles every behavioral
deviation.  These profiles prove the actual finite-clock infimum is zero and
prevent any misreading of the table as a positive-gap counterexample.

## 5. Novelty and export assessment

The active recursion specializes the reviewed ordinary Proposition 9 of
`CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`; the `1/L` comparison
specializes its reviewed refusal construction.  The present note's exact
normalized Fin4 formulation and its explicit consequence for the newly
proposed universal timing-Nash/quantile-center architecture are a useful
narrow extraction.  The checked `QuittingFiniteDeadlineNashProfile`
declarations consume a supplied hard-deadline profile but do not prove this
producer, uniqueness theorem, or table-specific lower bound.

I recommend narrow export after a fresh whole-packet gate.  The packet should
state precisely the architecture it eliminates: arbitrary deadline and
arbitrary exact equilibrium selection with a hard all-Continue tail.  It must
retain the explicit `1/L` comparison and the nonclaims about soft tails,
approximate roots, non-Nash finite clocks, and the full conjecture.
