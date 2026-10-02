# A fixed cap-to-solo pin forces coordinatewise debt expenditure at every exact root

Author: `CODEX_HAHN`

## Status

**Complete ordinary mathematics; not Lean-checked and not a renewable
consumer.**  The theorem below strengthens the exact-root debt drop at the
structured tropical paid source.  It is dimension-independent, decreases the
fixed paid coordinate itself, and needs neither positive global minimum debt
nor a separately supplied root-absorption floor.

This does not consume the paid-port component.  After one exact prefix, the
same cap-to-solo pin need not persist, so the coordinate decrease cannot yet be
iterated.

## Exact theorem

Let `I` be finite and let

\[
  X=(u,B)
\]

be a terminal semantic pair for a bounded quitting reward table.  Fix a player
`b`, write

\[
  s_b=r_b(\{b\}),\qquad d_b=B_b-u_b,
\]

and suppose, for constants \(M,\gamma>0\), that

\[
  |r_i(S)|\le M,\qquad |u_i|\le M,
\tag{1}
\]

for every player and nonempty terminal coalition, and

\[
  d_b\ge\gamma,
  \qquad |B_b-s_b|\le\frac{\gamma}{4}.
\tag{2}
\]

Let `q` be any exact independent product Nash root of the one-stage quitting
game whose all-Continue payoff is `u`.  Prefix `q` to `X` using the complete
behavioral cap in the second semantic coordinate.  Then

\[
 d_b(X)-d_b(\operatorname{Prefix}(q,X))
 \ge
 \delta_b,
 \qquad
 \delta_b:=\min\left\{\frac{\gamma}{2},
                       \frac{\gamma^2}{16M}\right\}>0.
\tag{3}
\]

Consequently the total semantic debt also drops by at least \(\delta_b\)
whenever all input debts are nonnegative.

The statement is pointwise in `X`: no compact carrier, global minimizer,
terminal exploitability witness, or asymptotic sequence occurs in the theorem.

## Proof

Let

\[
  c_b(q)=\prod_{j\ne b}(1-q_j)
\]

be the probability that all opponents of `b` Continue, and put

\[
  \alpha=1-c_b(q).
\tag{4}
\]

Thus \(\alpha\) is the probability that at least one opponent Quits in the
current row.

For an opponents' quitting coalition \(S\subseteq I\setminus\{b\}\), define

\[
 f(S)=
 \begin{cases}
   s_b-u_b,&S=\varnothing,\\
   r_b(S\cup\{b\})-r_b(S),&S\ne\varnothing.
 \end{cases}
\tag{5}
\]

If \(\pi_q\) is the opponents' product law, player `b`'s Quit-minus-Continue
endpoint gap is exactly

\[
  e=Q_b(q_{-b})-C_b(q_{-b};u_b)
   =\sum_S\pi_q(S)f(S).
\tag{6}
\]

The cap pin and positive debt give

\[
 s_b-u_b=(s_b-B_b)+d_b\ge\frac{3\gamma}{4}.
\tag{7}
\]

Every value in (5) has absolute value at most \(2M\).  Since the total mass of
the nonempty opponent coalitions is \(\alpha\), comparison with the point mass
at the empty coalition gives

\[
 |e-(s_b-u_b)|
 \le 4M\alpha.
\tag{8}
\]

There are two cases.

### Macroscopic opponent absorption

Suppose

\[
 \alpha\ge\frac{\gamma}{16M}.
\tag{9}
\]

For an exact root, the exact coordinate debt action is

\[
 d_b(\operatorname{Prefix}(q,X))
 =\left[c_b(q)d_b-[e]_+\right]_+
 \le c_b(q)d_b.
\tag{10}
\]

Therefore

\[
 d_b-d_b(\operatorname{Prefix}(q,X))
 \ge \alpha d_b
 \ge\frac{\gamma^2}{16M}.
\tag{11}
\]

### Small opponent absorption

Suppose instead

\[
 \alpha<\frac{\gamma}{16M}.
\tag{12}
\]

Equations (7)--(8) imply

\[
 e>\frac{\gamma}{2}>0.
\tag{13}
\]

Quit is therefore strictly better than Continue for `b` at the one-stage
root.  Exact Nash complementarity forces

\[
 q_b=1.
\tag{14}
\]

Using the exact debt action again,

\[
\begin{aligned}
 d_b-d_b(\operatorname{Prefix}(q,X))
 &=d_b-[c_b(q)d_b-e]_+\\
 &\ge\min\{d_b,e\}\\
 &\ge\frac{\gamma}{2}.
\end{aligned}
\tag{15}
\]

Equations (11) and (15) prove (3).  Since exact prefixing weakly decreases
every nonnegative semantic-debt coordinate, the same lower bound applies to
the total debt drop.

## Sequential form

Let \(X_n=(u_n,B_n)\) be any bounded sequence of terminal semantic pairs with
one fixed label `b` and

\[
 d_b(X_n)\ge\gamma,
 \qquad B_{n,b}\longrightarrow s_b.
\tag{16}
\]

For all sufficiently large `n`, (2) holds.  Thus the same \(\delta_b>0\)
works for every sufficiently late `n` and **every** exact product root against
`u_n`.  There is no diagonal selection and no separate absorption hypothesis.

## Adapter to the tropical stationary source

The reviewed packet
`FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md` supplies actual stationary
last-edge sources \(\tau_n\), a fixed final mover `b`, and a fixed
\(\gamma>0\) such that literal Quit at date zero attains `b`'s complete
behavioral cap with gain at least \(\gamma\).  Hence

\[
 d_b(\operatorname{Sem}(\tau_n))\ge\gamma.
\tag{17}
\]

Every semantic cluster has `b`-cap equal to \(s_b\).  Compactness upgrades
this to convergence of the scalar cap sequence:

\[
 B_b(\operatorname{Sem}(\tau_n))\longrightarrow s_b.
\tag{18}
\]

Apply the sequential theorem.  Every exact one-stage root against the literal
source payoff spends the same fixed amount of `b`'s complete behavioral debt.
The proof does not use the source stationary hazards, the number four, the
positive global minimum, or the separately proved uniform exact-root
absorption floor.

This strictly strengthens the conclusion of
`FIN4_STRUCTURED_PAID_SOURCE_EXACT_ROOT_DEBT_DROP.md`.  In particular, that
packet's positive-global-minimum boundary discussion is not sharp: positive
global minimum is unnecessary for its debt-drop conclusion once the fixed
cap pin and fixed debt are retained.

## Why the result is not renewable

For an actual source \(\tau_n\) and an exact root `q`, the child

\[
  q\mathbin{::}\tau_n
\]

is literal and its complete terminal-semantic debt has fallen by at least
\(\delta_b\).  But its new `b`-cap is

\[
 \max\{Q_b(q_{-b}),C_b(q_{-b};B_{n,b})\},
\tag{19}
\]

which need not approach \(s_b\).  The child is generally nonstationary, and
the inherited inner Quit-now response need not attain its new whole-profile
cap.  Therefore the hypothesis of the theorem need not hold again at the
child.

If the root's joint Continue mass has a positive lower bound, the old paid
inner row survives with fixed positive reached gain.  If that joint reach
vanishes, compactness produces a sole-quitter reset or a tail-screened
terminal limit.  Both alternatives retain literal ancestry, but neither
reconstructs the same cap-pinned stationary source.  The missing consumer is
still source re-entry or a different well-founded rank.

## Boundary tests

1. **No cap pin.**  Let \(s_b=0\), \(u_b=1\), and \(B_b=2\).  The debt is
   one, but the all-Continue root is exact in coordinate `b` and transports
   that debt without loss.  A fixed debt alone does not force expenditure.

2. **No fixed debt.**  With \(B_b\to s_b\) but \(d_b\to0\), the all-Continue
   endpoint gap and every possible coordinate drop may tend to zero.  The
   scale \(\gamma>0\) is essential.

3. **Approximate roots.**  The strict-gap case no longer forces \(q_b=1\)
   exactly for an approximate root.  A quantitative approximate extension is
   plausible but is not claimed here.

4. **Correlated recommendations.**  The proof applies to ordinary independent
   mixed-strategy roots.  It also applies verbatim to an exogenous opponents'
   coalition law independent of `b`'s action.  It does not cover a correlated
   recommendation that changes the information available to `b` or permits a
   deviation conditioned on a private signal.

5. **No renewal from one decrease.**  Even a fixed coordinate drop does not
   provide a natural-valued rank unless the cap pin is regenerated at the
   child.  Reusing the original source would turn distinct exact predecessors
   into siblings, not one temporal chain.

## Lean-facing boundary

The exact debt action is already checked as
`quittingTerminalSemanticDebt_prefix_eq_blockAct` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.  Exact root
complementarity and the root endpoint definitions are in the finite Bellman
and root-Nash files used by that theorem.  A formal version needs only:

1. the finite-sum estimate (8) for the opponents' root law;
2. the two scalar cases (9) and (12); and
3. the coordinate consequence of the checked block action.

A suitable static theorem is:

```text
fixedDebtor_capNearSingleton_exactRoot_coordinateDebtDrop_ge
```

with conclusion on one named coordinate.  The sequence and tropical-source
statements should be separate corollaries.  No global carrier-minimum field or
Fin4 type should occur in the static theorem.

## Exact remaining question

Can an actual exact-prefix child carrying this fixed coordinate drop and the
literal inherited paid suffix be regenerated with either the same cap pin or
a strict finite rank?  Without such a theorem, the stronger local expenditure
still stops at the quantitative paid-port waist.
