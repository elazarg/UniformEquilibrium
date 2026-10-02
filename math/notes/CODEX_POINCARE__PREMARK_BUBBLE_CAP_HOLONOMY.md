# Pre-mark bubble and cap holonomy in the strict normalized ray

Author: `CODEX_POINCARE`

## Status

Completed boundary analysis.  The exact common-prefix formulas, maximal-ray
bubble normal form, and pre-mark response split below are proved in ordinary
mathematics.  They sharpen the location of the remaining obstruction, but
they do **not** produce a terminal approximation, an admissible return, a
renewable rank descent, or a positive-gap table.  Accordingly this note is
not export-ready under the breakthrough-only question.

The main negative check is also precise: the hard residual's
`no_homogeneous` field cannot by itself force the maximal exact ray to become
eventually all Continue.  The tangent equation at a weak all-Continue cap
contains collision-membership coefficients, while the checked hard matrix is
the solo matrix.  A payoff-period or relative-error closure hypothesis is
needed before the existing homogeneous obstruction applies.

## Question

Work in Arm B of
`questions/FIN4_RENEWABLE_ORIENTATION_OR_COUNTEREXAMPLE.md`.  A finite word
of literal pre-mark roots carries a fixed pure pair at its terminal marked
date.  The word and pair have a positive survival/mass passport and a positive
same-stage endpoint gain.  The post-mark tail is on the minimum fibre but is
screened by the pure pair.

Can the historical paid endpoint be commuted through the pre-mark word to
produce an executable return or a well-founded source transition?

## Sources inspected

The bounded source set was:

- `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`
  in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`;
- the exact cap-prefix scaling and maximal ray summarized in
  `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean` and
  `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`;
- `exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff`
  and `sum_error_ge_of_successorPath_exists_not_mem_linearBasin`;
- `ResidualHardClass.no_homogeneous` and `normalizedSoloMatrix` in the LCP
  gate; and
- the reviewed returned-block theorem recorded in
  `formalized/RETURNED_BLOCK_HOMOGENEOUS_TANGENT_OBSTRUCTION.md`.

No paper theorem is used.

## 1. A finite common prefix acts coordinatewise on the cap

Fix a finite word `W` of product roots and a terminal-semantic tail

\[
 z=(u,b).
\]

Let

\[
 s(W)=\Pr_W(\hbox{all players Continue through the word})
\]

and, for player `i`, let

\[
 h_i(W)=\Pr_W(\hbox{all opponents of }i\hbox{ Continue through the word}).
\]

There are table/word-dependent scalars `A_i`, `K_i`, and `P_i` such that

\[
 U_i(W*z)=P_i+s(W)u_i,                                      \tag{1}
\]

and

\[
 \boxed{B_i(W*z)=\max\{K_i,A_i+h_i(W)b_i\}.}               \tag{2}
\]

Here `K_i` is the best payoff from a pure quitting time inside the word.
The second branch is the payoff from continuing through the word and then
using a full behavioral best response in the tail.  Formula (2) quantifies
over every behavioral deviation: before absorption the public history is a
deterministic all-Continue string, so the pure-time extremality theorem
reduces the finite prefix to the finitely many in-word deadlines plus the
pass-through tail option.

Consequently, for two tails `z=(u,b)` and `z'=(u',b')`,

\[
 U_i(W*z')-U_i(W*z)=s(W)(u_i'-u_i),                         \tag{3}
\]

while

\[
 B_i(W*z')-B_i(W*z)
 =\max\{K_i,A_i+h_i b_i'\}-\max\{K_i,A_i+h_i b_i\}.        \tag{4}

In particular the cap difference has the sign of `b_i'-b_i` and magnitude
at most `h_i|b_i'-b_i|`.

This is the exact prefix-horizontal commutator.  It has only one cap kink;
there is no hidden multidimensional dependence on the other tail-cap
coordinates.

## 2. Pure-pair siblings and exact mover debt subtraction

Let `C` be a nonsingleton pure coalition at the marked terminal row, and let
`C'=C triangle {p}` be player `p`'s better Boolean endpoint.  Write `Z_C` and
`Z_C'` for the tail-independent semantic pairs of the two pure rows.  Since
only `p`'s prescribed complete strategy changes,

\[
 (Z_C)_p^B=(Z_{C'})_p^B.                                  \tag{5}
\]

Applying (3)--(4) therefore gives

\[
 B_p(W*Z_{C'})=B_p(W*Z_C),                                \tag{6}
\]

and

\[
 d_p(W*Z_{C'})-d_p(W*Z_C)
 =-s(W)\bigl(r_p(C')-r_p(C)\bigr).                        \tag{7}

Thus the historical paid edge remains exactly executable before the remote
mark, with its full common-prefix survival factor.

For a spectator `j`, a positive debt recharge has the exact split

\[
 \Delta d_j=
 \underbrace{\Delta\max\{K_j,A_j+h_jb_j\}}_{\text{cap pass-through}}
 -s(W)\underbrace{(r_j(C')-r_j(C))}_{\text{prescribed atom}}.\tag{8}

If `Delta d_j >= c>0`, then either the prescribed marked-coalition term in
(8) has magnitude at least `c/2`, or the cap term is at least `c/2`.  In the
second case the maximizing target response is necessarily the pass-through
branch in (2).  It Continues through the whole pre-mark word and reaches the
tail comparison with opponent-survival weight satisfying

\[
 h_j(W)|b_j'-b_j|\ge c/2.                                \tag{9}

For reward bound `M`, `h_j(W)>=c/(4M)`.  Thus a cap-recharge observer cannot
hide its response strictly before the remote mark.  This adds an exact
positive-unilateral-reach field to the usual endpoint-rise atom decoder.

It still does not make the response an exact Nash--Bellman edge.  At the pure
pair the response is another horizontal endpoint update.

## 3. Root-defect holonomy through an exact source word

Suppose every root of `W` is exact cap--Nash for the source boundary `Z_C`.
Let `c_t` be its joint Continue masses and `S_t` their prefix products.  Put
`alpha=s(W)`.  Use the same literal word over `Z_C'`, and let `R_t(C')` be
the total cap-root defect at row `t` against the actual `C'`-suffix cap.
Repeated use of the arbitrary-root debt identity gives

\[
 \boxed{
 D(W*Z_{C'})-D(W*Z_C)
 =\sum_{t<|W|}S_tR_t(C')
   +\alpha\bigl(D(Z_{C'})-D(Z_C)\bigr).}                 \tag{10}

Every term `R_t(C')` is nonnegative.  Hence, whenever the boundary toggle
strictly lowers total pure-coalition debt but normalized-slice minimality
prevents a whole-debt decrease, (10) places a fixed amount of actual root
defect **before** the mark:

\[
 \sum_tS_tR_t(C')
 \ge \alpha\bigl(D(Z_C)-D(Z_{C'})\bigr).                \tag{11}

This is the strongest automatic placement statement found here.  The placed
work consists of genuine reached one-row behavioral gains, but the roots are
not exact and (11) alone is not an admissible return.

## 4. Exact remote-bubble normal form of the maximal ray

Start from the pure pair and recursively prefix maximal-absorption exact cap
roots:

\[
 P^k=q_{k-1}*\cdots*q_0*Z_C.
\]

Write `alpha_k=prod_{h<k}c_h`.  Exact cap-prefix scaling gives, coordinate by
coordinate,

\[
 \boxed{d(P^k)=\alpha_k d(Z_C),\qquad
 D(P^k)=\alpha_kH_C,}                                   \tag{12}

where `H_C=D(Z_C)`.  Positive global minimality implies

\[
 \alpha_k\ge D_*/H_C,
\]

so `alpha_k` converges to some `alpha>0`.

In the strict ray stall the maximal absorptions tend to zero, hence
`q_k -> allContinue`.  The chronological order in `P^k` is reversed:
the root at fixed date `t` is `q_{k-1-t}`.  Therefore every fixed calendar
root tends to all Continue.  Deleting the remote terminal bubble gives
literally the all-Never behavioral profile, whose semantic pair is

\[
 z_N=\bigl(0,(\max\{0,r_i(\{i\})\})_i\bigr).             \tag{13}

The carrier limit `x_bar` of `P^k` has

\[
 \boxed{d(x_{\rm bar})=\alpha d(Z_C),\qquad
 D(x_{\rm bar})=L=\alpha H_C.}                          \tag{14}

Its outcome law is a bubble law at infinity and retains `C`-mass at least
`alpha`.  If `u_bar,b_bar` are its semantic coordinates, the exact scalar
jump to the actual all-Never point is

\[
 \boxed{
 D(z_N)-L
 =\sum_i u_{{\rm bar},i}
  -\sum_i\bigl(b_{{\rm bar},i}-\max\{0,r_i(\{i\})\}\bigr).} \tag{15}

The first sum is the bubble's social reward moment; the second is the full
escaping cap jump.  Neither sign is automatic.

The hard-residual minimum-fibre singleton separation shows that `z_N` itself
cannot lie on the `D_*` fibre: if its prescribed payoff zero were a minimum
payoff, every own singleton reward would be uniformly negative, making
`D(z_N)=0`, contrary to `D_*>0`.  Thus bubble deletion produces another
off-minimum actual point, not an immediate minimum source.

## 5. Why `no_homogeneous` does not terminate the ray

A tempting argument is that infinitely many nonzero exact roots
`q_k -> allContinue` normalize to a forbidden homogeneous simplex solution.
The zeroth-order statement is valid: if

\[
 q_{k,i}/\sum_jq_{k,j}\to\lambda_i>0,
\]

then exact mixing forces

\[
 b_{{\rm bar},i}=r_i(\{i\}).                            \tag{16}

But the first-order raw Quit--Continue equation at such a weak cap uses

\[
 r_i(\{i,j\})-r_i(\{j\}),                              \tag{17}

the influence of `i` joining `j`.  The hard residual's checked matrix is

\[
 M_{ij}=r_i(\{j\})-r_i(\{i\}).                         \tag{18}

Moreover the cap is moving along the ray.  Its first-order displacement is
an inhomogeneous term in the root complementarity equations.  The reviewed
returned-block theorem eliminates this term only after payoff-period closure
or a Bellman residual which is little-oh of total hazard.  A ray with finite
total hazard supplies neither condition.

Therefore `ResidualHardClass.no_homogeneous` does not imply that the ray is
eventually exactly all Continue.  A separate collision-tangent exclusion or
returned-payoff closure would be needed.

## 6. Scalar placement boundary

Equations (8)--(11) answer the placement question as far as scalar Bellman
algebra can answer it:

* spectator recharge is either an executable prescribed atom at the remote
  mark or a cap response which traverses the entire pre-mark word with fixed
  unilateral reach;
* if a boundary endpoint lowers pure-coalition total debt, the exact source
  word develops a fixed positive amount of pre-mark root defect under that
  endpoint; and
* the strict infinite ray is a pure bubble over the actual all-Never point,
  with debt and the paid passport retaining exactly the same survival factor.

What is not proved is the required orientation of the placed root defects.
They may be spread over an unbounded word, and replacing the relevant player
at one row changes the cap data seen by earlier rows.  Nor does (15) have a
forced sign.  Thus this note does not yet satisfy the breakthrough-only
question.

The next falsifiable target is stronger than another atom decoder:

> Starting from the exact source word in (10), show that a fixed positive
> weighted sum of target-side pre-mark defects either admits sequential
> exactification with a payoff-near-return, or forces one endpoint boundary
> with strictly smaller canonical maximal-ray limit debt.

The second output would be a finite-coalition descent if strict at every
revisit; the first would enter the checked cumulative-return consumer.

## 7. Why a positive pre-mark cap defect is not yet a local repair

There is one important correction to the tempting ``Continue versus Quit''
dispatch for a positive term in (11).  The quantity `R_t(C')` is a root
defect against the **cap** of the successor.  If its better endpoint is
Continue, the endpoint means

\[
 \hbox{Continue at row }t\quad\hbox{and then use a tail best response}.
 \tag{19}
\]

It does not mean Continue at `t` and then resume the prescribed target
profile.  Thus a one-row Continue override which preserves the marked pair is
controlled by the prescribed-payoff endpoint difference, whereas (11) may be
carried entirely by inherited successor debt.  Replacing the player by (19)
can change all of that player's later actions and can stop before the marked
date.  This is precisely the cap-to-prescribed chronology gap, rather than a
sign ambiguity.

Tracing the best response to its first pure-time disagreement gives a clean
exhaustive split.  Since pure times (including Never) attain the cap supremum
up to arbitrary error, the response either:

1. Quits at a pre-mark date.  This produces an actual paid
   first-disagreement row and an absorbing sibling before the passport mark;
   or
2. Continues to the pure nonsingleton marked coalition.  Then the response at
   the mark is a Boolean endpoint action, the modified strategy deletes the
   player's pre-mark hazards, and the routed marked-coalition mass is no less
   than the source marked mass.

The second statement is exact.  If `P=W*C`, `|C|>=2`, and the pass-through
branch realizes `B_j(P)`, replace `j` by Continue throughout `W` followed by
its better Boolean endpoint at `C`.  Opponents are unchanged, so `j`'s cap is
unchanged; its prescribed payoff becomes that cap and therefore

\[
 d_j(P[j\leftarrow\hbox{pass-through best response}])=0. \tag{20}
\]

The new marked coalition is `C` or `C triangle {j}`, remains nonempty, and
its unconditional marked mass is at least the old one because only `j`'s
pre-mark stopping hazards have been removed.

This does not close the problem.  In the first arm the paid profile may enter
the already known inert paid-port stall.  In the second arm other players'
caps may recharge; repeating full best responses is better-response dynamics
in a finite timing game and need not decrease a potential.  A finite set of
players whose pre-mark hazards have been deleted is not a renewable rank,
because a later opponent update can make a deleted player's cap and debt rise
again.  Therefore (19)--(20) give a source-faithful no-loss placement split,
but not by themselves a return or rank consumer.

## 8. Final verdict and next check

The prefix-horizontal commutator does yield more than the earlier screening
diagnosis:

\[
 \boxed{
 \text{positive target-side pre-mark cap work}
 \Longrightarrow
 \begin{cases}
 \text{an actual pre-mark paid first-disagreement profile},\\
 \text{or a no-loss reaches-mark best response with own debt zero.}
 \end{cases}}
 \tag{21}
\]

The second arm retains a positive unilateral reach and the normalized marked
mass.  The first retains actual chronology but not that passport.  The exact
unresolved operation is to prevent cross-coordinate cap recharge from
alternating between these two arms indefinitely.

One concrete next test is therefore:

> Along successive no-loss reaches-mark replacements, does normalized-slice
> minimality force either a pre-mark paid response whose cap lift has positive
> charge, or a repeated semantic/law state?  A positive answer must retain the
> actual prescribed profiles and show that the repeated state carries
> consistently oriented prescribed-payoff charge; finite label recurrence
> alone is insufficient.

Without that additional orientation, treating deleted pre-mark hazards as a
rank would be invalid because opponent changes can reactivate their owners'
unrestricted debts.
