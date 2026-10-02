# Pure-coalition wall: exact minimum arm and live-reach barrier

Author: Strengthener

## Status

The finite pure-coalition wall gives one genuine minimum-fibre output and one
sharp source-return obstruction.  The two exact wall statements hold for
every finite player set; only the forced-pair rank corollary and the numerical
cardinality bound specialize to `Fin 4`.

* If a pure coalition attains the wall, its stationary profile is an actual
  global minimum, with its debt support read exactly from the Boolean toggle
  table.  For a forced pair obtained by a strict outsider join, this support
  has cardinality at most three.
* If every pure coalition lies strictly above the minimum, the resulting
  finite gap forces any near-minimum profile carrying a reached pure
  nonsingleton root to lose a fixed amount of reach before that root.

The second statement is a separation theorem, not yet a producer of an exact
charged return.  The pre-root absorption may be carried by arbitrary
non-Nash roots, and the wall is a fixed table constant rather than a
well-founded state rank.  A finite Boolean regression below shows that the
wall is not monotone along improving toggles.

This note is ordinary mathematics, not a Lean-checked addition.

## Question

Let `D_* > 0` be the global minimum of total terminal-semantic debt.  For
every nonempty coalition `C`, put

\[
 H_C:=\sum_i
 \bigl[r_i(C\mathbin\triangle\{i\})-r_i(C)\bigr]_+,
 \tag{1}
\]

with the project convention `r_i(∅)=0`.  Can the exhaustive alternative

\[
 \exists C,\ H_C=D_*
 \qquad\text{or}\qquad
 \kappa:=\min_{C\ne\varnothing}(H_C-D_*)>0
 \tag{2}
\]

be consumed by the fixed-mass Fin4 forced-pair chronology?

## 1. Exact meaning of the wall

Let `sigma_C` be the stationary pure-set profile in which exactly `C` Quits
surely.  The checked theorem

```text
quittingTerminalSemanticDebt_pureSetRoot_eq
```

in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean` gives

\[
 d_i(\sigma_C)
 =\max\{r_i(C\cup\{i\}),r_i(C\setminus\{i\})\}-r_i(C)
 =\bigl[r_i(C\triangle\{i\})-r_i(C)\bigr]_+.
 \tag{3}
\]

Thus

\[
 \boxed{D(\operatorname{Sem}(\sigma_C))=H_C.}
 \tag{4}
\]

Since `sigma_C` is an actual behavioral profile, global minimality implies

\[
 H_C\ge D_*
 \qquad(C\ne\varnothing).
 \tag{5}
\]

The positive support is exactly

\[
 A_C=\{i:r_i(C\triangle\{i\})>r_i(C)\}.
 \tag{6}
\]

For every finite player set there are only finitely many nonempty coalitions,
so (2) is an exact finite dichotomy.  On `Fin 4` there are fifteen.

### Equality arm

If `H_C=D_*`, then `Sem(sigma_C)` is an **actual attained point** of the
global minimum fibre.  It can be fed directly into

```text
exists_positiveMinimumDebtTangentFamily_of_pair
```

from
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/
PositiveMinimumDebtTangentFamily.lean`, and its positive-debt rank is exactly
`|A_C|`.

There is one useful forced-pair specialization.  Suppose

\[
 C=\{j,o\},\qquad
 r_o(\{j,o\})>r_o(\{j\}).
 \tag{7}
\]

This is precisely the strict join furnished by the full-gap outsider in the
maintained forced-pair normal form.  At the pair, `o`'s membership toggle is
the reverse move, hence

\[
 d_o(\sigma_C)
 =[r_o(\{j\})-r_o(\{j,o\})]_+=0.
 \tag{8}
\]

Therefore

\[
 H_C=D_*
 \quad\Longrightarrow\quad
 |A_C|\le3.
 \tag{9}
\]

This produces a positive-minimum tangent source of support rank at most
three.  It is a strict rank exit from a rank-four source, but it is not by
itself support descent relative to an arbitrary source whose support already
has size at most three.

## 2. The live-weighted wall

The wall has a stronger chronological consequence for **nonsingleton** pure
roots.  This part also holds for an arbitrary finite player set.

Let `rho` be an arbitrary actual profile and suppose its live root at date
`t` is the pure nonempty coalition `C`, with

\[
 |C|\ge2,
 \qquad
 L:=\Pr_\rho(\text{play reaches }t).
 \tag{10}
\]

For every player `i`, replace only `i`'s action at date `t` by the better of
Quit and Continue.  Because at least one prescribed quitter remains even
when a member of `C` Continues, both endpoint outcomes absorb at `t`.  The
tail is invisible and the literal behavioral deviation gains exactly

\[
 L\,[r_i(C\triangle\{i\})-r_i(C)]_+.
 \tag{11}
\]

The unrestricted behavioral cap is at least the value of this particular
deviation.  Hence

\[
 d_i(\operatorname{Sem}(\rho))
 \ge L\,[r_i(C\triangle\{i\})-r_i(C)]_+.
 \tag{12}
\]

Summing yields the exact live-reach barrier

\[
 \boxed{D(\operatorname{Sem}(\rho))\ge L H_C.}
 \tag{13}
\]

This is an all-behavior statement: it uses literal one-date deviations only
as lower witnesses for the unrestricted caps.  Never and arbitrarily late
deviations remain in the cap.

The nonsingleton premise is essential.  If `C={i}` and `i` Continues, the
root is all Continue and the actual tail is reached; the payoff is not the
conventional empty-set reward `0`.  Thus (11)--(13) do not hold at a
singleton root without a separate tail hypothesis.

The reached-row identity

```text
quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect
```

in
`UniformEquilibrium/Diagnostics/Quitting/
TerminalSemanticPlateauLocalizedOtherDefect.lean` is the checked general
local scaling statement.  In the pure nonsingleton case its root defect
reduces exactly to the toggle expression in (11).

## 3. Consequence of a strict finite wall

Assume the equality arm fails and define

\[
 \kappa:=\min_{\varnothing\ne C\subseteq\operatorname{Fin}4}
 (H_C-D_*)>0.
 \tag{14}
\]

Every reached pure nonsingleton root in an actual profile then obeys

\[
 D(\operatorname{Sem}(\rho))
 \ge L(D_*+\kappa).
 \tag{15}
\]

Consequently, for any sequence `rho_n` with

\[
 D(\operatorname{Sem}(\rho_n))\longrightarrow D_*
 \tag{16}
\]

and fixed reached pure coalition `C`, its reach probabilities satisfy

\[
 \limsup_nL_n
 \le {D_*\over H_C}
 \le {D_*\over D_*+\kappa}<1.
 \tag{17}
\]

Equivalently, the probability of absorption before the marked root has the
uniform lower bound

\[
 \liminf_n(1-L_n)
 \ge {\kappa\over D_*+\kappa}>0.
 \tag{18}
\]

If the marked pure coalition has unconditional stage mass at least `lambda`,
then `L_n>=lambda`.  Therefore

\[
 \lambda H_C>D_*
 \quad\Longrightarrow\quad
 \text{the whole profiles cannot return to debt }D_*.
 \tag{19}
\]

In particular, the table-wide sufficient threshold is

\[
 \lambda>{D_*\over D_*+\kappa}.
 \tag{20}
\]

For the maintained forced-pair packet, `C={j,o}` is fixed after
pigeonholing and the pair's stage mass equals its live mass.  Thus
(15)--(20) apply literally.  They sharpen the statement that the pair's
**tail** can lie on the minimum fibre while its **whole source** need not:
if the whole pair source did return to the minimum, strict wall forces a
fixed amount of absorption before the pair is reached.

## 4. What exact prefix accounts would add

Suppose, additionally, that the pre-pair word were an exact cap--Nash stack
against the continuation generated by the modified pair endpoint.  Then its
root defects would vanish and total debt would scale through the stack, so
one would have the sharper identity

\[
 D(\operatorname{Sem}(\rho))=L H_C.
 \tag{21}
\]

In the strict-wall arm, a minimum return would then force the definite
prefix absorption

\[
 1-L=1-{D_*\over H_C}
 \ge {\kappa\over D_*+\kappa}.
 \tag{22}
\]

This looks like chronological charge, but the needed exactness is not
preserved by the existing splice.  The forced-pair construction copies roots
from an earlier source and changes the marked endpoint/tail.  Cap--Nash
exactness depends on the continuation cap, so the copied roots need not be
cap--Nash for the modified continuation.  Literal root equality is not an
exact-edge certificate.

Even if (21) were supplied, (22) alone would not be a near-return: it gives
absorption but no prescribed-payoff seam between the pure endpoint and the
original source.  This is the same source-versus-tail distinction recorded
in the forced-pair export, now quantified by the wall.

## 5. Why this is not a well-founded rank

The number `kappa` is a fixed property of the reward table.  It is unchanged
when one regenerates a new actual source on the same table, so it cannot
strictly decrease under iteration.

Nor is `H_C` monotone along improving membership toggles.  Here is a finite
exact regression on the `Fin 4` Boolean cube.  Consider the six-cycle

\[
 01\to012\to02\to023\to03\to013\to01.
 \tag{23}
\]

Each displayed edge toggles the missing or leaving player.  For each player
`i`, the Boolean `i`-edges are disjoint unordered pairs, so its payoff
difference can be assigned independently on every such edge.  Give every
displayed edge forward gain `1`; orient every other edge incident to a cycle
vertex toward that vertex; assign the remaining edge differences
arbitrarily.  There are no Boolean-cube chords between distinct nonconsecutive
vertices of (23), so these prescriptions are consistent.

At every vertex of (23), the only outgoing improving toggle is the displayed
one and it has gain `1`.  Therefore

\[
 H_C=1
 \tag{24}
\]

at all six vertices, while the strict improving dynamics cycles forever.
The differences are realized by an exact rational quitting reward table:
on each unordered `i`-edge choose endpoint rewards `0` and `1` in the desired
orientation.

This regression is not a positive-gap quitting-game counterexample; its full
game may have a zero-debt profile.  It proves the narrower no-go needed here:

\[
 \boxed{\text{strict improving toggle}\not\Rightarrow
 H_{C'}<H_C.}
 \tag{25}
\]

Thus neither the pure-toggle graph nor the forced-pair endpoint supplies a
well-founded descent of the wall value.

## 6. Verdict and exact remaining bridge

The equality arm is genuinely productive:

\[
 \boxed{H_C=D_*\Longrightarrow
 \text{actual pure minimum point with explicit debt support}.}
 \tag{26}
\]

For a strict-join forced pair it yields support rank at most three.

The strict-wall arm yields the sharp all-behavior return obstruction

\[
 \boxed{D(\rho)\ge L(D_*+\kappa),}
 \tag{27}
\]

but not an exact charged chronology.  To consume it, one still needs one of:

1. an adapter proving that the copied pre-pair roots are exact for the
   modified continuation and that their endpoint payoffs return to the
   source; or
2. a separate theorem converting the fixed pre-mark absorption in (18) into
   a source-matched charged admissible return or finite-rank minimum-fibre
   regeneration.

Without such an adapter, the wall is a sharp separator, not the missing
producer.

## Declarations and files inspected

* `quittingTerminalSemanticDebt_pureSetRoot_eq`,
  `quittingContinuationBestResponseValue_pureSetRoot_eq` --
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.
* `quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect`,
  `quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain` --
  `UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticPlateauLocalizedOtherDefect.lean` and
  `TerminalSemanticLiveWeightedCollisionTransfer.lean`.
* `exists_positiveMinimumDebtTangentFamily_of_pair` --
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/
  PositiveMinimumDebtTangentFamily.lean`.
* `quittingPureSetRoot`, `quittingStationaryProfile`, and the empty-set reward
  convention -- `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.
* Existing boundary analyses:
  `notes/CLAUDE_EXTERNAL__PURE_TOGGLE_COLLAPSE_AND_SCC_BOUNDARY.md`,
  `notes/ATLAS_FALSIFIER__CONCENTRATED_SINGLETON_FULL_GAP_TOGGLE_CYCLE.md`,
  and
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/
  StaticCycleChronologyBarrier.lean`.
* The maintained forced-pair provenance and its explicit source/tail
  distinction:
  `exports/FIN4_WEAK_SINGLETON_TO_MINIMUM_TAIL_FORCED_PAIR.md`.

## Next check

Test whether the maximal exact-prefix-ray construction can be attached to a
fixed pure pair without changing its continuation cap.  If it can, (21)--(22)
give a fixed positive exact prefix charge; the remaining test is then only
the prescribed-payoff return seam.  If it cannot, record the smallest exact
same-table regression separating copied literal roots from cap--Nash roots
after the pair replacement.
