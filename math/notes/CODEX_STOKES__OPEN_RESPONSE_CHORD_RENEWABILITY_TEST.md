# Open minimum response chord: renewability test

Author: `CODEX_STOKES`

## Status

No terminal consumer, renewable rank, or contradiction is proved here.

The full open response chord has one stronger consequence not recorded in the
export: along the actual endpoint/mixed-profile triples, every player's
unrestricted cap has a common approximate maximizing sequence at the two
endpoints.  If one actual interior triple has exact cap affinity and its cap
is attained, the same behavioral deviation is an exact best response at both
actual endpoints.

This still does not orient the regenerated sources.  A fixed pure
nonsingleton row followed by a fixed outer word erases the entire chord
parameter from the whole semantic pair.  The current rerun construction does
not supply a continuous or source-anchored map from the chord back into itself.
Thus an intermediate-value or extremal argument cannot be applied at the
present interface.

The remaining concrete test is whether the common approximate cap witnesses
can be compactified into either one actual common best response or a
source-matched temporal-escape packet which crosses the pure-row seam.

## Question

Starting from
`exports/FIN4_MINIMUM_RESPONSE_CHORD_ACTUAL_LAW_REGENERATION.md`, can the
continuum of exact-law minimum sources force a renewable source transition, a
fixed semantic/law return with oriented charge, or an off-minimum
contradiction when the forced-pair construction is rerun across the mixture
parameter?

Any positive answer must retain the actual source and law.  Another static
atom, chord, or support handoff is not a solution.

## Sources inspected

The bounded source set was:

- `exports/FIN4_MINIMUM_RESPONSE_CHORD_ACTUAL_LAW_REGENERATION.md`;
- `questions/FIN4_RENEWABLE_ORIENTATION_OR_COUNTEREXAMPLE.md`;
- `quittingTerminalOutcomeMass_stoppingLawMixture_eq`,
  `quittingTerminalPayoff_stoppingLawMixture_eq`, and
  `quittingTerminalSemanticDebt_stoppingLawMixture_le` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`;
- `quittingTerminalSemanticDebt_stoppingLawMixture_eq_of_minimum_sameDebtSum`
  in `TerminalSemanticStoppingLawMinimumFiberAffine.lean`;
- `quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`
  in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`; and
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- the finite max-affine fence in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCommonWitnessPassportRegression.lean`;
  and
- `QuittingVanishingDebtAtomAccess` and
  `VanishingDebtAtomChronologicalConsumer` in
  `UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`.

## 1. Setting

Let `Y_n` and `Z_n` be actual endpoint and response profiles which differ
only in observer `j`'s complete behavioral strategy.  Let

\[
 H_{n,\theta}
 \]

be their literal stopping-law mixture, with weight `theta` on `Z_n`.  Along a
common subsequence suppose

\[
 \operatorname{Sem}(Y_n)\to Y,qquad
 \operatorname{Sem}(Z_n)\to Z,
\]

and

\[
 D(Y)=D(Z)=D_*.
\]

For every fixed `0<theta<1`, the response-chord theorem gives a minimum point
`H_theta`, after the common further subsequence on which

\[
 \operatorname{Sem}(H_{n,\theta})\to H_\theta,
\]

with

\[
 d_i(H_\theta)=(1-\theta)d_i(Y)+\theta d_i(Z).
\tag{1}
\]

Prescribed payoff is also affine, so

\[
 U_i(H_\theta)=(1-\theta)U_i(Y)+\theta U_i(Z).
\tag{2}
\]

Equations (1)--(2) imply cap affinity:

\[
 \boxed{
 B_i(H_\theta)=(1-\theta)B_i(Y)+\theta B_i(Z).}
\tag{3}
\]

This is stronger than coordinate debt affinity viewed in isolation.

## 2. Common approximate cap witnesses

This statement must be made on the actual realizing profiles, not by applying
a deviation to the possibly unattained carrier points `Y` and `Z`.

Fix a player `i` and `0<theta<1`.  Put

\[
 G_{n,i,\theta}
 :=(1-\theta)B_i(Y_n)+\theta B_i(Z_n)-B_i(H_{n,\theta}).
\tag{4}
\]

Cap convexity under a one-player stopping-law mixture gives

\[
 G_{n,i,\theta}\ge0.
\tag{5}
\]

Convergence of the three semantic pairs, together with the limiting cap
affinity (3), gives

\[
 G_{n,i,\theta}\longrightarrow0.
\tag{6}
\]

Choose any `epsilon_n -> 0`, and for each `n` choose one actual behavioral
deviation `eta_(n,i)` whose payoff against `H_(n,theta)` is within
`epsilon_n` of its unrestricted cap.  Then the same deviation is
simultaneously asymptotically optimal against both actual endpoint profiles:

\[
 B_i(Y_n)-U_i(Y_n[i\leftarrow\eta_{n,i}])
 \le \frac{G_{n,i,\theta}+\epsilon_n}{1-\theta},
\tag{7}
\]

and

\[
 B_i(Z_n)-U_i(Z_n[i\leftarrow\eta_{n,i}])
 \le \frac{G_{n,i,\theta}+\epsilon_n}{\theta}.
\tag{8}
\]

Both right sides tend to zero.  By behavioral pure-time extremality, the
common approximate witnesses may in addition be chosen among pure finite
quitting dates and Never, up to another vanishing error.

### Proof for `i != j`

Since only opponent `j` is mixed, the payoff of the fixed deviation is
affine:

\[
 U_i(H_{n,\theta}[i\leftarrow\eta_{n,i}])
 =(1-\theta)U_i(Y_n[i\leftarrow\eta_{n,i}])
  +\theta U_i(Z_n[i\leftarrow\eta_{n,i}]).
\tag{9}
\]

Subtract (9) from the weighted endpoint caps.  The result is

\[
\begin{aligned}
 &(1-\theta)
   \bigl(B_i(Y_n)-U_i(Y_n[i\leftarrow\eta_{n,i}])\bigr)\\
 &\quad+\theta
   \bigl(B_i(Z_n)-U_i(Z_n[i\leftarrow\eta_{n,i}])\bigr)
 \le G_{n,i,\theta}+\epsilon_n.
\end{aligned}
\tag{10}
\]

Both deficits are nonnegative by the definition of cap.  Bounding each
weighted summand separately proves (7)--(8).

### The moved observer `i=j`

The opponents of `j` are identical at `Y_n`, `Z_n`, and every mixture.
Updating `j` by `eta_(n,j)` overwrites the prescribed strategy which
distinguishes the profiles.  Hence both the cap and the payoff of the fixed
deviation are identical at all three actual profiles, and any approximate
best response is already common, with no `G` loss.

## 3. Exact attainment at an actual affine triple

The limiting carrier points need not be attained by profiles, so cap
attainment cannot be asserted directly at `H_theta`.  The exact finite-level
statement is nevertheless useful.  Suppose that for some actual triple
`Y_n,Z_n,H_(n,theta)` one has

\[
G_{n,i,\theta}=0,
\]

and player `i`'s cap at `H_(n,theta)` is attained by a behavioral strategy
`eta_i`.  Then (10) has right side zero.  Both endpoint deficits are
nonnegative and both weights are positive, so each deficit is zero.  Thus

\[
 \boxed{\eta_i\text{ is an exact best response at }Y_n,H_{n,\theta},Z_n.}
\tag{11}
\]

Thus the asymptotic obstruction has two precise pieces: the finite cap-affinity
gap `G_(n,i,theta)` may only tend to zero rather than vanish, and the
behavioral cap may fail to be attained because maximizing pure stopping times
escape to infinity.  There is no remaining cross-coordinate convexity loss.

This observation is not yet a consumer.  It localizes the remaining cap
nonlocality to temporal escape and finite-level affinity, rather than
cross-coordinate convexity.

### Simultaneous witnesses do not form a timing equilibrium

The construction above can be performed for every player at once, using one
common interior parameter.  This gives, for each `i`, one pure time which is
simultaneously nearly optimal against `Y_n` and `Z_n`.  It does **not** say
that the profile obtained by applying all four responses is approximately
Nash.  Each inequality fixes the other three prescribed strategies; after a
second player is replaced, the first inequality no longer applies.  The
uncontrolled terms are precisely the multi-player response cross-effects.

This failure is already visible in one pure terminal row.  Let players `0`
and `3` Quit surely, and let players `1,2` have matching-pennies membership
payoffs on every coalition containing `{0,3}`:

\[
 r_1(S)=\mathbf 1_{(1\in S)\leftrightarrow(2\in S)},\qquad
 r_2(S)=\mathbf 1_{(1\in S)\not\leftrightarrow(2\in S)},
\]

with players `0,3` indifferent.  At the row `{0,3}`, exact best endpoints
can be chosen simultaneously: player `1` Continues and player `2` Quits.
After applying both choices the row is `{0,2,3}`, where player `1` strictly
prefers to Quit.  Repeating exact endpoint updates follows the ordinary
matching-pennies cycle.  The finite membership game has a mixed equilibrium,
but selecting it anew does not preserve the source law, marked atom, or
response chord.

The same example may be placed before arbitrary tails, because the two sure
quitters screen those tails from the complete terminal semantics.  It is not
a positive-gap counterexample.  It proves only the exact interface no-go:

\[
 \boxed{
 \text{one common supporting cap witness per player}
 \not\Longrightarrow
 \text{their simultaneous or sequential replacement is a Nash chronology}.}
\]

Thus the common witnesses strengthen the cap bookkeeping but do not enlarge
the executable response square.  For one selected spectator, the witness
represents its cap change by the same pure-time payoff difference at both
endpoints; a positive debt rise then feeds exactly the existing
common-response atom decoder.  Without a cross-player sign or potential, the
simultaneous family gives no additional chronological conclusion beyond
applying that decoder coordinate by coordinate.

## 4. Why the chord topology is erased by the current rerun

Let `C` be a pure coalition with `|C|>=2`, let `W` be one finite outer word,
and let `tau_theta` be any family of tails, including the actual-law sources
regenerated along the response chord.  Pure nonsingleton screening gives

\[
 \operatorname{Sem}\bigl(W*(\operatorname{pure}C)*\tau_\theta\bigr)
 \quad\text{independent of }\theta.
\tag{12}

Thus a rerun which chooses the same marked coalition and the same outer word
does not define a nonconstant continuous self-map of the chord.  It is a
constant semantic map.  Allowing the word or labels to vary does not repair
this automatically: the present producer selects them existentially and
supplies no continuity, monotonicity, closed-graph selection, or image-in-chord
property.

Consequently neither the intermediate value theorem nor a fixed-point theorem
has the hypotheses needed at the current interface.

This is more than a generic warning.  It explains why the continuum of source
laws can coexist with one unchanged paid whole-source geometry: the law
parameter lives strictly behind a sure-exit screen.

## 5. Extremal arguments and the missing closure

The response edge has a genuine strict prescribed-payoff orientation for its
observer:

\[
 U_j(Z)\ge U_j(Y)+c
\tag{13}

for one fixed `c>0` in the retained rectangle branch.  If there were a
nonempty compact class `K` of minimum joint points satisfying:

1. every point of `K` were an eligible paid endpoint with the same observer
   `j`; and
2. its response endpoint also belonged to `K` and obeyed (10),

then maximizing `U_j` on `K` would give an immediate contradiction.

The actual class does not have this closure.  The response endpoint `Z`
regenerates a source, but rerunning the forced-pair producer gives a new paid
whole-profile cluster `Y'`; it does not identify `Y'` with `Z`, place `Y'` on
the old chord, or even control `U_j(Y')-U_j(Z)`.  The unsigned source-to-paid
transition can erase the strict gain in (10).

Maximizing over all minimum sources therefore does not solve the problem, and
maximizing over paid endpoints does not help unless response endpoints are
proved to remain in that paid-endpoint class.

## 6. Diagonal approach to the endpoint

Choose `theta_n -> 1`.  A diagonal selection gives actual near-minimum
profiles converging jointly to `(Z,nu_Z)` such that:

- the fixed routed atom retains asymptotic mass at least `lambda`;
- observer `j`'s debt is positive but tends to zero; and
- replacing `j` by the response endpoint reduces that debt by the affine
  chord amount, while the endpoint residual tends to zero.

This is a genuine vanishing-debt finite-atom family.  It is not automatically
a `QuittingVanishingDebtAtomAccess`: that checked structure is indexed by a
`QuittingPositiveMinimumDebtTangentFamily`, its mover must belong to the
base's positive-debt support, and its atom alternative arises from a fixed
off-diagonal replacement column.  Here `j` has zero debt at the limiting base
`Z`, and the displayed family approaches `Z` from a support-entry direction.

Treating the diagonal family as the checked access object would therefore
change its index and mover hypotheses.  A separate adapter is required.

## 7. Exact interface no-go model

The insufficiency can be represented without pretending to construct a
positive-gap quitting table.  Take an abstract minimum state interval

\[
 K=\{H_\theta:0\le\theta\le1\},
\]

with affine debt and law, and let `Z=H_1`.  Declare every point regenerable.
Let the source-to-paid producer ignore its input and return one fixed paid
state `Y`, and let the oriented response send `Y` to `Z`.

All conclusions of the open-chord theorem hold, including exact law
regeneration and the paid response.  Nevertheless the chord parameter never
enters the source-to-paid output, so topology on `K` cannot force a return or
rank decrease.  Equation (9) shows that this constant behavior is not alien
to the real interface: a pure nonsingleton row literally erases its tail
parameter.

This is an interface countermodel, not a quitting-game counterexample.  It
rules out a proof using only nonemptiness of regenerated sources, chord
affinity, and compactness.

## 8. Remaining sharpened test

The open chord supplies common approximate best responses at both actual
endpoint sequences.
The next non-diagnostic step would have to prove one of the following from the
actual Fin4 response packet:

1. one interior cap is attained, and the resulting common exact response
   crosses the marked pure-row seam into an executable chronology;
2. nonattainment forces an escaping pure-time packet whose bubble or exchange
   atom is source-matched to the retained response atom and is consumed by an
   existing return compiler; or
3. the rerun producer admits a closed response-stable subclass on which the
   strict payoff orientation (13) survives the source-to-paid transition.

The first sentence of each alternative is not enough by itself.  The output
must be a chronological return, a renewable finite rank, an off-minimum
contradiction, or a terminal approximation as required by the maintained
question.

## Conclusion

The full open chord eliminates ordinary cap curvature asymptotically: the two
actual endpoint sequences have common approximate maximizing deviations, and
exact affinity plus attainment at one actual interior triple gives a common
exact best response.  What it does not eliminate is temporal nonattainment,
the vanishing finite affinity gap, or source-to-paid nonanchoring.

At the present interface the chord parameter sits behind a pure nonsingleton
screen, so a fixed-word rerun is semantically constant in that parameter.
Topological and extremal arguments require an additional closure or seam
theorem; compactness and affinity alone do not force the missing renewable
orientation.
