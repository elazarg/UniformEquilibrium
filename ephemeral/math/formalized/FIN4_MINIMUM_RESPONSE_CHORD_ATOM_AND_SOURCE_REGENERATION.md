# Minimum response chords retain an atom, a paid rectangle, and same-law sources

Authors: `CODEX_RIEMANN`

Independent review:
[`CODEX_STOKES`](../feedback/CODEX_RIEMANN__MINIMUM_REGENERATION_ORIENTATION_AUDIT__BY_CODEX_STOKES.md)

## Exact statement

Let the player set be `Fin 4`, let terminal rewards be bounded in absolute
value by `R>=0`, and let the compact terminal-semantic carrier have positive
global minimum total debt `D_*`.  Fix on the same table a supplied
`FinFourQuantitativeFullSupportHardResidual reward bound`, so its terminal
witness and punishment-normal fields are retained unchanged.  Suppose a
source-attached response rectangle provides actual behavioral profiles

\[
 A_n,\qquad B_n=A_n[p\leftarrow b_n],\qquad
 C_n=A_n[j\leftarrow Q_{q_n}],\qquad
 D_n=B_n[j\leftarrow Q_{q_n}],
 \tag{1}
\]

with fixed distinct players `p != j`, marked dates `t_n`, and the following
literal data.

1. `A_n` and `B_n` differ only in player `p`'s action at `t_n`; strictly
   before and after that date their live-root data agree.
2. At `t_n`, `B_n` has a pure nonsingleton quitting coalition `S`, reached
   with unconditional mass at least `lambda > 0`.
3. `Q_(q_n)` is one common pure-time response of player `j`, where
   `q_n` is a finite date or `Never`.
4. For one fixed nonempty coalition `A` and one `eta>0`, the response square
   has the positive payoff-difference atom

   \[
    \eta\le
      \bigl(\Pr_{D_n}(A)-\Pr_{C_n}(A)\bigr)r_j(A).
   \tag{1a}
   \]

   Here the probabilities are complete terminal-law masses. In particular,
   the complete terminal laws of `C_n` and `D_n` are not equal.
5. The mover edge is uniformly paid:

   \[
   U_p(B_n)-U_p(A_n)\ge g_0>0.
   \tag{2}
   \]

6. Along one common subsequence, the joint semantic/law points of `B_n` and
   `D_n` converge to `(Y,nu_Y)` and `(Z,nu_Z)`, respectively, and

   \[
   D(Y)=D(Z)=D_*.
   \tag{3}
   \]

7. The common-response cross-difference has a fixed positive floor
   `kappa>0`:

   \[
   \begin{aligned}
    \mathsf{Cross}_n
      &:=[U_j(D_n)-U_j(B_n)]-[U_j(C_n)-U_j(A_n)]\\
      &\ge\kappa.
   \end{aligned}
   \tag{3a}
   \]

Then, after a further subsequence, one fixed nonempty coalition `T` satisfies

\[
 \nu_Z(T)\ge\lambda.
 \tag{4}
\]

For every fixed `0<theta<1`, mix only player `j`'s complete stopping law and
put

\[
 A_{n,\theta}=(1-\theta)A_n+_j\theta C_n,
 \qquad
 B_{n,\theta}=(1-\theta)B_n+_j\theta D_n.
 \tag{6}
\]

Here `+_j` is the executable one-player stopping-law mixture, not common
randomization and not a formal coordinatewise semantic mixture.  Then:

- `B_(n,theta)=A_(n,theta)[p <- b_n]` literally;
- the complete law of `B_(n,theta)` gives `T` mass at least
  `theta * lambda` in the limit;
- every joint cluster `(H_theta,nu_theta)` of `B_(n,theta)` satisfies

  \[
  \nu_\theta=(1-\theta)\nu_Y+\theta\nu_Z,
  \qquad
  D(H_\theta)=D_*;
  \tag{7}
  \]

- coordinate debts are exactly affine:

  \[
  d_i(H_\theta)=(1-\theta)d_i(Y)+\theta d_i(Z)
  \quad(i\in\operatorname{Fin}4);
  \tag{8}
  \]

- the response gain and response-square cross-difference from the chord point
  to `D_n` are exactly `1-theta` times their original values, so the latter
  remains at least `(1-theta)*kappa>0`; and
- `(Z,nu_Z)` and every `(H_theta,nu_theta)` admit complete same-law
  `FinFourMinimumAtomProducer` objects, with named finite atom `T` and the
  unchanged hard residual.

If in addition

\[
 0<\theta\le {g_0\over 2(g_0+2R)},
 \tag{5}
\]

then the mover edge remains paid by at least `g_0/2`.

There is also the following conditional support corollary. If

\[
 d_j(Y)>0,\qquad d_j(Z)=0,
\tag{8a}
\]

then every proper chord point satisfies

\[
 \operatorname{supp}^+d(Z)
   \subsetneq\operatorname{supp}^+d(H_\theta).
\tag{8b}
\]

Let `M_min` be the class of minimum joint semantic/law points on this table
which carry some positive finite atom. If the actual mover-reset endpoint
`(Y,nu_Y)` has maximum positive-debt-support cardinality in `M_min`, then

\[
 \operatorname{supp}^+d(Z)
   \subsetneq\operatorname{supp}^+d(Y).
\tag{8c}
\]

This maximal-support hypothesis is on `Y`, not on the incoming atlas source
or the source end of an earlier paid edge.

Thus a minimum response endpoint and every proper response-chord point retain
an actual positive finite atom and exact same-law causal source regeneration.
The chord is not merely a carrier segment: for every fixed sufficiently small
positive `theta`, it retains a literal paid mover rectangle.

## Conjecture-facing change

The response-rectangle arm previously stopped with a semantic support chord
and an unresolved realization/source-provenance objection.  This theorem
removes that objection.  The response time is forced to be at or after the
marked collision, so the response endpoint retains the full marked mass in
one finite coalition.  Same-point causalization then regenerates the complete
Fin4 minimum source at the response endpoint and throughout every proper
minimum chord, while a fixed fraction of the paid rectangle remains usable.

What remains is orientation: the usable response charge decays to zero at the
response endpoint, and the next atlas pass need not preserve the
incoming support or rectangle.  No renewable rank or terminal conclusion is
claimed.

## Definitions and assumptions

Terminal payoff is the undiscounted payoff at the first nonempty quitting
coalition; infinite continuation pays zero.  Behavioral strategies may depend
on the full observed history and use private randomization.  For a profile
`sigma`,

\[
B_i(\sigma)=\sup_{\tau_i}U_i(\sigma[i\leftarrow\tau_i]),
\qquad d_i(\sigma)=B_i(\sigma)-U_i(\sigma),
\qquad D=\sum_i d_i,
\]

where the supremum ranges over every unilateral behavioral replacement,
including Never and arbitrarily late stopping.

The marked mass in assumption 2 is unconditional: it already includes reach
to `t_n`.  A pure-time response `Q_q` Continues before `q` and Quits surely at
`q`, or Continues forever when `q=Never`.

The signed law lower bound in assumption 4 is exactly the positive terminal
atom supplied by the rectangle branch of
`HasQuittingStoppingLawVanishingDebtAtomAlternative`.  Only its nonvanishing
is needed to force the response-date order; its quantitative lower bound is
retained by the surrounding packet.

## Source correspondence

The response rectangle is produced by
`hasVanishingDebtAtomAlternative_of_endpointDebtRise` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`.
Its rectangle arm stores one common pure-time response and a positive
endpoint-response/source-response law atom.

The exact one-player law affinity and debt convexity are:

- `quittingTerminalOutcomeMass_stoppingLawMixture_eq`;
- `quittingTerminalSemanticDebt_stoppingLawMixture_le`; and
- `quittingTerminalSemanticDebt_stoppingLawMixture_eq_of_minimum_sameDebtSum`
  in `TerminalSemanticStoppingLawMinimumFiberAffine.lean`.

Same-point source causalization is
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` in
`TerminalSemanticLawCarrierCausalization.lean`.  Existing endpoint-law Fin4
packaging is represented by
`ConcentratedCollisionThreeRoleEndpointLaw.nonempty_finFourRegenerationOrAscent`
and `FinFourThreeRoleMinimumTargetRegeneration`.

The new content is the response-before-mark exclusion, lossless routed atom,
full-chord paid-rectangle retention, and simultaneous same-law source
regeneration throughout the chord.

## Proof

### 1. The response cannot occur before the mark

Suppose `q_n<t_n`.  In both response profiles `C_n,D_n`, player `j` Quits
surely at `q_n`.  The underlying siblings `A_n,B_n` are literal equals at
every date before `t_n`, and their only difference at `t_n` is never reached.
Consequently `C_n` and `D_n` have exactly the same complete terminal law.
This contradicts assumption 4.  Hence

\[
 q_n\ge t_n\quad\text{or}\quad q_n=\mathrm{Never}.
 \tag{9}
\]

This argument covers equality, unbounded finite dates, and Never; no bounded
response-class substitution is made.

### 2. The response endpoint retains the marked mass without loss

By (9), player `j` Continues surely before `t_n`.  It therefore cannot reduce
the probability of reaching the marked row relative to `B_n`.  At the mark
its action is deterministic: Quit if `q_n=t_n`, and Continue if `q_n>t_n` or
Never.

Route the pure coalition `S` by that Boolean action.  Quitting inserts `j`;
Continuing erases `j`.  Since `S` is nonsingleton, the routed coalition is
nonempty in either case.  Its unconditional stage mass in `D_n` is at least
the original marked mass `lambda`.

There are finitely many routed coalitions and two response modes.  Pass to a
subsequence on which both are fixed, and call the coalition `T`.  Evaluation
of a fixed coordinate is continuous on the finite terminal-law simplex, so
joint convergence gives (4).

### 3. The executable chord and its law

Stopping-law mixture and the mover replacement concern distinct players, so
they commute, proving

\[
 B_{n,\theta}=A_{n,\theta}[p\leftarrow b_n].
 \tag{10}
\]

Terminal laws are affine in one player's complete stopping law.  Hence

\[
 \operatorname{Law}(B_{n,\theta})
 =(1-\theta)\operatorname{Law}(B_n)
   +\theta\operatorname{Law}(D_n).
 \tag{11}
\]

Every law is nonnegative coordinatewise, and the `D_n` mass of `T` is at
least `lambda`.  Thus the chord law has `T` mass at least
`theta*lambda`.  Passing to a joint cluster gives the law identity in (7).

### 4. The paid mover rectangle survives

Put

\[
g_{0,n}=U_p(B_n)-U_p(A_n),
\qquad
g_{1,n}=U_p(D_n)-U_p(C_n).
\]

Terminal payoff is affine under the same one-player mixture, so

\[
U_p(B_{n,\theta})-U_p(A_{n,\theta})
=(1-\theta)g_{0,n}+\theta g_{1,n}.
\tag{12}
\]

Both payoff terms defining `g_(1,n)` lie in `[-R,R]`, hence
`g_(1,n)>=-2R`.  Using `g_(0,n)>=g_0` and (5),

\[
(1-\theta)g_{0,n}+\theta g_{1,n}
\ge g_0-\theta(g_0+2R)\ge g_0/2>0.
\tag{13}
\]

Thus `b_n` remains the strict better marked endpoint for `p` at every chord
point satisfying (5).

Updating player `j` from the mixed strategy in both chord siblings to the
full response produces `C_n,D_n`.  One-player payoff affinity gives exactly

\[
\begin{aligned}
 U_j(D_n)-U_j(B_{n,\theta})
  &=(1-\theta)[U_j(D_n)-U_j(B_n)],\\
 [U_j(D_n)-U_j(B_{n,\theta})]
 -[U_j(C_n)-U_j(A_{n,\theta})]
  &=(1-\theta)\,\mathsf{Cross}_n.
\end{aligned}
\tag{14}
\]

So the response rectangle remains quantitatively nondegenerate for every
fixed proper `theta`: its cross-difference is at least
`(1-theta)*kappa>0` by assumption 7.

### 5. Minimum-fiber affinity

Coordinate debt is convex under a one-player stopping-law mixture.  Taking
limits in (6) yields

\[
d_i(H_\theta)\le
 (1-\theta)d_i(Y)+\theta d_i(Z).
\tag{15}
\]

Summing and using (3) gives `D(H_theta)<=D_*`.  The cluster is an actual
carrier point, so global minimality gives the reverse inequality.  Equality
therefore holds in the sum.  Each coordinate convexity gap is nonnegative;
their finite sum is zero, so every gap is zero.  This proves (7)--(8).

In particular, for `0<theta<1`,

\[
\operatorname{supp}^+d(H_\theta)
=\operatorname{supp}^+d(Y)\cup\operatorname{supp}^+d(Z).
\tag{16}
\]

Under (8a), player `j` belongs to the support of every proper `H_theta` but
not to the support of `Z`; (8b) follows. For (8c), equation (16) shows that
`H_theta` has support containing that of `Y`. It also belongs to `M_min`,
because it is minimum and its actual law carries `T` with positive mass.
Maximality of the support cardinality attained by `Y` forces the union in
(16) to equal the support of `Y`. Hence the support of `Z` is contained in
that of `Y`, and (8a) makes the containment strict. Only finitely many support
cardinalities exist, so this conditional maximum requires no compactness of
the positive-atom subclass.

### 6. Same-law source regeneration

The joint clusters `(Z,nu_Z)` and `(H_theta,nu_theta)` belong to the joint
terminal-semantic/law carrier.  Their semantic debts equal the positive
global infimum, and their displayed laws give the fixed finite terminal `T`
positive mass, at least `lambda` and `theta*lambda`, respectively.

Apply same-point causalization to each joint point and its displayed `T`.
Together with the unchanged Fin4 hard residual, the output is a complete
`FinFourMinimumAtomProducer` at that exact joint law.  No arbitrary law lift,
independently selected realizer, or weaker semantic-equivalence substitution
is used.

## Boundary tests

- If `q_n<t_n`, the two response laws are equal exactly; hence the positive
  response-law atom is essential and gives the sharp ordering conclusion.
- Nonsingleton cardinality is essential.  Erasing the unique member of a
  singleton at the mark can expose the tail and loses the nonempty routed
  atom conclusion.
- At `theta=1`, the retained mover gain may disappear. The paid-mover
  conclusion uses a fixed proper chord point satisfying (5), not the closed
  response endpoint. The atom, minimum, affinity, and same-law regeneration
  conclusions hold for every fixed `0<theta<1`.
- If either endpoint has debt strictly above `D_*`, convexity no longer forces
  coordinatewise affinity or minimum-source regeneration.

## Adapter and consumer

The intended input adapter is the rectangle arm of the checked stopping-law
vanishing-debt atom alternative after the endpoint and response labels are
frozen.  No checked declaration currently constructs the required
`FinFourMinimumResponseRectanglePacket` from that arm.  Conditional on the
supplied packet, the theorem outputs complete `FinFourMinimumAtomProducer`
objects at the actual response and chord laws, while retaining a literal paid
rectangle at each sufficiently small proper chord point.

This removes source realization as an excuse for not iterating the response
geometry.  It does not orient that iteration.  The consumer still needed is
an executable return or renewable rank using the regenerated rectangle; the
usable response charge scales by `1-theta` and vanishes at the response
endpoint.

## Lean handoff

Suggested declarations:

```text
responseAtom_pos_impureTime_ge_mark_or_never
responseEndpoint_routedStageMass_ge
minimumResponseChord_jointLaw_tendsto
minimumResponseChord_debt_eq_affine
minimumResponseChord_paidMoverGain_ge_half
minimumResponseChord_responseCross_eq_scale
minimumResponseChord_nonempty_finFourSources
```

The first two lemmas are finite-date stopping-law identities.  The chord law
and debt proofs should reuse the named stopping-law affinity declarations
above.  The dependent final structure should retain one common subsequence,
the fixed routed terminal, both endpoint joint limits, the proper chord
parameter, and the exact regenerated source objects.

## Scope and nonclaims

- The conditional response-chord compiler is checked in Lean under the
  supplied `FinFourMinimumResponseRectanglePacket` interface described below.
- It does not prove terminal approximants, a uniform payoff, or a positive
  admissible return.
- The support union in (16) is a one-time handoff, not a renewable rank from
  the incoming source.
- Choosing the incoming minimum source with maximal support does not make
  `Y` maximal; the forced-pair whole-source cluster is tail-blind.
- The proper chord retains less response charge as `theta` approaches one.

## Formalization record

The mathematical response-chord compiler is formalized by one generic
Research module and one Fin4 Research adapter.  The adapter starts from a
supplied pre-route response-rectangle packet; no declaration currently
constructs that packet from the stopping-law endpoint-rise decoder or an
atlas branch.

1. `Research/Quitting/MinimumResponseChordLaw.lean` proves the complete-law
   prefix screen
   `quittingTerminalOutcomeMass_update_pureTime_eq_of_liveRoot_eq_before` and
   the chronology theorem `responseAtom_pos_imp_pureTime_ge_mark`.  A strictly
   positive fixed complete-law rectangle atom therefore excludes every
   finite response before the marked row, while `Never` remains allowed.
2. In the same module,
   `quittingLiveMass_update_pureTime_eq_opponentSurvivalWeight_of_le`,
   `quittingPureTimeHazard_eq_pure_responseMode`, and
   `quittingStageCoalitionMass_le_update_pureTime_routed` prove exact
   at-or-after-mark no-loss routing.  The last theorem routes the marked
   coalition through the actual Boolean response action and does not accept
   a routed mass inequality as a hypothesis.
3. `Research/Quitting/FinFourProducerAtlas/MinimumResponseChordRegeneration.lean`
   defines `FinFourMinimumResponseRectanglePacket`.  It retains the actual
   source and endpoint profiles, literal mover update and pure marked row,
   marked stage-mass floor `lambda`, fixed positive complete-law response
   atom, paid mover and response-cross floors, one common joint-law
   subsequence, its endpoint and response limits, and their exact equality to
   the incoming minimum debt.  These fields are supplied data; in particular,
   this declaration is an interface, not a packet producer.
4. `FinFourMinimumResponseRectanglePacket.nonempty_minimumResponseRectangle`
   freezes the finite response mode on a strict refinement of that same
   common subsequence and defines the routed nonempty terminal.
   `FinFourMinimumResponseRectangle.responseChoice_ge_mark`,
   `responseHazard_eq_routedAction`, and `routedStageMass_floor` then derive
   the post-response floor from the packet's pre-route
   `markedStageMass_floor`.  Continuity yields
   `lambda_le_responsePoint_terminalMass` and
   `responsePoint_terminalMass_pos` at the exact response law.
5. For every supplied `0 < theta < 1`,
   `FinFourMinimumResponseRectangle.nonempty_minimumResponseChord` takes one
   further strict compactness refinement and constructs an actual joint
   chord point.  The accessors
   `FinFourMinimumResponseChord.terminalLaw_eq_affine`, `debt_eq_affine`,
   `support_eq_union`, and `theta_mul_lambda_le_terminalMass` expose the exact
   law, coordinate-debt, support, and atom identities.  The conditional
   theorems `response_support_ssubset_chord_of_killed` and
   `response_support_ssubset_endpoint_of_endpoint_maximal` state the precise
   observer-debt and endpoint-maximality hypotheses needed for strict support
   comparisons.
6. `FinFourMinimumResponseRectangle.endpointChord_eq_update_sourceChord`
   retains the same literal mover replacement throughout the executable
   rectangle.  `moverGap_div_two_le_chordGain` gives the exact `g / 2` floor
   under `theta <= g / (2 * (g + 2 * R))`, while
   `responseCross_eq_scale`, `one_sub_mul_crossFloor_le_responseCross`, and
   `responseCross_pos` retain the exact `(1 - theta)` response charge.
7. `FinFourMinimumAtomProducer.regeneratedAtLawPoint` applies named-terminal
   causalization to a supplied same-minimum joint law with a positive displayed
   atom.  `FinFourMinimumResponseRectangle.responseSource` and every
   `FinFourMinimumResponseChord.chordSource` use that constructor.
   `FinFourMinimumResponseChord.regeneratedSources_same_source` records the
   exact incoming hard residual, displayed response and chord points, and
   common routed terminal for both regenerated sources.

Evidence seals:

- **M:** PASS.  The complete-law screen, late-or-Never chronology, no-loss
  routing, joint compactification, exact affine law and debt identities,
  support statements, quantitative rectangle bounds, and same-law
  causalization match the reviewed mathematics.
- **L:** PASS.  The named declarations above check in Lean under the stated
  imports.  Promotion checks include direct and named module builds, the
  FinFour Research reader and full build, trust, documentation, import-graph
  and unit checks, proof-duplicate and derivable-telescope checks, and
  line/diff hygiene.  Important axiom prints use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- **A:** NOT SEALED.  The route and its mass floor are constructed from the
  supplied pre-route packet, but no checked theorem constructs
  `FinFourMinimumResponseRectanglePacket` from the actual stopping-law
  endpoint-rise/vanishing-debt branch or another maintained atlas source.
- **C:** NOT SEALED.  The output is a response source and a family of proper
  chord sources with a paid rectangle.  No theorem orients them into an
  executable return, renewable rank decrease, terminal approximation, or
  uniform-equilibrium conclusion.

The endpoint and chord points are compact joint semantic/law limits and need
not be attained by one behavioral profile.  Same-law causalization supplies
new deep chronologies, but does not retain the old response rectangle inside
them or make regeneration a chronology return.  The support comparison is a
one-time conditional handoff, not a renewable rank.  The companion packet
`FIN4_MINIMUM_RESPONSE_CHORD_ACTUAL_LAW_REGENERATION.md` remains in the export
lane because its advertised atlas response-rectangle/source decoder is not
formalized.  The mathematical provenance remains this packet and its linked
independent review; no external paper theorem is imported.
