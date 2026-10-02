# Minimum-law regeneration does not orient a paid endpoint cycle

Author: `CODEX_RIEMANN`

## Status

The requested Arm A consumer is **not proved** here.  I tested finite-label,
support, lexicographic-debt, and joint-law extremal selections against the
new paid-cycle recharge theorem and the actual target-law regeneration
theorem.

There is one source-provenance strengthening: in the all-minimum cycle arm,
the same argument regenerates a complete minimum-atom source at **both** ends
of every frozen cycle edge, with the displayed source and target coalitions
as their named law atoms.  Thus lack of a source at the left endpoint is not
the obstruction.

That strengthening also exposes the exact no-go.  If every vertex of the
literal paid `4/6/8` cycle is on the minimum fiber, the regenerated joint-law
source graph contains the same closed directed cycle.  Debt vectors, supports,
cycle labels, and the endpoint terminal laws all return exactly.  No strict
rank depending only on those data can orient every successor edge.  An
orientation must use data not periodic under the horizontal loop, such as a
response-generated atom together with an executable vertical chronology, or
must prove that one vertex is actually off minimum.

This is a boundary result, not one of the accepted terminal/rank/counterexample
outputs in `questions/FIN4_RENEWABLE_ORIENTATION_OR_COUNTEREXAMPLE.md`.

A later source-coherence audit of the checked forced-pair/maximal-ray path
sharpens the obstruction further.  Even if one first chooses a minimum point
with globally maximum positive-debt-support cardinality and constructs a
same-point minimum-law source there, the ray's whole semantic source is not
that chosen point.  It is the tail-independent semantic point of a sure pure
pair.  In the minimum-return arm the source compactification has exactly the
normalized debt vector of that pure-pair point.  Thus maximum-support
selection gives one honest support drop relative to the global maximum, but
the regenerated child does not constrain the next pure-pair ray source.  The
drop is not renewable.  Section 11 gives the exact calculation.

## Self-contained setting

Let `I = Fin 4`, let `r` be a finite quitting reward table, and write

\[
 d_i(\sigma)=B_i(\sigma)-U_i(\sigma),\qquad
 D(\sigma)=\sum_i d_i(\sigma).
\]

The cap `B_i` ranges over every behavioral unilateral replacement.  Assume
the terminal-semantic carrier has global minimum `D_*>0`.

Suppose one source-attached literal family contains a fixed simple cycle of
nonsingleton coalitions

\[
 C_0\xrightarrow{p_0}C_1\xrightarrow{p_1}\cdots
 \xrightarrow{p_{K-1}}C_K=C_0,
 \qquad K\in\{4,6,8\},
\tag{1}
\]

and actual sibling profiles `sigma_(n,k)` obtained by changing only the
marked pure root.  Thus

\[
 \sigma_{n,K}=\sigma_{n,0}
\tag{2}
\]

as complete behavioral profiles.  The marked live mass is at least
`lambda>0`, and every selected toggle is a literal profitable deviation with
gain at least

\[
 g_0=\lambda D_*/4.
\tag{3}
\]

Assume after a common subsequence that every joint semantic/law sequence
converges:

\[
 (\operatorname{Sem}(\sigma_{n,k}),\operatorname{Law}(\sigma_{n,k}))
 \longrightarrow (Z_k,\nu_k).
\tag{4}
\]

The genuinely difficult arm is

\[
 D(Z_k)=D_*\qquad(0\le k<K).
\tag{5}
\]

If (5) fails, one already has the strict off-minimum endpoint arm.

## 1. Dual endpoint-law regeneration

At the marked date of `sigma_(n,k)`, the pure coalition is `C_k`, and its
unconditional mass equals the common live mass.  Therefore

\[
 \lambda
 \le \operatorname{Law}(\sigma_{n,k})(C_k).
\tag{6}
\]

Evaluation at a fixed finite terminal is continuous on the finite law
simplex.  Passing to (4) gives

\[
 \boxed{\nu_k(C_k)\ge\lambda>0.}
\tag{7}
\]

The joint point `(Z_k,nu_k)` belongs to the joint carrier because it is the
limit of the literal sibling profiles.  Under (5), it is a global-minimum
joint point and has the same positive literal debt infimum as the incoming
hard residual.  Applying

```text
exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom
```

to `(Z_k,nu_k)` and the **particular** terminal `C_k` produces a
`QuittingMinimumLawCausalSuffixAtom` whose named terminal is exactly `C_k`.
Together with the unchanged Fin4 hard residual, this packages a fresh

```text
FinFourMinimumAtomProducer r M
```

at `(Z_k,nu_k)`.

This applies to every vertex simultaneously because the cycle is finite.
In particular, the source end of the spectator-recharge edge regenerates just
as honestly as its target end.  No arbitrary law lift or independently
selected semantic representative is needed.

This strengthens the one-sided target-law regeneration statement to

\[
 \boxed{
 \text{all-minimum paid cycle}
 \Longrightarrow
 \text{a complete minimum source at every actual cycle law}.}
\tag{8}
\]

It does **not** identify the fresh causal chronology at one vertex with the
old marked sibling family.

## 2. Exact closure defeats a debt/support/label rank

Equation (2) gives, after taking limits,

\[
 (Z_K,\nu_K)=(Z_0,\nu_0).
\tag{9}
\]

Let `R` be any purported strict rank whose value is determined by any
combination of

* the semantic debt vector `d(Z_k)`;
* its positive support;
* the displayed coalition and mover labels;
* the full endpoint terminal law `nu_k`; and
* the unchanged table-level hard residual.

If every regenerated successor in (1) were required to satisfy

\[
 R(Z_{k+1},\nu_{k+1},C_{k+1})
 <R(Z_k,\nu_k,C_k),
\tag{10}
\]

then chaining (10) around the finite cycle and using (9) would give

\[
 R(Z_0,\nu_0,C_0)<R(Z_0,\nu_0,C_0),
\]

which is impossible for any strict well-founded order.

The debt ledger alone already admits the sharp rotating model.  If the mover
sequence is `p_0,...,p_(K-1)` with consecutive movers distinct, set

\[
 d(Z_k)=g e_{p_k}
\]

and let edge `k` subtract `g` from `p_k` and add `g` to the next mover.  Total
debt stays equal to `g>0`, every mover is killed exactly, every edge has a
spectator rise `g`, and the vector returns after `K` steps.  This is an
abstract ledger test, not a positive-gap quitting table; it shows why an
inequality-only potential cannot prove the needed orientation.

## 3. Why lexicographic/extremal selection does not repair closure

Several natural selections fail for the same exact reason.

### Coordinate extrema

On a minimum edge, exact own-cap invariance subtracts the mover's gain and
total-debt equality transfers the same aggregate amount to spectators.  A
large weight on the mover makes one chosen edge decrease a weighted debt
sum, but the mover changes around the cycle.  No fixed weighting decreases
all edges of a returned cycle.

Choosing a maximum or minimum of one observer coordinate also fails.  That
coordinate has total signed increment zero around the loop.  A positive rise
can occur away from its maximum and a negative change can occur away from its
minimum.

### Support cardinality

An observer response in the rectangle decoder may drive that observer's debt
to zero, but other coordinates can enter.  The literal half stopping-law
mixture gives a genuine union-support parent and hence a one-time strict
support handoff.  It does not make the response endpoint the successor of the
incoming source under a renewable rule.  Reapplying the atlas can construct a
new union-support parent, so the cardinality need not continue downward from
the previous child.

### Coalition or joint-law labels

The actual laws carry the directed point masses `C_k -> C_(k+1)`, but the
coalition labels themselves form (1), and the full joint law returns by (9).
Adding those labels to the state records the loop more faithfully; it does
not orient it.

## 4. The surviving nonperiodic datum

The spectator-recharge theorem does produce information not contained in the
returned sibling state.  On one frozen edge and one observer it yields

```text
HasQuittingStoppingLawVanishingDebtAtomAlternative
```

with fixed positive charge and vanishing error.  In its rectangle arm, a
common pure-time observer response has vanishing debt at the double-reset
endpoint.  In its prescribed arm, a fixed signed terminal atom witnesses a
payoff-law difference.  Neither datum is a coordinate of the horizontal
cycle state, and neither is known to return after one loop.

Accordingly the smallest plausible orientation theorem must use this
response-generated datum and prove one of:

1. it occurs on an executable successor chronology and supplies cumulative
   admissible charge;
2. its minimum-fiber endpoint regenerates a source in a class closed under
   a strict support drop; or
3. failure of (1)--(2) forces one cycle vertex off the minimum fiber.

Merely regenerating sources at `(Z_k,nu_k)` cannot prove any of these: (8)--(9)
show that regeneration is compatible with exact horizontal recurrence.

## 5. A rectangle response retains a uniform finite atom

There is one useful strengthening on the rectangle side.  It does not orient
the recursion, but it removes a possible source-regeneration objection at the
vanishing-debt response endpoint.

Let an actual profile have a pure nonsingleton coalition `C` at a marked date
`t`, reached with unconditional probability `L > 0`.  Fix a player `j`, and
replace `j`'s complete strategy by a pure stopping time `q` in
`Nat union {Never}`.  Without using the rectangle atom yet, the resulting
profile has some finite terminal coalition of total-law mass at least

\[
  L/2^{|I|-1}.
\tag{11}
\]

For `Fin 4` the bound is `L/8`.

The proof is a direct split.

* If `q <= t`, the response player Continues surely before `q` and Quits
  surely at `q`.  Opponent survival to `q` is at least the original joint
  survival to `t`, namely `L`.  At date `q` the three opponents generate one
  of at most eight coalitions, so one terminal containing `j` has stage mass
  at least `L/8`.
* If `q > t` or `q = Never`, the response player Continues at `t`.  The
  marked root becomes `C \ {j}` when `j in C`, and remains `C` otherwise.
  It is still nonempty because `|C| >= 2`.  The response profile reaches the
  mark with probability at least `L`, so this terminal itself has stage mass
  at least `L`.

Complete terminal-law mass dominates the displayed stage mass.  Along a
sequence, finite pigeonhole freezes one terminal label, and compactification
retains the same positive lower bound in the limiting law.

For the actual rectangle decoder the factor `1/8` is unnecessary.  The
source-response and endpoint-response profiles differ only at the marked
mover row.  If `q < t`, the observer Quits surely before the mark, so those
two response profiles have identical terminal laws.  Their rectangle atom is
then zero, contradicting its fixed positive lower bound.  Hence every
positive rectangle atom has

\[
 q\ge t\quad\text{or}\quad q=\mathrm{Never}.
\tag{11a}
\]

At the mark the response action is therefore deterministic: Quit if `q=t`,
Continue if `q>t` or Never.  The endpoint's pure nonsingleton coalition is
routed by this action to a still nonempty pure coalition, and the response
profile reaches the mark with probability at least `L`.  Thus a rectangle
response retains a finite atom of mass at least **`L` itself**, with no
pigeonhole loss.  The routed coalition label can be frozen along the usual
finite subsequence.

Consequently, in the rectangle arm of the spectator-recharge decoder, if the
double-reset response cluster `Z` also satisfies `D(Z)=D_*`, then its **own
actual limiting law** has a positive finite atom at the original marked-mass
floor.  Same-point causalization
therefore packages a complete `FinFourMinimumAtomProducer` at `Z`; no
arbitrary law lift is needed.

Moreover, the half stopping-law mixture `H` between the mover-reset endpoint
`Y` and the response endpoint `Z` retains at least half this atom.  If both
endpoints are on the minimum fiber, coordinatewise debt convexity plus global
minimality makes the midpoint debt vector exact:

\[
 d(H)=\tfrac12 d(Y)+\tfrac12 d(Z).
\tag{12}
\]

The observer has positive debt at `Y` and zero debt at `Z`; hence

\[
 \operatorname{supp}^+ d(Z)
   \subsetneq
 \operatorname{supp}^+ d(H).
\tag{13}
\]

Both ends of (13) now carry honest minimum-law source regeneration.  This is
stronger provenance than the bare semantic support handoff.

It is still not a renewable rank from the incoming source.  The parent in
(13) is the newly constructed midpoint `H`, not the mover-reset source `Y`.
After restarting at `Z`, the next response can construct a different union
parent and reintroduce a previously removed debt coordinate.  Thus (13)
cannot be chained as a decreasing support sequence without an additional
no-entry or anchoring theorem.

## 6. Extremal selection: the exact missing anchoring

There is a sharp compact-extremal way to see what stronger anchoring would
buy.  On a minimum stopping-law chord, terminal laws and prescribed payoffs
are affine, debt is coordinatewise convex, and equality of total debt forces
every coordinate inequality to be equality.  Hence the complete joint
semantic/law midpoint is the literal midpoint of its two minimum endpoints.

More directly, for a fixed observer `j`, the prescribed-payoff coordinate
`U_j` attains a maximum on the compact minimum joint carrier.  If the paid
source endpoint were such a maximizer, the rectangle response endpoint could
not also be minimum: that response increases `U_j` by a fixed positive
amount.  This avoids any claim that the full minimum set is globally convex.

The current construction does not allow that selection.  It starts from an
incoming minimum source, copies a nonvanishing prefix and pure pair over its
near-minimum tail, and compactifies the resulting **whole** profiles.  Their
source cluster `X` is not declared equal to the incoming `source.point`.
Selecting the incoming source to be extreme therefore does not select `X` to
be extreme.  Target-law regeneration repairs realization at the target but
does not identify the next paid source with that target.

Thus the extremal route would become decisive under either of the following
genuine strengthenings:

\[
 \text{paid whole-source cluster}=\text{incoming source point},
\tag{14}
\]

or closure of the class of paid whole-source clusters under the response
endpoint and its minimum chord.  Neither property is present in the checked
interfaces, and the nonvanishing copied marked mass makes (14) implausible in
general.

### Maximal support gives only a conditional no-entry theorem

Let `M` be the set of minimum joint semantic/law points carrying a positive
finite atom, hence admitting same-point source regeneration.  (The strict
positivity condition need not define a closed set, so compactness is not
claimed.)  Since there are only five possible support cardinalities and `M`
is nonempty in the present source branch, choose a point of `M` whose
positive-debt support has maximum cardinality.

If an Arm A **mover-reset endpoint cluster** `Y` itself has that maximum support,
and its response endpoint `Z` is also minimum, then the midpoint `H` from
(12) belongs to `M` and

\[
 \operatorname{supp}^+d(H)
 =\operatorname{supp}^+d(Y)\cup\operatorname{supp}^+d(Z).
\tag{15}
\]

Maximality forces the union in (15) to equal the support of `Y`.  Since the
response kills one coordinate which was positive at `Y`, this gives the
genuine anchored inclusion

\[
 \operatorname{supp}^+d(Z)
 \subsetneq
 \operatorname{supp}^+d(Y).
\tag{16}
\]

This is the strongest valid support-extremal statement.

It does not follow by choosing the **incoming** `source.point` to have maximum
support.  The forced-pair construction copies a nonvanishing prefix and pure
marked row in front of a tail tending to that point.  The resulting paid
endpoint cluster `Y` is another minimum point whose debt support need not
contain, equal, or otherwise be ordered with the incoming support.  In fact a
pure nonsingleton marked row screens the tail debt at that row, so there is no
general support-containment mechanism.

Nor does (16) iterate by itself.  Regeneration at `Z` gives a chronology whose
tails tend to `Z`; the next generic construction again selects a whole-profile
endpoint cluster `Y'` after a new copied marked prefix.  No checked field gives

\[
 \operatorname{supp}^+d(Y')\subseteq
 \operatorname{supp}^+d(Z).
\tag{17}
\]

Thus the next step may restore every coordinate removed in (16).  The global
maximum support of the table is unchanged, so induction on that table-level
maximum also makes no progress.  A renewable support proof needs precisely
the missing anchoring/no-entry property (17), or a backward compiler which
consumes the single maximum-support drop without restarting the generic
construction.

## 7. The response chord is closed under a smaller paid rectangle

The response chord has more structure than was used above. It remains a paid
rectangle at every sufficiently near proper interior point, although its
quantitative response charge decays toward the killed-observer endpoint.

Write the four actual rectangle corners as

\[
 A_n,\quad B_n=A_n[p\leftarrow b_n],\quad
 C_n=A_n[j\leftarrow q_n],\quad
 D_n=B_n[j\leftarrow q_n],
\tag{18}
\]

where `p != j`, `b_n` differs from `A_n(p)` only at the marked row, and
`q_n` is the common pure-time response. Suppose

\[
 U_p(B_n)-U_p(A_n)\ge g_0>0
\tag{19}
\]

and all terminal rewards have absolute value at most `M`. For fixed
`theta in (0,1)`, mix only player `j`'s complete stopping law and define

\[
 A_{n,\theta}=(1-\theta)A_n+_j\theta C_n,
 \qquad
 B_{n,\theta}=(1-\theta)B_n+_j\theta D_n.
\tag{20}
\]

The notation denotes the executable one-player stopping-law mixture, not a
formal mixture of semantic carrier points. Mover replacement commutes with
this mixture:

\[
 B_{n,\theta}=A_{n,\theta}[p\leftarrow b_n].
\tag{21}
\]

Terminal payoff is affine in one player's stopping law. If

\[
 g_{1,n}=U_p(D_n)-U_p(C_n),
\]

then

\[
 U_p(B_{n,\theta})-U_p(A_{n,\theta})
 =(1-\theta)g_{0,n}+\theta g_{1,n}.
\tag{22}
\]

Since `g_(1,n) >= -2M`, every fixed

\[
 0<\theta\le \frac{g_0}{2(g_0+2M)}
\tag{23}
\]

retains mover gain at least `g_0/2`. In particular, the selected pure action
of `p` is still the exact better marked endpoint against the mixed observer
root. The mark itself need not remain a pure coalition, but the endpoint law
retains the response terminal atom with mass at least `theta*lambda`.

Updating `j` in the two mixed profiles back to `q_n` gives `C_n,D_n`
exactly. Hence both the observer response gain and its endpoint-versus-source
cross-difference scale by the common factor `1-theta`:

\[
\begin{aligned}
 U_j(D_n)-U_j(B_{n,\theta})
   &=(1-\theta)(U_j(D_n)-U_j(B_n)),\\
 [U_j(D_n)-U_j(B_{n,\theta})]
  -[U_j(C_n)-U_j(A_{n,\theta})]
   &=(1-\theta)\,\mathsf{Cross}_n.
\end{aligned}
\tag{24}
\]

Assume the joint limits of `B_n,D_n` are the minimum points `Y,Z`.
Minimum-fibre stopping-law affinity shows that the joint limit `H_theta` of
`B_(n,theta)` is minimum and

\[
 d(H_\theta)=(1-\theta)d(Y)+\theta d(Z),
 \qquad
 \nu_{H_\theta}=(1-\theta)\nu_Y+\theta\nu_Z.
\tag{25}
\]

Thus every sufficiently near proper chord point is itself an actual-law
minimum paid mover endpoint, retains the same observer response rectangle,
and has a complete same-law source regeneration. This improves the
conditional maximal-support statement: maximality may be taken inside the
class of response-decorated paid minimum endpoints, provided that class is
defined without a fixed lower charge threshold.

It still does not produce a renewable rank. Repeating the partial response
with a fixed `theta` gives

\[
 H^{(m)}=(1-\theta)^mY+
   (1-(1-\theta)^m)Z,
\tag{26}
\]

while its usable response charge is `(1-theta)^m` times the original charge.
Every finite `H^(m)` has the same union support, but the sequence converges to
`Z`, where precisely the killed coordinate and the response charge vanish.
Consequently:

* the nondegenerate decorated class is not closed at its `U_j`-maximizing
  boundary;
* imposing a fixed positive charge makes the chord leave the class at that
  boundary; and
* normalizing by the charge records the degeneration but does not stop it.

This is an exact obstruction to the simplest compact-extremal argument. A
maximum of `U_j` exists only after adjoining the zero-charge endpoint which
no longer carries the operation that was meant to contradict maximality.

## 8. Terminal SCCs do not turn the one-time drop into a rank

Consider the directed relation generated by:

1. choosing a source-attached paid minimum endpoint from a regenerated
   minimum source;
2. taking its minimum response endpoint; and
3. regenerating at the actual target law and, if desired, at every proper
   response-chord law.

Passing to a terminal strongly connected component does not orient this
relation. Inside such a component, a response edge can strictly remove one
debt coordinate, while the next source-to-paid-endpoint construction can
restore it. The checked construction contains no support-containment field on
that second edge. Adding every chord point makes the component larger and
introduces the zero-charge boundary (26); it does not make support monotone.

The condensation order is therefore useful only until a terminal component
is reached. A terminal component can still contain the exact circulation

\[
 \text{paid endpoint }Y
 \longrightarrow Z
 \longrightarrow \text{new paid endpoint }Y'
\]

with `supp d(Z) proper-subset supp d(Y)` and `supp d(Y')` unrelated to
`supp d(Z)`. No finite-label or source-law SCC rank decreases on an edge
internal to that component.

## 9. A preserved Never-limit coordinate also saturates

The late-or-Never fact (11a) suggests another finite state. Suppose the
marked dates tend to infinity. Then the response player's pure stopping laws
converge weakly to literal Never. Same-point causalization can be run on these
supplied response realizers rather than on an unrelated realizing sequence.
The chosen exact cap-prefix words have survival product tending to one because
both prefix and suffix debts tend to `D_*>0`; hence the probability that the
observer quits inside the added prefix tends to zero. The regenerated
chronology can therefore retain the named observer's Never-limit marginal.

This can make the set of retained Never-limit players monotone if every later
same-stage modification is performed on the inherited chronology. It is not
a terminal rank: after at most four additions every marginal may converge to
Never while a fixed finite coalition law atom survives through relative
timing at dates tending to infinity. That is exactly the already-known
all-player compactness bubble, not a contradiction. Nor does the recharge
selector guarantee that the next observer is outside the retained set.

Thus marginal-Never provenance is useful chronological information, but it
does not supply the missing minimal-rank consumer.

## 10. Normalized chord tangent: valid at `Y`, wrong-way at `Z`

The vanishing-charge chord does retain a nonzero normalized direction:

\[
 \frac{d(H_\theta)-d(Z)}{1-\theta}=d(Y)-d(Z).
\tag{27}
\]

This does not, however, give the same tangent-family input at the two
endpoints.

At `Y`, the observer `j` is active and the full replacement by `q_n` has
endpoint `Z` with vanishing `j` debt. Taking `theta_n -> 0`, synchronizing
the source excess so it is `o(theta_n)`, and choosing the response accuracy
`o(theta_n)` gives one legitimate flat tangent column based at `Y`:

\[
 T_j=d(Z)-d(Y),\qquad
 T_j(j)=-d_j(Y),\qquad
 \sum_iT_j(i)=0.
\tag{28}
\]

If `Y` has maximum support among the atom-carrying minimum endpoints, the
full response chord proves that this particular column has no inactive
support entry, and its full-replacement cluster `Z` is a minimum endpoint
with strict support loss. The checked minimum-fibre re-extraction theorem can
therefore build a new positive-minimum tangent family at `Z` with smaller
support. This recovers the one-time support handoff in the native tangent
language.

At `Z`, equation (27) points in the opposite strategic direction. Player `j`
has zero debt at `Z`, so `j` is not in the active-mover index set of
`QuittingPositiveMinimumDebtTangentFamily`. The family requires a
debt-killing full replacement for **every active base mover**. Moving from
`Z` back toward `Y` instead changes an inactive player's strategy and creates
its debt. Hence the normalized rectangle at the killed endpoint is not a
source-attached positive-minimum tangent family input of the existing type.

Running the generic tangent extractor at `Z` does not fix this mismatch. It
chooses new full replacements for the active coordinates of `Z`; it retains
neither the `Y-Z` column, the union-support parent, the terminal-law atom, nor
the four-corner rectangle. Its reduced support-rank theorem may terminate in
positive total slope, zero-debt support entry, or an off-minimum paid row.
Those are precisely chronological consumer obligations, not terminal
outputs. Rerunning the Fin4 forced-pair producer on that new family may in
turn enter the strict normalized inert arm, but no checked transition from
that arm returns to a subset of `supp d(Z)`.

Thus normalized tangency gives an honest and potentially formalizable
one-step adapter

\[
 (Y,Z,\text{maximum-support no-entry})
 \longrightarrow
 \text{smaller-support tangent source at }Z,
\tag{29}
\]

but not a renewable adapter. The exact missing compatibility is stronger
than nonvanishing normalized charge: the tangent re-extraction at `Z` would
have to retain the old union parent or constrain every newly selected
full-replacement support to `supp d(Z)`. Neither follows from (27)--(28).

The checked `FiniteResetCirculationRegression` is the sharp strategy-class
fence: exact full replacements with killed mover debt and constant total debt
can rotate support forever. Its table has global minimum zero, so it is not a
counterexample to the present positive-minimum theorem. It does show that the
missing compatibility cannot be obtained from the normalized tangent column,
exact self-cap invariance, and profile recurrence alone.

## 11. Globally maximal support does not attach to the canonical ray source

This section audits the stronger proposal of choosing the incoming minimum
source first.  The conclusion is negative for the current canonical
forced-pair/maximal-ray construction, for an exact source-typing reason.

Let `z` be a minimum semantic point whose positive-debt support has maximum
cardinality among all points of the minimum fibre.  Because the player set is
finite, such a cardinality maximum can be chosen without any topological
claim.  Suppose a joint law with a positive finite atom at this same `z` has
been selected and causalized, so that it supplies a
`FinFourMinimumAtomProducer` whose semantic point is literally `z`.

The forced-pair packet displays a pure pair `C`.  Define its tail-independent
semantic point

\[
 P_C=\left(r(C),\ i\mapsto
   \max\{r_i(C\cup\{i\}),r_i(C\setminus\{i\})\}\right).
\tag{30}
\]

This is exactly `packet.raySource` in
`FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`.  For every selected
reference tail `tau_n`, the base profile is the sure pair `C` at date zero
followed counterfactually by `tau_n`, and the checked theorem

```text
rayBaseProfile_semantic_eq
```

states

\[
 \operatorname{Sem}(C*\tau_n)=P_C.
\tag{31}
\]

Thus the reference tail may converge jointly to the selected source `z`, but
it has no influence on the whole base semantics.  The maximal-prefix word is
then constructed from `P_C`, not from `z`:

\[
 X_n=\Phi_n(P_C).
\tag{32}
\]

The minimum point `z` is used in this construction only as the global lower
bound and as the limit of the counterfactual post-mark tail debts.  In
particular, changing the same-point source while retaining the same pair
label does not change (31)--(32).

The exact scalar-ray identity gives, for every player `i`,

\[
 d_i(X_n)=c_n d_i(P_C),
 \qquad
 D(X_n)=c_nD(P_C),
\tag{33}
\]

where `c_n` is the common maximal-prefix survival.  In the minimum-return arm,

\[
 D(X_n)\longrightarrow D_*>0,
 \qquad
 c_n\longrightarrow c_*:=\frac{D_*}{D(P_C)}>0.
\tag{34}
\]

Consequently every compact semantic source limit `X` used by the endpoint
support handoff satisfies

\[
 \boxed{d_i(X)=c_*d_i(P_C)\quad\text{for all }i,}
 \qquad
 \boxed{\operatorname{supp}^+d(X)=
        \operatorname{supp}^+d(P_C).}
\tag{35}
\]

This follows directly by coordinate continuity from (33)--(34).  It is also
the limiting form of the checked finite-depth declarations

```text
quittingMaximalCapSemanticPrefixOrbit_positiveDebtSupport_eq
quittingTerminalSemanticDebt_normalized_maximalCapSemanticPrefixOrbit_eq
```

Hence equality of the ray source cluster with the preselected point,

\[
 X=z,
\tag{36}
\]

is not an output of same-point causalization.  A necessary condition for
(36) is the additional normalized-debt identity

\[
 \frac{d_i(z)}{D_*}=\frac{d_i(P_C)}{D(P_C)}
 \quad\text{for every }i,
\tag{37}
\]

and full semantic equality requires still more than (37).  No field of
`FinFourMinimumAtomProducer`,
`FinFourOwnerCompressedMinimumReturnForcedPairSource`, or
`FinFourOwnerCompressedMinimumReturnForcedPairPacket` imposes (37).
The same-point finite-atom theorem produces actual profiles converging to
`z`; it does not turn the sure-pair point (31) into `z`.

There is nevertheless one exact payoff from selecting `z` globally maximal.
Let `Y` be a minimum endpoint of the paid mover update and `H` the checked
half-mixture parent between the source cluster `X` and `Y`.  The support
handoff proves

\[
 \operatorname{supp}^+d(Y)
   \subsetneq \operatorname{supp}^+d(H),
 \qquad D(H)=D_*.
\tag{38}
\]

If `r=|supp^+ d(z)|` is the global maximum on the minimum fibre, then (38)
implies

\[
 \boxed{|\operatorname{supp}^+d(Y)|<
        |\operatorname{supp}^+d(H)|\le r.}
\tag{39}
\]

Thus the endpoint regenerated at its actual target law has strictly smaller
support than the originally selected globally maximal point, even though
`X` need not equal `z`.  This is a valid one-step comparison.

It is not a renewable rank.  Rerunning the forced-pair construction from the
source regenerated at `Y` again replaces the whole semantic ray source by a
new sure-pair point `P_(C')`.  Its minimum-return source cluster `X'` obeys

\[
 \operatorname{supp}^+d(X')=\operatorname{supp}^+d(P_{C'}),
\tag{40}
\]

with no checked inclusion in `supp^+ d(Y)`.  Equation (39) therefore cannot
be applied inductively with `Y` as the new parent: the next entrance can
restore any coordinate removed by the preceding endpoint update.  The rank
`r-|supp^+d(current)|` can decrease again at this entrance, so it is not
monotone either.

This settles the actual adapter question for the checked path.  Global
maximum-support selection plus same-point source regeneration does **not**
anchor the canonical ray at the selected point.  A positive renewable theorem
needs one of the genuinely stronger source-coherence fields

\[
 \operatorname{SemSourceCluster}=\text{incoming source point},
 \quad\text{or at least}\quad
 \operatorname{supp}^+d(P_{C'})\subseteq
   \operatorname{supp}^+d(\text{regenerated child}).
\tag{41}
\]

Neither is a consequence of the present finite atom, target-law, or
maximal-ray interfaces.  This is a no-go for the proposed selection strategy,
not a counterexample to Fin4 and not a proof that a different source-anchored
ray construction is impossible.

## 12. Prescribed-payoff extremality reaches the zero-response boundary

There is a clean compact class on which maximizing one prescribed-payoff
coordinate is legitimate, and the response endpoint remains in that class.
The extremal argument nevertheless stops exactly because the **outgoing
response operation** is not closed at that endpoint.

### 12.1 The endpoint gain needs the full common-response witness

The reviewed response-chord packet records a positive cross-difference.  A
cross-difference alone does not imply that the endpoint response increases
the observer's payoff: numbers

\[
 U_j(A)=U_j(B)=0,
 \quad U_j(C)=-2,
 \quad U_j(D)=-1
\]

have positive cross-difference `1` but negative endpoint gain `-1`.

The actual rectangle produced by
`QuittingStoppingLawCommonResponseWitness` is stronger.  With the earlier
notation and response error `e_n -> 0`, it gives

\[
 d_j(A_n)+\kappa-e_n
 \le U_j(D_n)-U_j(B_n).                                    \tag{42}
\]

Therefore, if `A_n` has semantic cluster `X`, while `B_n -> Y` and
`D_n -> Z`, then

\[
 \boxed{U_j(Z)-U_j(Y)\ge d_j(X)+\kappa\ge\kappa>0.}         \tag{43}
\]

Thus prescribed-payoff orientation is valid for the full source object.  It
must not be attributed to the isolated cross-difference hypothesis of the
focused response-chord export.

### 12.2 The broad compact atom-source class

For a joint terminal law `nu`, let

\[
 a(\nu)=\sum_{\varnothing\ne T\subseteq I}\nu(T)
       =1-\nu(\mathsf{Never})
\]

be its total finite-absorption mass.  Define

\[
 \mathcal K_\lambda=
 \{(z,\nu)\text{ in the joint carrier}:
       D(z)=D_*,\ a(\nu)\ge\lambda\}.                      \tag{44}
\]

The joint carrier is compact, while `D` and `a` are continuous.  Hence
`K_lambda` is compact.  Every member has some fixed finite terminal of mass
at least

\[
 \lambda/(2^4-1)=\lambda/15,
\]

and therefore admits complete same-point minimum-source causalization (with
the unchanged hard residual).  This is the broadest canonical compact class
needed here: it retains quantitative finite-atom source attachment without
requiring one terminal label to survive a response that may route `S` to a
different `T`.

The pure marked pair gives `a(nu_Y)>=lambda`, and the no-loss response routing
gives `a(nu_Z)>=lambda`.  Thus both `(Y,nu_Y)` and `(Z,nu_Z)` belong to
`K_lambda`.  Every response-chord law

\[
 \nu_\theta=(1-\theta)\nu_Y+\theta\nu_Z
\]

does as well.  Prescribed payoff is affine under the executable one-player
stopping-law mixture, so

\[
 U_j(H_\theta)
 =(1-\theta)U_j(Y)+\theta U_j(Z).                           \tag{45}
\]

By (43), this is strictly increasing in `theta`.  The maximum on the closed
chord is attained at the honest, source-attached endpoint `Z`.

### 12.3 Why the maximum is inert

For every proper `theta<1`, the old pure-time response still maps the mixed
profile to `D_n`, and its response gain and cross charge are scaled by
`1-theta`.  At `theta=1`, the response has already been fully applied.  Its
gain and charge are zero.  Same-law causalization at `Z` regenerates a source,
but does not regenerate a **fresh outgoing response rectangle based at `Z`**.

This gives an exact closure dichotomy.

* If the decoration means only “has a positive finite atom and remembers an
  incoming rectangle”, the class is compact and contains `Z`, but its
  maximizer need not carry an outgoing operation.
* If the decoration means “currently carries a nondegenerate outgoing
  response rectangle with observer `j`”, every proper chord point is in the
  class but `Z` is not.  The class is not closed; its supremum is reached only
  after adjoining the zero-charge endpoint.
* Imposing a fixed positive response-charge floor makes a closed truncated
  chord, but the full response leaves that truncated decorated class.  It
  does not create an internal contradiction.

The paid-mover qualification is even narrower: the reviewed lower bound
guarantees it only for a fixed initial subinterval of the chord.  This does
not affect (43)--(45), but it makes closure of the full paid rectangle still
less plausible.

### 12.4 Exact extremal closure theorem still needed

Let `C` be a nonempty compact class of source-attached minimum joint points.
If one could prove, for one fixed observer `j`, that every `P in C` has a
source-attached response successor `R(P) in C` satisfying

\[
 U_j(R(P))>U_j(P),                                          \tag{46}
\]

then a maximizer of `U_j` on `C` would give an immediate contradiction.
This theorem needs no uniform gain floor.

The current response-chord result verifies (46) once at the mover-reset
endpoint `Y`, and verifies that its target `Z` remains an atom-carrying
minimum source.  It does **not** verify (46) again at `Z`.  Rerunning the
generic forced-pair construction from the regenerated source produces a new
whole-profile paid endpoint `Y'`, not `Z`; `U_j(Y')` is unrelated to
`U_j(Z)`, and even the next observer need not be `j`.

Finite label stabilization freezes labels along a chosen infinite
subsequence but does not supply the missing equality `Y'=Z` or the inequality
`U_j(Y')>=U_j(Z)`.  Lexicographic maximization and positive weighted sums do
not help, because response payoffs in the other coordinates are uncontrolled.

Hence the minimal closure field for this extremal route is:

\[
\boxed{
\begin{array}{c}
\text{the regenerated response endpoint itself is an admissible next}\
\text{paid whole-source endpoint, with the same observer and a fresh}\
\text{strictly positive common-response gain.}
\end{array}}                                                \tag{47}
\]

A weaker sufficient form would preserve membership in any compact class and
the strict `U_j` increase in (46).  Actual-law source regeneration, atom
retention, and historical rectangle labels do not imply (47).

Thus prescribed-payoff extremality gives a genuine one-edge orientation and
an exact compact maximizer, but the maximizer is precisely the fully responded
zero-charge boundary.  This is an interface no-go for the current recursive
source adapter, not a table counterexample and not a proof that a stronger
source-closed construction is impossible.

## Source audit

The bounded source set inspected for this note was:

* `questions/FIN4_RENEWABLE_ORIENTATION_OR_COUNTEREXAMPLE.md`;
* `exports/PAID_NONSINGLETON_CYCLE_SPECTATOR_RECHARGE_AND_ATOM_DISPATCH.md`;
* `formalized/FIN4_THREE_ROLE_MINIMUM_TARGET_LAW_SOURCE_REGENERATION.md`;
* `exports/FIN4_CANONICAL_PAIR_MINIMUM_ENDPOINT_SUPPORT_RANK_HANDOFF.md`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawGlobalRetention.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`;
* `Research/Quitting/FinFourProducerAtlas/Source.lean`;
* `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean`;
* `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`;
* `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`;
* `Research/Quitting/FinFourProducerAtlas/CanonicalPairMinimumEndpointSupportRankHandoff.lean`;
* `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`;
* `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FlatCirculationSupportRankElimination.lean`;
* `Research/Quitting/FiniteResetCirculationRegression.lean`.

The atom decoder is a static two-deviation alternative.  The universal
`VanishingDebtAtomChronologicalConsumer` is reward-by-reward equivalent to
uniform-payoff existence, so invoking it would merely restate the conjecture.

## Exact next question

Given an all-minimum actual paid cycle together with the fixed response atom
alternative on one edge, does the response profile admit either a
source-matched exact prefix chronology whose accumulated signed defect is
positive, or a minimum joint-law source whose next response construction is
confined to a strict subset of the union-support parent?

A theorem which only returns another minimum source at one of the cycle laws
does not answer this question.
