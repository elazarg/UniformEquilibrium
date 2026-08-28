# Fin4 minimum response chords regenerate their actual laws

Authors: `CODEX_RIEMANN`

Independent review:
[CODEX_STOKES](../feedback/CODEX_RIEMANN__MINIMUM_REGENERATION_ORIENTATION_AUDIT__BY_CODEX_STOKES.md)

The reusable response-chord compiler and an actual normalized-return decoder
are checked in Lean.  The actual source theorem is
`FinFourNormalizedReturnSourceCapstone.nonempty_minimumResponseActualSourceOutcome`
in
`Research/Quitting/FinFourProducerAtlas/MinimumResponseChordActualDecoder.lean`.
It exhaustively retains strict inertness, endpoint ascent, routed singleton,
prescribed atom, response ascent, or a compiled rectangle.  In the compiled
arm, every proper chord has the exact affine law and debts, regenerated
same-law sources, and a strict one-time response-support drop.  The checked
canonical origin also retains the literal mover, observer, mass, gain, debt,
charge, and response-square constants recorded by the decoder.

The packet is not fully formalized as written.  Its advertised actual-data
adapter is the paid spectator-recharge cycle, whereas the checked adapter
starts from the normalized-return equality endpoint and its actual three-role
law.  No theorem transfers that paid-cycle branch into this decoder, proves
that a regenerated chronology contains the displayed edge, makes the support
handoff renewable, or consumes any returned branch.  Thus the integrated
surface has `M`, `L`, and `A` relative to the normalized-return source, but no
`C`; revisit the packet when its advertised paid-cycle source seam or a
renewable chronology/rank consumer is checked.

## Exact statement

Let `I = Fin 4`, let

\[
 r:\{C\subseteq I:C\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a finite quitting-game reward table, and assume that its terminal-semantic
carrier has positive global minimum total debt

\[
 D_*>0.
\]

Fix `M>0` with `|r_i(C)|<=M` for every player and nonempty coalition.

For an actual behavioral profile `sigma`, let `U_i(sigma)` be its prescribed
terminal payoff, let `B_i(sigma)` be the supremum against all complete
unilateral behavioral replacements, and put

\[
 d_i(\sigma)=B_i(\sigma)-U_i(\sigma),\qquad
 D(\sigma)=\sum_i d_i(\sigma).
\]

Assume the table carries the fixed Fin4 hard residual needed to package a
`FinFourMinimumAtomProducer` whenever a joint semantic/law minimum with a
positive finite atom is supplied.

For every `n`, suppose:

- `S_n` and `E_n` are literal behavioral profiles which differ only in one
  mover's action at one marked date `t_n`;
- their marked roots are fixed pure nonsingleton coalitions differing by that
  mover's membership;
- the common probability of reaching the marked row is `L_n >= lambda > 0`;
- a fixed observer `j`, distinct from the mover, uses one pure stopping time
  `q_n in Nat union {Never}` in both profiles;
- `S_n^q` and `E_n^q` are the corresponding source-response and
  endpoint-response profiles; and
- for some nonempty coalition `A_n`, the endpoint-response/source-response
  payoff-difference atom

  \[
   \bigl(\Pr_{E_n^q}(A_n)-\Pr_{S_n^q}(A_n)\bigr)r_j(A_n)
  \]

  is strictly positive.  Here `Pr_profile(A)` is complete terminal-law mass,
  not mass at one preselected date.

Assume also that the original mover edge and common-response rectangle have
fixed positive floors `g,kappa>0`:

\[
 U_p(E_n)-U_p(S_n)\ge g,
\tag{0a}
\]

\[
 \bigl(U_j(E_n^q)-U_j(E_n)\bigr)
 -\bigl(U_j(S_n^q)-U_j(S_n)\bigr)\ge\kappa.
\tag{0b}
\]

Assume, after one common subsequence,

\[
 (\operatorname{Sem}(E_n),\operatorname{Law}(E_n))
   \longrightarrow (Y,\nu_Y),
\tag{1}
\]

\[
 (\operatorname{Sem}(E_n^q),\operatorname{Law}(E_n^q))
   \longrightarrow (Z,\nu_Z),
\tag{2}
\]

and

\[
 D(Y)=D(Z)=D_*.
\tag{3}
\]

Finally suppose the response is the vanishing-debt response supplied by the
stopping-law endpoint-rise decoder, so that for one fixed `c>0`,

\[
 d_j(Y)\ge c,\qquad d_j(Z)=0.
\tag{4}
\]

Then all of the following hold.

### 1. Late-or-Never response and full atom retention

For every `n`,

\[
 q_n\ge t_n\quad\text{or}\quad q_n=\mathrm{Never}.
\tag{5}
\]

After a further subsequence there is one fixed nonempty coalition `T` such
that

\[
 \operatorname{Law}(E_n^q)(T)\ge L_n\ge\lambda
\tag{6}
\]

and hence

\[
 \boxed{\nu_Z(T)\ge\lambda>0.}
\tag{7}
\]

There is no `1/8` pigeonhole loss in (6): the positive response atom itself
excludes every stopping time before the mark.

### 2. Every interior response-chord point is an actual-law minimum source

Fix `theta` with `0<theta<1`.  At rank `n`, mix only observer `j`'s complete
strategy in `E_n`, with weight `theta` on the pure-time response used in
`E_n^q`.  Let `H_(n,theta)` be this literal behavioral profile.  There is a
joint cluster point

\[
 (H_\theta,\nu_\theta)
\]

such that

\[
 \nu_\theta=(1-\theta)\nu_Y+\theta\nu_Z,
 \qquad
 \nu_\theta(T)\ge\theta\lambda>0,
\tag{8}
\]

\[
 D(H_\theta)=D_*,
\tag{9}
\]

and, coordinatewise,

\[
 \boxed{
 d_i(H_\theta)
   =(1-\theta)d_i(Y)+\theta d_i(Z)
 }
 \qquad(i\in I).
\tag{10}
\]

Consequently,

\[
 \operatorname{supp}^+d(H_\theta)
   =\operatorname{supp}^+d(Y)\cup\operatorname{supp}^+d(Z),
\tag{11}
\]

and (4) gives

\[
 \boxed{
 \operatorname{supp}^+d(Z)
   \subsetneq\operatorname{supp}^+d(H_\theta).}
\tag{12}
\]

The actual joint points `(Z,nu_Z)` and `(H_theta,nu_theta)` both carry the
named finite atom `T` with positive mass.  Same-point causalization therefore
constructs complete `FinFourMinimumAtomProducer` objects at both exact laws,
with the unchanged hard residual.

### 3. Conditional maximal-support no-entry

Let `M` be the class of minimum joint semantic/law points on this table which
carry some positive finite atom.  Suppose the mover-reset endpoint
`(Y,nu_Y)` has maximum positive-debt-support cardinality among `M`.  Then

\[
 \boxed{
 \operatorname{supp}^+d(Z)
   \subsetneq\operatorname{supp}^+d(Y).}
\tag{13}
\]

The hypothesis in this statement is on `Y`, not on the incoming source point
or the source end of the paid edge.

### 4. Proper chord points retain an executable paid rectangle

For fixed `theta in (0,1)`, form both literal observer mixtures

\[
 S_{n,\theta}=(1-\theta)S_n+_j\theta S_n^q,
 \qquad
 E_{n,\theta}=(1-\theta)E_n+_j\theta E_n^q.
\tag{14}
\]

The mover update commutes literally with this one-player stopping-law
mixture, so `E_(n,theta)` is obtained from `S_(n,theta)` by the same mover
replacement. Replacing observer `j` by the common pure-time response sends
the mixed profiles back to `S_n^q,E_n^q` exactly.

For every

\[
 0<\theta\le \frac{g}{2(g+2M)},
\tag{15}
\]

the mover edge remains paid at the uniform floor

\[
 U_p(E_{n,\theta})-U_p(S_{n,\theta})\ge g/2.
\tag{16}
\]

The common-response rectangle charge satisfies

\[
\begin{aligned}
 &\bigl(U_j(E_n^q)-U_j(E_{n,\theta})\bigr)
  -\bigl(U_j(S_n^q)-U_j(S_{n,\theta})\bigr)\\
 &\quad=(1-\theta)
 \left[
   \bigl(U_j(E_n^q)-U_j(E_n)\bigr)
   -\bigl(U_j(S_n^q)-U_j(S_n)\bigr)
 \right]\\
 &\quad\ge(1-\theta)\kappa>0.
\end{aligned}
\tag{17}
\]

Thus every sufficiently near proper chord point is both a same-law minimum
source and the endpoint of a literal paid mover edge with the same executable
full response, response atom, and response endpoint. The absolute rectangle
charge vanishes as `theta` tends to one, so this does not close the operation
at `Z`.

## Conjecture-facing change

The response arm of the paid-cycle spectator-recharge decoder previously
ended with a vanishing-debt response semantic point whose actual finite atom
and source regeneration were not retained.  The theorem proves:

\[
\boxed{
\begin{array}{c}
\text{minimum mover-reset endpoint and minimum response endpoint}\\
+\ \text{positive response atom}
\end{array}
\Longrightarrow
\begin{array}{c}
\text{full-scale finite response atom}\\
+\ \text{same-law sources on the entire open response chord}.
\end{array}}
\]

Thus lack of an actual law or a regenerable source at the response endpoint
or its union-support parent is no longer an obstruction.  What remains is
orientation: the strict support handoff is not known to be renewable from the
incoming source.

The theorem also corrects a tempting overstatement.  Maximum support of the
incoming `source.point` does not imply (13), because the forced-pair whole
cluster `Y` need not have support contained in, equal to, or ordered with the
incoming support.

## Definitions and semantic scope

The terminal law is the complete law on finite nonempty quitting coalitions
and the all-Never outcome.  Stage mass is unconditional and includes the
probability of reaching the marked live history.

A pure stopping time `q` Continues surely before `q` and Quits surely at `q`;
`Never` Continues forever.  The response changes observer `j`'s complete
behavioral strategy, not only its marked action.

The stopping-law mixture is a literal private mixture of one player's two
complete stopping laws.  It is an executable behavioral strategy.  No common
randomization across players and no formal convexification of arbitrary
semantic pairs is used.

## Proof

### Step 1: positivity excludes a response before the mark

Suppose `q_n<t_n`.  The profiles `S_n` and `E_n` are literal equals before
`t_n`.  In both response profiles observer `j` Quits surely at `q_n` if play
has survived that long.  Thus their difference at `t_n` is never reached,
and `S_n^q` and `E_n^q` have identical complete terminal laws.

Every terminal payoff-difference atom between those two laws is therefore
zero, contradicting the assumed strictly positive atom.  This proves (5).

### Step 2: route the pure nonsingleton row without mass loss

If `q_n=t_n`, observer `j` Quits at the marked row.  If `q_n>t_n` or
`q_n=Never`, it Continues there.  Because the endpoint coalition is
nonsingleton, inserting `j` or erasing `j` leaves a nonempty coalition.

The pure-time response forces `j` to Continue before `t_n`, so it can only
increase the probability of reaching the marked row.  The response endpoint
therefore terminates at the routed pure coalition with stage mass at least
`L_n`.  The two possible marked actions and finitely many coalition labels
permit a subsequence on which the routed coalition is one fixed `T`.  Complete
terminal-law mass dominates stage mass, giving (6).  Evaluation at a fixed
law coordinate is continuous, so (2) yields (7).

### Step 3: exact law retention on the stopping-law chord

For each fixed `theta`, terminal outcome mass is exactly affine under the
one-player stopping-law mixture:

\[
 \operatorname{Law}(H_{n,\theta})
  =(1-\theta)\operatorname{Law}(E_n)
   +\theta\operatorname{Law}(E_n^q).
\tag{18}
\]

Compactness of the joint carrier supplies a semantic cluster along a further
subsequence.  Equation (18) and (1)--(2) identify its law as `nu_theta` and
give (8).

### Step 4: minimum-fibre convexity becomes coordinate affinity

Stopping-law debt convexity gives

\[
 d_i(H_{n,\theta})
 \le(1-\theta)d_i(E_n)+\theta d_i(E_n^q).
\tag{19}
\]

Pass to the joint limit.  Equations (1)--(3) yield

\[
 D(H_\theta)\le D_*.
\]

The cluster is in the terminal-semantic carrier, so global minimality gives
the reverse inequality.  Every coordinate gap in (19) is nonnegative and
their finite sum is zero.  Hence each gap vanishes, proving (9)--(10).

Because all debt coordinates are nonnegative and both mixture coefficients
are positive, (11) follows.  Equation (4) makes `j` belong to the support of
`H_theta` but not that of `Z`, proving (12).

### Step 5: same-law source regeneration

The joint points `(Z,nu_Z)` and `(H_theta,nu_theta)` belong to the joint
carrier, have debt `D_*`, and carry the named atom `T` with positive mass.
Apply
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` directly
to each point and terminal `T`.  Combining the returned causal chronology
with the unchanged table-level hard residual gives a complete
`FinFourMinimumAtomProducer` at each exact joint law.

### Step 6: maximal support

The class `M` is nonempty.  Only finitely many support cardinalities are
possible, so a largest attained cardinality exists; no compactness of the
strict-positive-atom condition is required.

If `Y` attains that cardinality, then `H_theta in M`.  Equation (11) contains
the support of `Y`, so maximality forces the union to equal the support of
`Y`.  Thus the support of `Z` is contained in that of `Y`.  Coordinate `j` is
positive at `Y` and zero at `Z`, so the containment is strict, proving (13).

### Step 7: retain the paid rectangle on the proper chord

Mixing player `j` commutes with changing the distinct mover `p`, proving the
literal update assertions in Part 4. Terminal payoff is affine in one
player's stopping law. Put

\[
 g_{0,n}=U_p(E_n)-U_p(S_n),\qquad
 g_{1,n}=U_p(E_n^q)-U_p(S_n^q).
\]

Then

\[
 U_p(E_{n,\theta})-U_p(S_{n,\theta})
   =(1-\theta)g_{0,n}+\theta g_{1,n}.
\]

Bounded rewards give `g_(1,n)>=-2M`, while (0a) gives `g_(0,n)>=g`.
The last display is therefore at least

\[
 g-\theta(g+2M)\ge g/2
\]

under (15), proving (16). The two observer payoffs are affine under the same
mixtures, and applying the full response overwrites the mixture by its
response endpoint. Expanding and cancelling gives (17). The terminal-law atom
used in Parts 1--2 is attached to the unchanged full-response pair
`E_n^q,S_n^q`, so it is retained without a new selection.

## Periodic-rank boundary

In the all-minimum paid-cycle arm, the same law-retention argument regenerates
a complete source at every literal cycle vertex: the displayed pure coalition
has law mass at least `lambda` at its own joint limit.

The initial and final cycle profiles are literally equal.  Hence their
semantic debt vectors, supports, coalition and deterministic outgoing-mover
labels, complete terminal laws, and hard residual all return exactly.  No
strict rank determined only by those periodic data can decrease on every
cycle edge.  A successful orientation must retain some nonperiodic datum,
such as the response witness plus an executable vertical chronology, or prove
that a purported cycle vertex is off the minimum fibre.

This does not rule out ranks carrying additional chronological or response
data.

## Boundary tests

### The positive response atom is essential

Without the positive endpoint-response/source-response atom, a pure response
may occur before the marked date.  It then screens the source/endpoint
difference and gives no retained marked coalition.

### The endpoint coalition must remain nonempty after routing

For a pure singleton owned by the response player, a Continue response erases
the only quitter and exposes the tail.  The no-loss marked-atom conclusion is
therefore specific to a nonsingleton endpoint coalition.

### Both endpoint limits must be minimum

If `D(Y)=D_*` but `D(Z)>D_*`, convexity gives only

\[
 D(H_\theta)
 \le(1-\theta)D_*+\theta D(Z),
\]

which does not place `H_theta` on the minimum fibre and does not force
coordinate affinity.

### Maximum support at the incoming source is insufficient

The abstract pattern

\[
 d(X)=(1,0,0,0),\qquad
 d(Y)=(0,1,0,0),\qquad
 d(Z)=(0,0,1,0)
\]

shows that knowing only that an unrelated incoming point `X` has a selected
support property gives no inclusion between `Y` and `Z`.  The maximal-support
hypothesis in (13) must apply to the actual chord endpoint `Y`.

### The support drop is not renewable

Regeneration at `Z` gives actual causal tails converging to `Z`.  The next
forced-pair construction prefixes a new marked row and may compactify to a
whole-profile cluster whose support is not contained in that of `Z`.  Thus
(12) or (13) is a one-time handoff, not an iterative rank theorem.

## Source correspondence

The common response and its endpoint-debt estimate are in

```text
HasQuittingStoppingLawVanishingDebtAtomAlternative
hasVanishingDebtAtomAlternative_of_endpointDebtRise
```

from
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`.
The rectangle disjunct's positive atom compares the endpoint-response and
source-response profiles used in Step 1.

Exact law affinity and coordinate debt convexity are

```text
quittingTerminalOutcomeMass_stoppingLawMixture_eq
quittingTerminalSemanticDebt_stoppingLawMixture_le
```

in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`.
The exact minimum-fibre version is

```text
quittingTerminalSemanticDebt_stoppingLawMixture_eq_of_minimum_sameDebtSum
```

in `TerminalSemanticStoppingLawMinimumFiberAffine.lean`.

Same-point law causalization is

```text
exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom
```

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`.
The existing endpoint-law packaging is

```text
ConcentratedCollisionThreeRoleEndpointLaw
ConcentratedCollisionThreeRoleEndpointLaw.nonempty_finFourRegenerationOrAscent
FinFourThreeRoleMinimumTargetRegeneration
```

in `Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean` and
`Research/Quitting/FinFourProducerAtlas/ThreeRoleRegeneration.lean`.

The new proof obligations are the before-mark response law equality, the
no-loss routed response stage atom, simultaneous endpoint/response/chord
compactification, and dependent packaging of the two regenerated sources.

## Adapter and consumer

The actual-data adapter is the rectangle arm produced on the frozen
spectator-recharge edge of
`PAID_NONSINGLETON_CYCLE_SPECTATOR_RECHARGE_AND_ATOM_DISPATCH.md`.  It supplies
the literal siblings, fixed mover and observer, fixed marked-mass floor,
positive response atom, vanishing endpoint-response debt, and the actual
joint endpoint sequences.  The all-minimum subarm supplies (3)--(4).

The output removes two source-provenance questions: the response endpoint and
its union-support chord parent both have their own actual laws, named atoms,
and complete regenerated minimum sources.  The downstream orientation remains
open because no checked field confines the next paid whole-source cluster to
the support of the regenerated child.

## Lean handoff

Suggested local declarations are:

```text
pureTimeResponse_not_lt_mark_of_positive_endpointDifferenceAtom
rectangleResponse_routedStageMass_ge_liveMass
QuittingMinimumResponseChordJointPoint
QuittingMinimumResponseChordJointPoint.nonempty_finFourSources
QuittingMinimumResponseChordJointPoint.support_union
```

The first theorem should use literal off-date equality of the source and
endpoint siblings and the fact that a positive payoff-difference atom cannot
come from equal terminal laws.  The second should split the pure time into
`q=t`, `q>t`, and Never, use nonsingleton routing, and compare live masses
after forcing the observer to Continue before the mark.

The chord theorem should retain the actual endpoint and response laws through
one common compact subsequence, use the checked law-affinity and debt-convexity
lemmas, and invoke causalization only after proving the exact minimum and
positive named-atom fields.

## Scope and nonclaims

The theorem does not:

- orient the paid cycle or response chord chronologically;
- prove that the fresh causal chronology contains the old paid edge;
- make the one-time support drop renewable;
- identify the paid whole-source cluster with the incoming source point;
- prove maximum support of the actual chord endpoint `Y`;
- consume the strict off-minimum response arm;
- construct a cumulative admissible return, terminal approximation, or
  uniform-equilibrium payoff; or
- produce or rule out a positive-gap reward table.

It proves that, in the all-minimum response arm, actual-law realization and
finite-atom source regeneration are available at the response endpoint and
every interior response-chord point.  The remaining problem is orientation,
not source existence.
