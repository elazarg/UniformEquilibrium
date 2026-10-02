# Finite clock clearing eliminates the fully screened forced-pair arm

Author: `CODEX_AMPERE`

## Status

Ordinary mathematics, not checked in Lean.

This note gives an actual-data producer for the fully screened arm of
`FIN4_ACTUAL_ZENO_DELETED_SURVIVAL_HOST_OR_FULL_SCREENING.md`.  Under the
terminal exploitability witness, a finite common prefix in front of the
retained pure pair can be cleared one player at a time.  At each step one of
three things happens:

1. a deleted-survival host already exposes the original marked pair at fixed
   mass;
2. a finite pure-time witness produces a new fixed-mass premark atom, with a
   positive literal source-to-target gain and zero marked mover defect; or
3. forcing one previously uncleared player to Continue through the prefix is
   itself a fixed positive unilateral gain.

The third alternative can occur at most four times.  Hence the fully screened
arm cannot persist:

\[
\boxed{
\text{finite prefix before the source pure pair}
\Longrightarrow
\text{fixed-resolution source-attached concentrated packet after at most four paid clears}.}
\]

This is stronger than merely forcing all four players to Continue, which
would manufacture a strategically empty pure row.  Every **iterative** clock
clear in the low-deleted-survival branch is an actual profitable unilateral
change.  The terminal host compression need not itself be profitable; no such
claim is needed, because the original pair's historical paid sibling and zero
marked-owner defect survive.  If the process ends at a premark date, that last
one-date change is profitable and its marked mover is exactly best responding
at the new root.  The resulting terminal atom is then converted, according to
its cardinality, to the existing generic recurrent concentrated-packet
interface.  It is not asserted to be a
`FinFourAtlasConcentratedSingletonEndpoint`.

The result does not consume the resulting concentrated packet.  In
particular it does not prove target-side near-minimality or control the other
three whole-profile caps.  Its conjecture-facing content is the removal of
**full screening as a separate normalized-passport/Zeno residual**.

## Question

Let an actual descendant of the fixed Fin4 forced-pair source have the form

\[
W*(\text{pure pair})*(\text{retained tail}),
\]

where `W` is the **new arbitrary prefix word** and the displayed forced-pair
base may itself contain a finite source chronology before its pure pair.
Suppose all four deleted reaches through `W` are small.  Does the positive terminal gap
force a fixed-mass event before the invisible pair, or can the screening word
persist after source-faithful modifications?

The theorem below gives the first answer.  It uses the terminal gap on each
literal modified profile; it does not infer a large atom from the original
diffuse word.

## Sources inspected

- `Research/Quitting/NormalizedPassportPrefixOrbit.lean`, especially the
  literal descendant profiles, shifted marks, exact postmark spine, and common
  prefix scaling identities;
- `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean` and
  `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean` for the fixed
  pure pair, comparison sibling, marked-owner defect, and source attachment;
- `Research/Quitting/PureTimeWitnessEscapeDichotomy.lean` and the underlying
  pure-time best-response representation;
- `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` for the exact
  one-root endpoint factorization;
- `exports/FIN4_ACTUAL_ZENO_DELETED_SURVIVAL_HOST_OR_FULL_SCREENING.md`; and
- `exports/FIN4_FULLY_SCREENED_TIMING_NASH_RETURN_FLOOR_NO_GO.md`.

The timing-Nash result says exact Nashification cannot retain full screening,
but its all-Continue equilibrium can be the useless identity block.  The
result here instead keeps the given literal word and extracts a finite paid
clearing chain followed either by a paid premark atom or by exposure of the
already-paid historical forced pair.

## 1. Finite source data

Let rewards be bounded by `R>0`:

\[
|r_i(C)|\le R.
\]

Assume a terminal exploitability witness `gamma>0`:

\[
\forall\sigma,\qquad \max_i d_i(\sigma)\ge\gamma .       \tag{1}
\]

Every deviation payoff and prescribed payoff lies in `[-R,R]`, so necessarily
`gamma <= 2R`.

Fix one actual forced-pair source row.  Write its comparison and target base
profiles as `beta^0,beta^1`.  They have the same behavior away from the fixed
marked update.  In `beta^1`, one fixed pair is pure at its marked date.  Assume
the base marked-pair mass has the retained floor

\[
\Pr_{\beta^1}(\text{marked pair})\ge\rho>0.              \tag{2}
\]

The base source-to-pair gain also has its retained positive floor.  Strictly
after the base mark lies the retained literal reference tail.

Let the newly adjoined arbitrary prefix be the finite word

\[
W=(q_0,\ldots,q_{T-1}).
\]

Thus the actual decorated siblings are `W*beta^0,W*beta^1`.  Keeping `W`
separate from the base chronology is essential: only changes to this newly
adjoined word remain raw descendants of the same normalized prefix orbit.
The original source packet retains its pair label, positive source-to-pair
table gap, zero coordinate defect at the marked pair, and complete postmark
tail.

For a set `A` of already cleared players, let `W^A` be the word obtained by
replacing

\[
q_t(i)\quad\text{by pure Continue whenever }i\in A,       \tag{2a}
\]

at every `t<T`.  Apply the same word replacement to both forced-pair
siblings.  Thus every `W^A` is still a literal arbitrary-prefix descendant of
the same source rank, with the same pair, labels, postmark tail, and comparison
sibling.

Write `sigma_A` for its target profile.  For each player `i`, put

\[
H_i^A
 :=\Pr(\text{every opponent of }i\text{ Continues through }W^A). \tag{3}
\]

Set

\[
\eta:=\frac{\gamma}{16R},\qquad
\lambda:=\rho\frac{\gamma}{128R}.                        \tag{4}
\]

Both are positive, and `eta<=1/8`.

## 2. Host exit

Suppose some player `h` has

\[
H_h^A\ge\eta.                                             \tag{5}
\]

Clear `h` through the whole **adjoined** word.  This final compression is not
asserted to improve `h`'s payoff.  The probability of reaching the base
profile is now exactly `H_h^A`.  Conditional on that return, the base
pair still has its old mass at least `rho`.  Hence the original pair's
unconditional stage mass is at least

\[
\rho H_h^A\ge\rho\eta>\lambda.                           \tag{5a}
\]

No endpoint at the pair has to be reselected.  The target remains the same
forced pure pair.  Consequently the construction retains literally:

- the original pair label;
- the original comparison sibling and its fixed table-gap payment;
- the original zero marked-owner defect;
- the complete postmark behavioral tail and law; and
- the source rank and every remaining root of the premark word.

The historical source-to-pair gain is multiplied by the new joint reach
`H_h^A`, so it also has a fixed positive floor.  Thus payment comes from the
retained pair comparison, not from the last host compression.  This is the
strong form of the earlier host compression for the forced-pair packet.

## 3. The clearing-versus-premark-atom lemma

Assume instead

\[
H_i^A<\eta\qquad\text{for every }i.                       \tag{6}
\]

Apply (1) to the actual profile `sigma_A`.  Choose a player `i` with
`d_i(sigma_A)>=gamma`.  By the unrestricted pure-time representation of the
behavioral cap, choose either `Never` or one deterministic quitting date whose
gain over prescribed play is greater than

\[
\frac{3\gamma}{4}.                                       \tag{7}
\]

Let `c_i sigma_A` be the profile obtained by forcing only player `i` to
Continue at every row of `W^A`, and then restoring its prescribed strategy
literally on entry to the entire base profile `beta^1`.  All opponents remain
unchanged.  This is exactly `sigma_{A union {i}}`.

There are two alternatives.

### Paid clock clear

If

\[
U_i(c_i\sigma_A)-U_i(\sigma_A)\ge\frac\gamma2,            \tag{8}
\]

record the actual unilateral paid move and replace `A` by `A union {i}`.

The selected player is new: if `i in A`, then `c_i sigma_A=sigma_A`, so (8)
is impossible.  Because only `i`'s own prescribed strategy changed, its
unrestricted best-response envelope is unchanged and its whole-profile debt
falls by exactly the gain in (8).

The same coordinate clearing on the comparison sibling preserves the
arbitrary-prefix provenance.  It weakly increases the old marked-pair mass,
and the historical source-to-pair gain increases by the same joint-survival
factor.

### Paid premark atom

Suppose (8) fails.  The selected witness in (7) cannot be `Never`, and a
finite selected date cannot satisfy `t>=T`.  Here `T` is the end of the
**adjoined** word, not the later base marked date.  Indeed, `Never` and every
post-prefix pure time differ from the clearing strategy only on the event that
all opponents survive `W^A`.  By (6), their payoff difference from the
clearing strategy has absolute value at most

\[
2R H_i^A<2R\eta=\frac\gamma8.                            \tag{9}
\]

Together with the failure of (8), this contradicts (7).

Hence the selected pure quitting date satisfies `t<T`.  Modify it harmlessly
after date `t` so that, if the prescribed Quit at `t` were counterfactually
replaced by Continue, it follows the literal suffix of `c_i sigma_A`.  Call
the resulting target `pi`.  This modification does not change the selected
pure-time payoff, because the player Quits surely at `t` whenever that suffix
could be reached.

The comparison and target profiles now agree before `t`, agree strictly after
`t`, and differ only in player `i`'s action at `t`: Continue in
`c_i sigma_A`, Quit in `pi`.  From (7) and the failure of (8),

\[
U_i(\pi)-U_i(c_i\sigma_A)>\frac\gamma4.                  \tag{10}
\]

Let `G_i(t)` be the probability that every opponent survives to the live root
at date `t`.  Exact one-row factorization gives

\[
U_i(\pi)-U_i(c_i\sigma_A)
 =G_i(t)\,[Q_i(t)-C_i(t)].                               \tag{11}
\]

The endpoint difference is at most `2R`, so

\[
G_i(t)>\frac{\gamma}{8R}.                                \tag{12}
\]

Player `i` Quits surely at that root.  Conditional on reach, the three
opponents generate only `2^3=8` coalitions.  One nonempty terminal coalition
containing `i` therefore has unconditional stage mass greater than

\[
\frac{\gamma}{64R}>\rho\frac{\gamma}{128R}=\lambda.      \tag{13}
\]

Equation (11) is positive, so Quit is the strict better Boolean endpoint for
`i`.  The target's marked `i`-coordinate root defect is exactly zero.  The
comparison and target retain the same literal postdate tail, and (10) is a
fixed positive actual source-to-target payoff gain.  Thus (13) is a genuine
concentrated stage-atom producer, not an unpaid atom selected elsewhere on the
table.  Section 5 gives the exact cardinality-sensitive packet adapter.

## 4. Finite termination

Start with `A=empty`.  At each stage:

1. if some `H_h^A>=eta`, take the host exit of Section 2;
2. otherwise apply Section 3;
3. if the premark-atom arm occurs, stop;
4. otherwise add one new player to `A` by a paid clock clear.

The fourth step can occur at most four times.  These, and only these iterative
steps, are claimed to be paid.  If all four players have been
cleared, then every `H_i^A=1`, so the host exit applies (the base profile is
entered surely, and its old pair retains mass at least `rho`).  Therefore the
algorithm terminates after at most four paid clears and returns an actual
positive stage atom of mass at least `lambda`, together with a marked
zero-defect owner either directly or after one best-endpoint route.

The construction is uniform in the length of `W`.  Applied termwise to a
fully screened Zeno actualizer sequence, finite pigeonhole permits one strict
subsequence on which the following data are fixed:

- the number and ordered labels of paid clears;
- host versus premark-atom exit;
- in the atom arm, the marked mover and terminal coalition; and
- all forced-pair labels already fixed by the incoming packet.

Calendar dates may still move; the mass and gain floors do not.

## 5. Exact output and packet adapter

For every actual fully screened forced-pair descendant, the construction gives
one of:

\[
\begin{array}{ll}
\textbf{forced-pair host:}&
\text{the original pair at mass }\ge\lambda,
\text{ with all original packet fields;}\\[1mm]
\textbf{premark atom:}&
\text{a terminal atom at mass }\ge\lambda,
\text{ zero marked mover defect,}\\
&\text{literal postdate-tail equality, and gain }>\gamma/4.
\end{array}                                               \tag{14}
\]

The output used downstream is a generic
`QuittingReprojectionConcentratedPacket`, constructed as follows.  This
cardinality split is essential: an arbitrary premark atom is not directly a
Fin4 singleton-atlas endpoint.

### Premark nonsingleton

Let `C` be the coalition from (13).  It contains the marked mover `i`.  If
`|C|>=2`, repeat the literal target `pi` constantly, take packet owner `i`,
terminal `C`, cutoff `t+1`, mark `t`, identity subsequence, and any positive
scale tending to zero (canonically `1/(n+1)`).  The stage mass is at least
`lambda`, the semantic-prefix incidence follows from its positivity, and the
normalized marked-owner defect is identically zero because Quit is the exact
better endpoint for `i`.  These fields directly define a constant generic
`QuittingReprojectionConcentratedPacket`.

### Premark singleton

If `C={i}`, choose one outsider `o != i`.  Apply
`QuittingStageAtomConcentratedPacketAdapter` to the actual atom with packet
owner `o`.  Its required condition `C != {o}` holds.  The adapter changes only
`o` at the same date to its exact better endpoint, routes the atom without
loss to a nonempty coalition, makes the marked `o`-defect exactly zero, and
its existing `packet` constructor repeats the target as a generic
`QuittingReprojectionConcentratedPacket`.  The new routed coalition may be the
same singleton or the pair `{i,o}`; no singleton conclusion is claimed.

### Forced-pair host

Repeat the exposed original pair target constantly with its already stored
zero-defect marked owner, cutoff one past the base mark, the base mark itself,
identity subsequence, and scale `1/(n+1)`.  Its mass is at least `lambda` and
its normalized marked-owner numerator is identically zero.  This directly
defines the same generic concentrated packet while retaining the historical
paid sibling and full forced-pair source provenance.  The final host
compression need not be a paid edge.

All three packet constructions store the incoming minimum source and the
complete finite chain of actual modifications as external provenance.  In the
premark arm the new marked tail need not be on the minimum fibre.  In the host
arm the whole target need not be near the minimum.  Thus (14) and its packet
adapter do not by themselves imply a support drop, admissible return, terminal
approximation, or uniform payoff.

What (14) does establish is that the scalar Zeno boundary has no additional
fully screened escape once the positive terminal gap is used dynamically.
The remaining obligation is the already named source-attached generic
concentrated-packet/collision consumer; one does not need a separate
full-screening consumer.

## Lean-facing decomposition

The proof should be factored into the following declarations rather than one
atlas-sized theorem:

```text
quittingFinitePrefix_pureTime_or_paidClear_or_concentratedAtom
quittingForcedPairPrefix_clockClearingStep
quittingPremarkAtom_to_constantConcentratedPacket
quittingForcedPairHost_to_constantConcentratedPacket
FinFourFullyScreenedForcedPair.nonempty_paidClearChain_or_concentratedPacket
FinFourNormalizedVanishingDensity.fullScreening_to_concentratedPacket
```

The first theorem is generic for a finite player type, with the `2^(n-1)`
pigeonhole constant.  The second records that coordinate clearing remains a
literal arbitrary-prefix descendant and preserves the forced-pair
gain-to-mass identity.  Only the last two declarations use `Fin 4` and the
source packet.

## 6. Adapter from the previously defined full-screening passport

The deleted reaches in
`FIN4_ACTUAL_ZENO_DELETED_SURVIVAL_HOST_OR_FULL_SCREENING.md` were defined
through the combined word consisting of the arbitrary prefix and the base
premark chronology.  Let `\widehat H_i` denote that combined deleted reach,
and let `H_i` be the deleted reach through the arbitrary word alone.  The base
opponent survival to its pair is at least its joint live mass, hence at least
`rho`.  Therefore

\[
\widehat H_i
 =H_i\,H_i^{\rm base}
 \ge \rho H_i.                                           \tag{15}
\]

Consequently `\widehat H_i -> 0` implies `H_i -> 0` for every player.  Thus
the old fully screened subsequence enters the low-`H` starting branch of the
finite clearing algorithm after discarding finitely many ranks.  No root of
the base chronology is modified, and all cleared profiles remain literal raw
decorations of the same source rank.
