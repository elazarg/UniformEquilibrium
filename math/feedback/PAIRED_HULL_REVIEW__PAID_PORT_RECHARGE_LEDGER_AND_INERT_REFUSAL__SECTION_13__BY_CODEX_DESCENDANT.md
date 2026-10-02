# Review of Section 13: receiving-earlier causal absorption and one-refusal completion

Reviewer: `CODEX_DESCENDANT`

Date: 2026-09-01

Verdict: **REVISE.**  The orientation-specific absorption floor, the
three-free-player Nashification, the one-refusal identity, and the eight-cell
split are sound.  The nonempty-cell arm overstates cap attainment: for an
arbitrary infinite post-mark suffix, the observer's unrestricted behavioral
cap need not be attained by one literal response.  The valid output is an
arbitrarily small observer-debt sequence, or a zero-debt joint-carrier cluster
after compactification.  This does not affect the preceding exact identities,
but it does affect the claimed literal target and source adapter.

## Claim checked

In the receiving-earlier orientation of a quantitative paid row, the receiving
observer $i$ Quits surely at the marked date.  If $\ell$ is opponent
survival to that date and the paid gain is $g$, Section 13 claims:

1. actual marked-row absorption is $\ell\ge g/(2M)$;
2. fixing $i$ to Quit and taking a product Nash point of the induced binary
   game on the other three players yields a literal first-row-absorbing suffix
   $Z$ with zero unrestricted debt for every nonowner;
3. positive global minimum then forces the entire debt of $Z$ into $i$,
   so $d_i(Z)=D(Z)\ge D_*$;
4. one of the eight free-quitter cells has positive weighted owner refusal at
   least $D_*/8$, hence probability at least $D_*/(16M)$; and
5. a nonempty selected cell gives a literal owner-Continue target with zero
   mover debt, whereas the empty cell is a cap/tail seam.

## Steps that pass

### The marked absorption is actual and has the asserted orientation

When `receivingEarlier` holds, the receiving pure time is the marked date.
The observer has Continued surely before that date and Quits surely there.
Thus the joint reach of the marked date is exactly the opponents' survival
$\ell$, and conditional absorption is one.  The unconditional absorption
is therefore exactly $\ell$.  The checked live-mass inequality
$g\le2M\ell$ gives the stated floor.  This argument does not misuse a
terminal atom as row mass and does not apply in the later-receiving arm.

### Complement Nashification controls unrestricted strategies

With $i$ sure-Quit at the first shifted row, the continuation suffix is
unreachable under the prescribed profile.  For every free player $j$, an
arbitrary behavioral deviation matters only through its binary action at
that first live history.  If $x$ is a mixed Nash equilibrium of the finite
three-player binary game

\[
u_j(A)=r_j(\{i\}\cup A),
\]

then no unrestricted behavioral replacement of $j$ improves its payoff.
Hence $d_j(Z)=0$ for all $j\ne i$.  This is a full behavioral-cap
statement, not merely root Nash.

Since $Z$ is an actual profile, $D(Z)\ge D_*>0$.  Debt nonnegativity then
gives exactly

\[
d_i(Z)=D(Z)\ge D_*.
\]

The owner cap conditional on Continuing at the first row is

\[
\sum_{A\ne\varnothing}p(A)r_i(A)
+p(\varnothing)B_i(\sigma^+).
\]

Because the owner has positive debt, this value is larger than its prescribed
Quit value.  Therefore the displayed identity

\[
d_i(Z)=\sum_Ap(A)(C_i(A)-Q_i(A))
\]

is correct at the level of supremum values; it does not require attainment.

### The cell constants are correct

Eight terms sum to at least $D_*$, so some fixed cell has weighted
contribution at least $D_*/8$.  Both a terminal reward and an unrestricted
cap lie in the reward box, hence

\[
|C_i(A)-Q_i(A)|\le2M.
\]

For the selected positive term this gives

\[
p(A)\ge {D_*\over16M}.
\]

If $A\ne\varnothing$, changing $i$'s marked action from Quit to Continue
does route that literal cell from $\{i\}\cup A$ to $A$, preserving its
positive row absorption.  If $A=\varnothing$, the change reaches the
post-mark suffix and supplies only a cap/tail seam.  This split is exhaustive.

### The copied-prefix qualification is exact

Replacing the marked root while copying every earlier root and the literal
post-mark suffix gives an actual whole profile with the same marked reach
$\ell$.  The zero-debt claims concern the shifted suffix $Z$, not the
whole copied-prefix profile; pre-mark deviations can create additional debt.
Section 13 states this limitation correctly.

## Required repair: the observer cap need not be attained

The sentence in the nonempty-cell arm asserting a literal one-player target
whose mover debt is zero does not follow from the supplied data.  The value
$B_i(\sigma^+)$ is the supremum over all behavioral responses to an arbitrary
infinite suffix.  No exact cap-attaining response is supplied.

This is a real infinite-clock boundary, not a technicality.  Against an
opponent with unbounded finite stopping support and positive Never mass, take
the observer's payoff to be $2$ when that opponent quits first and its own
singleton payoff to be $1$.  The values of later and later finite Quit
times can increase to

\[
2\Pr(\text{opponent eventually Quits})
+\Pr(\text{opponent Never}),
\]

while Never itself gives only the first term.  With no last finite support
time, the supremum is not attained by any pure time; behavioral mixing cannot
exceed the same supremum.  Such a suffix can be placed behind the all-free-
Continue cell without affecting the finite induced game at the marked row.

The valid repair is one of the following.

1. For every $\varepsilon>0$, choose an $\varepsilon$-cap response after
   owner-Continue.  The resulting literal target has owner debt at most
   $\varepsilon$, and the nonempty selected cell still has mass at least
   $D_*/(16M)$.
2. Along $\varepsilon_n\downarrow0$, jointly compactify the complete
   semantic pairs and terminal laws of those literal targets.  The resulting
   carrier point has zero owner debt and retains the nonempty cell mass.  It
   is a limit object; a separate supplied-family causalization/source wrapper
   is needed before calling it a regenerated literal source.
3. Add an explicit cap-attainment hypothesis for the observer on
   $\sigma^+$.

The first repair is purely literal but approximate; the second is exact in
the joint carrier but loses one finite ancestry code unless the existing
causalization interface is instantiated on this supplied family.

The second repair also gives the cleanest valid contraction.  In the
nonempty-cell arm, the compact target has zero owner debt and terminal
opponent incidence at least $D_*/(16M)$.  Hence it is either strictly
off-minimum, or, if its total debt is $D_*$, it enters the existing
positive-incidence reset-rigid minimum dispatch.  To call this a regenerated
source rather than only a carrier landing, the proof must apply the supplied-
family causalization theorem to the literal $\varepsilon_n$ responses and
retain the marked reach.  This routes the arm to the established
off-minimum/reset-rigid waist; it still does not consume that waist.

There is a stronger chamber contraction which does not require the selected
cell to be nonempty.  Starting from the unique-debtor suffix $Z$, choose
literal owner responses with payoff tending to $B_i(Z)$.  Each response is
one additional full replacement after the three finite free-player root
replacements used to construct $Z$.  A common semantic/law cluster $Y$ has

\[
d_i(Y)=0.
\]

If $D(Y)>D_*$, it is the existing off-minimum response target.  If
$D(Y)=D_*$, the hard-residual minimum law has a positive finite atom.  Were
the owner opponent incidence zero, that law would be supported on
$\{i\}$ and Never.  Positive singleton mass plus zero owner debt would make
the owner cap equal its singleton payoff, contradicting the minimum
singleton margin; zero singleton mass would contradict the positive finite
atom.  Therefore the minimum cluster has positive opponent incidence and
enters the reset-rigid dispatch.

Thus, after supplied-family causalization, **the entire receiving-earlier
arm** contracts to off-minimum or reset-rigid.  The eight-cell split remains
valuable because only its nonempty arm supplies a retained causal absorbing
cell; the empty-cell arm remains an obstruction to producing charge, but not
to the chamber landing.

## Falsification boundaries

- The finite Nash equilibrium may be all free players Continuing surely.
  Then the selected positive cell can be $A=\varnothing$, and the theorem
  ends in the inert cap/tail seam.  Positive minimum does not exclude this.
- In the nonempty arm, after the owner changes to Continue the free players'
  old Nash inequalities can reverse because their terminal coalition changes
  from $\{i\}\cup A$ to $A$.  The target is not a Nash row.
- Recomputing a complement Nash point around a new sure-Quit anchor is a
  simultaneous horizontal reselection.  It need not preserve old zero debts,
  the selected cell, or literal target-to-next-source identity.  Hence no
  renewable unsafe-player rank follows.

## Consequence and novelty

After the attainment repair, Section 13 is a genuine strengthening of the
orientation-free participant-safe atom certificate.  It proves that the
receiving-earlier arm has a co-realized causal absorption floor and reduces
simultaneous safety completion to one macroscopic owner refusal.  The refusal
then localizes to either a positive-mass nonempty leave cell or the precise
all-free-Continue tail seam.

It does **not** consume the quantitative paid port.  Even in the nonempty arm,
the free-player defects after owner-Continue are uncontrolled, and the exact
zero-debt target requires compactification or an added attainment hypothesis.
The absent renewable datum remains literal target-to-next-source typing under
subsequent safety completion.

## Delta review of Sections 15--16

### Verdict

**PASS, with one source-interface qualification.**  The nonempty-cell support
contraction and the empty-cell coordinate identity are correct.  They sharpen
the split but do not consume its remaining line.

### Nonempty cell

For every literal response profile \(Y_n\), the marked coalition is exactly
\(A\) with mass at least \(D_*/(16M)\).  If \(A\) is a singleton, this is the
input of
`FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass`.
If \(|A|\ge2\),
`quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint` applies
directly to this arbitrary actual profile: its hypotheses require a global
positive minimum and the displayed stage-mass floor, not near-minimality of
\(Y_n\).  Its terminal orbit has at most three strict edges in Fin4 and retains
the requested floor at a literal singleton endpoint.  This is enough to build
the same strong packet and invoke the existing strategic-versus-collision-
minimum consumer after the minimum source/hard residual is supplied.

The exact qualification is that the direct screened endpoint is attached to
the literal \(Y_n\), whereas the typed atlas consumer is indexed by a complete
`FinFourMinimumAtomProducer`.  In the minimum-cluster arm this producer is
obtained from the supplied \(Y_n\)-family by causalization; in an off-minimum
arm one must not describe the \(Y_n\) themselves as a new minimum producer.
The note's minimum-cluster ordering respects this distinction.

### Empty cell

Let \(c=p(\varnothing)\).  For the root \((i\text{ Continue},x)\), the owner
has zero *root* defect because Continue is the better endpoint against the
response-tail cap.  Coordinatewise cap-prefix debt scaling therefore gives
exactly

\[
d_i(Y_\varepsilon)=c\,d_i(\sigma^+_\varepsilon).
\]

The already proved response bound \(d_i(Y_\varepsilon)\le\varepsilon\) and
\(c\ge D_*/(16M)\) imply the stated tail bound and hence zero \(i\)-debt at
every compact minimum cluster.  Exact cap attainment is not being smuggled
back in: the argument is uniform along the literal
\(\varepsilon\)-best-response family.

If the tail cluster is off minimum, it is an actual-profile entrance to the
generic off-minimum paid port.  If it is minimum, a joint law subsequence and
the maintained hard residual supply a positive finite atom, and supplied-
family causalization prefixes the same literal tails.  Exact prefix scaling
preserves the limiting zero \(i\)-debt.  To call this an outer transition, the
wrapper must retain the preceding response profiles as siblings of these
tails; causalization alone does not turn the horizontal owner replacement
into a Nash--Bellman edge.

The final nonclaim is necessary.  A later owner replacement changes an
opponent strategy for \(i\), so \(i\)'s cap and debt can reactivate.  The
current zero is preserved into its immediate literal successor, but old zeros
are not preserved through a new owner phase.  Thus Sections 15--16 give a
real support contraction in the nonempty arm and a real one-step killed-owner
transition in the empty arm, not a renewable zero-set rank.
