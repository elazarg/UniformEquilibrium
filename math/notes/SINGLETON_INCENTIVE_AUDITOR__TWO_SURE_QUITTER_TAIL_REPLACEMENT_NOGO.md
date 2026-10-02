# Two-sure-quitter tail replacement cannot create minimum return

Author: `SINGLETON_INCENTIVE_AUDITOR`

## Status

Complete ordinary-mathematics no-go.  It applies to the collision mode of the
source-attached strong singleton packet and eliminates two natural sequential
repairs: obtaining whole-profile near-minimality merely by replacing the
marked continuation, and telescoping the singleton owner's tail gap with the
forced outsider collision.  The second collision changes the relevant
counterfactual and destroys the tail-cap channel exactly.

The statement quantifies over arbitrary behavioral tails and arbitrary
unilateral behavioral deviations.  It is not Lean-checked as one composed
semantic-pair theorem.  The root-level survival fact is already represented by
`QuittingTwoPairGateRoles.secondRoot_update_continueMass_eq_zero` in
`UniformEquilibrium/Quitting/Chronology/TwoPairClockBoundary.lean`.

## Theorem

Let \(I\) be finite.  Fix a finite executable prefix through a marked date
\(t\).  At date \(t\), suppose two distinct players \(a,b\) Quit surely.  All
other coordinates of the marked product root may be arbitrary.

For any two complete behavioral tails \(\tau,\tau'\), let \(P\triangleright
\tau\) and \(P\triangleright\tau'\) denote the profiles with this common
prefix and the indicated continuation after the all-Continue outcome at the
marked row.  Then

\[
\boxed{
\operatorname{Sem}(P\triangleright\tau)
=
\operatorname{Sem}(P\triangleright\tau').}
\tag{1}
\]

In particular, their prescribed payoffs, all unrestricted behavioral
best-response caps, coordinate debts, and total debts are exactly equal.

## Proof

Under prescribed play, conditional on reaching the marked row, both \(a\)
and \(b\) Quit.  The row therefore absorbs with probability one, and the tail
is not reached.

Fix a player \(i\) and replace its complete behavioral strategy by an
arbitrary deviation.  If \(i\notin\{a,b\}\), the prescribed strategies of
both \(a\) and \(b\) remain, so both still Quit surely at the marked row.  If
\(i=a\), player \(b\) remains a sure quitter.  If \(i=b\), player \(a\)
remains a sure quitter.  Thus, under every unilateral deviation, at least one
prescribed sure quitter remains and the marked row still absorbs with
probability one conditional on reach.

The two profiles agree before and at the marked row.  Hence their terminal
payoffs agree under prescribed play and under every fixed unilateral
behavioral deviation.  Taking the supremum over all deviations preserves
equality, proving (1).

The proof includes Never, arbitrarily late deterministic stopping, randomized
stopping laws, and history-dependent behavior: none can remove both distinct
prescribed sure quitters.

## Application to the strong concentrated collision

Start from an owner-compressed singleton row \(\{j\}\) and update a distinct
packet owner \(o\) to its exact best Boolean endpoint.  In the collision mode,
that endpoint is Quit.  Thus \(j\) and \(o\) both Quit surely at the marked
row.

Replacing the continuation after that row by a minimum-approaching reference
profile is useful: it makes the *literal post-row tail debt* tend to \(D_*\),
which removes the off-minimum tail-cluster alternative in
`QuittingConcentratedCollisionMinimumResidual`.

But (1) shows that this replacement cannot alter the semantic pair of the
*whole collision profile* at all.  Therefore it cannot manufacture

\[
D(\text{collision profile})\le D_*+\varepsilon
\tag{2}
\]

unless (2) was already true before the replacement.  The whole-source
near-minimum premise of the existing three-role transfer consumer cannot be
obtained from self-tail closure, two-anchor tail closure, or any other change
made strictly after the two-sure-quitter row.

## Exact scope

This no-go does not prevent a construction that changes roots before the
marked collision, proves their whole semantic debt near-minimal by an
independent account, or uses only the minimum-return tail data.  It rules out
only the exhaustive route

\[
\text{two-sure-quitter collision}
+\text{near-minimum replacement tail}
\Longrightarrow
\text{near-minimum whole source}.
\]

It also explains the asymmetry in the current minimum-return packet: the tail
can be repaired exactly, while the current collision debt and pre-row cap
effects are frozen.

## The singleton-to-collision channel switch

The same calculation rules out a second tempting composition: first use a
punishment tail to control the singleton owner, and then add the forced
outsider collision as if the two gains were successive charges.

Start the profile at the pure singleton row \(\{j\}\), followed by an actual
tail \(\tau\).  The complete all-behavior debts at this suffix are exactly

\[
d_j=\bigl[B_j(\tau)-r_j(\{j\})\bigr]_+,
\qquad
d_i=\bigl[r_i(\{i,j\})-r_i(\{j\})\bigr]_+
\quad(i\ne j).
\tag{3}
\]

Thus punishment normality can act only through the first coordinate in (3):
an approximate \(j\)-punishment can make the owner term arbitrarily small,
while every outsider term is literally unchanged.  This is the semantic
content behind the checked atomic-blocker completion and the full-gap
collision handoff in
`PunishmentNormalAtomicCollision.lean`.

Now force one outsider \(k\ne j\) to Quit at the same row.  The quitting
coalition becomes \(\{j,k\}\).  Formula (1) shows that the whole continuation
is now invisible, and the debts become the finite toggle defects

\[
\begin{aligned}
d_j&=\bigl[r_j(\{k\})-r_j(\{j,k\})\bigr]_+,\\
d_k&=\bigl[r_k(\{j\})-r_k(\{j,k\})\bigr]_+,\\
d_i&=\bigl[r_i(\{i,j,k\})-r_i(\{j,k\})\bigr]_+
\quad(i\notin\{j,k\}).
\end{aligned}
\tag{4}
\]

In particular, the former owner-refusal term
\(B_j(\tau)-r_j(\{j\})\) is not transported into (4).  If \(j\) deviates at
the collision row, \(k\) still Quits and the alternative payoff is
\(r_j(\{k\})\), not the tail cap \(B_j(\tau)\).  The punishment channel and
the collision channel are mutually exclusive counterfactuals at the same
history.

Consequently the implication

\[
\text{positive singleton owner-tail gap}
+\text{positive outsider join gap}
\Longrightarrow
\text{two successive chronological charges}
\tag{5}
\]

is false as an accounting principle.  The join update may still be useful:
if the pair in (4) is toggle-stable it is an exact terminal equilibrium, and
otherwise it launches the finite horizontal toggle problem.  What it cannot
do is retain the owner-tail charge for later expenditure.  Any successful
consumer must therefore spend the tail gap *before* creating the second sure
quitter, or obtain progress solely from the finite collision geometry after
the channel switch.
