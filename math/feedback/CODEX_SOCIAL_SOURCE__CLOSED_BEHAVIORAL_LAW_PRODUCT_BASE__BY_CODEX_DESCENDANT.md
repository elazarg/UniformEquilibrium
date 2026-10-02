# Second-gate review of the closed behavioral-law product-base theorem

Reviewer: `CODEX_DESCENDANT`

Date: 2026-08-31

Verdict: **PASS for Theorems 5.1 and 6.1, with one mandatory qualification.**
The one-root closure theorem and the padded full-cap realization survive
attempted falsification, including deviations before the selected root and
replacement of a member of the almost-sure pair.  The proposed strengthening
to uniform terminal-law convergence under arbitrary interventions is false
for the fixed one-row-padded realization.  Player-deleted laws do converge;
arbitrary intervention laws converge only to the moving long-padded
reference, unless the interventions are reindexed or otherwise compressed.
The false stronger sentence is not in the current author note, so it does not
block that note.  It must not be added to an export without this repair.

## Claim checked

The note proves two statements.

1. A limit of ordinary behavioral terminal laws with zero Never mass and
   zero singleton mass is exactly the law of one product root with at least
   two sure quitters.
2. If the limiting cap satisfies (B_i\ge r_i(\{i\})) for every player,
   then one all-Continue padding row followed by that root and then Never
   realizes the complete limiting prescribed payoff and unrestricted
   behavioral cap.

I checked the first-efficient-root argument, the total-variation coupling,
the padding option, deviations before the selected root, and the case in
which the deviator is one of the two sure quitters.

## The law theorem is sound

At every date before the first root satisfying (b(q)\le\delta_n a(q)),
the reverse strict inequality gives

\[
E_n\le \sigma_n/\delta_n\longrightarrow0.
\]

The local estimate (a-b\le {N\choose2}a^2) rules out vanishing absorption
at the selected efficient root.  A compact root limit with (b=0<a) must
have at least two coordinates equal to one.  Coupling the source profile to
the selected one-root profile then fails only on early absorption or failure
of the selected pair to quit together, so

\[
d_{\rm TV}(\mu_n,\nu_n)
\le E_n+1-q^n_iq^n_j\longrightarrow0.
\]

This proves the claimed product law.  The Fin4 support cardinalities
(1,2,4) are exactly (2^{|A|}) with at most two fractional coordinates
outside the sure core.

## The padded full-cap realization is sound

Fix player (i).  Compare the original opponents with opponents who Continue
until the selected calendar date, use the selected product root there, and
Never stop later.  Under the same arbitrary behavioral replacement of (i),
the induced outcomes can disagree only if an original opponent stops before
the selected date or every opponent Continues at the selected root.  The
first probability tends to zero with (E_n).  The second tends to zero even
when (i) is a sure-core member, because the other member of the stabilized
pair remains among (i)'s opponents.

This comparison is uniform over the complete unilateral behavioral class,
so taking suprema transports the cap.  A deviator who Quits before the
selected root obtains exactly the singleton reward.  A long passive prefix
therefore contributes no option beyond

\[
\max\{r_i(\{i\}),Q_i(q_{-i}),C_i(q_{-i})\},
\]

which is also the cap of the one-row-padded realization.  If the selected
date is zero, the source first gives the unpadded maximum; (B_i\ge
r_i(\{i\})) makes the added padding option neutral.  Thus the passage from
the moving selected date to one passive row is valid for scalar caps.  The
prescribed payoff and ordinary law are unchanged by passive padding.

## Boundary: arbitrary intervention-law convergence is false

The first review proposes a further claim: install the same arbitrary
behavioral replacements for a set (A) not containing the whole sure pair,
and obtain uniform terminal-law convergence from the source to the fixed
one-row-padded product realization.  The coupling only proves this for the
reference whose passive prefix has the original selected length.  Compressing
that prefix to one row changes calendar-dependent interventions.

Here is an exact regression.  Let the sure pair be (P=\{0,1\}).  For every
(n\ge2), let the source profile Continue for (n) dates, use the pure pair
(P) at date (n), and Never thereafter.  Its ordinary law is always
(\delta_P), and it satisfies the closure construction with zero early
absorption.  The fixed realization Continues once and uses (P) at date
one.

Replace only player (2) by the calendar strategy which Quits surely at date
one and Continues otherwise.  In every source profile, terminal coalition is
(\{2\}), because the pair is scheduled later.  In the fixed one-row-padded
profile, terminal coalition is (\{0,1,2\}), because the replacement meets
the pair at date one.  The two intervention laws have total-variation
distance one.  The intervention set does not contain either member of (P).

The same failure occurs when replacing a sure-core member: replace player
(0) by Quit at date one.  The long-padded source terminates at (\{0\}),
while the fixed padded profile terminates at (\{0,1\}).  Thus retaining one
unchanged sure-core member screens the tail after the selected root, but does
not erase calendar-sensitive behavior before that root.

## What does strengthen correctly

Two precise strengthenings survive.

1. Against the **moving long-padded reference** with its product root at the
   original selected date, the coupling is uniform under intervention sets
   which leave at least one stabilized sure-core member unchanged.
2. Every one-player deleted law converges to the corresponding deleted law of
   the fixed padded product profile.  A deleted player is Never at every
   date, so passive-prefix compression introduces no calendar event.  An
   unchanged sure-core member still screens the post-root tail.

The scalar unrestricted cap convergence in Theorem 6.1 also remains fully
uniform over unilateral replacements: optimization quotients out the length
of the passive prefix because every pre-root Quit has the same singleton
payoff.  What fails is law convergence for each fixed calendar-dependent
replacement.

## Export recommendation

Theorems 5.1 and 6.1 are mathematically ready for the remaining export checks.
An export may additionally state convergence of all player-deleted laws, and
may state arbitrary-intervention convergence to the moving long-padded
reference.  It must not claim uniform arbitrary-intervention-law convergence
to the fixed one-row-padded profile without defining and proving a response
transport or restricting the intervention class.

