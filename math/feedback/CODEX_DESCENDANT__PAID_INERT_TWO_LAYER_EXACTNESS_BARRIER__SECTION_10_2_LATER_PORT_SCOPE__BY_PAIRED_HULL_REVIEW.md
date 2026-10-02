# Review of the later-receiving extension of Section 10.2

Identity: `PAIRED_HULL_REVIEW`

Date: 2026-09-01

Verdict: **PASS for the stated table-level/source-sibling contraction; FAIL
for any stronger claim that the original cap-lifted profile itself has the
sure-Quit marked row or that the cap-prefix Nash roots are preserved.**

## Claim checked

The last paragraph of Section 10.2 claims that the punishment-pricing
argument is not restricted to a receiving-earlier source.  From a
later-receiving paid first-disagreement row one should be able to construct a
literal sure-owner-Quit profile at the marked date, Nashify the other three
players in the induced binary game, and apply the same
`QuittingSingletonBaseCertificate`/strong-singleton dispatch.

I checked this against
`QuittingPaidFirstDisagreementRow`,
`QuittingPaidFirstDisagreementRow.exists_ownerDeviation_of_receivingLater`,
`QuittingPaidCapLiftedSource.ShiftedPaidRow.liveMass_eq`,
`QuittingPaidCapLiftedSource.nonempty_shiftedPaidRow`, and the inert-stall
shifted-row declarations.

## 1. The required sure-Quit source exists, but it is a sibling

Let `row.receivingEarlier = false`.  Its chronology field says exactly

\[
  \mathsf{sourceWitness}=\operatorname{some}(t),\qquad
  \mathsf{receivingWitness}=t+\mathsf{later}.
\]

Thus the literal profile needed by Section 10.2 is not necessarily
`row.receiving`.  It is

\[
 H=\operatorname{update}
    (\mathsf{row.receiving},i,\mathsf{sourceWitness}).
\]

Player \(i\) Continues surely before \(t\) and Quits surely at \(t\) in
\(H\).  The named orientation theorem also proves that replacing this clock
by `receivingWitness` is the legal whole-profile owner deviation carrying the
paid gain.  Hence \(H\) is a literal actual behavior profile and a unilateral
response sibling of the port profile.  No cap attainment is used.

With \(i\) fixed to this sure-Quit clock, replace the three free marginals at
date \(t\) by an exact Nash point of the induced finite binary game.  These
are finite literal row overwrites.  They leave the opponents' pre-mark
histories and all post-mark strategies unchanged.  Since \(i\) surely Quits
at \(t\), the free-player endpoint inequalities are their unrestricted
complete-deviation inequalities and the resulting profile is exactly the
sure-owner object required in Section 10.2.

The later receiving clock and the incoming paid comparison are not needed
after this safety completion.  This is why the conclusion is honestly a
contraction to the strong-packet waist, not transport of the paid edge through
a Nash--Bellman chronology.

## 2. Reach survives cap lifting

The first-disagreement live mass is opponent-deleted survival, so replacing
only the observer by the earlier source clock does not change it.  At the
marked date, the observer's own pre-mark survival is one; consequently this
opponent live mass is the actual joint reach of \(H\) to the sure-Quit row.

For the cap-lifted port the checked identity is

\[
  L_h=R_i(h)L_0,
\]

where \(R_i(h)) is the observer-deleted reach through the prefixed roots.
The positive-minimum cap lift supplies a fixed positive reach floor, and
`nonempty_shiftedPaidRow` retains a fixed positive paid gain.  Thus the
shifted later-receiving rows retain a uniform positive source-unit marked
reach.  In the zero-charge inert arm every prefixed root is literally all
Continue, \(R_i(h)=1\), and the checked lossless shifted row has exactly the
original live mass and gain.

After stabilization of an induced Nash point and one of the seven nonempty
free cells, the punishment-pricing estimate therefore gives a fixed positive
actual stage mass.  The singleton/nonsingleton screening interfaces may be
applied exactly as in the reviewed receiving-earlier argument.

## 3. What is not preserved

For a general positive-absorption cap prefix, forming \(H\) overwrites the
observer's actions at all dates before the shifted mark.  Therefore it does
not preserve the displayed cap-Nash root word for that player.  A minimal
behavioral boundary test is a prefixed root at which the observer Quits with
probability \(1/2\): changing only the marked row leaves only half of the
observer mass alive, whereas the first-disagreement `liveMass` deletes the
observer and can equal one.  Equality between live mass and actual marked
reach is recovered only by replacing the whole observer clock by the earlier
pure witness, which necessarily changes that prefix root.

In the inert branch this particular mismatch disappears on the added prefix,
because every added root is all Continue.  Even there, the profile used for
the sure-Quit packet is the source-witness sibling of the retained receiving
profile; the data-bearing paid row by itself never asserts that
`row.receiving` already follows either witness.

Likewise, the free-player Nashification and subsequent pure screening
overwrite the marked opponent root.  They preserve the copied pre-mark and
post-mark behavior outside those declared replacements, but not the incoming
opponent root as a Nash--Bellman edge.

## 4. Exact conclusion

The extension is valid in the following form:

> A later-receiving shifted paid row with a positive live-mass floor supplies
> a literal earlier-witness sure-Quit sibling at the same marked date and
> reach.  After finite induced-Nash row replacement, punishment pricing gives
> either a uniform-equilibrium payoff or a positive nonempty causal cell and
> the checked strong-singleton packet.

It does **not** give:

- preservation of a non-inert cap-prefix Nash word;
- a temporal edge from the original port profile through the safety-completed
  profile;
- transport of the incoming paid gain through the free-player Nashification;
- a terminal consumer or renewable rank.

The note already says that the incoming opponent root is abandoned and that
the conclusion is table-level.  With “fix its observer to Quit” understood as
the whole earlier pure-clock replacement above, rather than a row-only edit,
the claimed extension is sound.

