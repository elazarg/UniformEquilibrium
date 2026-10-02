# Review of signed-retraction hybrid-rank no-go

Reviewer: CODEX_SPINOZA

Reviewed artifact:
`notes/CODEX_HAHN__SIGNED_RETRACTION_HYBRID_RANK_NOT_RENEWED_BY_CAP_PORT.md`

Reviewed SHA256:
`ba4defa51b0e3efbd886b0c2df13a02c9666d5d34fd905b708f7053634ed7b33`

## Verdict

**PASS.**  The note correctly distinguishes the counterfactual horizontal
retraction edge (A\to B) from the literal conditional-tail transition of a
root prefix (W\star A).  The proposed Hamming-to-(S) rank is therefore not
renewable from the checked cap-port output.

## Checks

1. For every finite prefix word (W), joint survival through all its roots
   recovers the literal continuation (A), not (B).  If that survival is
   zero, the old tail and its internal paid row are not reached.  This is the
   correct root-then-continuation orientation.
2. In the signed-retraction leakage arm, the paid observer (j\ne i) need
   not be the coordinate changed by (A\to B).  No response target of (j)
   is identified with (B), so completing (j)'s cap cannot be counted as
   another copied source coordinate.
3. The Fin4 regression is exact.  With all rewards zero except
   (r_0(S)=-1) for (0\in S), the profiles (S=\mathrm{Never}^4) and
   (X=(Q_1,\mathrm{Never},\mathrm{Never},\mathrm{Never})) satisfy
   (D(S)=0), (D(X)=1), and the edge (X\to S) pays player (0) one.
   All Continue is an exact one-stage root both against the cap vector zero
   and against the literal tail payoff (U(X)=(-1,0,0,0)): player (0) is
   strict in the former comparison and indifferent in the latter.  Repeated
   all-Continue prefixing thus keeps (X) as the reached tail and never
   realizes the lower hybrid (S).
4. The note correctly limits this example to a structural no-go: its global
   minimum is zero, so it is not offered as a positive-(D_*) quitting-game
   counterexample.
5. Processing (B) afresh does terminate the finite horizontal path, but it
   discards the unresolved port and its ancestry.  Rank zero is the retained
   hard source itself and is not contradictory.

## Nonblocking wording observation

The sentence saying player (0) “strictly prefers Continue” is literally the
comparison against the cap vector (B(X)=0).  Against the actual tail payoff
(U(X)), Continue and Quit alone tie.  The root remains exact in both cases,
so this does not affect the theorem or regression.
