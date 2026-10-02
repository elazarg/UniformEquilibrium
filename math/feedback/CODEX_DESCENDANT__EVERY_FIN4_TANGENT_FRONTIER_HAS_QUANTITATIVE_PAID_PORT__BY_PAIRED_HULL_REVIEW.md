# Review of every Fin4 tangent frontier has a quantitative paid port

Reviewer: `PAIRED_HULL_REVIEW`  
Verdict: **PASS**

## Claim checked

For an arbitrary Fin4 positive-minimum tangent family, arbitrary active mover
(p), and arbitrary compact full-replacement cluster (y), the literal
full-replacement target profiles along the cluster subsequence eventually
carry a paid first-disagreement row for one fixed nonmover (j), with gain
(D_*/16), a source witness in the actual stopping-law support, and the
displayed own-, opponent-, and joint-reach floors.  The argument is claimed
to precede the positive-slope / flat-support-entry / off-minimum split and
therefore to reduce all three tangent producer tags to the generic paid-port
waist.

## Mathematical audit

The proof is correct.

1. `FullReplacementCluster.cluster_mem` puts (y) in the same terminal
   semantic carrier on which the frontier base is globally minimizing.
   Therefore (D(y)ge D_*).

2. `FullReplacementCluster.mover_debt_eq_zero` is unconditional in slope and
   fibre status.  It follows from the exact diagonal identity and the
   vanishing-regret full-replacement selection, so it applies to every
   cluster considered here.

3. Carrier debts are nonnegative.  On `Fin 4`, after removing the zero mover
   coordinate, three nonmover debts sum to at least (D_*).  Hence a fixed
   nonmover (j) has (d_j(y)ge D_*/3).  This is a choice at the limiting
   cluster, not a moving observer selection.

4. `FullReplacementCluster.fullReplacement_tendsto` is convergence of the
   actual semantic pairs of
   `frontier.fullReplacementProfile p (endpoint.subseq n)`.  Continuity of
   the (j)-debt therefore gives the eventual safe bound
   (d_j(Y_n)ge D_*/4).

5. Applying
   `positiveDebt_exists_actualJointReach_paidRow_mem_support` with
   (Delta=D_*/4) gives exactly a row of declared gain
   (Delta/4=D_*/16), the support clause, and

   \[
   \Delta\le4M\,S_j,
   \qquad
   \Delta\le8M\,H_j,
   \qquad
   \Delta^2\le32M^2\,S_jH_j.
   \]

   Here (S_j) is the observer's own survival to the row start,
   (H_j) is the opponents' live mass, and their product is the literal
   joint reach.  No cap attainment, finite-clock restriction, or terminal
   atom assumption is inserted.

6. By definition the target (Y_n) is the literal full replacement of only
   player (p)'s complete behavioral strategy in the retained source at the
   same rank.  The paid row is on (Y_n) itself.  Thus the ancestry is one
   actual horizontal replacement edge followed by a row internal to its
   literal target; the note does not misstate either object as a temporal
   Nash--Bellman edge.

## Adversarial branch tests

- **Positive slope:** neither the zero-mover identity nor the debt averaging
  uses the sign of total slope, so the row exists before that tag is read.
- **Flat support entry:** a newly positive coordinate can be the selected
  observer, but need not be; the pigeonhole argument only needs one of the
  three nonmovers.  No no-entry hypothesis is used.
- **Minimum-fibre endpoint:** (D(y)=D_*) still leaves total nonmover debt
  (D_*).  The theorem gives a paid row but does not temporalize the
  horizontal full replacement or contradict minimality.
- **Off-minimum endpoint:** (D(y)>D_*) only strengthens the total-debt
  lower bound.  No return to the minimum is inferred.
- **Small or empty debt support:** the incoming base support is nonempty, so
  an active mover exists.  Even if the endpoint positive support changes
  completely, mover debt zero plus (D_*>0) forces a nonmover debtor.

## Novelty and exact consequence

The ambient terminal exploitability gap already supplies some paid row at
every actual profile, so the existence of a paid row alone is not new.  The
new useful content is the uniform quantitative row on the literal
full-replacement target, with fixed observer after subsequence selection,
actual stopping-law support, and explicit reach floors derived solely from
positive minimum debt.

It is therefore mathematically correct to collapse the three tangent *row
producer* obligations to the generic quantitative paid-port waist.  This
does not consume that waist: the charged-return, quantitative-descent, and
inert outputs remain exactly as the note states.  It also does not erase the
renewable support descent as a potentially useful alternative; it shows only
that one may route every tangent frontier to the paid waist without first
classifying its terminal tag.

No repair is required.
