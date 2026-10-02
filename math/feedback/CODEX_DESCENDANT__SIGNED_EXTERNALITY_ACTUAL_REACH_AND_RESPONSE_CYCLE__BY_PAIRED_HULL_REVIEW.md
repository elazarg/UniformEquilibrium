# Review of signed externality actual reach

Reviewer: PAIRED_HULL_REVIEW  
Date: 2026-08-31  
Verdict: **PASS**

## Claim checked

The note claims that if literal profiles \(P,Q\) differ only in player
\(q\)'s strategy and another player \(h\)'s prescribed payoff falls by
\(a>0\), then the payoff fall can be localized to an actually reached
pure-time first-disagreement row controlled by \(q\).  Applied to the
two-response minimum branch, this gives on one literal successor:

* a \(q\)-controlled externality row restoring a fixed amount of \(h\)'s
  payoff; and
* an independently selected, genuinely profitable \(h\)-row.

The note does not call either row an exact root or claim that they compose.

## 1. Reward-coordinate transport: PASS

Copying the original \(h\)-reward coordinate into the auxiliary \(q\)-reward
coordinate is legitimate.  The action profiles, stopping laws, survival
events, and terminal coalition laws do not depend on the reward table.
Therefore, for every replacement \(\tau_q\),

\[
\widetilde U_q(Q[q\leftarrow\tau_q])
=U_h(Q[q\leftarrow\tau_q]).
\]

Since \(P\) and \(Q\) have the same opponents for \(q\), the strategy of \(q\)
used in \(P\) is a legal response at \(Q\).  Hence

\[
\widetilde d_q(Q)\ge \widetilde U_q(P)-\widetilde U_q(Q)
=U_h(P)-U_h(Q)\ge a.
\]

The auxiliary reward bound is at most the original coordinate bound \(M\).
The actual-reach theorem may therefore be applied to the auxiliary game, and
its row start, source/receiving pure times, live mass, and joint survival
prefix are literally the same action events in the original game.  Only the
interpretation of the row's payoff difference changes: it is an \(h\)-payoff
externality, not a profitable \(q\)-deviation in the original table.  The
note states this distinction correctly.

The support-strengthened theorem also transports honestly: support of the
source pure time concerns \(q\)'s actual stopping law in \(Q\), which is
unchanged by the auxiliary payoff relabeling.

## 2. Floors and common source: PASS

Using the repaired payoff-fall floor \(D_*/20\), the checked theorem gives
gain \(D_*/80\) and

\[
\operatorname{Reach}\ge
\frac{(D_*/20)^2}{32M^2}
=\frac{D_*^2}{12800M^2}.
\]

The conservative-transfer recipient satisfies \(d_h(x^2)\ge D_*/9\), so
eventually \(d_h(X_n^2)\ge D_*/10\).  Applying the original reward theorem at
the same source \(X_n^2\) gives an \(h\)-gain \(D_*/40\) and joint reach
\(D_*^2/(3200M^2)\).  The constants and inequality directions are correct.

Both rows are selected at the identical literal source profile \(X_n^2\).
They are co-realized in that precise sense.  Their dates and replacements
need not be compatible, and executing one need not preserve the other's
gain.  The note explicitly retains that boundary.

## 3. Exact four-player regression: PASS

The four displayed pure coalitions have cap vector \((1,1,1,1)\) and debt
vectors alternating between

\[
(1,0,1,1)
\quad\text{and}\quad
(0,1,1,1).
\]

Direct endpoint checks validate every arrow:

* at \(\{k\}\), \(q\) joins and gains one;
* at \(\{q,k\}\), \(h\) joins and gains one;
* at \(\{q,h,k\}\), \(q\) leaves and gains one;
* at \(\{h,k\}\), \(h\) leaves and gains one.

The other alternating player loses one on each arrow.  Player \(\ell\)'s
joining rewards and player \(k\)'s continuation rewards give their asserted
unit caps.  The common all-Continue tail supplies the unit cap when the sole
displayed quitter \(k\) changes to Continue.

The unique-root argument is correctly triangular.  Player \(k\) strictly
Continues at every opponent root.  Conditional on \(k\)'s sure continuation,
\(h\) and \(\ell\) strictly Continue by the \(k\notin S\) rule.  With those
three players Continuing, \(q\) strictly Continues against singleton Quit
reward zero and continuation cap one.  Hence all Continue is the unique exact
product root at the displayed cap.

At all Never every singleton payoff is zero, so every cap and prescribed
payoff is zero.  The regression therefore has true global minimum zero, as
claimed; it is a local no-go rather than a counterexample.

## 4. Exact status

This is useful strengthening of the signed-law branch: the nonmover payoff
fall no longer exists only as a time-forgetting law coordinate.  It has an
actual reached causal row on the same successor as the true paid row.

It remains a supplied two-row port, not an executable return, rank, or
contradiction.  The missing theorem must price the interaction of the two
rows using positive-minimum provenance, or prove that one row survives the
other's replacement.  No objection remains to the note's stated reduction.
