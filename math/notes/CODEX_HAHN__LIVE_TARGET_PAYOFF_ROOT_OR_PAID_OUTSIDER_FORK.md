# A live target gives a payoff-root word or a paid outsider row

Author: CODEX_HAHN

## Status

**Exact ordinary mathematics; not Lean-checked and not a terminal
consumer.**  Once the unique host's cap-band target deterministically
survives the old finite word, there is an elementary but useful exhaustive
fork.  Either every actual row is uniformly approximate Nash against its
literal successor **payoff**, or a fixed outsider has a fixed-gain literal
one-date deviation at a uniformly reached row before the tail.

The first branch supplies exact Bellman equations and ordinary
coordinatewise approximate root Nash after reversal.  It does **not** supply
the support-wise Nash field required by the checked finite-forward consumer:
a root may place vanishing probability on an action with a fixed endpoint
loss.  The second branch is one chronological paid edge, not a return.

## 1. Self-contained input

Let \(I=\operatorname{Fin}4\).  For each \(n\), let an actual behavioral
profile have a finite displayed word of length \(m_n>0\) over an actual tail:

\[
 Y_n=(y_{n,0},\ldots,y_{n,m_n-1})\triangleright Z_n.
\tag{1}
\]

Let \(U_{n,t}\) be the prescribed payoff vector of the actual suffix
beginning at row \(t\).  Hence the Bellman identities are literal:

\[
 U_{n,t}=F(y_{n,t},U_{n,t+1})
 \qquad(t<m_n).
\tag{2}
\]

Assume the full profile reaches its tail with one fixed floor

\[
 a_n:=\Pr_{Y_n}(T_I\ge m_n)\ge\eta>0.
\tag{3}
\]

Fix one player \(k\) and assume

\[
 d_k(Y_n)\le e_n,
 \qquad e_n\longrightarrow0.
\tag{4}
\]

The live cap-band target constructed from the unique-sure exact word has
exactly these fields: player \(k\) Continues surely through the word, the
opponents supply (3), and vanishing cap-band widths supply (4).

For each row and player define the ordinary payoff-root defect

\[
 h_{n,t,i}:=
 \max\{Q_i(y_{n,t};U_{n,t+1}),
          C_i(y_{n,t};U_{n,t+1})\}
   -U_{n,t,i}\ge0.
\tag{5}
\]

This is not the cap-anchored defect.  Both endpoint comparisons and the
Bellman equality use the one common continuation vector \(U_{n,t+1}\).

## 2. Exact fork

After passing to a subsequence, one of the following holds.

### A. Uniform ordinary approximate payoff-root word

There are numbers \(\varepsilon_n\downarrow0\) such that

\[
 h_{n,t,i}\le\varepsilon_n
 \qquad(t<m_n, i\in I).
\tag{6}
\]

Together with (2), this is a literal finite ordinary approximate
Nash--Bellman word:
every row is \(\varepsilon_n\)-Nash against the prescribed payoff of its
actual successor, and every Bellman equation is exact.

### B. Fixed paid outsider row

There are a fixed player \(i\ne k\), a number \(\xi>0\), and row indices
\(t_n<m_n\) such that player \(i\) has a literal one-date deviation at the
actual suffix \(t_n\) of gain at least \(\xi\).  Copying the prescribed
strategy through the preceding word and changing only that row gives an
actual complete behavioral response at \(Y_n\) with exact gain

\[
 A_{n,t_n}h_{n,t_n,i}\ge\eta\xi,
\tag{7}
\]

where \(A_{n,t}\) is joint survival through the rows strictly before \(t\).
Its first disagreement is the displayed row \(t_n\), strictly before the
live tail boundary.

## 3. Proof

Set

\[
 H_n:=\max\{h_{n,t,i}:t<m_n, i\in I\}.
\tag{8}
\]

This maximum exists because the word and player set are finite.  If
\(\liminf H_n=0\), refine so that \(H_n\to0\) and take
\(\varepsilon_n=H_n\).  The equivalence between coordinate Nash-defect
bounds and approximate product-root Nash proves (6).  Equation (2) supplies
the common-continuation Bellman identity, so A follows.

Otherwise, after refinement \(H_n\ge\xi>0\).  Choose \(t_n,i_n\) attaining
the maximum.  Finite pigeonhole fixes \(i_n=i\).  At the actual suffix
beginning at \(t_n\), replace only player \(i\)'s current root marginal by a
pure action attaining the better of its Quit and Continue endpoints, and
follow the prescribed continuation thereafter.  By (5), its suffix gain is
exactly \(h_{n,t_n,i}\).

At all earlier rows the response copies the prescribed behavioral strategy.
The source and response therefore differ only on the event that every player
survives to \(t_n\).  The exact copied-prefix identity gives whole-profile
gain \(A_{n,t_n}h_{n,t_n,i}\).  Survival is nonincreasing in the cutoff, so

\[
 A_{n,t_n}\ge a_n\ge\eta,
\]

which proves (7).

It remains to exclude \(i=k\).  The copied one-date deviation is one member
of player \(k\)'s unrestricted complete deviation class, so its whole-profile
gain is at most \(d_k(Y_n)\le e_n\).  Hence, for every row,

\[
 h_{n,t,k}\le {e_n\over A_{n,t}}
 \le {e_n\over\eta}\longrightarrow0.
\tag{9}
\]

The maximizing label in the positive lower-bound branch is therefore not
\(k\) for all sufficiently large \(n\).  This proves B and exhaustiveness.

## 4. Exact relation to the checked forward consumer

Reverse the finite word by putting

\[
 v_{n,s}=U_{n,m_n-s},
 \qquad
 q_{n,s}=y_{n,m_n-1-s}.
\tag{10}
\]

Then (2) becomes the forward policy equation

\[
 v_{n,s+1}=F(q_{n,s},v_{n,s}),
\tag{11}
\]

and (6) gives `IsεQuittingRootNash` against the common continuation
\(v_{n,s}\).  It does not give `IsQuittingRootSupportApproxNash`.

Indeed, if one action is worse by one and the root plays it with probability
\(1/n\), then the coordinate Nash defect is \(1/n\), while the loss of the
played action remains one.  This is an exact one-player endpoint regression
for the attempted implication

\[
 \text{ordinary approximate Nash}
 \Longrightarrow
 \text{support-wise approximate Nash}.
\tag{12}
\]

Thus no currently identified forward-packet consumer accepts branch A.
In particular, `QuittingFiniteForwardPacket` in
`UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`
requires the stronger support-wise field, as well as:

1. every value to lie above the punishment floor up to the same error;
2. a fixed compact carrier; and
3. arbitrarily large accumulated absorption charge for each requested
   tolerance.

The current fork supplies neither the floor nor arbitrary charge, and it
does not identify \(Z_n\) with the next renewable source.  In particular,
\(\varepsilon_n\to0\) is a maximum per-row error statement; it does **not**
say that the sum of row errors tends to zero when \(m_n\to\infty\).

## 5. Relation to the cap ledger

The cap-anchored ledger remains useful for accounting, but it is not needed
to obtain this fork.  A row can have zero cap-root defect and positive
payoff-root defect because its successor cap and prescribed payoff differ.
Such a row falls directly into B.  Conversely, if no such fixed mismatch
survives, A uses the correct common payoff continuation and is an honest
approximate Nash--Bellman word.

Thus the cap/payoff distinction creates no third branch at the level of
ordinary expected Nash defect.  At the support-wise level there is an exact
third boundary: a fixed endpoint loss can be carried by vanishing played
mass.  What remains is global:

- purify or otherwise control the vanishing-mass support mistakes in A, and
  then renew or accumulate the resulting words while preserving the
  punishment floor; or
- connect the paid outsider row in B to a return or finite rank without
  invalidating the preceding owner update.

## Sources inspected

- `notes/CODEX_SPINOZA__EXACT_WORD_FORCES_LATE_CAP_BAND_RECEIVER_AND_LIVE_TARGET.md`;
- `notes/CODEX_HAHN__LIVE_CAP_BAND_TARGET_LEDGER_DICHOTOMY.md`;
- `UniformEquilibrium/Quitting/Root/NashDefect.lean`;
- `UniformEquilibrium/Quitting/Root/LiteralPrefixDeviationTransport.lean`;
- `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`;
  and
- `UniformEquilibrium/Quitting/Projective/ForwardBlockSingleSeam.lean`.

## Boundary tests and nonclaims

- The positive final reach floor is essential.  Without it, a fixed local
  defect can hide behind a vanishing copied-prefix coefficient, and (9) does
  not exclude the owner.
- A small maximum row error is weaker than a small sum of row errors.
- A small expected Nash defect is weaker than a small support-wise action
  loss.  This is why branch A is not a checked finite forward packet.
- The paid row in B has an exact whole-profile gain, but the response child
  need not preserve any other row's Nash comparison.
- No punishment admissibility, return, renewable rank, terminal approximate
  Nash profile, or uniform-equilibrium payoff is claimed.
