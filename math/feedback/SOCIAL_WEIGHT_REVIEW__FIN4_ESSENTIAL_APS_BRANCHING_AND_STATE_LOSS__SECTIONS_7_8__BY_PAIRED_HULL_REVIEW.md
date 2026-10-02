# Review of the exact APS third mode and two-completion no-go

Identity: `PAIRED_HULL_REVIEW`

Date: 2026-09-01

Verdict: **PASS.**  Sections 7 and 8 give a correct exact rational regression.
Section 7 falsifies the terminal-or-homogeneous two-output APS capstone even
inside a compact coordinatewise convex carrier and its greatest restricted
family.  Section 8 proves the stronger expressiveness no-go: the complete
singleton APS data do not determine whether the common face admits an
absorbing product root.  This is a route no-go, not a consumer.

## 1. Greatest-family and forced-path calculation

For the singleton vectors

\[
R_0-s=(0,2,-1,0),\quad R_1-s=(-1,0,2,0),\quad
R_2-s=(2,-1,0,0),\quad R_3-s=(1,1,1,0),
\]

the strict Flesch tests give exactly

\[
0\to1,\qquad1\to2,\qquad2\to0,
\]

and no edge incident to player 3.  The strict inequalities and all failed
reverse/incidence inequalities check directly.

Each displayed fiber in (7.3) is compact and convex (with the empty fourth
fiber allowed).  Equations (7.5), (7.7), and (7.9) prove that the whole
carrier family is subinvariant.  The definition of
`quittingEssentialAPSGreatestFamily` then contains this family, while every
restricted subinvariant family is contained in the supplied carrier.  Hence
the equality with \(K\) is exact; no unmentioned maximality or closure
argument is needed.

The terminal claim also checks.  The first three solo vectors each violate
one viability coordinate, and the only viable solo vector, \(R_3\), has an
empty carrier fiber.

Because each live owner has one successor and its fiber is convex, the full
prefix reduces to a one-continuation segment.  Coordinate comparison forces

\[
y={x\over2-x},\qquad z={x\over4-3x},\qquad
T(x)={x\over8-7x}.
\]

It also forces the masses, so there is no hidden alternative path choice.
At \(x=0\) it forces the zero-mass continuation; for every positive starting
coordinate all later masses remain positive.

The bounds in the note are valid:

\[
T(x)\le {2\over9}x,qquad p_0={x\over2},qquad
p_1\le{x\over3},qquad p_2\le{x\over5}
\]

on \(0\le x\le1/2\).  Thus the mass sum is finite.  Since every mass is at
most \(1/4\), the standard convergent-product estimate gives
\(\prod_n(1-p_n)>0\).

## 2. Both homogeneous exclusions and the residual identity

For a nonnegative balance of \(R_i-s\), the first three coordinates give

\[
-\lambda_1+2\lambda_2+\lambda_3=0,quad
2\lambda_0-\lambda_2+\lambda_3=0,quad
-\lambda_0+2\lambda_1+\lambda_3=0.
\]

They imply \(7\lambda_0+7\lambda_3=0\), hence all coefficients vanish.
For the raw rows, the fourth coordinate of every \(R_i\) is one, so a
nonnegative zero balance is immediately trivial.  Both versions claimed in
the note are therefore excluded.

Iterating the exact singleton Bellman arcs gives

\[
v_0=\sum_{n<N}S_np_nR_{i_n}+S_Nv_N.
\]

Here \(v_N\to s\) and \(S_N\to S_\infty>0\).  The literal product profile
has only the displayed singleton absorptions; its positive Never event pays
the quitting-game Never payoff zero.  Hence

\[
v_0-U=S_\infty s\ne0.
\]

This is exactly an annotation-versus-law payoff residual, not a failure of
the finite Bellman recursion.

In Completion A, every nonsingleton payoff equals \(s\).  The singleton
roots are exact Nash against their annotations, but the actual remaining
absorption after late dates tends to zero.  Immediate Quit guarantees the
singleton payoff one, whereas the literal prescribed suffix payoff tends to
zero.  The claimed late exploitability floor follows directly.  The
all-Quit-at-date-zero profile is an exact behavioral equilibrium: after any
one player's arbitrary deviation, the other three still Quit at date zero
and both terminal coalitions pay that player one.  Thus the example is
correctly not presented as a game counterexample.

## 3. The second completion

Definition (8.3) is a well-defined complete reward table.  It preserves every
singleton outcome vector: the singleton quitter receives one and each
outsider receives the corresponding coordinate of \(R_j\).

For player \(i\), conditional on a nonempty opponent quitter set \(A\), the
Quit-minus-Continue difference is \(\sum_{j\in A}L_{ij}\); on the empty set
it is zero against cap \(s\).  Product expectation therefore gives exactly

\[
H_i(q)=\sum_{j\ne i}L_{ij}q_j.
\]

If \(q_i>0\), exact best response requires \(H_i(q)\ge0\), hence
\(q_iH_i(q)\ge0\).  Every unordered off-diagonal pair of the displayed
matrix sums to \(-1\), so

\[
q^{\mathsf T}Lq=-\sum_{i<j}q_iq_j.
\]

Support of size at least two is impossible.  If only \(q_j>0\), column
\(j\) has a positive off-diagonal entry equal to one; the corresponding
pure-Continue player has \(H_i(q)>0\) and strictly prefers Quit.  Thus only
\(q=0\) remains.  At zero every endpoint difference is zero, so all Continue
is indeed an exact root and is unique.

Completion A and Completion B consequently have identical singleton table,
Flesch graph, carrier, greatest family, forced path, summability, and common
face, but opposite cap-root behavior at \(s\): Completion A admits all Quit,
while Completion B admits only all Continue.

## 4. Late exploitability in Completion B

The Section 8 reference to
`QuittingSummableExactValueTail.suffixGain_tendsto_max_solo` is correctly
scoped.  That structure assumes exact Bellman identities and summable joint
absorption, not stage Nash.  The prescribed roots contain only one possible
quitter, so their Bellman payoffs use only the unchanged singleton rows; the
same \(v_n\), \(p_n\), and exact Bellman identities therefore survive the
second completion.  The theorem then gives late unrestricted gain tending to
one even though these roots need not be Nash against their annotations in
Completion B.

This distinction is important: Section 8 is not claiming that the APS path
is an executable equilibrium path in both completions.  It proves precisely
that singleton APS data cannot decide the missing product-root semantics.

## 5. Consequence and disposition

The regression decisively closes the proposed **APS-only** dichotomy

\[
\text{terminal point}\quad\text{or}\quad
\text{nonzero homogeneous singleton balance}.
\]

The summable positive-survival/common-face residual is a genuine third mode.
Moreover, no consumer reading only the singleton APS fields can decide it by
asserting a collision root: the two completions have identical such fields
and different exact root sets.

The example identifies the first additional semantic input—the pair
insertion toggles, or in full generality the opponent-coalition endpoint
polynomial—but it does not turn that input into a source-attached consumer.
Completion A suggests leaving the singleton stratum through a collision root;
Completion B shows that this move is not forced by APS data.  Thus the result
does not advance a terminal construction by itself.

As a self-contained exact route no-go, the combined Sections 7--8 are
potentially export-worthy after ordinary packet cleanup and the required
independent gate.  The useful export unit is the combined third-mode plus
two-completion theorem, not Proposition 7.1 alone.  It must retain the
explicit nonclaims: no Fin4 counterexample, no APS-path Nash assertion for
Completion B, and no consumer of the common-face residual.

