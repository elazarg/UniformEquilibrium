# Consume the four-player product-base paid singleton exit

## Mathematical data

Let \(I=\{0,1,2,3\}\) and let \(r(S)\in\mathbb R^I\) be the reward of every
nonempty quitting coalition.  For a behavioral profile write \(U\) for its
terminal payoff, \(B\) for its unrestricted unilateral best-response cap,

\[
d_i=B_i-U_i,
\qquad
D=\sum_i d_i.
\]

Assume that the minimum of \(D\) on the closed terminal-semantic carrier is
\(D_*>0\), and fix a global-minimum point \(z=(U,B)\) with full debt:

\[
D(z)=D_*,
\qquad
d_i(z)>0\quad(i\in I).
\]

Suppose \(z\), together with its terminal law, is attained by playing one
product root \(q\in[0,1]^I\) and then Never after all Continue.  Equivalently,
stationary repetition of \(q\) realizes the same complete semantic pair and
law.

Let

\[
K=\{i:q_i=1\},
\qquad |K|\ge2,
\]

and assume \(K\) is maximal among the sure quitters of \(q\).  Also assume
the minimum singleton separation

\[
B_i-r_i(\{i\})\ge D_*>0
\qquad(i\in I).
\]

For every \(p\in K\), changing \(q_p=1\) to \(q_p=1-\theta\), with
\(\theta>0\) sufficiently small, is a literal unilateral improvement.  A
finite sequence of at most three such softenings can leave exactly one
member of the original sure core, and therefore produces a literal terminal
law with a positive singleton atom.  Throughout a sufficiently small common
neighborhood:

- every debt remains positive;
- each cap is one fixed product-endpoint polynomial;
- every singleton option remains strictly suboptimal; and
- every softening edge has a strictly positive exact payoff gain.

The endpoint of this finite paid path need not remain on the minimum fibre.
If a softening does remain on the minimum fibre, its sure-core cardinality
strictly decreases.  If it leaves the minimum fibre, its excess debt is
locally affine in the softening scale and can be of the same first order as
the mover's payoff gain.

## Question

Use the complete global-minimum source, the attained product profile, and the
finite paid softening path to prove one of the following:

1. terminal approximate Nash profiles for every positive error, with payoff
   vectors converging to one fixed vector;
2. a uniform-equilibrium payoff;
3. a source-matched positive cumulative admissible-payoff return;
4. a source-preserving finite-rank transition whose terminal outputs all have
   consumers of type 1--3; or
5. incompatibility of the supplied configuration with a positive terminal
   exploitability gap.

An equally complete negative answer is an explicit four-player reward table,
a number \(\gamma>0\), and a proof that every behavioral profile admits a
unilateral behavioral deviation gaining at least \(\gamma\), while the table
realizes all the supplied data.

## Required distinction

The positive singleton atom at the end is not by itself a consumer.  The
softening changes other players' unrestricted caps, and an off-minimum
endpoint cannot be declared a return merely because it is connected to the
minimum by paid unilateral edges.  A valid proof must control the complete
cap leakage, construct an executable return, or produce a genuinely renewable
rank on complete source objects.

The following are not answers:

- another concentrated-singleton packet without a terminal consumer;
- a real-valued decrease without a well-founded renewable rank;
- replacement by an unrelated minimum law or profile;
- an approximate payoff match without cap and source compatibility; or
- a local product-root calculation that does not use the positive global
  minimum and its source provenance.
