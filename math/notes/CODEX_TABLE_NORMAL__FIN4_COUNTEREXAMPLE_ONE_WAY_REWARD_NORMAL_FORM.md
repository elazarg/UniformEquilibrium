# A one-way reward-table normal form for a Fin4 counterexample

## Status

This note assembles table-level necessary conditions already proved in the
project, together with one independently reviewed ordinary-mathematics social
costate exclusion. It is a **one-way reduction**, not a characterization:
tables satisfying the displayed conditions may still have an exact or uniform
equilibrium.

The conclusion is precise:

> If every four-player reward table in the class below has a uniform-equilibrium
> payoff, then every four-player quitting game has a uniform-equilibrium payoff.

No reduction in the dimension of the reward-table parameter space is claimed.
The only continuous normalization used below is one common positive scale.

## 1. The table class

Let \(I=\operatorname{Fin}4\), let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I,
 \qquad
 R=\max_{i,S}|r_i(S)|,
\]

and put

\[
 s_i=r_i(\{i\}),
 \qquad
 M_{ij}=r_i(\{j\})-r_i(\{i\}).
\]

Call \(r\) a **screened hard Fin4 table** if it has all the following
properties.

### T1. No pure terminal coalition

No nonempty pure quitting coalition is an exact terminal Nash profile. This is
a finite collection of reward comparisons, including the unique quitter's
option to Continue forever in the singleton case.

### T2. Full normal hard singleton core

Every player is punishment-normal, the normal core of \(M\) is all of \(I\),
and \(M\) is standard-\(Q\) with no homogeneous simplex solution but is not
projective-\(\overline Q\). Equivalently for the present use, some proper
nonempty principal submatrix is not projective-\(Q\), while the full matrix is
standard-\(Q\) and has no homogeneous solution.

There is also a full-support singleton packet: there are
\(m\in\Delta(I)\) and \(u\in\mathbb R^I\) such that every \(m_j>0\),

\[
 s_i\le u_i,
 \qquad
 \operatorname{Pun}_i\le u_i,
 \qquad
 u_i\le\sum_jm_jr_i(\{j\}),
\]

with the packet's supported owners satisfying its exact own-coordinate
indifference. If the table has terminal exploitability gap \(\gamma>0\) and
is bounded by \(R>0\), the checked quantitative construction gives

\[
 m_j\ge \frac1{1+6R/\gamma}
 \qquad(j\in I).
\]

### T3. Uniform singleton-collision exits

For every singleton owner \(j\), some \(o\ne j\) satisfies

\[
 r_o(\{j,o\})\ge r_o(\{j\})+\gamma.
\]

The choices may be made as a fixed-point-free map \(j\mapsto o(j)\). Some
owner also satisfies

\[
 r_j(\{j\})\ge\gamma.
\]

These are literal reward-table inequalities. They do not assert that the
corresponding horizontal collision move is a chronological edge.

### T4. A strict robust-join background reversal

There are distinct players \(a,b\) and a nonempty

\[
 C\subseteq I\setminus\{a,b\}
\]

such that

\[
 r_b(\{a\})+\gamma\le r_b(\{a,b\})
\]

but

\[
 r_b(C\cup\{a,b\})<r_b(C\cup\{a\}).
\]

Up to a player relabeling, the topology of this witness is

\[
 a=0,\qquad b=1,\qquad
 C=\{2\}\quad\hbox{or}\quad C=\{2,3\}.
\]

Thus a favorable singleton join must reverse on either a one-player or a
two-player disjoint background. The first inequality has the terminal-gap
margin; the reverse inequality is only known to be strict.

### T5. One of three hard-principal shapes

The nonprojective principal has cardinality two or three, and the following
checked finite dispatch is exhaustive, up to relabeling.

1. **Two-player crossing.** The principal is \(\{0,1\}\),

   \[
   M_{01}<0,\qquad M_{10}<0,
   \]

   and each harmed receiver has a positive helper outside the principal:
   for some \(h_0,h_1\in\{2,3\}\), not necessarily distinct,

   \[
   M_{0h_0}>0,\qquad M_{1h_1}>0.
   \]

2. **Three-player external helper.** The principal is
   \(\{0,1,2\}\), player \(3\) is its unique outsider, and after relabeling
   within the principal,

   \[
   M_{10}<0,\qquad M_{13}>0.
   \]

3. **Three-player cyclic boundary.** The principal is
   \(\{0,1,2\}\). After relabeling or reversing its cyclic orientation,
   it may be written

   \[
   \begin{array}{lll}
   M_{01}<0,&M_{02}>0,&M_{10}>0,\\
   M_{12}<0,&M_{20}<0,&M_{21}>0,
   \end{array}
   \]

   and

   \[
   M_{01}M_{12}M_{20}+M_{02}M_{10}M_{21}\le0.
   \]

The relabeling which puts T4 into its canonical topology need not be the same
relabeling which puts T5 into one of these displayed labelings. A completely
labelled normal form is therefore a finite union over their relative player
placements, not one simultaneous canonical labeling.

### T6. Failure of every closing nonnegative social costate

There is no vector \(\theta\in\mathbb R^I_{\ge0}\) with at least two positive
coordinates such that

\[
 \theta\mathbin\cdot s\ge0
\]

and

\[
 \theta\mathbin\cdot(r(S)-s)\le0
 \qquad(S\ne\varnothing).
\]

Existence of such a costate gives zero minimum semantic debt and hence a
uniform-equilibrium payoff. The arbitrary-nonnegative-costate form is checked
production Lean and recorded in
`formalized/NONNEGATIVE_WEIGHT_SOCIAL_CHAMBER_AND_SPARSE_REWARD_BOUNDARY.md`;
it remains logically separate from the singleton/LCP conditions above.

## 2. One-way reduction theorem

Assume a Fin4 table has no uniform-equilibrium payoff. The terminal
exploitability characterization supplies \(\gamma>0\). It has no pure terminal
Nash profile, so T1 holds. The checked hard-residual construction supplies T2
and T3. The robust-join compiler says that absence of T4 would itself produce
a uniform-equilibrium payoff. The hard-principal size and finite dispatch
supply T5. The social-costate consumer says that absence of T6 would again
produce a uniform-equilibrium payoff.

Therefore every Fin4 counterexample is a screened hard Fin4 table. This proves
the advertised implication:

\[
 \boxed{
 \bigl(\text{every screened hard Fin4 table has a UE payoff}\bigr)
 \Longrightarrow
 \bigl(\text{every Fin4 table has a UE payoff}\bigr).}
\]

The converse is false as a proof principle: the conditions are necessary
screens, not a counterexample certificate. Existing regression tables satisfy
large parts of T2--T5 and nevertheless have exact equilibria.

## 3. Exact invariances and normalization

Player relabeling preserves the quitting game, equilibrium property, and every
screen above. A common positive scaling

\[
 r\longmapsto ar,\qquad a>0,
\]

also preserves best-response comparisons and existence of a uniform-equilibrium
payoff, while scaling \(R\), \(\gamma\), punishments, payoffs, and semantic debt
by \(a\). Thus a hypothetical counterexample may be put at \(R=1\); all
quantitative information then depends on the dimensionless gap
\(\gamma/R\).

No additive translation is used here. Because the payoff of Never is fixed at
zero, translating all finite terminal rewards without simultaneously changing
the model's Never payoff is not an innocuous game equivalence. The subtraction
in \(M_{ij}=r_i(\{j\})-r_i(\{i\})\) is an algebraic comparison, not a license to
replace the entire quitting table by a translated one.

Likewise, no parameter-count claim follows from player relabeling, which is a
finite quotient, or from the existential witnesses in T2--T6. Common scaling
permits one scalar normalization only.

## 4. What the normal form does not constrain

A Fin4 reward table has \(4(2^4-1)=60\) real entries. The singleton matrix
records only singleton-row differences. T3 constrains selected singleton-to-
pair comparisons. T4 constrains one selected pair comparison and one selected
background comparison. T5 is again singleton-matrix geometry. T1, punishment
normality, the packet, and T6 impose global existential or disjunctive
conditions, but they do not assign signs or values to every coalition entry.

In particular, the present theorem gives no coordinatewise canonical values
for most pair, triple, or grand-coalition rewards. They remain subject only to
the displayed finite comparisons and the global table properties. This is why
the normal form is a finite screen rather than a low-dimensional parametrization.

## 5. Endogenous data are not part of the table normal form

The following stronger information is available only after selecting semantic
carrier points, laws, atoms, and causal realizers. It must not be folded into
a reward-table classification:

- the positive minimum debt \(D_*\) and a minimum semantic/law point;
- the minimum singleton moat and weighted aggregate-surplus inequalities;
- a source-attached positive terminal-law atom and its actual causal dates;
- the full-debt versus reset-rigid minimum chamber;
- forced singleton, partner, payer, and marked-row roles after subsequences;
- bounded exact-block hazard capacity;
- exact-prefix saturation, inert ports, and same-law reset data.

These objects distinguish different realizing sequences or different minimum
points for the same reward table. They are the current consumer inputs, not
additional coordinates of \(r\).

## 6. Narrow source record

Checked declarations inspected:

- nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff;
- finFour_exists_uniformPayoff_of_noStrictBackgroundReversal and
  selectedCycle_has_strictBackgroundReversal_of_no_uniformPayoff in
  RobustJoinStrictBackgroundReversal.lean;
- exists_nonprojectivePrincipal_card_two_or_three in
  FullSupportHardPrincipalSize.lean;
- hardPrincipalDispatch, cardTwoCrossing, and
  cardThree_externalHelper_or_cyclicBoundary in
  FullSupportHardPrincipalDispatch.lean; and
- the positive and negative terminal semantic endpoints named in SOURCES.md.

The social costate exclusion is the checked theorem recorded in
`formalized/NONNEGATIVE_WEIGHT_SOCIAL_CHAMBER_AND_SPARSE_REWARD_BOUNDARY.md`.

## Next question

Can one consume one of the three hard-principal cases using the robust reversal
in its **actual relative labeling**, without selecting new source data? A valid
answer must either construct a stationary/finite-block equilibrium, or attach
the table geometry to the source-derived full-debt/reset-rigid minimum chamber.
