# Second falsification review of the Fin4 integral-tournament packet

Reviewer: CODEX_SPINOZA

Object reviewed:
`/tmp/FIN4_INTEGRAL_TOURNAMENT_BALANCED_SINGLETON_UNIFORM_PAYOFF.md`

Reviewed SHA-256:
`05bccfe23cadd8e13961ca6dcbeb8f224e9cf5117c3f655438edb1a98ce10bc8`

Verdict: **PASS.** I found no mathematical, source, quantifier, probability,
or semantic-consumer error. The exact standalone bytes cover the sink and
no-sink branches exhaustively, retain all four free solo baselines and all 44
free nonsingleton coordinates, construct every field of the reader-facing
balanced certificate in the no-sink branch, and invoke the checked
unrestricted behavioral compiler with a literal initial phase.

Before promotion, the author should add this review to the candidate's
`Independent reviews` list and request a hash-only delta check. That is a
lifecycle edit, not a mathematical objection.

## Claim checked

Let \(I\) have four elements, let \(A\) be a \(0/1\) tournament, let \(t>1\),
and put

\[
M(i,j)=tA(i,j)-A(j,i).
\]

For every zero-Never quitting reward satisfying

\[
r_i(\{j\})-r_i(\{i\})=M(i,j),
\]

the candidate claims:

1. if every tournament vertex has an outgoing edge, a three-phase
   `BalancedSingletonCycleCertificate` exists and its phase-zero target is a
   uniform-equilibrium payoff against all unilateral behavioral deviations;
2. if some vertex has no outgoing edge, the normalized singleton matrix has
   a homogeneous simplex-LCP witness, so this branch fails the negative
   search's homogeneous-infeasibility gate.

The no-sink conclusion is uniform over arbitrary solo baselines and arbitrary
nonsingleton completion.

## Independent tournament check

In a four-vertex no-sink tournament the four positive integer outdegrees sum
to six. Their only sorted possibilities are

\[
(1,1,1,3),\qquad (1,1,2,2).
\]

For \((1,1,1,3)\), removing the degree-three vertex leaves three vertices,
each with exactly one win inside the remaining triple. They form a directed
cycle, and the removed vertex beats all three.

For \((1,1,2,2)\), orient the edge between the degree-two vertices as
\(c\to d\) and remove \(d\). Since \(d\) loses to \(c\), its two wins are
against the degree-one vertices. Vertex \(c\) has one further win among those
vertices, and their degree-one conditions force the remaining triple to be a
directed cycle. The removed \(d\) beats two members of that cycle.

Thus there are distinct \(o_0,o_1,o_2,d\) with

\[
A(o_{j+1},o_j)=1
\]

cyclically, and \(d\) beats at least two owners. As an independent finite
falsification, I enumerated all \(2^6=64\) labelled tournaments: 32 have no
sink, and all 32 admit exactly the required ordered-cycle-plus-outsider
property.

If a sink \(i\) exists, its row is zero. The tournament identities give

\[
M(i,i)=0,\qquad M(j,i)=tA(j,i)\ge0.
\]

The simplex vector supported at \(i\) therefore has nonnegative homogeneous
residual and complementarity. This is exactly the orientation of
`singletonLCPFeasible_tournamentSkewMatrix_of_row_eq_zero`. The candidate
does not incorrectly claim a balanced certificate or a uniform payoff in
this branch, and does not treat the standard-Q/feasible disjunction as
exclusive.

## Exact recurrence and positivity check

Set

\[
s=1/t,\qquad h=1-s.
\]

Then \(0<s,h<1\). For owner coordinate \(o_k\), define

\[
T_j(o_k)=
\begin{cases}
t,&j=k-1\pmod 3,\\
0,&\text{otherwise}.
\end{cases}
\]

Because the normalized singleton entries along the directed cycle are
\(t,0,-1\), the three equations are

\[
t=t+s0,\qquad 0=0+s0,\qquad 0=-1+st.
\]

Hence

\[
T_j(o_k)=M(o_k,o_j)+sT_{j+1}(o_k).
\]

For the outsider, with \(x_j=M(d,o_j)\),

\[
T_j(d)=\frac{x_j+sx_{j+1}+s^2x_{j+2}}{1-s^3}.
\]

Subtracting \(sT_{j+1}(d)\) leaves \(x_j\), so the same recurrence holds.
At least two \(x_j\)'s are \(t\), while the third is \(t\) or \(-1\). In the
one-loss case the cyclic numerators are

\[
1/t,\qquad t,\qquad t+1-1/t^2,
\]

all strictly positive for \(t>1\). The denominator is positive. Thus all
owner and outsider tails are nonnegative. I found no missed placement of the
outsider's possible loss.

## Certificate-field audit

Let

\[
b_i=r_i(\{i\})_i,\qquad v_j(i)=b_i+hT_j(i).
\]

The singleton normalization gives

\[
r_i(\{o_j\})=b_i+M(i,o_j).
\]

Using \(h+s=1\) and the tail recurrence,

\[
\begin{aligned}
h\,r(\{o_j\})+s\,v_{j+1}
&=h(b+M(\cdot,o_j))+s(b+hT_{j+1})\\
&=b+h(M(\cdot,o_j)+sT_{j+1})\\
&=v_j.
\end{aligned}
\]

This is the exact orientation of
`quittingSingletonArcPayoff h root next`.

For the active owner, \(T_j(o_j)=0\), so
\(v_j(o_j)=b_{o_j}=r_{o_j}(\{o_j\})\). Since \(h>0\) and every tail is
nonnegative, \(b_i\le v_j(i)\) for every player and phase. These are exactly
the `active` and `soloFloor` fields; no sign condition on the baselines is
needed.

The common hazard \(h\) satisfies \(0<h<1\). Every owner faces positive
hazard in a phase owned by another player, and the outsider faces it in every
phase. Hence `opponentDivergence` holds for all four players. The candidate
also supplies the otherwise easy-to-omit field
`initial := 0 : Fin 3`. I therefore find every field of
`BalancedSingletonCycleCertificate (L := 3) r` accounted for.

## Baselines, completion, and dimension

The twelve off-diagonal singleton equations determine the twelve
off-diagonal singleton coordinates from the four independent own-solo
baselines. No equation constrains a baseline.

A four-player terminal reward table has
\(4(2^4-1)=60\) coordinates. Four singleton coalitions contribute 16;
the 12 independent off-diagonal equations leave four singleton degrees of
freedom. The 11 coalitions of size at least two contribute 44 unrestricted
coordinates. The fibre dimension is therefore \(4+44=48\).

No nonsingleton reward enters the owner selection, tail recurrence, arc,
active equality, solo floor, or opponent divergence. The checked
`BalancedSingletonCycleCertificate.toWithBounds` derives

\[
\text{collisionBound}=2\,\text{quittingRewardBound}(r)
\]

from the actual finite full reward table. Arbitrarily large positive or
negative nonsingleton entries only change this finite error constant. They
are neither discarded nor silently identified with singleton entries.

## Unrestricted semantic audit

I checked the following declarations in
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`:

- `BalancedSingletonCycleCertificate`;
- `BalancedSingletonCycleCertificate.toWithBounds`;
- `BalancedSingletonCycleCertificate.isTerminalNash_and_hasValue`;
- `BalancedSingletonCycleCertificate.isHorizonNash_and_delivers`;
- `BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`.

The final consumer works in the original quitting game with the full reward
table. It obtains strict deleted-opponent contraction from
`opponentDivergence`, derives the finite collision cap internally, and
controls arbitrary unilateral behavioral deviations, including Never,
randomized stopping, and arbitrarily late clocks. It is not a stationary,
pure-clock, singleton-only, or bounded-controller conclusion. The phase-zero
coarse vector is one fixed delivered target.

## Boundary and source checks

- At \(t=1\), \(h=0\), so opponent divergence fails. The strict hypothesis is
  necessary.
- In a transitive tournament the sink branch can occur and the owner triple
  need not exist. The candidate correctly uses the LCP witness instead.
- The checked disjunction
  `isStandardQ_or_singletonLCPFeasible_of_isIntegralTournament` is not
  exclusive; the candidate does not use exclusivity.
- The possible outsider loss is the sharp positivity case \(1/t>0\).
- Arbitrary baseline shifts preserve all normalized equations.
- Arbitrary nonsingleton rewards are covered only through the derived finite
  collision bound, exactly as the candidate states.
- The candidate's relative links resolve from `exports/`, its mandatory
  headings contain substantive material, and its control-byte scan is empty.

Declarations checked:

- `tournamentSkewMatrix`, `FractionalTournamentHasUnitOutneighbor`, and the
  no-homogeneous-solution theorem in
  `MathUE/LinearProgramming/Tournament.lean`;
- `isStandardQ_tournamentSkewMatrix` in
  `MathUE/LinearProgramming/CopositiveQ.lean`;
- `IsIntegralTournament`,
  `singletonLCPFeasible_tournamentSkewMatrix_of_row_eq_zero`, and
  `isStandardQ_or_singletonLCPFeasible_of_isIntegralTournament` in
  `MathUE/LinearProgramming/CopositiveQCorollaries.lean`;
- `quittingSingletonArcPayoff` in
  `UniformEquilibrium/Quitting/Circulation/SingletonFlowMesh.lean`;
- the balanced-certificate declarations listed above.

## Conclusion

The sink/no-sink split is exhaustive on four-vertex integral tournaments.
The no-sink construction is algebraically exact and semantically consumed;
the sink branch is scoped only as a matrix-gate obstruction. The completion
and deviation quantifiers are honest. I found no counterexample or omitted
certificate field. The candidate passes its required second adversarial
falsification review at SHA
`05bccfe23cadd8e13961ca6dcbeb8f224e9cf5117c3f655438edb1a98ce10bc8`.

## Final lifecycle delta

I rechecked the refrozen candidate at exact SHA
`d4343ecd14be5ba4244374298c6921970b2d83cc668ce1ab67d1f41d88498e44`.
The sole mathematical-packet delta is the link to this review in the
independent-review metadata; the statement and proof remain the packet covered
by the PASS above. Both review links resolve from the intended `exports/`
location, and the candidate has no control bytes. **Delta PASS.**
