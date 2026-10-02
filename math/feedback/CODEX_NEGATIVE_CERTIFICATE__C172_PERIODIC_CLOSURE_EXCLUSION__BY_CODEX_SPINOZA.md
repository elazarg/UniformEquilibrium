# Review of the C172 period-four exclusion certificate

Identity: CODEX_SPINOZA

Date: 2026-09-02

Verdict: **PASS as exact ordinary mathematics, with two scope
clarifications.** The radical period-four profile is an exact terminal Nash
profile against unrestricted behavioral deviations. The complete C172 table
therefore has a uniform-equilibrium payoff and cannot carry a positive
terminal exploitability gap. The twelve-inequality family is also sound.

This is a strong candidate exclusion and a reusable exact search screen. It
does not by itself satisfy any output of
questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md: its singleton rows are
fixed equalities, it is not a complete residual chamber produced by the
finite outer hierarchy, and the candidate-specific radical data are not a
Lean instance.

## 1. Claim checked

I checked the following claims in
notes/CODEX_NEGATIVE_CERTIFICATE__C172_PERIODIC_CLOSURE_EXCLUSION.md:

1. the four hazards and return in \(\mathbb Q(\sqrt{889})\);
2. all sixteen Bellman coordinates and four owner indifferences;
3. all twelve outsider pair inequalities and displayed slacks;
4. all four opponent-cycle survival products and their \(1/9\) bounds;
5. the upgrade from phasewise root inequalities to arbitrary behavioral
   unilateral deviations, including Never and arbitrarily late stops;
6. the count and scope of the free reward coordinates;
7. the rational stationary payoff, full unilateral caps, and debt bound; and
8. the finite-clock truncation estimate.

The semantic checker used for comparison was
QuittingCyclicRepairCertificate in
UniformEquilibrium/Diagnostics/Quitting/ExactRepairCertificate.lean.

## 2. Radical return and owner equations

Put \(s=\sqrt{889}\) and

\[
 a=\frac{517-11s}{450},\qquad b=\frac{1+7s}{270}.
\]

Substitution into the displayed rational return map gives exactly

\[
 z^4-z^0=(0,0,0,0).
\]

For the owner order \(0,1,3,2\), exact simplification gives

\[
\begin{aligned}
q_0&=(517-11s)/300,\\
q_1&=16/9-5s/126,\\
q_3&=(12209-205s)/14424,\\
q_2&=(241-7s)/60.
\end{aligned}
\]

The elementary bounds \(29<s<30\) prove \(0<q_j<1\) in all four cases.
For every phase \(k\), direct substitution gives all four coordinates of

\[
 z^k=(1-q_j)z^{k+1}+q_j E_{\bullet j}.
\]

The active owner's current and next excess coordinates are both zero. Since
every own singleton payoff is one, the owner's Quit and Continue endpoints
are both one. Thus the four support equalities are genuine owner
indifferences, not only policy equations.

## 3. Twelve outsider inequalities

For outsider \(i\) at owner \(j\)'s phase, the note's identity

\[
 C_i-Q_i
 =q_j\left(\frac{(1-q_j)z^{k+1}_i}{q_j}
 -\bigl(r_i(\{i,j\})-r_i(\{j\})\bigr)\right)
\]

is exact. A unilateral replacement can realize only \(\{i\}\) or
\(\{i,j\}\), so no omitted coalition coordinate enters this comparison.

Independent symbolic substitution reproduced every displayed threshold:

\[
\begin{array}{c|ccc}
j=0&i=1:0&i=2:1/3&i=3:(-103+5s)/198\\
j=1&i=0:1/3&i=2:(-73+5s)/264&i=3:0\\
j=3&i=0:(-55+5s)/192&i=1:1&i=2:0\\
j=2&i=0:0&i=1:(-19+s)/30&i=3:2/3.
\end{array}
\]

The C172 ordered pair increments are respectively

\[
(-7/6,1/4,-3/2),\quad
(1/4,-7/6,-7/6),\quad
(-7/6,1/4,-3/2),\quad
(-7/6,-3/2,1/4).
\]

All twelve are strictly below their thresholds. Exact simplification also
reproduced all twelve slack expressions printed in the note, with zero
difference. Their positivity follows from \(29<s<30\). Hence every phase
root is exact Nash against its displayed successor.

## 4. Opponent contraction and unrestricted deviations

Deleting deviator \(i\)'s own prescribed marginal leaves the product of the
other three owner survivals. The four exact products simplify to

\[
\begin{aligned}
h_0&=-5/3+5s/84,\\
h_1&=-7427/4808+265s/4808,\\
h_2&=-473/1080+19s/1080,\\
h_3&=-13841/1200+467s/1200.
\end{aligned}
\]

All lie strictly in \((0,1/9)\). The only bounds not immediate from
\(29<s<30\) are still elementary exact square comparisons. For example,

\[
 h_0<1/9\iff s<448/15,
\quad 889\cdot225=200025<200704=448^2,
\]

and the tight upper bound for \(h_3\) is

\[
 h_3<1/9\iff 1401s<41923,
\quad
 889\cdot1401^2=1744930089<1757537929=41923^2.
\]

Positivity of \(h_3\) follows from

\[
889\cdot467^2=193881121>191573281=13841^2.
\]

This contraction is exactly the field required by
QuittingCyclicRepairCertificate.contracts.

There is no hidden restriction to stationary or bounded-period deviations.
Against fixed periodic opponents, the only live public history determines a
phase. A deterministic unilateral strategy is a phase-indexed pure stopping
time, including Never; a behavioral strategy is a probability law over
those pure times. Iterating the four local Bellman inequalities dominates
every finite pure stop. The residual continuation term after \(L\) cycles is
bounded by \(h_i^L\) and vanishes, which covers Never and stops tending to
infinity. Linearity then covers every behavioral mixture. Equivalently, the
checked cyclic certificate theorem performs exactly this upgrade.

The joint four-owner survival is about \(0.03999\), hence below one. The
periodic Bellman solution is therefore unique and equals the actual
geometric terminal payoff; the annotations are not phantom values.

## 5. Chamber scope

The scope claim is correct, with a useful counting clarification.

- The sixteen singleton coordinates are fixed.
- The twelve pair-member coordinates vary subject to the displayed upper
  bounds on their ordered increments.
- The twelve pair-spectator coordinates are completely arbitrary.
- All twenty coordinates of the four triples and grand coalition are
  completely arbitrary.

Thus exactly thirty-two coordinates are unrestricted, as claimed. The
relative semialgebraic family actually has forty-four variable coordinates:
the thirty-two unrestricted coordinates plus twelve independently
upper-bounded pair-member coordinates. Calling it a “32-free-coordinate
chamber” is sound if “free” means completely absent from the proof; it should
not be read as saying the entire family has dimension thirty-two.

Arbitrary values in the thirty-two coordinates cannot affect a deviator's
payoff under a one-owner phase, so the exact periodic equilibrium remains
valid throughout this family.

## 6. Rational stationary audit

For

\[
q=(3/1024,13/512,1/256,5/1024),
\]

direct exact coalition enumeration reproduces all four displayed prescribed
payoffs.

For player \(i\), stationary opponents reduce every pure stopping time to a
convex combination of two endpoints: Quit immediately, or Never and accept
the first opponents-only coalition. Because opponent absorption is positive,
the unrestricted behavioral cap is the maximum of those two rational
values. Exact enumeration gives precisely

\[
(533325977/536870912,\ 66631/61748,\
344015443/212541732,\ 78928987/51606996).
\]

The maximizing endpoint is immediate Quit for player \(0\) and Never for
players \(1,2,3\). Subtracting the prescribed payoff shows that player \(0\)
has the largest debt,

\[
\frac{593830313859663199}{8139042563882483712}
<\frac3{40}<\frac1{10}.
\]

Thus the stationary calculation is an exact unrestricted-cap regression,
not a finite deviation-menu computation.

## 7. Finite truncation

Truncate all prescribed hazards after \(L\) full cycles. For the prescribed
payoff, the two profiles differ only if all four owners survive those cycles,
an event of probability \(P^L\le h_i^L\). For a unilateral deviation by
player \(i\), couple the two opponent profiles. They differ only if the other
three prescribed owners survive \(L\) cycles, an event of probability
\(h_i^L<9^{-L}\), uniformly over the deviator's complete behavioral rule.

Because all rewards have absolute value at most \(2\), the payoff difference
under either coupled experiment is at most \(4\) times the exceptional
probability. Taking the supremum over deviations preserves the bound, so

\[
|U_i^L-U_i|\le4\,9^{-L},\qquad
|B_i^L-B_i|\le4\,9^{-L}.
\]

The infinite periodic profile is exact terminal Nash, hence \(B_i=U_i\), and
therefore

\[
\operatorname{Expl}(\sigma_L)\le8\,9^{-L}.
\]

The phrase “event on which the cap changes” should be understood as this
uniform coupling for every deviation; a cap itself is a supremum, not a
random event. With that interpretation, the truncation argument is correct.

## 8. Export and escape-aware relevance

The note is export-relevant as a reviewed exact exclusion packet after the
minor scope clarifications above. A useful export would state:

1. the explicit C172 table has the displayed exact period-four terminal Nash
   profile;
2. the twelve threshold inequalities give a uniform-payoff chamber with
   thirty-two completely irrelevant coordinates; and
3. the finite truncations have the explicit all-behavior error bound.

It does **not** answer ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH. In particular:

- it supplies an upper/exclusion certificate, not a positive lower
  certificate;
- it does not give a terminating decision algorithm;
- it does not arise as a proof-producing elimination of one complete live
  outer-hierarchy residual chamber; and
- the fixed singleton equalities make it an affine slice rather than an open
  normalized reward-table chamber.

Its exact contribution to that question is as a mandatory regression and a
hard rejection screen: any search retaining all twelve weak inequalities on
these singleton rows must discard the candidate before attempting a
positive-gap certificate.
