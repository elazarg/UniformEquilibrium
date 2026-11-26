# Independent mathematical review: passive-bound triple selection

Reviewer: NEVER_DOMAIN_REVIEW.

**Verdict: PASS, with no unresolved mathematical objection.** This review
checks the entire export, Sections 1--8, as ordinary mathematics. It includes
an adversarial check of the unrestricted behavioral consumer and independent
exact calculations for the final example and its controls. It does not certify
Lean compilation or settle arbitrary Fin4.

Reviewed artifact: `math/exports/PASSIVE_BOUND_TRIPLE_SELECTION_UNIFORM_EQUILIBRIUM.md`.
The reviewed bytes were supplied as `/tmp/PASSIVE_BOUND_TRIPLE_SELECTION_PACKET.md`,
580 lines, SHA-256:

    fb8d0ebe59dd05959f09c03bcd53fc6b6cf147e562305c98abda7a2811112a14

Approval is scoped to these exact bytes. Earlier drafts do not substitute for
this whole-artifact review.

## 1. Claim and strategic completeness

The raw conditions (R), (Q0), and either branch of (Q1) produce absorbing
independent profiles with total native terminal Nash debt tending to zero.
For nonnegative original own levels, this gives one fixed uniform-equilibrium
payoff against every complete unilateral behavioral replacement. There are
no supplied strategies, continuation values, roots, punishment objects,
minimizers, or realized certificates among the theorem's premises.

**Unproduced strategic inputs: none.** The finite raw inequalities are actual
reward-table hypotheses, not strategic data. Nash existence, separation,
compactness, degree, and the stated terminal-to-uniform endpoint are the
mathematical inputs. The packet gives its own closed-domain consumer rather
than claiming that the existing low-output consumer directly handles sure
roots.

The first-Quit-time representation includes all complete behavioral deviations:
before absorption the live public history is unique, and a deviator's first
Quit law mixes all finite deadlines and literal Never. The cap recurrence is
therefore a full best-response recurrence. The final shift comparison uses
absorption and nonnegative own levels correctly; it does not assert an affine
normalization for arbitrary nonabsorbing profiles.

## 2. Raw algebra and root selection

I checked the elimination of active player 0, singleton supports, and pairs
13 and 23. For the remaining pair and triple, dividing by positive opponent
survival gives exactly (5)--(6). When W=0, the positive second component of
these equations is incompatible with the passive bound.

For W>0, the estimate x_1<X applies to every positive triple candidate.
The Q_3 inequality has a positive denominator by G>0. Substituting its strict
bound for x_2 in phi_3 gives (7), with the displayed numerator and signs.
The affine endpoint tests imply nonnegativity on the whole interval; strict
positivity of v_3 survives equality in either endpoint guard. The resulting
bound x_2<Y then establishes BLOCK directly.

Under INDEX, the determinant formula and lower bound (9) are valid even when
c_12<0. Its negative contribution is bounded using upper bounds for both
positive factors, whereas B'C F' uses positive lower bounds. Solving the
second and third equations gives a connected feasible interval, and the
derivative of the first equation is det(Dphi)/(D'F'). Thus there is at most
one bad triple, with nonsingular positive active determinant.

The clipped map has total ambient degree +1. Strict inactive rows contribute
identity rows to Id-T; the active block contributes the factor (-1)^k.
Hence the bad triple and the permitted regular bad pair have index -1.
Inactive player 0 is automatically strict at every bad root, because its
Continue output is positive and its Quit offer is nonpositive.

The pair degeneracies are removed without a global regularity assumption.
When c_12=0, perturb v_1 away from zero. When c_12>0, there is at most one
pair candidate and its inactive-player-3 tie excludes only one v_3 value.
The mixed singleton signs give nondegenerate passive intervals in those two
coordinates, permitting relative perturbation at box boundaries while
preserving a strictly negative minimum. Assuming every root bad then leaves
at most two isolated negative-index roots, contradicting total degree +1.
Closedness of both Nash and good-root graphs removes the perturbations.
For min v=0, AllContinue is already a good root. These arguments prove (V)
on the entire literal closed passive box, including its degenerate faces.

## 3. Closed-domain local induction and actual profiles

I recomputed the residual identity following (4). Its three terms have the
stated nonnegative signs. Together with B>=e and B>=U it forces U=B=e in
the passive domain at every positive-survival zero-debt endpoint. No bound
on an intermediate prescribed payoff by its passive interval is needed.

The local proof uses closedness of the *good* correspondence only. It does
not silently require all nearby roots to be small. The kernel alternative
has core drift O(epsilon^2), cap offers O(epsilon), and a fixed small total
hazard; positive outsiders retain a strict Continue buffer.

In the separating alternative, the exact solo-column seed lies in the
closed domain and has a zero coordinate, while its signed weighted value
is positive. Its initialized caps are explicitly virtual. This avoids an
unjustified interior perturbation and any claim that the solo prefix itself
has those caps. The choices delta<eta/16 and
c_0=min(eta/4,rho/(8M),1/4) give both the displacement estimate and the
strict survival slack used at the minimizing fiber.

At a nonzero good root, the same zero-debt fiber persists and survival
strictly decreases. If only AllContinue remains good, the positive weighted
value excludes the full old zero set. Induction therefore applies to a
strictly smaller zero set. Every inner word preserves the original signed
inequality, because its support remains in the old zero set. Approximation
of the old compact endpoint followed by each finite extension, with strict
survival slack, places the new limit in the original minimizing closure.
No conditional tail receives a reset Never mass. Uniform nonexpansiveness
then removes the seed without a word-length restriction.

The actual carrier argument uses the original marginal Never masses.
Moving a smallest mass changes four prescribed payoffs and three opponent
caps by at most 2M times that mass each, while the moved owner's cap is
unchanged. Thus the coefficient 14M in (16) is valid. The all-Never point
makes the zero-debt carrier nonempty. Positive A_Z would force a positive
minimum Never product; a nonzero good root or the local escape decreases
that same minimum. This proves A_Z=0 for the complete deviation class.

## 4. Numerical corollary and final exact controls

I independently checked the Section 6 substitutions, including alpha=190,
the affine slope 58, and Delta>24719/2. BLOCK covers a<=0; INDEX covers
a>=1/2 and a>=0,p=0. Their union therefore covers every real a when p=0,
under the stated raw caps. The remaining opposed-pair strip is expressly
a boundary of this producer, not an exhaustive Fin4 frontier.

For Section 7 I reconstructed all sixty native entries using exact rational
arithmetic. Direct checks verify W=10, c_21=19999/10000, c_12=-1/4,
J_21<0, X<6, F>59, G>94, Y<72/59<2, B_*>93, and the stated strict
lower bound for Delta. The nontrivial participant caps are strict. The
finite maximum W is continuous; consequently the strict guards and positive
own levels persist in an open neighborhood of all sixty original rewards.

Exact enumeration of the safe-positive edges gives precisely
0->1, 1->0, 0->2, 2->1, 2->3, 3->0. Every one of the fourteen proper
nonempty marked sets has an entering edge. The proposed sole-quitter
witness satisfies all quiet comparisons for sufficiently small epsilon and
has strictly positive outputs on the marked set.

Independent symbolic coalition expansion for the full marked set gives the
five leading coefficients, in the packet's order:

    1/8, 53/20000, 10, 24803/800, -47/200.

They establish all strict margins for sufficiently small positive epsilon.
Every passive interval contains zero in its interior. Thus all fifteen
controls occur in the closed passive box and in every open neighborhood of
zero. They refute universal one-step marked invariance, not selected return;
the packet correctly labels their continuations virtual.

I independently recomputed the modified J_21=1 boundary. Its output is
(249/100,1/40,1/10,159/20); the two active indifferences hold exactly, and
the quiet Quit offers are -2099/10000 and -809/100. In particular the first
number includes the final Z_0(01)=-1/100 entry. Both quiet comparisons are
strict, and the joining product -3/4 yields ambient index +1. This control
shows the limitation of the negative-index argument, not failure of UE.

## 5. Evidence and remaining scope

The unrestricted behavioral conclusion is proved in the packet's ordinary
mathematics. No Lean command or build was run for this review, and no new
L, A, or C seal is asserted. Section 8 correctly distinguishes its new
closed-domain low-or-sure adapter from existing named formal interfaces.
The displayed negative reciprocal products and premium core cardinality
also verify the stated failures of the three specifically named raw sources.

The separate finite audit of stationary, sure-first, child-lift, reset, and
weighted producers is not a premise in this proof. I did not independently
rerun that broader audit in this review. Its result requires its own pinned
coverage reviews. No unrestricted exploitability gap follows from producer
exclusions. The packet preserves this distinction and explicitly leaves the
full Fin4 conjecture open.
