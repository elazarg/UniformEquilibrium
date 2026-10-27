# Independent review of two-owner fixed-cap replacements

Reviewer: I2_CONTACT_REVIEW. Ordinary mathematical review; no Lean build.

Reviewed artifact: `math/notes/CODEX_COORDINATOR__TWO_OWNER_CONTACT_REPLACEMENT.md`.
SHA256: `0bdcfa6244e4eec3e49e4c8dfebb3168b1ed1c435930977600e6d1fe28f10bc5`.

**Verdict: PASS for the complete stated source normal form.** No unresolved
mathematical objection remains. The result does not eliminate I2 or produce
an equilibrium. Its compensated quiet-owner activation obligation is explicit.

## Scope checked

The inputs are an actual I2 minimum at a fixed generic native table with
positive absorbing full-debt gap, positive marginal Never masses, zero observer
debts and ALL-END caps. The uniform three-owner dispersion theorem supplies
one constant for every actual conditional two-owner tail; conditional tails
are not assumed to minimize the source objective.

The conclusions checked are the conditional moment rigidity, existence of an
actual replacement retaining the complete semantic tuple and the old head,
the finite-window contact bound, and infinitely many quiet contacts when
late common support is forced. The last conclusion is existential in the
choice of an equivalent actual minimum, not a claim about every minimum.

## Main checks and attempted objections

1. Direct splitting into the five events p-only, i-only, p-first, i-first
   and tie gives the displayed quiet Never payoff. Integrating the partner's
   contact equality gives b=(1/rho-1)T. The pivot debt and all marginal Never
   masses then depend only on P,I,T. The nondegeneracy determinant is exactly
   (1-P)(a_h K_k-a_k K_h). Competing tails in the rigidity statement explicitly
   retain zero observer debts and ALL-END; ALL-END alone would not suffice.

2. Fixing the pivot law fixes the partner's entire response menu. Restricting
   partner atoms to its contact set makes the partner exactly optimal under
   every feasible replacement. Each other pure-deadline comparison is an
   affine continuous functional of the partner law. Together with Never,
   these comparisons cap every privately randomized complete stopping law.

3. Compactness is not inferred from fixed total mass. Every feasible actual
   law is observer-exact and ALL-END, and its conditional tails retain these
   properties. Uniform dispersion and pivot-versus-Never coupling therefore
   give f_i <=(2M/c)f_p, hence I_n <=2M P_n/(c N_p). The pivot law and N_p>0
   are fixed. This proves uniform tightness before taking limits, so there is
   no appeal to an escaped or abstract law. Coordinate convergence plus the
   uniform tail bound gives total-variation convergence, which preserves all
   affine constraints and the moment T.

4. The squared l2 norm is strictly convex and continuous on this compact
   subset of l1. Any maximizer is an extreme point. On a finite physical-date
   interval, the two moment equations and the tied comparison equations give
   the stated dimension count. Strict comparisons in that interval are a
   finite list and remain strict under sufficiently small signed steps.
   Before the interval, fixed partner total mass retains all relevant future
   survival terms; after it, the remaining pair law is identical. Fixed global
   Never payoffs, supplied by the two moments and contact support, show that
   every comparison outside the interval is unchanged. Thus the direction
   really is a two-sided feasible variation in the infinite feasible set.

5. The retained tuple fixes U,B,N coordinatewise, not just the pivot objective.
   The exact finite-head recursion therefore retains the whole source tuple
   with the old head unchanged. Infinite partner support follows from uniform
   dispersion applied to any supposed eventual pivot-only tail.

6. The raw O screen gives eventual common support for the replacement by the
   same contact and comparability argument. If both quiet players had only
   finitely many ties, the interval bound would leave at most two late partner
   atoms without pivot contact. Eventually both atom rates would be constant,
   rho and s=A/C. Infinite tails make 0<s<1. Comparability forces s=rho,
   contradicting A-rho C>0 (equivalently GC-AJ !=0). Cases C=0 or absence of
   admissible pivot contacts already contradict the contact count.

## Source and overlap check

I inspected the uniform dispersion theorem and the actual I2 source and raw
screens in the current residual partition, as well as the fixed-cap controlled
window result. The latter requires full-support windows and a raw concavity
criterion; it does not provide this compact pair-law replacement. The splice
source names are `quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`) and
`quittingTerminalSemanticPair_rootThenContinuation`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`). This review
confers no new Lean or actual-to-UE consumer seal.

The canonical note correctly remains an internal source normal form. Infinitely many
quiet ties make activation feasible at the level of the entrant's comparison;
they do not supply a compensating variation or a strict pivot-objective descent.

## Canonical artifact and inherited-head check

I reread the complete canonical artifact and compared it with the reviewed
source draft. Its mathematical core is unchanged. The appended inherited-head
paragraph is also correct: if joint head survival is s and opponent head
survival is h, then h/s=1/N_p(head). Dividing the full source objective by s
gives, up to a head-dependent additive constant, the variable expression
lambda B_p-U_p+r nu on the branch continuing through the head. The exact
functional retains the maximum of this cap branch and the old finite-response
branch. The warning at a tie is necessary and correctly stated. No tail
minimality is inferred. This final-artifact verdict covers that addition as
well as the entire replacement theorem.
