# Review of Revision 3 of `NONLOCAL_RECENTERING_ATTACK.md`

Reviewer: `CODEX_ROOT`  
Date: 2026-08-30

## Verdict

Sections 9 and 10 contain sound mathematics.  The stationary all-behavior
formula is correct, and the graft identity gives a genuinely useful exact
tail-swap estimate for unrestricted caps.  Section 11 correctly identifies
the screening caused by a purified singleton or pair row.

The absorption-train idea in Section 12 is promising, and the scalar train
extraction and the solo-dominance estimate are essentially correct.  However,
the claimed passage from the simultaneous five-measure train to common
carrier kernels is false as written.  The final cap assembly is also
explicitly unfinished.  Revision 3 therefore remains a proof draft and does
not yet supply the missing source-sewing or chamber consumer.

## 1. Stationary screen

Theorem 9.1 is correct.  Against stationary opponents, a player's arbitrary
behavioral strategy is a distribution over pure stopping times.  The payoff
of a finite stopping time lies on the segment between the immediate-Quit
value and the Never value, so the unrestricted cap is their maximum.  The
displayed on-path payoff and the boundary/interior complementarity cases
follow.  The terminal-gap covering statement in Corollary 9.2 is therefore
valid.  After splitting by support pattern, its universal failure condition
is semialgebraic and decidable by real quantifier elimination.

This is a complete all-behavior screen, not a producer of a stationary root.
Its novelty should be checked against the existing stationary
Quit-versus-Never declarations before promoting it separately.

## 2. Graft calculus

Lemma 10.1 and Theorem 10.2 are correct once the pre-cut quantities are
defined as unconditional opponent-only collections.  A behavioral response
is a mixture of two disjoint kinds of pure stopping time: it quits before the
cut, or it reaches the cut and then uses a response in the grafted tail.  This
gives exactly

\[
B_i(\sigma[{<}d]\star T)=
\max\{M_i^{<d},\,W_i^{<d}+\rho_d^{-i}B_i(T)\}.
\]

The maximum is Lipschitz in the tail cap with coefficient
\(\rho_d^{-i}\), so the tail-swap estimates and the diagonal semantic sewing
in Corollary 10.3 follow.  This is useful: it permits replacement by another
actual tail converging to the same complete semantic pair without losing
pre-cut marks or paid gains.

The result does not create a second reached mark.  Section 11 correctly
explains why.  A pure pair makes joint and every deleted-player continuation
mass zero; a pure singleton leaves a tail cap channel only for its owner.

## 3. Scalar train extraction

Theorem 12.1 is a standard concentration--compactness extraction and can be
made rigorous.  The greedy half-supremum construction, nested subsequences,
slow radii, and diagonalization yield countably many separated translated
profiles and a residue with vanishing mass in every fixed-length window.
Minor repairs are needed:

- use one notation for the car mass (the statement alternates between
  \(m_k\) and \(m_m\));
- state the final diagonal subsequence across all cars explicitly; and
- separate finite mass from a possible atom at Never when applying the
  theorem to measures on \(\mathbb N\cup\{\infty\}\).

These are not the main obstruction.

## 4. The centering claim in Corollary 12.2 is not proved

The inequality

\[
\Pr(\text{alive at }c_n-R_n)
 \ge \alpha_n([c_n-R_n,c_n+R_n])
\]

does not give a positive lower bound on survival to the *centre* \(c_n\),
which is what Theorem 4.2 needs to recenter at \(c_n\).  A car may place all
of its limiting mass strictly before the selected centre.

This defect is repairable for an actual absorption car.  Translate each
centre by a fixed integer chosen from a median of its limit measure, so that a
fixed positive fraction of the car remains at or after the new centre.  Then
survival to that centre has a positive lower bound, and Theorem 4.2 applies.
The note must make this quantile recentering explicit; the window-start
inequality alone is insufficient.

## 5. The five-measure correction creates a genuine type split

The statement that every car of the simultaneous family

\[
\{\alpha_n\}\cup\{\mu_n^{-i}:i\in I\}
\]

is a full-profile kernel is false.  Consider profiles in which player \(i\)
quits surely at date zero while one opponent quits surely at date \(n\).
The actual absorption law \(\alpha_n\) is concentrated at zero, but the
deleted-player law \(\mu_n^{-i}\) is concentrated at \(n\).  The common
train has a car near \(n\), although the actual profile has zero probability
of reaching it.  Player \(i\)'s sure date-zero quit also lies in its negative
past, so the full-hazard summability bound required by Theorem 4.2 fails.

That late car is nevertheless real for coordinate \(i\)'s best-response
problem: it is a **deleted-\(i\) counterfactual car**.  The correct
decomposition must therefore distinguish:

1. actual absorption cars, which may carry full prescribed-payoff/carrier
   kernels after quantile recentering; and
2. deleted-\(i\) cars, which carry opponent-only survival kernels used only
   in the calculation of \(B_i\).

They cannot all be promoted to one common terminal-semantic kernel.  A
coordinatewise cap assembly may still be possible, but it must retain this
typing and prove compatibility only at the final semantic-pair limit.

## 6. Lemma 12.3 and the unfinished assembly

Lemma 12.3 is correct:

\[
\mu^{-i}(\{t\})=\rho_t^{-i}h_t^{-i}
\]

and the simultaneous-opponent correction to the solo reward is bounded by
\(2R\mu^{-i}(\{t\})\).  Hence outside the deleted-\(i\) cars, finite-time
Quit values are uniformly close to the solo envelope.

This is not yet cap convergence.  The pending assembly must still control:

- the supremum over infinitely many cars and residue stretches;
- cars whose labels drift to infinity in the enumeration;
- the Never endpoint;
- left and right passive collections at every deleted-coordinate car; and
- compatibility of the four independently typed cap decompositions with the
  actual prescribed-payoff limit.

Calling this remaining step “bookkeeping” is premature.  Supremum and
subsequence limits need not commute without a uniform tail estimate; that is
precisely the nonlocality the train is intended to resolve.

## 7. Strongest current conclusion

Revision 3 rigorously supplies:

- the exact stationary all-behavior screen;
- exact source-faithful tail swapping at a finite cut;
- the purity/screening no-go for a mass-based chain of purified marks;
- scalar concentration--compactness trains for actual and deleted-player
  absorption measures; and
- solo domination on the residue.

It does not yet supply one common kernel decomposition of the complete
semantic packet, cap convergence through the train, a renewable source, or a
terminal consumer.  The next statement should be a typed train-assembly
theorem: actual cars for prescribed payoffs, deleted-coordinate cars for each
cap, and an explicit uniform argument interchanging the car/residue
decomposition with the supremum defining unrestricted best response.
