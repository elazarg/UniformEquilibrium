# Review of normalized paid finite-cut descent

**Reviewer:** CODEX_EULER  
**Date:** 2026-08-25  
**Target:**
[`notes/CHATGPT_EXTERNAL__NORMALIZED_PAID_FINITE_CUT_DESCENT.md`](../notes/CHATGPT_EXTERNAL__NORMALIZED_PAID_FINITE_CUT_DESCENT.md)

## Verdict

**REVISE.** The fixed-source, fixed-label finite-cut lemma is correct after a
small row-packaging clarification. The proposed unconditional marked-class
infimum closure is not proved. In particular, the checked producer does not
supply a label-mass lower bound uniform over renewed marked sources, and the
suggested approximate-minimizer choice uses a descent constant defined only
after that minimizer has been selected. The inert all-Continue arm gives the
literal zero-mass boundary.

The strongest valid result is therefore a conditional local descent theorem,
not a well-founded closure theorem. The note should remain internal. Its local
calculation is mostly a composition of checked declarations and has no current
consumer satisfying the export gate.

## 1. Exact local theorem that survives

Fix one `source : QuittingPaidCapLiftedSource reward`. Write

\[
D_N=D(x_N),\qquad D_0=D(x_0),\qquad D_*=D(\text{source.minimum})>0,
\]

and let the two original pure-time witnesses have exact payoff difference
\(\Delta _0>0\). Let \(P_N\) be the joint suffix reach and \(R_N\) the
observer-deleted reach. Suppose one fixed nonempty terminal coalition \(T\)
satisfies

\[
  0<\mu\le \sum_{n\ge0}m_n(T),
\]

where \(m_n(T)\) is the coalition mass of \(T\) under the selected cap root at
stage \(n\). Then, for

\[
  \theta=\Delta _0/D_0>0,
\]

every finite prefix satisfies

\[
  \Delta_N=R_N\Delta_0\ge P_N\Delta_0=\theta D_N
  \ge \theta D_*.
\]

For every \(0<\lambda<1\), some finite \(N\) also satisfies

\[
  D_N\le D_0-\lambda D_*\mu.
\]

This is an actual finite prefix profile, not merely a semantic-port limit.
The conclusion preserves a paid-density **lower bound** \(\Delta_N/D_N\ge
\theta\); equality of the normalized density is neither asserted nor needed.

The positivity of \(D_0\), which is needed to define \(\theta\), follows from
`QuittingPaidCapLiftedSource.initialDebt_pos`.

## 2. Density calculation

The following checked declarations in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`
give the calculation directly:

- `quittingCapLiftedPrefixProfile_debt_eq_suffixReach_mul` gives
  \(D_N=P_ND_0\);
- `QuittingPaidCapLiftedSource.suffixReach_le_observerReach` gives
  \(P_N\le R_N\); and
- `QuittingPaidCapLiftedSource.pureTimePayoff_sub_shift` gives the exact
  shifted difference \(\Delta_N=R_N\Delta_0\).

All reach factors are nonnegative. Hence multiplication preserves the
inequality and gives

\[
R_N\Delta_0\ge P_N\Delta_0
=P_ND_0(\Delta_0/D_0)=D_N\theta.
\]

This calculation does not require a cap-to-prescribed-payoff conversion.

## 3. Exact paid-row packaging

The shifted pure-time witnesses themselves carry the inequality
\(\Delta_N\ge\theta D_N>0\). To package this as a
`QuittingPaidFirstDisagreementRow` with gain parameter \(\theta D_N\) (or the
uniform weaker parameter \(\theta D_*\)), explicitly invoke

`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`.

The existing `QuittingPaidCapLiftedSource.nonempty_shiftedPaidRow` is closely
related, but its `ShiftedPaidRow.row` is parameterized by the checked constant
`source.reachFloor * source.gain`. One should not silently change that
structure field to \(\theta D_N\). A fresh application of the decoder to the
exact shifted payoff inequality is the clean handoff.

The decoder preserves the observer and uses precisely the shifted two pure
times. Thus this is an exact finite row, with unrestricted behavioral
semantics inherited from the pure-time extremality/decoder interface; it is
not a Bellman edge or a prescribed-payoff chronology.

## 4. Finite labelled-mass cut and debt drop

The terms \(m_n(T)\) are nonnegative and obey
\(m_n(T)\le a_n\), where \(a_n\) is total cap-root absorption. Since their
series has sum at least \(\mu>0\), monotone convergence of finite partial sums
gives, for every \(0<\lambda<1\), a finite \(N\) such that

\[
  \lambda\mu\le\sum_{n<N}m_n(T)
  \le\sum_{n<N}a_n.
\]

Then
`QuittingPaidCapLiftedSource.minimum_mul_partialAbsorption_le_debtDrop`
gives

\[
 D_*\sum_{n<N}a_n\le D_0-D_N,
\]

and therefore

\[
 D_N\le D_0-\lambda D_*\mu.
\]

This is the advertised finite partial-sum descent. The display in the target
currently contains the Markdown/LaTeX typo `m_n(T)le`; it should read
`m_n(T)\le`.

`SummableChargeSignedTerminalPort.mass_lower` is a valid way to obtain such a
fixed \((T,\mu)\) when a particular nonzero port displacement \(\rho\) is
already supplied. It gives the source-dependent scale

\[
 \mu=\rho/\bigl(2M(2^{|I|}-1)\bigr).
\]

It does not make this scale uniform over a renewed class of sources.

## 5. The marked-class infimum argument is circular

Let \(m=\inf_{\sigma\in\mathcal M_\theta}D(\sigma)\). The proposal would pick
\(\sigma_0\) with

\[
 D(\sigma_0)<m+\kappa(\sigma_0)/2,
 \qquad
 \kappa(\sigma_0)=D_*\mu(\sigma_0)/2.
\]

The infimum property only permits choosing an approximate minimizer after a
fixed positive tolerance has been specified. Here that tolerance is known
only after the point has been chosen. Nothing in the checked producer excludes
\(\mu(\sigma)\to0\) along every sequence approaching \(m\).

A scalar model isolates the error. Take marked states \(x\in(0,1]\), debt
\(D(x)=x\), and a valid local move \(x\mapsto x/2\) whose certified decrease is
\(\kappa(x)=x/2\). Every state admits a strict state-dependent descent, but
\(\inf D=0\) and there is no contradiction. This has exactly the logical form
of a displacement/mass scale vanishing near the infimum.

With a genuine uniform constant

\[
 \exists\mu_*>0\ \forall\sigma\in\mathcal M_\theta,
 \quad \sum_n m_n(T_\sigma)\ge\mu_*,
\]

the argument would become valid: first fix
\(\kappa_*=D_*\mu_*/2\), then choose a \(\kappa_*/2\)-approximate minimizer,
and apply the local cut. No current declaration supplies this producer.

## 6. Nonemptiness and closedness of the proposed marked class

The initial paid source makes an appropriately defined marked class nonempty.
But `actual profiles carrying paid difference at least theta*D(profile)` must
be formalized carefully. At minimum it must existentially package:

- a positive debt and positive paid gain;
- an observer;
- two pure-time witnesses in `Option Nat` with their orientation; and
- the payoff-difference inequality.

Without positivity, a zero-debt profile with a zero difference would satisfy a
bare inequality vacuously and would not be a renewable paid source.

Closedness is not automatic. For fixed finite witnesses the payoff inequality
is closed, but the existential union ranges over countably many pure times.
Those witnesses can escape to the `Never` boundary, and a countable union of
closed witness slices need not be closed. A proof via an enriched compact
profile-and-witness space would need an explicit compact topology, continuity
of the pure-time payoff evaluation including `Never`, and closedness of the
projection. None of this is supplied in the proposal.

If one instead proved that the marked debt minimum is attained and that its
minimizer has one positive labelled mass, no global uniformity would be
needed: apply the source-dependent cut once at that minimizer. But both
attainment and non-inertness at the minimizer remain open.

## 7. The inert boundary is a genuine obstruction

In the checked zero-total-absorption arm, every selected cap root is literally
all Continue. The original paid row persists through every prefix, but cap
displacement \(\rho\) and the signed label-mass floor \(\mu\) are zero. Thus
the normalized paid mark alone does not force any positive finite-cut debt
drop.

This agrees with the exact boundary in
`PaidCapPortExactTrichotomy.lean`: positive total absorption pays debt drop;
positive displacement pays a quantitative drop through the absorption bound;
the remaining \(A=0\) case is literal inertness with persistent rows. The
finite-cut proposal does not eliminate that arm.

## 8. Strongest valid conditional closure

The following two distinct additional hypotheses each suffice:

1. **Uniform regeneration:** a fixed \(\mu_*>0\) works at every renewed marked
   source. Then the infimum argument yields a contradiction.
2. **Attained non-inert minimum:** \(D\) attains its minimum on a correctly
   defined marked class, and the minimizing source has some fixed terminal
   label of positive total mass. Then the one-source finite cut contradicts
   minimality.

Neither hypothesis follows from paid-density preservation, and neither is a
current output of the same-source cap-port construction.

## 9. Novelty and export recommendation

The exact local proof is a useful, transparent combination of already checked
prefix scaling, labelled mass, and finite debt-budget declarations. The only
small new wrapper is the debt-normalized application of the existing paid-row
decoder plus finite partial-sum selection. It does not close the inert port,
produce uniform marked regeneration, or furnish a well-founded rank.

Therefore:

- **local finite-cut lemma:** PASS after the explicit decoder handoff and the
  density/typo wording repairs above;
- **unconditional marked-class closure:** FAILS as presently stated;
- **export/formalization recommendation:** keep internal. Do not export a
  conditional fixed-\(\mu\) producer as though its uniform source hypothesis
  had been constructed.

