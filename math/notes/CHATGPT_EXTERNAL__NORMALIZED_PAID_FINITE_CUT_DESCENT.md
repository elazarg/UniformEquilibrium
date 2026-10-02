# Normalized paid finite-cut descent

**Author:** external ChatGPT submission supplied by the user  
**Status (2026-08-25):** two independent reviews pass the fixed-source,
fixed-label finite-cut marked-descent lemma and reject the claimed
unconditional well-founded closure.  The signed mass floor is
source-dependent and can vanish along renewed sources.

Independent reviews:

- [`CODEX_RAMSEY`](../feedback/CHATGPT_EXTERNAL__NORMALIZED_PAID_FINITE_CUT_DESCENT__BY_CODEX_RAMSEY.md)
- [`CODEX_EULER`](../feedback/CHATGPT_EXTERNAL__NORMALIZED_PAID_FINITE_CUT_DESCENT__BY_CODEX_EULER.md)

## Self-contained local question

Let `source : QuittingPaidCapLiftedSource reward`, with literal prefix profiles
`x_N`, cap roots `q_N`, total debts `D_N`, joint suffix reaches `P_N`, and paid
observer reaches `R_N`.  Suppose the original paid witnesses have exact payoff
difference `Delta_0>0`.  Let a fixed nonempty terminal label `T` on the same
cap roots satisfy

\[
0<\mu\le\sum_{n=0}^{\infty}m_n(T).
\]

Can one cut at a finite actual profile which both strictly decreases total
debt and retains a renewable paid mark?

## Surviving finite-cut calculation

The checked identities give

\[
D_N=P_ND_0,\qquad P_N\le R_N,qquad
\Delta_N=R_N\Delta_0.
\]

With paid density

\[
\theta=\Delta_0/D_0>0,
\]

one obtains

\[
\boxed{\Delta_N\ge\theta D_N.}
\]

Thus every finite literal prefix carries the same observer, temporal
orientation, relative delay, and normalized paid density.  Since
`D_N>=D_*>0`, it also carries an ordinary row with gain at least
`theta*D_*`.  The existing `ShiftedPaidRow` is parameterized by the coarser
fixed gain `reachFloor*source.gain`; to package the sharper normalized gain,
invoke `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` again
on the same shifted witnesses and the displayed lower bound.

Given `0<lambda<1`, nonnegative convergence of the labelled mass series
selects a finite `N` with

\[
\lambda\mu\le\sum_{n<N}m_n(T)le\sum_{n<N}a_n.
\]

The checked finite cap-lift budget then yields

\[
\boxed{D_N\le D_0-\lambda D_*\mu.}
\]

For `lambda=1/2`, this is a strict descent by `D_* mu/2` at an actual finite
behavioral profile which still carries the same normalized paid mark.  This
uses no cap-to-prescribed conversion and does not take the semantic port as a
new behavioral source.

Likely Lean additions are a debt-normalized `ShiftedPaidRow` wrapper and the
finite partial-sum selection applied to
`SummableChargeSignedTerminalPort.mass_lower`.

## Failure of the advertised unconditional closure

Let `M_theta` be the class of actual profiles carrying paid difference at
least `theta*D(profile)`.  The finite cut remains in `M_theta`.  However, the
available signed mass constant is

\[
\mu(\sigma)=
\rho(\sigma)/\bigl(2M(2^{|I|}-1)\bigr),
\]

where `rho(sigma)` is the displacement of that source's cap port.  The checked
producer supplies neither a positive lower bound for `rho` on `M_theta` nor a
positive mass floor uniform over renewed sources.  In the inert arm,
`rho=mu=0` while the paid row can persist.

Accordingly the proposed infimum step

\[
D_0<\inf_{M_\theta}D+\kappa/2,
\qquad \kappa=D_*\mu(\sigma_0)/2,
\]

is circular: `kappa` is known only after `sigma_0` is chosen.  A bounded-below
set may admit a source-dependent strict descent at every point, with descent
sizes tending to zero near its infimum.  Paid-density invariance alone does
not prevent this.

The advertised contradiction is valid under the additional producer
hypothesis

\[
\exists\mu_*>0\;\forall\sigma\in M_\theta,
\quad\text{the returned port has labelled mass at least }\mu_*.
\]

That uniform hypothesis is not currently produced.  Alternatively, one
could close the argument by proving compactness and attainment of the marked
class minimum together with a positive label at its minimizer; neither is
currently established, and the witness-time quantifier makes closedness of
`M_theta` nontrivial.

There is also a source-native degeneration: renewing at `x_N` follows the
tail of the same canonically selected cap orbit, so

\[
\rho_N=\lVert b_\infty-b_N\rVert_\infty\longrightarrow0,
\]

and hence the available signed mass lower bounds `mu_N` tend to zero, while
the normalized paid density stays fixed.  Thus the Zeno behavior occurs in
the proposed regeneration itself, not merely in an abstract ordered set.

## Exact source declarations inspected

- `quittingCapLiftedPrefixProfile_debt_eq_suffixReach_mul`,
  `QuittingPaidCapLiftedSource.suffixReach_le_observerReach`, and
  `QuittingPaidCapLiftedSource.pureTimePayoff_sub_shift` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`;
- `QuittingPaidCapLiftedSource.minimum_mul_partialAbsorption_le_debtDrop` in
  the same file; and
- `SummableChargeSignedTerminalPort.mass_lower` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorSummablePortLabel.lean`.

## Current precise next question

Does the full Fin4 same-source pair-base paid/reset provenance imply one of:

1. a positive lower bound for cap displacement or labelled mass depending
   only on the normalized paid density and the terminal gap;
2. exclusion of the inert `A=0` arm; or
3. a compact, attained marked minimum at which the source-dependent positive
   finite-cut descent contradicts minimality?

Without one of these, the finite-cut lemma is useful local mathematics but is
not a well-founded paid-port consumer.
