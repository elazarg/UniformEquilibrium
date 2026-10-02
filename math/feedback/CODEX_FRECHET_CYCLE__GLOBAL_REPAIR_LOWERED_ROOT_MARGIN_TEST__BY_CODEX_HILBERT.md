# Independent check of the lowered-root strict MAX margin

Reviewer: CODEX_HILBERT. Ordinary mathematical review, not Lean-checked.

Read the complete author note
`notes/CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_LOWERED_ROOT_MARGIN_TEST.md`
at verified SHA-256

    e98d2be429759903c7a760b04d6a26718f58d05573856f6424604f643d8e5efc

**Verdict: PASS.** The absorption-relative error estimate was derived
independently before reading this draft. The finite-repair inequality,
its relaxed-boundary handling, and the unrestricted minimum extension
survive the checks below. No zero-minimum conclusion is implied.

## 1. Sign-specific root defect

Fix q exact Nash at W=U−h1, with h>0. Raising continuation to U changes
C_i by c_i h and the prescribed root payoff by (1−q_i)c_i h.

- If q_i=0, Continue was best and remains best, so e_i=0.
- If 0<q_i<1, the endpoints were equal at W; therefore e_i=q_i c_i h.
- If q_i=1, Quit was best at W and its new defect is
  max(0,C_i(W)+c_i h−Q_i)≤c_i h.

Thus e_i≤q_i c_i h≤a h in every case, including c_i=0 and sure-Quit
roots. The sign of the continuation change matters: this argument is not
a symmetric perturbation bound. No sign restriction on reward entries or
singleton rewards was used. It bounds the maximum player defect, not a
sum mistakenly normalized by absorption.

## 2. Finite-calendar estimate and shifted reward box

Substitution into the independently checked arbitrary-root contraction
gives exactly m_(N+2)≤m−a[m²/(32M)−h]. At h=m²/(64M), the bracket is h.
The source's U is never replaced by W; W is used only to choose q.

The shifted continuation lies in [−M−h,M], not necessarily [−M,M]. If
x=max_i(s_i−W_i)_+>0, the root gap in a maximizing coordinate is at least
x−(x+2M)(1−c_i). Since x≤2M+h and h≤M/16, this is at least
x−5M(1−c_i). The author's absorption argument therefore proves a≥x/(5M),
including the case where strict root advantage forces q_i=1. This validates
the displayed finite strict-margin inequality with its stated constant.

Positive-α implementations retain U exactly, so W, q, a, h and its
absorption-relative defect bound remain fixed at the nonattained boundary.
The existing N+2 calendar proof applies with only a vanishing additive
implementation error. No extra tail truncation or α-dependent deadline
enters. Uniformity over all global optimizer choices follows from the
same bound in terms of m_N and m_(N+2).

## 3. Every unrestricted MAX-minimizing carrier point

Section 4 correctly removes canonical/geometric assumptions while retaining
four players and M>0. At an arbitrary minimizing carrier pair, choose q
once against U−h1 and use actual semantic approximants p_n. Their root
defects are bounded by a h+2‖U(p_n)−U‖∞. Approximate complete responses
with errors tending to zero suffice; no response attainer is assumed.

The fixed mixture weight θ=a m/(32M) gives the same strict limsup bound
m−a h when a>0. Every competitor is an actual independent profile, so this
contradicts the unrestricted infimum without requiring repaired-law or
semantic convergence. Thus every exact root at U−h1 is all-Continue.
Finite root existence yields U_i−s_i≥h=m²/(64M) for every i.

The conclusion is for EVERY minimizing carrier pair, not only for clusters
of one selected sequence of finite optimizers. It supplies a strict MAX
margin without punishment normality, unlike the cited minimum-SUM theorem.

## 4. Global m_0 guardrail

The Section 5 example is valid. At N=0 all opponents are Never, and every
pivot law with finite mass λ has debts 1−λ and λ on each follower, hence
m_0=1/2. If the pivot law remains fixed, its prescribed payoff is 1/2 and
its Quit-0 cap is one. If instead a follower remains Never, its debt is
joint absorption A, while pivot debt is at least 1−A. Therefore changing
at most three complete laws cannot lower the maximum below 1/2. All four
players Quit-0 is exact Nash. The example is below the singleton floor;
it is not an obstruction in the remaining strict-margin region.

## 5. Scope

The full-cap prefix, mixture, carrier and MAX-margin declarations inspected
in the preceding contraction review support the reused steps. Their actual
scope was retained: the old MAX singleton margin gives U≥s but not this
quantitative strict margin. The minimum-SUM strict-isolation statement has
a different objective and additional punishment-normality assumptions.

Combining this result with the independently authored all-player tie proof
leaves every positive MAX minimum all-tied and strictly above singleton
payoffs. This is a stronger necessary structure, not a contradiction, a
finite-menu approximation producer, or an export-ready solution claim.
