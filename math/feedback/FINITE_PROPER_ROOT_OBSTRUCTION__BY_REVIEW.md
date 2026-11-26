# Independent whole review: isolated observer oval and global one-date minima

Reviewer: STRATEGY_INDEPENDENT. Ordinary mathematics; no Lean build.

Artifact reviewed:
`math/notes/CODEX_COORDINATOR__FINITE_PROPER_ROOT_OBSTRUCTION.md`, SHA256
`2ebea03674cae5e7b1d5a3fc7c8f537ae9665f977303f47d6f261c6199b985a9`.
The complete final canonical artifact was compared with the reviewed draft;
only status, references, and the explicit remaining-task wording changed.
This review covers the entire final proof, including the complete reward
embedding, all Nash supports, the canonical finite absorbing comparison,
positive-error separation, all axis comparisons, and the actual stationary
escape. No unresolved mathematical objection remains.

**Verdict: mathematical PASS as a finite-controller selection obstruction.**
It refutes global-minimum-to-spanning-component selection in the one-date
partial-Nash correspondence, including vanishing observer error within that
controller class. It is not a positive-gap table or a closure of Fin4 case F.

## Independently reconstructed checks

1. **Full table and complete deviations.** Each G_i is multiaffine in opponents'
   probabilities, independent of the owner's probability, and zero at the
   origin. Thus vertex interpolation gives exactly the printed joining
   advantage. The reward rule assigns each of the sixty cells once and
   preserves every Gamma singleton literally. Against one-date opponent
   laws, every later deadline and Never gives the same passive payoff P_i.
   Consequently B_i=P_i+max(G_i,0) and d_i=max(G_i,0)-q_i G_i price ALL
   complete unilateral laws. There is no added correlation or observability.

2. **All observer supports.** Splitting on y using G2=x-z independently gives
   the seven printed pieces. For y=0, Nash requires x<=z and the other
   inequalities force p=0,x=0. For interior y, x=z; x=z=0 gives exactly the
   strip, x=z=1 is excluded, and interior x gives the quadratic curve. For
   y=1, x>=z; x=0 gives the strip top, interior x gives z=2p-1 and the
   rational branch or the p=1/2 segment, and x=1 gives the final two pieces.
   In particular the rational branch satisfies
   x-z=2(54p^2-73p+27)/(63-54p)>0 and x<=1 exactly when p<=9/11.
   This is an exhaustive support check, not a sampled root census.

3. **Exactly two components.** The discriminant polynomial becomes
   576s^4-124s^2+4 after p=s+1/2. This yields precisely the four radical
   roots printed in the artifact. The four probability-boundary evaluations
   are correct; both indicated quadratics have negative discriminants.
   They locate the one feasible origin arc and the central closed oval,
   with no high-p interior branch. The seven nonoval pieces attach in
   order and span p=0 to1. The oval lies strictly inside the cube and is
   separated from that compact component. Simple discriminant roots prove
   regularity at its folds; away from them the observer Jacobian determinant
   is -g_t. Thus the two regular slice roots have opposite indices.

4. **Pivot sign, finite absorbing minimum, and global minimizers.** The
   substitution into F factors exactly as printed. The final quadratic has
   discriminant -1537623<0. The oval's unique G0-zero point is therefore
   (p,x,y,z)=(1/2,2/3,1/3,2/3), and the sign test at the other p=1/2 root
   gives G0/delta=-19/44. Hence the whole oval is ALL-END. Independently
   differentiating the curve at its zero point gives y'=1/11,p'=6/11,
   (G0/delta)'=0 and nu'=-53/198; thus that point is not minimizing.
   The printed lower bounds on every other component piece are correct.
   All absorbing observer equilibria were separately checked: the exact
   minimum is9delta/34, attained at p=9/34,x=z=0,y=1. With r=m1/2,
   every global minimizer lies on the oval and has G0<0 strictly. The
   actual full-calendar absorbing minimum is not used in this argument.

5. **Positive source scalars and axis families.** The two x,y lower-bound
   substitutions are correct: 60p^2-34p+5 has discriminant-44, and
   12p^2-14p+1 is negative on[1/4,3/4]. Thus all opposing pair probabilities
   on the oval are at least1/36, and P_i>=-M+K/36>4delta+r.
   Together with |G0|<=111delta/44 this proves all stated payoff and cap
   inequalities. The delta restriction gives r<=alpha/(4S^2), whereas the
   oval has lambda>4/3. The complete axis append difference is therefore
   strictly positive at every T>0, including T=infinity. The exact direct
   replacement minimum and its integrated bound >=7r/8 are correct.
   These arguments retain the full old cap maximum and observer comparisons.

6. **Small-error separation.** The prescribed rho is positive because O,E,
   and the cube boundary are disjoint compact sets. Its closed neighborhood
   U remains inside the cube and misses E. The continuous observer regret
   R has no zero on boundary U, so epsilon_boundary>0. The second compact
   set L has no zero of R either, since its J threshold is below every
   exact equilibrium in E. The value gamma=7delta/22032 is exactly
   (delta/162-delta/204)/4. Thus both the path obstruction and the global
   near-minimum assertion follow. Their constants are fixed for ONE date;
   the proof supplies no uniform separation as the calendar grows.

7. **Actual infinite-clock Nash escape.** At the displayed calibration,
   Gamma^-1 e0=(1,2/5,2/5,1/5), so alpha=1,S=2. Both the delta and K
   hypotheses hold. With hazards8/9 and1/2 for players1 and3, their passive
   one-step values are -1/2 and-8/9 and their Quit values are both-1.
   Waiting until the other active player quits also pays-1. Thus every pure
   deadline and Never ties for each active player. For the quiet players,
   the prescribed and Quit values are exactly those printed, with margins

       u0-Q0=(8K+3)/306-2delta/11>0,
       u2-Q2=(8K-108)/306>0.

   At K=1000,delta=1/4 these inequalities hold strictly. A quiet player's
   deadline T has payoff (1-c^T)u_i+c^T Q_i, c=1/18; Never pays u_i.
   Hence all complete deviations are covered. Absorption occurs almost
   surely and the true arbitrary-calendar minimum is0, despite m1=9/136.

## Scope and falsification discipline

The component-isolation assertion has deliberately been restricted to the
complete ONE-DATE graph, including all its support faces. It is not isolation
in the graph of arbitrary complete clock laws. The actual stationary escape
shows why that distinction matters, rather than leaving it as a hypothetical
caveat. The source's true positive absorbing gap is absent in the calibration.

The proof also does not assert generic row distinctness or a raw Fin4 class
exclusion. Its durable output is an exact falsifier of the stated finite
selection mechanism and its small-error relaxation. It leaves unrestricted
whole-calendar continuation and its connection to genuine global-minimum
ancestry unresolved.

All displayed factorizations and rational identities were independently
checked with symbolic algebra or Fraction arithmetic, and the inequalities
were checked analytically. No tracked edit, Lean command, or git operation
was performed for this review.
