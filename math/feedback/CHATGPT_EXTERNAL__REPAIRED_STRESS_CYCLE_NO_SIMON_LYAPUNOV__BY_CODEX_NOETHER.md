# Review of repaired-stress Simon Lyapunov obstruction

Reviewer: `CODEX_NOETHER`

Reviewed note:
`notes/CHATGPT_EXTERNAL__REPAIRED_STRESS_CYCLE_NO_SIMON_LYAPUNOV.md`.

## Verdict

**ACCEPT as the complete candidate-level negative answer expressly allowed by
`questions/SIMON_LYAPUNOV_CERTIFICATE.md`.** I found no mathematical
objection. The rational table at `epsilon=1/2` contains an exact positive-cost
cycle in the full production Simon correspondence, so no strict global
potential and hence no finite-cell Lyapunov certificate can exist for this
candidate. The every-positive-tolerance subdivision is also valid.

This is not a new repaired-stress circulation construction. The table,
vertices, phase identities, floor, and discretized support-perfect orbit are
already present in the repaired-stress circulation source. The exact new
packaging is the carrier/edge adapter to the production Simon correspondence
and the consequent no-Lyapunov conclusion. That is nevertheless a complete
answer of the kind the named question and `exports/README.md` explicitly
accept.

## 1. Table and carrier

The displayed sixteen nonempty-coalition rows agree with
`RepairedFourPlayerStress.stressWeight`. The four singleton rows rotate as
stated. For example,

\[
 \frac{8R^0+4R^1+2R^2+R^3}{15}=(1,2,2,1)=v^0,
\]

and rotation gives the other three identities. All coefficients are positive
and sum to one, so every `v^k` is exactly Simon-feasible, not merely near the
feasible hull.

The checked source bound
`quittingPunishmentValue_le_stressFloor`
(`UniformEquilibrium/Quitting/Circulation/UniformPayoffExamples.lean`) gives
`chi_i<=1`. Since every vertex coordinate is at least one, every `v^k` is
individually rational even at error zero. Thus the four vertices belong to
`QuittingSimonFiniteOrbitCarrier reward (1/2)`.

For the subdivided phase, write `t=beta^m`. Because
`1/2=beta^N<=t<=1`, the state

\[
 x_m^k=(1-t)R^k+t v^{k+1}
\]

is exactly feasible. It is also the segment between `v^(k+1)` and `v^k`, so
all of its coordinates lie in `[1,2]`; hence it belongs to the production
carrier at every positive tolerance.

## 2. Full correspondence inequalities

At `epsilon=1/2`, use the product root in which only owner `k` Quits, with
probability `1/2`. The exact Bellman identity is

\[
 v^k=\tfrac12R^k+\tfrac12v^{k+1}.
\]

The four Quit-minus-Continue endpoint differences, in the cyclic positions
`k,k+1,k+2,k-1`, are respectively

\[
 0,\qquad-\tfrac32,\qquad-\tfrac32,\qquad\tfrac12.
\]

The owner uses both actions, so its two support clauses hold with equality.
Each passive player uses Continue only, so only the upper endpoint inequality
is required; all three values are at most `1/2`. These are precisely the full
support-local clauses of `IsQuittingRootSupportApproxNash`, including the
passive players. No unplayed-Quit lower inequality is being smuggled in.

For the all-tolerance refinement, choose `N>=1`,
`beta=2^(-1/N)`, and `h=1-beta<=epsilon`. For an actual microedge
`m=0,...,N-1`, put `t=beta^m`. In cyclic order the endpoint differences are

\[
\begin{aligned}
 D_k&=0,\\
 D_{k+1}&=\beta-3+2\beta t\le-3h,\\
 D_{k+2}&=\beta-2=-(1+h),\\
 D_{k-1}&=1+h-2\beta t\le h.
\end{aligned}
\]

The last inequality uses `m+1<=N`, hence
`beta*t=beta^(m+1)>=beta^N=1/2`. Thus every passive upper clause is at most
`epsilon`, while the active owner remains exactly indifferent. The note's
Continue-payoff lower bound `2 beta^N=1` is therefore correctly indexed: the
terminal endpoint `m=N` is not the tail of another microedge.

## 3. Orientation, closure, and cost

`QuittingSimonFEdgeAt reward epsilon tail current` stores the continuation
first and its Bellman predecessor second. Since

\[
 x_{m+1}^k=hR^k+\beta x_m^k,
\]

each microedge is directed `x_m^k -> x_(m+1)^k`. A phase therefore runs
`v^(k+1) -> v^k`, and the four phases concatenate as

```text
v^0 -> v^3 -> v^2 -> v^1 -> v^0.
```

This agrees with the production graph orientation. The cost is symmetric
Euclidean distance, so every macroedge has cost `sqrt(2)`. Microedges are
collinear and move monotonically; hence each phase has total variation
`sqrt(2)` and the closed microcycle has exact variation `4*sqrt(2)`.

If `Phi(y)<=Phi(x)-c0*c(x,y)` held on every graph edge with `c0>0`, summing
around either closed cycle would give

\[
 0\le-4c_0\sqrt2,
\]

a contradiction. This excludes every global potential without needing
boundedness. Since
`HasFiniteCellLyapunovCertificate.exists_globalPotential`
(`MathUE/Topology/CompactEdgeBudgetedPrefixRelation.lean`) converts finite-cell
data to such a global potential, finite-cell certificates are excluded too.

## 4. Probability and strategy scope

Each row is a simultaneous independent product root; only the named owner has
positive Quit probability. Terminal ties use the displayed coalition row.
The claim is about the support-local production correspondence, not about a
terminal, discounted, finite-horizon, or uniform Nash profile. It does not
claim control of arbitrary behavioral deviations. That limitation is exactly
appropriate for a candidate-level falsification of the Simon certificate
question and must remain explicit in the export.

## 5. Source and novelty audit

The following content is already present:

- `stressWeight`, `stressVertex_step`, `stressCirculation`, and
  `exists_stressCirculation_orbit`
  (`UniformEquilibrium/Quitting/Circulation/RepairedFourPlayerStressCirculation.lean`)
  give the table, reversed four-phase circulation, exact affine identities,
  floor, and all-tolerance support-perfect subdivision;
- `quittingPunishmentValue_le_stressFloor` and
  `exists_uniformEquilibriumPayoff_stressWeight`
  (`UniformEquilibrium/Quitting/Circulation/UniformPayoffExamples.lean`) give
  the production punishment-floor comparison and already compile this table
  as a positive uniform-payoff example; and
- `isQuittingRootSupportApproxNash_rootOfHazard_of_isSupportPerfectRow` and
  `quittingRootSuccessorPayoff_rootOfHazard_eq_oneStageNext`
  (`UniformEquilibrium/Quitting/Circulation/MultiOwnerFaceCirculationPath.lean`)
  are the existing row-level semantic adapters.

I found no existing specialization of these data to
`QuittingSimonFiniteOrbitCarrier`, `QuittingSimonFiniteOrbitGraphAt`, or a
no-finite-cell-certificate theorem for `stressWeight`. The new result is
exactly that specialization and telescope. It must not be advertised as a new
cycle, a new uniform-payoff theorem, or a branch exclusion.

## 6. Bounded repairs needed for export

No mathematical repair is needed. A self-contained export packet should make
only these bounded presentation additions:

1. Replace the notebook `Status` line by the standard packet author/review
   metadata and do not add a lifecycle-status header.
2. Name `QuittingSimonFiniteOrbitCarrier`, `QuittingSimonFEdgeAt`,
   `QuittingSimonFiniteOrbitCost`, and
   `HasFiniteCellLyapunovCertificate.exists_globalPotential`, with their
   files, in a source-correspondence section.
3. State the four microedge formulas above explicitly; they remove any doubt
   about the predecessor inequality and the `m=N` boundary.
4. Say plainly that the circulation and subdivision are old, while the Simon
   carrier/graph obstruction is new.
5. Add boundary tests: the unsubdivided `1/2` cycle fails the support bound
   below tolerance `1/2`; subdivision repairs it, while zero-cost self-loops
   alone would not contradict a strict cost-weighted inequality.
6. Give a narrow Lean handoff: first package the rational `epsilon=1/2`
   vertex membership and four `QuittingSimonFEdgeAt` witnesses, then telescope
   them to exclude a positive-constant finite-cell certificate. The stronger
   every-epsilon algebraic subdivision can be a separate theorem.

With those additions, the result meets the export gate as an exact negative
answer to the named question. It needs no branch exclusions or supplied Simon
necessity hypothesis because it claims only failure of this candidate's
strict certificate, not a terminal-gap counterexample.
