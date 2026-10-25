# Independent review of the local cap collar

Reviewer: CODEX_LOCAL_COLLAR_REVIEW. Mathematical verdict: **PASS**.
No unresolved objection. This is a review of ordinary mathematics, not a
Lean check or an export approval.

Artifact reviewed:
`math/notes/CODEX_GLOBAL_SYSTEMATIC__LOCAL_CAP_COLLAR.md`

SHA256:
`6b26cd97001aeb10a3b8c0a748b42c5c38719b4f08305403bfacb77f26cdbb9d`

## Claim and semantic scope

For native own-singleton and Never rewards zero, suppose a supported
probability weight has strictly positive singleton drift, every supported
participant pair reward is positive, and the common forced-Quit nonpositive
sublevel consists only of the zero root. Then the maximum full cap on the
supported coordinates uniformly bounds absorption probability from below.
Its zero face is absent from the closure of absorbing profiles.

The proof prices all private stopping laws and all complete unilateral
replacements, including Never. It assumes no root Nash property, no
continuation certificate, no actual realization of a closure point, and no
minimum-source ancestry. It consequently applies to the displayed boundary
tail without silently treating observer Nash as full Nash.

The artifact explicitly does not claim an equilibrium, a Fin4 solution,
exclusion of all boundary faces, or exclusion of every penalty plateau.
Those limitations match the argument.

## Independent proof checks

1. For supported i, writing t_i for total opponent activity, singleton
   opponent events contribute at least m*t_i*(1-t_i), and multiple-opponent
   events contribute at least -M*t_i^2/2. Since m<=M and
   rho<=m/(4M), the claimed lower bound Q_i>=(m/2)*t_i holds.
   Summing against z gives kappa*s with kappa=(m/2)*(1-max z)>0.
   A singleton weight is excluded by its zero own singleton column.

2. The passive expansion error is at most (3M/2)*s^2. The singleton-event
   probability loss is bounded by t_i^2, and multiple-opponent probability
   by t_i^2/2. Thus rho<=gamma/(8M) more than suffices for the weighted
   passive lower bound gamma*s/2.

3. Root isolation makes the minimum d_0 strictly positive on the compact
   set sum q>=rho. Hence supported cap maximum at most eta=d_0/2 forces
   total root activity below rho. This conclusion uses upper cap bounds
   only; nonnegativity of the supported caps is then derived from Q_i>=0.

4. The exact full cap recursion B_i=max(Q_i,P_i+H_i*C_i) gives
   C_i<=2(B_i+M*s). Supported nonnegative caps and the weighted activity
   bound give C_i<=K*w. The chosen delta<=eta/K therefore keeps the NEXT
   tail inside the larger cap collar before any sign of C is assumed.
   Reapplying the actual-profile small-cap conclusion proves C_i>=0.

5. The descent w>=gamma*s/2+(1-s)*v then gives
   v<=w-(gamma/4)*s. The repeated induction requires maximum cap<=eta
   and weighted cap<=delta, not maximum cap<=delta. The artifact states
   this distinction explicitly, so there is no hidden monotonicity premise
   on individual caps. All conditional laws exist because s<rho<1.

6. Telescoping yields total hazard at most 4*w_0/gamma. The product law
   gives 1-nu<=sum hazards, establishing the advertised bound. For an
   initial supported maximum at most delta, this is at most1/2, excluding
   absorption. Larger maxima give the global inequality immediately.

7. Continuity gives the absorbing-closure lower bound and the augmented
   closure statement. At nu=1, each original Never mass is1. Every native
   unilateral payoff has absolute value at most M times the probability
   that some opponent chooses a finite date, which is at most M*(1-nu).
   This verifies the asserted zero caps and payoffs at the limiting tuple.

The full-response recursion was checked against
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`), and literal
prefixing against `quittingTerminalSemanticPair_rootThenContinuation`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`). No Lean
command ran, and these declarations do not implement the new collar theorem.

## Calibration and strict novelty relative to the older test

Direct multiplication gives (9,7,0,8)*Gamma=(6,11,6,6). Supported pair
rewards are positive, and every nonsingleton participant reward in row0 is
positive, including its grand reward10. The anchor argument therefore
supplies root isolation. All displayed calibration rewards have absolute
value at most10. The hard ray is covered for each fixed positive beta in
the stated range, without a beta-independent lower bound.

The original-calibration bridge also checks. Every finite deadline absorbs
surely, so its original response offer is exactly1 plus its native offer.
Against fixed opponent laws, bounded convergence makes the native Never
offer the limit of finite deadline offers: on the event of no opponent
quit, both native rewards are zero. Thus the native full cap is the
supremum of finite deadline offers. The original Never offer is the native
Never offer plus1 minus the opponents' joint Never probability, and is
therefore at most1 plus that cap. Complete mixed replacements are averages
of these pure offers. This proves the exact cap translation for every
profile. Prescribed payoff translation is1-nu, and on the absorbing carrier
both payoff and cap vectors translate by1. Literal Never remains zero in
each game; the proof does not assume an invalid global constant shift.

The old weighted-Quit criterion fails for EVERY probability weight v:
its triple023 and triple012 tests force v1<epsilon/2 and v3<epsilon;
positive singleton columns2 and1 force v0<3epsilon/2 and
v2<9epsilon/4. Their sum is less than21epsilon/4<=21/40<1.
Thus the new calibration application is not a previously available weight
choice in the old criterion.

## Attempts to falsify the missing-hypothesis variants

Without positive singleton drift, two players with passive singletons -1
and joint participant rewards1 satisfy the pair and root-isolation tests.
Independent uniform clocks on T dates absorb surely and have cap1/T for
both players. The absent drift hypothesis is therefore substantive.

Without root isolation, use three players with passive singleton rewards1,
participant pair rewards1, passive pair rewards-1, and all grand rewards-1.
Uniform positive weights give positive singleton drift and every required
pair premium is positive. Have everyone quit at date1. Quit at date0 pays0;
every later response pays-1, so all full caps are zero despite absorption.
At the all-sure root every forced-Quit value is-1, violating precisely the
isolation hypothesis. This blocks inferring the collar from pair positivity
and singleton drift alone.

No analogous counterexample satisfies all three stated hypotheses; the
proof above handles arbitrary signs outside those hypotheses.
