# Composition review: punishment-free polynomial edge certificates

Reviewer: CODEX_HILBERT. Complete combined surface reviewed at
`notes/CODEX_RENY__PUNISHMENT_FREE_POLYNOMIAL_FORWARD_CERTIFICATE.md`,
SHA-256 `3b4139751b4c342fa650ab72f02fa79c934c3ca7772ec0783f31545b847aa053`.

Verdict: **PASS, ordinary mathematics; no required correction.** This is a
bounded composition and quantifier check after my independent complete
reviews of the separator and finite burn-in ingredients. It is not a new
independent review of my own earlier necessity adapter. Frozen originals,
exports and Lean sources were not changed.

## Exact characterization checked

Fix a four-player zero-Never table, M>0 bounding every absolute reward,
semantic punishment normality P_i≤s_i, and at least one s_j>0. Set the
single box radius B=M+2 before all other parameters. Let ℛ_δ(B) contain
**every** pair of endpoints in that box and every independent product root
whose ordinary regret and Bellman residual are at most δ times its
absorption probability. No endpoint floor is included. Then the proposed
equivalence is valid:

    no UE ⇔ not C_sure and ∃ rational δ∈(0,1/4], rational polynomial H,
               H(v)−H(w)≥a(q) on every ℛ_δ(B) edge.

C_sure means that some player quits surely at an exact root Nash against
P. Neither its exclusion nor normality has disappeared from the claim.

## Seam checks

1. **The floor-free analytic theorem is legitimate.** The plain outer cube
   remains compact. Finite-horizon capacity over paths of at most n edges
   has nonempty compact fibers because zero paths are allowed. Its value
   is USC, and the bounded all-horizon supremum is Borel. Concatenation
   gives the capacity drift on all outer edges, including arbitrary starts.
   Positive common translations preserve the tighter edge inequalities
   exactly as in the reviewed separator; deleting the floors removes a
   constraint and introduces no new translation estimate. Outer box room,
   zero extension, one-sided smoothing, C¹ approximation and rational
   coefficient perturbation are unchanged. The displacement estimate is
   still proportional to a(q). At a=0 the endpoint equation gives w=v.

2. **Burn-in retains the same B.** For target tolerance τ choose
   e≤min(τ,τ/4,τ²/(16M)), then choose an integer L with
   Lτ²/(8M)>M+B. Request charge Q+L at tolerance e in the original box.
   The two weighted errors imply endpoint error at most 2e. Deleting the
   first L construction rows loses at most L charge and gives the τ-floor
   at both retained ends and every intermediate annotation. No reattachment
   or box enlargement is used. Thus WP⁰(B)⇔WP(B) under normality.

3. **Negation supplies the right capacity bound.** Under no UE, the checked
   weighted consumer and burn-in rule out WP⁰(B+1), not merely one chosen
   component. Negating its all-tolerance/all-charge quantifiers supplies
   one positive t and one finite unattainable charge target. Every path in
   ℛ_t(B+1) consequently has a common finite budget. Choose a positive
   rational ε≤min(1,t). Relation inclusion preserves bounded capacity;
   the analytic theorem gives δ=ε/4 and rational H on the prescribed
   inner box B=M+2. There is no claim that a rational tolerance can be
   effectively recovered from the existential negation.

4. **The converse uses the identical box.** Assuming UE and excluding
   C_sure, the reviewed normal-positive-singleton necessity adapter yields
   WP(M+2): S.1 uses the translated stationary annotations and S.3 uses
   translated reward-box packets. Forgetting their floors produces
   arbitrarily charged ℛ_δ(B) paths at the certificate's own δ and B.
   Telescoping polynomial drift bounds their charge by one finite
   oscillation, a contradiction. No smaller arbitrary box or horizon-
   dependent box is substituted.

5. **Semantic assumptions are not circular.** The no-UE direction uses
   normality for burn-in. The reverse direction assumes UE only to invoke
   the already reviewed necessity disjunction; it does not assume an
   approximate-equilibrium producer while deriving one. The sure-root
   consumer uses an individually chosen punishment, not a joint realization
   of P. Positivity is needed in the cited necessity adapter, not in the
   floor-free analytic theorem or the burn-in implication alone.

The exact canonical H cycle is also an edge cycle of the larger floor-free
relation. Summing its three half-unit charges would contradict any proposed
potential. Removing floors does not create a negative certificate on that
solved table, and no spurious positive drift is imposed on zero-charge
self-loops.

## Scope of the new composition

The new conclusion removes P from the universal polynomial **edge test**.
Those inequalities involve only raw reward entries, root probabilities,
annotations, the fixed bound, the tolerance and the polynomial. It does not
remove P from normality or C_sure, compute P, give a degree bound, or
establish an effective decision algorithm. For rational input, existing
negative-certificate procedures are not replaced or claimed to be new.

The production packet and consumer correspondence was checked in
`UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacket.lean`
and `AbsorptionWeightedForwardPacketProducer.lean`, including
`HasAbsorptionWeightedFiniteForwardPackets` and
`quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets`.
The new composition is ordinary mathematics over those checked interfaces
and the separately reviewed necessity and burn-in adapters. It supplies
no actual negative table or general unbounded-charge producer.
