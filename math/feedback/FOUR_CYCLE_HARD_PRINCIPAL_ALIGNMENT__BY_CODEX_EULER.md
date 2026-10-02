# Whole-packet gate for `FOUR_CYCLE_HARD_PRINCIPAL_ALIGNMENT`

Reviewer: `CODEX_EULER`

Verdict: **PASS**, no repair or removal.  Under the user's explicit
finite-alignment placement decision, the packet satisfies every applicable
`exports/README.md` item.  Its exact classification, proof, source adapter,
finite consumers, boundary tests, probability audit, novelty check, Lean
handoff, and nonclaims all pass.

## Statement and proof

The selected proper hard principal has cardinality two or three.  In the pair
case, reciprocal negativity from `cardTwoCrossing` combines with the rooted
four-cycle exactly as claimed: an adjacent pair closes a strict two-cycle,
and an opposite pair closes either length-two arc into a strict three-cycle.
Taking the minimum of `gamma` and the new strict margins gives one positive
`eta`; the packet correctly does not preserve `gamma` on new edges.

For the literal owner--collider hard pair, the collision certificate excludes
collider leave.  Owner leave and `M(o,c)<0` compose to (5), while the remaining
toggle arm is the outsider join (6).  Helpers lie in the exact pair
complement.  Disjoint card-two subsets of `Fin 4` are complements, so both
helpers lie in the owner--collider pair; one-role intersection forces no
stronger identity.  These incidences are exhaustive.

For a hard triple, the checked external-helper/cyclic-boundary dispatch is
exhaustive.  The complement field identifies the helper with the omitted
vertex `x`, and its helped receiver cannot be `successor(x)` because that
same matrix entry is strictly negative on the four-cycle.  In the cyclic arm,
the two inherited consecutive negative entries determine the strict
three-cycle orientation and force the closing negative chord.  The
owner/collider cases then match the one-tail-to-three and rooted-three marked
forms exactly.

## Remaining gate items

- **Conjecture-facing finite change:** this is the final pass on the three
  rooted four-cycle constructors after the reviewed eight length-two and six
  length-three cases.  The output is shorter-cycle or literal-helper
  incidence, not a semantic chamber closure.  This placement is expressly
  user-authorized.
- **Probability and behavioral semantics:** the new proof is deterministic
  finite matrix algebra.  Its only terminal semantic step invokes the checked
  unrestricted terminal toggle and immediate collision certificate.  No
  strategy-class restriction, correlation, or conditioning is added.
- **Source and consumer:** the packet names the actual full-support hard
  residual, proper-principal size theorem, card-two/card-three consumers,
  marked geometry, and finite relation source.  The new composition is not an
  existing declaration.  No literature result is repackaged.
- **Boundaries:** arbitrarily small reverse margins, opposite pairs,
  external-helper triples, forced cyclic triples, and one-role pairs test all
  proof boundaries and justify the exact `eta`/incidence scope.
- **Lean handoff:** the proposed rooted-four decoder, finite pair-distance
  cases, collision exclusion, unique-complement identities, and strict
  orientation lemma are the narrow implementation and do not assume a hard
  output in the decoder.
- **Nonclaims:** no Bellman edge, Nash root, chronology, sure-exit repair,
  semantic debt decrease, or uniform-payoff consumer is inferred.  The packet
  does not align separately selected semantic/tangent data.

The independent theorem audit by CODEX_CEDAR and this whole-packet gate leave
no unresolved objection.
