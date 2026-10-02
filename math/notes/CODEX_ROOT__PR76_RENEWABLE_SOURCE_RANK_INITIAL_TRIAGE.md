# PR 76 renewable source rank: initial triage

## Later status

The source regeneration and phase/support rank, combined with the subsequently
reviewed minimum-fibre common-response compiler, constitute an
ordinary-mathematics answer to the renewable-handoff question. The preserved
combined statement and its still-pending formal/export gate are recorded in
`CODEX_ROOT__RENEWABLE_HANDOFF_COMPLETION_WITH_COMMON_RESPONSE.md`.

## Status

Initial mathematical and repository assessment only. This is not an
independent proof review and not an export recommendation.

PR #76, `Make canonical Fin4 endpoint source rank renewable`, has substantial
nonzero value. Its principal result is a genuine finite classification of the
minimum-fiber, flat, no-support-entry renewal lane. It does not consume the
three residual exits and therefore does not prove Fin4 uniform equilibrium.

The local `PR_76/RESPONSE.md` describes an earlier head. The current remote
head inspected here is `fd50bfc8c619d71d94a2b17a7d6bd81104303b61`.

## Durable mathematical core

Starting from a canonical minimum-endpoint handoff, the PR constructs:

1. a joint semantic/law compact limit of the exact retained endpoint profiles;
2. a complete `FinFourMinimumAtomProducer` at that same endpoint semantic
   cluster, with the same hard residual and a positive atom retained from the
   literal endpoint law;
3. a public causal chronology whose suffix profiles are a subsequence of the
   literal endpoint profiles;
4. at every later minimum-fiber full-replacement endpoint, another complete
   same-residual source reconstructed from the literal replacement sequence;
5. under flatness and absence of support entry, a strict inclusion of the
   child's positive-debt support in the parent's support; and
6. a finite trace obtained by strong induction on that support cardinality.

The phase tag resolves the old origin-edge problem honestly. The initial
canonical handoff is assigned a one-use `incoming` phase; all reconstructed
sources live in the `tangent` phase. The initial transition lowers the phase
part of the rank, while every recursive transition strictly lowers support
cardinality. Regeneration has no constructor returning to `incoming`.

This is more than renaming an endpoint: every recursive child has a complete
minimum source, retained residual, joint law, positive finite atom, causal
chronology, and tangent frontier at the reconstructed semantic point.

## Exact boundary

The trace stops at one of three predicates:

```text
positive total tangent slope;
flat support entry;
off-minimum paid first disagreement.
```

These are called `FinFourRenewableTerminalExit` in the PR, but “terminal” means
only nonrecursive in this finite transition system. It does not mean terminal
Nash, uniform equilibrium, contradiction, or an already compiled return.

Accordingly the PR proves

```text
canonical handoff
  -> finite same-residual descent
  -> one of three named residual exits,
```

not

```text
canonical handoff -> uniform-equilibrium payoff.
```

The theorem producing a uniform payoff is explicitly conditional on consumers
for all three exit kinds.

## Backward-compiler claim

The restricted no-compiler claim is logically sound: if every terminal exit
has a conclusion depending only on the fixed reward table, one may consume the
terminal descendant directly because every regenerated source retains that
same table and residual. No theorem needs to transport a child deviation
comparison back through the parent's horizontal replacement seam.

This does not supply a backward compiler for source-indexed conclusions. The
PR itself records the missing stronger condition as
`HasVanishingHorizontalDeviationLeak`.

There is also a provenance limitation worth retaining: the reconstructed
child source chronology uses the parent's literal full-replacement profiles,
but the tangent family attached at the child point may be independently
extracted rather than a subsequence of that chronology. This is sufficient for
the support-cardinality rank. It is not sufficient to transport an incoming
response edge or cap comparison into the next tangent family.

## Common-response side result

The PR additionally proposes a useful seam lemma: if two profiles differ only
in one mover's complete stopping law and both total debts approach the same
global minimum, then every nonmover admits one pure-time response sequence
whose regret tends to zero at both endpoints. Consequently the cap difference
is asymptotically represented by the difference of payoffs from one common
response.

The ordinary-mathematics proof appears plausible: use the half stopping-law
mixture, coordinatewise convexity of debt, global minimality, and pure-time
near-attainment. This still does not bound the horizontal deviation leak for
arbitrary responses and is not a consumer for the three renewal exits.

## Current formal status

The PR is a draft and is not Lean-green at the inspected head. The focused
Lean job fails while building
`Research.Quitting.StoppingLawMinimumFiberCommonResponseCompiler`, reporting a
syntax/elaboration failure at the structure construction near line 286; the
dependent full-replacement target is consequently not built. The exact-source
artifact job succeeds, but that is not kernel validation of the declarations.

Therefore the PR currently carries no new Lean seal despite containing actual
Lean source and a coherent theorem architecture.

## Files and declarations inspected

- `CanonicalPairEndpointSourceRegeneration.lean`:
  `nonempty_endpointJointLimit`, `nonempty_endpointSourceRegeneration`, and
  `CanonicalPairEndpointSourceRegeneration.next`;
- `CanonicalPairFullReplacementSourceRegeneration.lean`:
  `nonempty_fullReplacementSourceRegeneration`,
  `nonempty_supportDescent`, and `HasVanishingHorizontalDeviationLeak`;
- `CanonicalPairRenewableSourceRank.lean`:
  `terminalExit_or_nonempty_supportDescent`, `nonempty_renewalTrace`, the
  phase-tagged transition/rank, and `nonempty_renewalCertificate`;
- `CanonicalPairMinimumEndpointRenewal.lean`: terminal-descendant consumption
  and the conditional uniform-payoff theorem; and
- `StoppingLawMinimumFiberCommonResponseCompiler.lean`: the proposed common
  pure-time response and cap-difference interfaces.

## Initial disposition

Worth repairing and then sending through adversarial mathematical review. The
review should concentrate on:

1. whether every source reconstruction retains exactly the minimum-fiber and
   positive-atom hypotheses used in the next recursive step;
2. whether the arbitrary tangent re-extraction loses any field later claimed
   as source-faithful;
3. whether the support-entry branch is merely named or has a genuine global
   consumer; and
4. whether the common-response lemma remains true after the current Lean
   syntax repair without strengthening its hypotheses.
