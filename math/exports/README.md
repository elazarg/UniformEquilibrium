# Export Queue for Lean Formalization

This directory is the only conference output consumed by external Lean
formalization agents. It must stay small. A packet here means that independent
researchers regard the result as complete, rigorous, and indisputable
mathematical progress toward the quitting-game conjecture. It does not mean the
result is already proved in Lean.

## What qualifies

Significant conjecture-facing progress is required, not merely a correct new
theorem. A packet must demonstrably narrow the possible uniform-equilibrium
counterexamples: prove existence on a previously surviving reward-table class,
eliminate an actual residual mode under its already established hypotheses,
or impose a genuinely stronger necessary condition on every counterexample.
A complete unrestricted counterexample also qualifies. A theorem about a
supplied object does not pass this test merely because that object has a
conjecture-related name.

For a new existence class, compare with both implemented results and previously
accepted existence packets. Give exact raw-table evidence that the class is
not already covered by the applicable criteria. Check existential producers
over their complete selection sets, not only pointwise reward screens or one
selected witness. In particular, failure of stationary repetition does not
exclude an implemented punishment-tail consumer of the same induced Nash
row. A stronger exact-profile conclusion on an already covered UE class is
not an additional counterexample exclusion. For a residual reduction,
identify the configurations excluded and show that the actual incoming source
supplies every hypothesis. Proving another interface, sharpening a constant,
counting roots more precisely, or refuting a proof architecture without
narrowing the surviving counterexample class belongs in `notes/`.

The increment is measured against the project's implemented mathematical
capabilities, not against the published literature. An export is guidance for
formalization, not a publication submission. A complete, faithful handoff for
a relevant published theorem qualifies when its needed scope is not already
implemented and its use meets the coverage requirement above. Attribute the
theorem and explain that use; no claim of publication novelty is required.

An export must be one of the following and identify a concrete, goal-relevant
gap in the project's implemented mathematics or proof boundary that it fills:

- a complete rigorous answer of any kind explicitly accepted by a named item
  in [`../questions/`](../questions/README.md), including a candidate-level
  falsification when that question lists one as an acceptable answer;
- a complete proof of a missing arbitrary-game producer or a new direct route
  to an established semantic endpoint;
- a complete handoff for a relevant published result whose needed mathematical
  scope is missing from the project, with its proof, semantic translation,
  and intended use made explicit;
- a complete counterexample with the all-behavior terminal-gap conclusion;
- a special-case existence theorem for a precisely defined class whose needed
  scope is not already implemented, with an actual-data adapter and semantic
  consumer;
- a proved equivalence or reduction that strictly narrows an open obligation;
  or
- an exact counterexample or impossibility theorem that decisively removes a
  purportedly exhaustive conjecture route.

A promising construction, experiment, numerical pattern, literature analogy,
bounded-controller search, supplied-certificate verifier, local lemma without
a consumer, or conditional statement whose source hypothesis remains open
does not qualify. Keep it in `notes/`, however valuable it is.

In particular, audit the complete input-to-conclusion chain. A special-case
existence theorem may restrict the reward table by explicit mathematical
conditions, but must produce the strategies, continuation values, rates,
return data, or other strategic witnesses it uses for every table in that
class. Assuming one of those witnesses is not a substitute for producing it.
Calling an assumed witness a source, passport, or certificate does not change
this boundary.
For a new existence-class claim, defining the class itself as tables admitting
the desired strategy or certificate does not supply an actual-data adapter.
Give an independent reward-table criterion and prove that it produces the
required witnesses; otherwise classify the result as a supplied-object
characterization and apply the conditional exception where needed.

An exceptional conditional result requires a separate, explicit justification
of its independently important mathematical contribution and must still meet
the counterexample-class narrowing requirement above. State the exact
unproduced input, what the theorem settles without that input being available,
and why this is more than another interface or restatement of the open
consumer. Independent reviewers must assess that justification as well as
soundness. Do not count such a result as an eliminated branch, a new existence
class, or progress along a completed source-to-UE chain. Absent that affirmative
case, retain it in `notes/`.

Placement in `questions/` does not waive the coverage requirement. A complete
answer may still be an interesting internal theorem rather than a significant
export. The prospect of useful formalization, an accepted answer format, and
the soundness of a conditional implication are not substitutes for a concrete
narrowing of the surviving counterexample class.

## Mandatory gate

Every packet has all of the following:

1. An exact self-contained statement with every quantifier and finiteness
   assumption.
2. Complete definitions and a proof or exact counterexample with no deferred
   lemma.
3. An audit of probability mode, observation, randomization, stopping, and the
   power of one unilateral behavioral deviator.
4. A named actual-data adapter and downstream semantic consumer, or a precise
   proof that the packet strictly closes or narrows a named live obligation.
   Reviewers assess the concrete counterexample-class narrowing, including
   overlap with implemented theorems and already accepted packets.
   Reviewers explicitly list any strategic inputs not produced by the packet
   or its cited theorems. If any remain, they must affirm the conditional
   exception and its independent mathematical value, not merely the validity
   of the implication.
5. Exact positive and negative boundary tests relevant to the claim.
6. A source audit against the relevant `UniformEquilibrium/` declarations and,
   for paper-derived results, the original paper material. Identify the scope
   missing from the implementation and verify the attribution and semantic
   translation. This is an implementation-overlap check, not a demand for
   publication novelty; an already implemented equivalent or stronger theorem
   should be reused rather than exported as new work.
7. At least one substantive independent review with no unresolved objection,
   recorded outside the packet. A full-conjecture result or unrestricted
   strategy-class claim requires two independent reviews and an explicit
   falsification attempt. Queue membership indicates that this gate passed;
   the packet does not repeat its review history.
8. A Lean handoff that identifies likely definitions and theorem shape without
   assuming the desired conclusion as a structure field.

The author may assemble the packet after review, but may not waive a gate item.
If a later objection survives, remove the packet from this queue. Preserve a
packet under `revisit/` when it has checked useful content or a concrete
repair/completion path; use `notes/` for material that is no longer a formal
target. A packet moves to `formalized/` only when its useful stated content is
covered by checked Lean declarations.

## Freeze boundary

Promotion into `exports/` is a byte-level freeze. Run the final link,
formatting, review-count, and integrity checks before placement. Once placed,
do not edit an export for renamed questions, documentation cleanup, wording,
formatting, stronger constants, additional reviews, or later refinements.
The packet must already be self-contained under the reference policy below;
temporary conference files must not be retained merely to keep its links alive.

If a substantive mathematical error is discovered, remove the packet from
`exports/` immediately and repair it in `notes/` or `revisit/`. A corrected
packet must pass the complete gate again before a new frozen version is
promoted. Do not silently patch an export that an external formalizer may
already be using.

## Packet format

Use a stable uppercase mathematical result name, not an agent name:

```markdown
# Result title

## Exact statement

Use ordinary mathematical language and define every object.

## Conjecture-facing change

Name the prior open obligation, the exact improvement, and what remains open.

## Strategic inputs

List every strategic witness required by the conclusion and where it is
produced, including any witness needed again after a recursive step.
If a required witness remains assumed, state the conditional result's
independent mathematical importance. Record the exceptional admission
decision in the separate review record, not in the packet.

## Definitions and assumptions

Include probability, information, agency, and strategy-class data.

## Source correspondence

Name existing Lean declarations and files, paper theorems or sections, and the
exact new content. Explain every semantic translation.

## Proof

Give the complete proof, including auxiliary lemmas.

## Boundary tests

Show exact positive examples and attempted falsifiers.

## Adapter and consumer

Explain how arbitrary source data reaches the theorem and how its output
reaches a named semantic endpoint. Separate existing checked Lean from new
ordinary mathematics.

## Lean handoff

Suggest declarations, dependencies, useful finite tests, and the narrowest
checks. Do not prescribe speculative repository refactors.

## Scope and nonclaims

State everything the result does not establish.
```

The containing directory is the packet's lifecycle status and evidence that
the export gate passed. The packet contains mathematics and its formalization
handoff, not the story of its preparation. Do not include review links,
reviewer or assembly credits, acceptance verdicts, source-manuscript hashes,
gate checklists, migration history, or descriptions of which agent ran which
checks. Retain those records separately. Mathematical attribution to published
results remains appropriate.

## Self-containment and references

Packets must not refer to other content under `math/`, including other export
packets, questions, notes, feedback, archives, and temporary `gpt/` files.
This applies to plain-text dependencies and reproduction commands as well
as Markdown links. Local references must resolve to content tracked by Git;
check this with `git ls-files`, not merely filesystem existence. Cite
implemented results by exact declaration name and tracked source file.
Published mathematical results may be identified by their stable original
bibliographic citation, rather than an untracked local copy or reading note.

If a proof needs mathematics that exists only in a conference file, include
the necessary definitions, statement, and proof in the packet. Removing a
link while leaving an appeal to "the other packet" does not make a proof
self-contained. Likewise, an exact boundary example must include the data
and calculation it uses; a temporary checker or its reported counts are
not a substitute. Reproduction commands may depend only on tracked code
and tracked inputs, or on complete code and inputs contained in the packet.

Self-containment does not require duplicating verified tracked library
theorems. State their needed hypotheses and conclusion, cite the declaration,
and explain how the packet supplies those hypotheses. Keep the distinction
between those existing theorems and the mathematics to be formalized.

## External formalizer protocol

An external formalization agent reads a packet, rechecks the mathematics, and
implements it in the appropriate `Research`, `MathUE`, or `UniformEquilibrium`
lane under the root project policy. The agent must not import conference files
or encode the packet as an axiom. It reports any mathematical mismatch in
`feedback/` and stops claiming the export as accepted until the conference
resolves it.

Only the resulting checked Lean declarations can earn `L`, and only actual
checked adapters and consumers can earn `A` and `C`. The export packet itself
is at most mathematical (`M`) evidence.
