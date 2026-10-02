# Ideas and Technique Lenses

This directory is a deliberately low-commitment catalogue of mathematical and
physical ways to think about the conference's recurring obstructions. It is
not a theorem-status lane, a task queue, or a substitute for `notes/`.

The distinction is intentional:

- `ideas/` names broad techniques, analogies, and architectural bets;
- `notes/` contains a self-contained mathematical question, source audit,
  calculations, and an honest proof status;
- `feedback/` contains independent criticism of a named note; and
- `exports/` contains only reviewed mathematical results ready for attempted
  formalization.

An entry here may be vague. It may suggest a useful language without asserting
that the language applies. A statement does not become conference mathematics
until somebody formulates its finite data and quantifiers in an owned note.

## Files

- [`NONLOCALITY_TECHNIQUE_CATALOGUE.md`](NONLOCALITY_TECHNIQUE_CATALOGUE.md)
  gives stable identifiers for recurring mathematical and physical responses
  to nonlocality.
- [`CURRENT_NONLOCALITY_RECOMMENDATIONS.md`](CURRENT_NONLOCALITY_RECOMMENDATIONS.md)
  records a dated, provisional judgement about which lenses currently appear
  most relevant to the quitting-game frontier.

The catalogue should change slowly. Recommendations may change whenever a
proof, no-go result, or new interface changes the frontier.

## How to visit an idea

1. Choose one catalogue identifier, such as `NL-06`.
2. State one exact conjecture-facing question in a new owned `notes/` file.
3. Use `SOURCES.md` to inspect only the declarations and paper sections needed
   for that question.
4. Test small positive and negative examples before building an abstraction.
5. Record the strongest surviving statement, including a counterexample or
   no-go when the proposed localization fails.

There is no completion checklist. Several independent visits to one technique
are preferable to marking a broad idea "done."

## Research-lane candidates

A reviewed conditional lemma may still be worth implementing in the
repository's `Research` lane when compilation would test a plausible producer
interface, expose hidden hypotheses, or prevent later re-derivation. Record a
narrow theorem shape and the exact diagnostic purpose in its owned `notes/`
file. This recommendation does not promote the lemma to `exports/`, establish
an arbitrary-game producer, or earn checked adapter/consumer status. The
conference itself does not write Lean; Research implementation remains an
external formalization task under the repository policy.
