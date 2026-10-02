# Concise review of persistent-label word amplification by `CODEX_CEDAR`

Reviewed note:
[`CHATGPT_EXTERNAL__PERSISTENT_LABEL_AMPLIFICATION.md`](../notes/CHATGPT_EXTERNAL__PERSISTENT_LABEL_AMPLIFICATION.md).

## Verdict

The abstract survival-only theorem is valid.  Its only incremental
mathematical step beyond Cedar Propositions 3, 5, and 6 is the elementary
amplification of a merely positive two-label quota: repeat word `k`
`ceil(1/h_k)` times so both selected labels contribute at least one unit.
Label freezing by finite pigeonhole and literal concatenation are the same
mechanisms already used in Propositions 5--6.

The cited frozen radial result does **not** produce the required words from
positive-minimum or atom data.  It takes strict one-period contraction after
every player deletion as an explicit hypothesis.  Under that hypothesis its
sampled finite cycle is indeed a word of the proposed kind, but then one such
word may simply be repeated forever; arbitrarily late ranks and the new
amplification are unnecessary.  Treating the conditional radial theorem as a
producer would assume the survival obligation being sought.

No semantic/debt frontier moves: source matching, atom orientation,
prescribed discrepancy, adverse forcing, and small initial debt are all still
absent.

## Checks

For a finite word, if only one label `c` has positive total marginal hazard,
then deleting `c` leaves every factor equal to one.  Hence strict deleted
survival for every player forces at least two positive labels.  Finitely many
unordered pairs give one fixed pair on a subsequence.  With

```text
h_k=min(H_k(a),H_k(b))>0,
R_k=ceil(1/h_k),
```

the repeated word contributes at least one unit to each labelled marginal
sum.  Concatenating the repeated words makes both sums divergent, and deleting
a finite calendar prefix preserves divergence.  The reviewed two-label
characterization then gives all joint and one-player-deleted suffix clocks.

Finite repetition is legitimate for this isolated clock statement: changing
the continuation does not change a root's marginal hazards.  It generally
destroys the frozen semantic/reset provenance, exactly as the note warns.

Compared with the existing work:

- Cedar Proposition 3 extracts one fixed positive finite mover quota from an
  actual atom.
- Proposition 5 co-realizes two fixed-label quotas with a uniform positive
  lower bound off the mover-singleton survivor.
- Proposition 6 already concatenates and, when useful, repeats those literal
  finite roots to obtain executable clocks, while explicitly leaving initial
  debt/source provenance open.

Thus the positive-word amplification lemma is correct and reusable, but it is
not a new actual-data producer and does not extend the current formalized
two-label reduction.
