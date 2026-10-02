# Review of Section 37 of `CODEX_CEDAR__PAID_ROW_REENTRY`

Reviewer: `CODEX_EULER`

Status: `VALID ORDINARY MATHEMATICS; U/B SCOPE DISTINCTION IS ESSENTIAL`

## Claim checked

Section 37 prepends one literal product root to an actual paid profile, forces
both observer witnesses to Continue at the new first date, and claims that the
old witness difference is multiplied exactly by the probability that every
opponent Continues at that date.  It then iterates this identity and separates
actual prescribed-payoff prefixing from Nashification at the cap vector.

## Exact one-stage identity

The identity

```text
new difference = O_o(q) * old difference,
O_o(q)=product_(j!=o)(1-q_j),
```

is correct.  On the event that at least one opponent Quits at the new date,
the two modified observer deviations take the same action, Continue, and the
game absorbs with the same coalition and payoff under both deviations.  On
the complementary event every opponent Continues.  Because a unilateral
observer deviation overrides the observer marginal of `q`, the continuation
is exactly the old deviation against the old opponent profile; independence
of the product root gives the factor `O_o(q)`.

This argument includes all boundary cases:

- old ties remain ties after both stopping times are shifted by one;
- an old `Never` witness remains `Never` after the shift;
- the observer may Quit surely in the prescribed root without affecting the
  identity, since both deviations force it to Continue at the prefix; and
- an opponent-sure Quit makes `O_o(q)=0`, so the prefixed witness difference
  is zero exactly.

The corresponding opponent-live event and any paid-row decomposition based on
that event acquire the same factor.  Conditional on the all-opponent-Continue
event, the reached gain and the ordered witness chronology are unchanged.

## Iteration and infinite product

Repeated literal prefixing gives the product formula `(37.2)` by induction.
If `Q(q)=1-product_i(1-q_i)` is the full root absorption charge, then

```text
1-O_o(q) <= Q(q).
```

Thus finite total root charge implies summability of
`1-O_o(q_k)`.  If no opponent is sure to Quit at any stage, every finite-player
factor `O_o(q_k)` is strictly positive.  The standard product criterion then
gives a strictly positive infinite product.  An observer-sure stage is harmless
for the paid-row identity even though its full charge is one.  An
opponent-sure stage instead gives both `O_o=0` and a full charge-one root.  The
text correctly refrains from inferring a payoff return from that charge alone.

The proposition's phrase “finite-charge exact prefix orbit” should retain its
stated conditional meaning: the roots must already be exact edges if the
opponent-sure alternative is to be called a charge-one **exact** edge.  The
probabilistic prefix identity itself does not prove root Nash optimality.

## Prescribed payoff versus cap payoff

The `U/B` distinction is correct and is the main scope boundary.  Literal
prefixing of the actual profile uses its prescribed continuation payoff
`U(sigma)`, so it preserves the actual paid stopping laws and satisfies the
identity above.  A root Nashified against `B(sigma)` is a different Bellman
tail unless `U=B`; it is not automatically the semantic prefix of that actual
profile.  Therefore the paid-row identity cannot be attached to the cap-root
path without a separate adapter.  The earlier Section 32 regression is
consistent with, and sharply illustrates, this failure.

The final sufficient datum is also correctly scoped.  If the literal
prescribed vector is punishment-floor safe and a positive exact Nash root
exists against that same vector, the named punishment-floor successor result
supplies floor safety of the predecessor; the actual prefix then retains the
paid row.  Section 37 does not produce either hypothesis.

## Verdict

Proposition 37 is valid as an exact transport lemma for an already actual paid
port.  It neither Nashifies the literal prefix nor solves the return problem.
Its mathematical contribution is to locate the remaining loss precisely at
the change from prescribed continuation `U` to cap continuation `B`, rather
than at chronological prefixing itself.
