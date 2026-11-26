# Review of the actual three-owner decay control

Reviewer: CODEX_ACTUAL_GLOBAL_VARIATION.

**PASS for Section 10 and its current-summary paragraph as internal ordinary
mathematics.** This review does not recheck Sections 1--9, approve an export,
or certify a positive-gap exclusion or Lean theorem.

Reviewed source:
[the boundary note](../notes/CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md).
Section 10, from its heading through EOF, has SHA256
`3ff52100b662f3beb0a9f7d64f72513e1bc4bc0d4138b17afd3a960d38d42b94`.
The entire file before adding review links has SHA256
`298bf5b2b3c9d6d28afb32742dff0458052b6f3db5af5e47855955031ccc8fc1`.

## Mathematical checks

The table assigns all sixty entries consistently. I independently checked
the row-distinctness counts, every displayed principal determinant, the
strict inverse column, all six pair determinants, the four joining triple
determinants, the contact pencil and the outside inverse row with exact
SymPy arithmetic. They agree with the section. The negative singleton-column
argument proves the stated R0 property, and the negative-row argument rules
out a nonnegative inverse for each other triple.

The core identities are exactly Q(q)=4q and
P(q)+(1-q)^2 4q'=4q, with P(q)=q-q^2/2. The geometric bound gives literal
positive Never mass and infinitely many positive finite atoms. Since the
continuation annotation tends to zero, the residual vanishes even though
survival stays positive. This proves the actual payoff and full cap,
including Never and all randomized behavioral replacements. The pivot's
strictly positive conditional Never payoff dominates each nonpositive
current Quit offer; preceding signed passive rewards cancel in that
comparison.

An independent exact check of the asymptotics is

    (1-q_n)^2(1-8q_(n+1))=1-8q_n,
    N_n^2=1-8q_n.

The second identity follows by telescoping and q_n tending to zero.
Consequently f_n/q_n tends to 4, and B_i/beta_n tends to 1/3.
Geometric domination separately gives the squared-atom sum and the stated
collision ratio 1/21. None of these claims infer a positive absorbing gap.

The repetition argument retains the old full cap menu and takes limits of
finite blocks for each fixed number of copies. Thus it does not schedule an
operation after an infinite calendar. The resulting geometric payoff and
cap sums have different survival factors, N^3 and N^2. Their limiting debt
is indeed 1/6. The explicitly specified sure-core profile is an absorbing
full Nash profile, so both A=0 and m=0 hold directly.

## Scope and utility

This control adds a precise failure of the proposed asymptotic argument:
an actual infinite improper Nash tail can retain three comparable owners,
positive active caps of order total finite mass, and a positive normalized
collision scale. Repeating these arbitrarily small tails produces a fixed
observer regret. The existing finite-exact-Nash control instead supplies a
one-cohort improper Nash and an infinite proper Nash; it does not establish
these asymptotic properties. The retained-cap mechanism itself was already
known, and the section correctly identifies this as an exact realization of
that obstruction.

The example has pivot Never and m=0. It neither satisfies the subcritical
global-source hypotheses nor refutes case (1). The top summary and Section
10 state this limitation explicitly. No mathematical objection remains in
the reviewed scope.
