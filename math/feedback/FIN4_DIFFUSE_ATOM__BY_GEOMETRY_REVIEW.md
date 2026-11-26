# Final adversarial geometry review

Reviewer: ATOM_GEOMETRY_REVIEW. Ordinary mathematics, not Lean checked.

Reviewed artifact:
`math/notes/CODEX_COORDINATOR__DIFFUSE_APPROXIMATION_ATOM_OBSTRUCTION.md`.
SHA256: `9395ca7fbde32b38462b3b379e7db67e62941ced0c06a0afbd7a4046b3709a3f`.

**Verdict: PASS on the complete no-absorption-path theorem and its uniform
neighborhood inference.** The actual-profile compactness adapter has a
separate reviewer; this review does not claim a new positive UE class or
an unrestricted exploitability gap.

The zero-set derivative argument is sound. Simultaneous zero rows of
cardinality at least two have measure zero by principal nonsingularity.
The union of zero sets is closed and has full measure, so a row is zero at
every time. This makes each unique-zero region open and its components
literal straight arcs; it does not assume local finiteness in advance.

I specifically checked the possible Zeno gap. A double-zero point has a
neighborhood containing exactly one switch, by integrating the two scalar
row equations on both sides. Near a triple-zero point b the fourth owner
cannot move, and invertibility makes b the only triple-zero time. Every
other nearby point is locally finite by the double-zero calculation.
Consequently an accumulation on one side really does yield an infinite
ordinary directed word on three vertices, with all three triangle transitions
recurring. Left accumulation forces B^{-1}>=0 from the actual nonnegative
remaining-mass difference vectors, which forbids any right continuation.
Right accumulation symmetrically forces B^{-1}<=0 and forbids arrival from
the left. These contradictions rule out all interior accumulations, including
an attempted Cantor set of switches.

An isolated triple contact also follows the opposition graph. Its adjacent
owners cannot coincide: a newly zero other row would then retain the same
nonzero slope on both sides and violate nonnegativity. For distinct adjacent
owners the incoming and outgoing arcs give exactly the asserted opposite
signs. Thus the chronological tail word and recurrent-owner argument are
legitimate. A final single-owner arc is ruled out by a negative entry in
its full column. Three recurrent owners give every inverse column and every
outside inverse-row coordinate, so they contradict the stated bad-child
hypothesis.

The four-owner graph classification is complete. Strong connectivity without
a Hamiltonian cycle leaves precisely the bowtie; its missing reciprocal pair
must be negative because every other pair is opposition and a negative pair
exists. Positive row normalization preserves the path conditions. In the
normalized bowtie the derivative identity for D is exact. If e>=c,
complementarity gives D'>=0 on {D>0}; absolute continuity and D(1)=0 force
D<=0 globally. Any positive u_3 would then give two zero rows on a set of
positive measure, impossible. The symmetric case deletes owner 2. This is a
direct branch elimination and does not depend on the earlier switching
argument.

The canonical matrix's determinant list and Farkas row identity were checked
exactly in the preceding review. The Hamiltonian exclusion in Section 5 is
also correct: with both opposite chords negative, each principal triple's
two determinant products are negative. Positive full determinant makes every
inverse diagonal negative, contradicting any strictly positive inverse column.

The compactness-to-uniform-neighborhood contradiction in Section 4 has the
correct quantifiers. The maximum-positive-own-level variant still provides
nu<=E/m by choosing one positive owner; the additional M*nu term in the cone
bound accounts for the other, possibly negative own levels. No bounded date
of the required atom is asserted. The statement expressly does not exclude
counterexample tables or produce an approximate equilibrium.

Final clarifications were checked against these exact bytes: the introduction
includes the positive-own-level condition, the date-mass statement uses the
maximum over dates, Section 3 explicitly defines v=Gamma*a, and the isolated
triple-contact argument explicitly excludes coincident adjacent owners.
No unresolved mathematical objection remains in the geometry reviewed here.
