# Independent reviews: the universal-descent mechanism boundary

Reviewers: UNIVERSAL_JOINT_PRICES and UNIVERSAL_FINITE_HEAD.
Both independently checked the final quantitative argument and returned PASS.
These are ordinary mathematical reviews; no Lean build was run.

## Reviewed artifacts

- [Canonical note](../notes/CODEX_COORDINATOR__BOUNDED_CROSSING_SELECTION.md),
  SHA256 `500b201f0fb9ffb73e8bb10943949511534ed405131fd9cea0e25fe0e246d1dc`.
- [Frontier note](../notes/CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md),
  SHA256 `3a07f53da9bcffe6b5a6196e4a8d0233dab9b87dbbfca4b838bb057ba198e7be`.

Scope: Section13 and its introductory, verification and frontier summaries.
Earlier proofs retain their prior scoped reviews. UNIVERSAL_FINITE_HEAD
independently derived the qualitative proper-head exclusion; the explicit
constants and positive-gap strengthening were independently checked against
the coordinator's quantitative proof. Neither review treats experiments or
finite tests as proving the unrestricted statement.

## Full-cap accounting and the quantitative estimate

For a finite chronological word the exact identity is

    D=sum_t S_t R(q^t;b^(t+1)),

where b^(t+1) is the next FULL CAP vector. Evaluating the regret at the
prescribed continuation payoff instead would invalidate this identity.
The note retains the full cap throughout. Since each chronological reach
S_t is at least the final head survival h, D>=h E for the unweighted sum E.

Both reviewers checked the suffix bootstrap. Activity A<=2delta keeps
Continue above Quit by at least eta-6M delta>=eta/2 and moves the cap by
at most2M A. If E is below eta delta/2, a suffix of individually small
roots cannot accumulate delta activity. Either the entire head is small,
giving E>=eta(1-h)/2, or the last large root has a trailing cap within
4M E/eta of w. Each root-regret summand is1-Lipschitz in its cap input;
the four-row sum is4-Lipschitz. Thus E>=gamma-16M E/eta. The displayed
constant c proves D>=c h(1-h), uniformly in word length.

The compact minimum gamma is strictly positive because its root set avoids
the unique Nash root0. No root nondegeneracy or chosen cap maximizer is
assumed. Intermediate caps outside the protected suffix may be signed.

Countable heads are approximated in total variation, uniformly over all
responses. The complete annotation map then passes the bound to compact
head limits with ORIGINAL marginal Never retained. At h=1, the head's
finite masses vanish and its full annotation is empty. At h=0, the bound
correctly becomes vacuous; an absorbing exact head is not excluded by
root inertia alone.

## Actual source application and absorbing endpoint

The source application uses an UNMARKED global least-Never zero-debt point.
A nonzero Nash root there would preserve zero debt and lower Never, so its
positive-payoff branch supplies root inertia. This reasoning cannot simply
be transferred to a marked minimum whose prefixed output loses its mark,
or to an inherited fixed-payoff minimum after changing the payoff.

Both reviewers checked the A_Z>0 upgrade. With h0=(A_Z/(28M))^4, the repair
inequality gives D>=A_Z/2 for h<=h0, and the proper-head bound gives
D>=c h0(1-h) otherwise. The reward bound A_Z<=8M ensures h0<1.
Consequently kappa=min(A_Z/2,c h0) gives the all-head absorption-relative
floor. This is a restriction on a proposed producer, not such a producer.
An arbitrary native absorbing profile is not automatically a valid head:
the extra through-continuation response must still be checked.

## Fixed-payoff obstruction and scope

For the note's indicator reward table, every response pays at most the
indicator that some opponent has a finite clock. Never attains its
expectation, so B_i=e_i=1-product_(j!=i)N_j on the entire actual carrier.
At zero debt this gives nu^3=product_i(1-u_i). When every u_i<1 the Never
product is fixed and positive; the stated solo profile realizes the
one-zero fibre exactly. Pure solo absorption is already Nash for this
table. The example therefore has A_Z=0 and does not refute a repair theorem
using the counterexample's positive gap or genuine global ancestry.

The overlap attribution is accurate: the prior global finite-block regret
theorem concerns a positive original MAX-debt minimum and a lowered
continuation. Section13 instead derives the proper-head estimate from
positive root inertia alone at a native zero-debt continuation. The proof
extends the existing positive-buffer method by the last-large-root argument.
The frontier correctly reports a mechanism restriction, with no new raw
UE class or universal Fin4 descent claimed. No unresolved objection remains
within this review scope.

## Constructive whole-law extension: independent review

The same two reviewers independently checked the added subsection "A local
whole-law descent beyond every finite exact Nash profile" and its status
summaries against these final artifacts:

- Canonical note SHA256
  `7dfe62beee27f6411d222f90786f0a081edc3d0a48231fd08f9605b0feaee4db`.
- Exact geometry checker SHA256
  `6a9568989cf27c2bc0770db21b4d0e6982e5f7b5d494df89bf5f55f3738e530f`.
- Frontier note SHA256
  `c8de3d9e92af0705ea894a01c63419c382ac6e8ae3c577bf224863cb83d5bac7`.

Both returned PASS. The prior review above retains its earlier artifact
scope. The introduction now explicitly excludes NONEMPTY proper heads,
preserving the empty-head case of the theorem.

The existing GLOBAL_CREATIVE reward table gives exactly Q=2p-p^2,
P=p+p^2 and H=(1-p)^2. The recurrence s(T(p))=(Q-P)/H and bound
T(p)<=3p/5 are correct on[0,1/2]. Thus the constructed laws are actual
natural-date laws with strictly positive literal Never, rather than only
compact semantic limits. Telescoping the response values proves that every
finite core deadline and Never pays s(p_0). The observer's Never response
dominates all finite replies. The full Nash assertion is therefore valid.

The uniform geometric estimate controls every summed quadratic remainder.
With p_0=1/2-epsilon, the tail hazard sum is4epsilon+O(epsilon^2), yielding
log nu=log(1/8)-6epsilon+O(epsilon^2) and nu'= -3/4 at zero. Total-variation
distance tends to zero because both the old first-root change and new tail
mass are O(epsilon). The independent finite-head review also supplied and
checked the exact interval0<epsilon<=1/32: the first three survival factors
already have product below1/2. The other reviewer checked that argument in
the integrated note.

The truncation formulas are exact: core cap s(p_0), prescribed shortfall
N_L^3 s(p_L), Never shortfall N_L^2 s(p_L), and total debt3N_L^3 s(p_L).
The observer still has zero debt. Hence the finite approximants have
positive debt tending to zero, rather than being silently asserted exact.

The finite-head reviewer independently rechecked the referenced complete
root and finite-word census, including exclusion of sure roots against
actual cap vectors with nonnegative observer cap. Thus the comparison is
against ALL finite exact Nash laws, not a symmetric search. The retained
checker reuses the existing reward fixture, runs its assertions and checks
the new symbolic recurrence, derivative, interval and truncation identities.
Both reviewers ran it successfully; all seven reported groups passed.

This is a local change of the existing first root together with an infinite
tail, so it does not contradict proper-prefix rigidity. The old expanding
orbit mechanism and head compensation are attributed. The construction
does not use global minimum assumptions and does not produce the direction
for arbitrary tables. No new UE reward class or universal descent is
claimed; no unresolved objection remains in this extension's scope.
