# Independent mathematical review of RESET_REGEN response and PR #86

## Verdict

The repaired one-step mathematics is sound and materially stronger than the
old interface.  PR #86 makes the canonical maximal successor's actual profile,
minimum, observer, stored paid scalar, shifted witnesses, every debt
coordinate, total debt, and inherited reset incidence part of the public
record.  An arbitrary inhabitant can no longer discard those equations.

The new ray file also proves a useful **conditional** Zeno normal form from a
supplied infinite ray: exact product scaling, a uniform survival floor,
constant positive-debt support and normalized debt, inherited-incidence
lower bounds, summable absorption, vanishing late absorption tails, and Fin4
terminal-Nash separation.

However, the response overstates what PR #86 currently exposes.

* The public type is
  `QuittingPaidCapLiftedSource.CanonicalMaximalPositiveRay`, not
  `QuittingPaidResetInfiniteRay`.
* PR #86 contains no theorem named `finiteStop_or_nonempty_infiniteRay`, and no
  theorem inhabiting `CanonicalMaximalPositiveRay` from an initial source.
  The file assumes the complete infinite sequence as input.
* It contains no marked-stage causal-atom theorem.
* The PR head does not compile: the strengthened one-step module built, but
  `PaidResetCanonicalZenoRay.lean` failed at its tail-limit proof and its Fin4
  specialization.  Those failures look repairable, but the checked status in
  the response is not the status of PR head `4349797`.

The missing recursion theorem is mathematically available by classical
dependent choice from the strengthened one-step alternative.  The marked
atom and Cauchy estimates are also straightforward.  They should be added
explicitly rather than reported as already checked.

There is one important scalar distinction.  The stored descendant annotation
is exactly multiplied by **joint** Continue mass.  The literal difference of
the two shifted pure-time deviations is exactly multiplied by the observer's
**opponents-only** Continue mass.  These factors need not agree.

Therefore:

* **PASS** as a valuable conditional boundary/formalization package after the
  compile errors, producer theorem, and wording are repaired.
* **FAIL** as a current export or conjecture-facing completion.  It supplies
  neither a finite rank nor positive late charge, return, terminal
  approximants, or inconsistency of the infinite ray.

## 1. Exact one-step result actually established

Let `S` be a `QuittingPaidCapLiftedSource`, let `r,o` be reset labels, and
assume

\[
d_r(S)=0,
\qquad
I_{r,o}(S)>0.
\]

Let `q(S)` be the selected maximum-absorption exact root against the complete
behavioral cap of `S.profile`.  Put

\[
c(S)=\Pr_{q(S)}(\text{all Continue}),
\qquad
a(S)=1-c(S).
\]

The strengthened
`MaximalOneStepPaidResetRegeneration` record in PR #86 states that the positive
absorption arm has one successor `S+` satisfying, literally,

\[
S^+.\mathrm{profile}
=\operatorname{Prefix}(q(S),S.\mathrm{profile}),
\tag{1}
\]

\[
S^+.\mathrm{minimum}=S.\mathrm{minimum},
\qquad
S^+.\mathrm{observer}=S.\mathrm{observer},
\tag{2}
\]

\[
S^+.\mathrm{gain}=c(S)S.\mathrm{gain},
\tag{3}
\]

and the two stored pure-time witnesses are shifted by exactly one date.
Moreover, for every player `i`,

\[
d_i(S^+)=c(S)d_i(S),
\qquad
D(S^+)=c(S)D(S).
\tag{4}
\]

The reset coordinate remains zero, inherited reset incidence satisfies

\[
c(S)I_{r,o}(S)\le I_{r,o}(S^+),
\tag{5}
\]

and a fresh fixed-law reset dispatch exists at the actual successor law.

If maximal absorption is zero, maximality plus nonnegativity proves that every
exact root at that cap has zero absorption, hence is literally all Continue.
Thus the one-step theorem gives

\[
\boxed{
\text{positive canonical successor}
\quad\lor\quad
\text{unique all-Continue exact cap root}.}
\tag{6}
\]

This part is a real public-interface repair.  The focused PR build reached and
built `PaidCapMaximalOneStepRegeneration.lean` before failing in the new ray
module.

## 2. Joint survival is not the exact shifted payoff factor

Let

\[
\Delta(S)=
V_{S.\mathrm{observer}}(S.\mathrm{row.receivingWitness})
-V_{S.\mathrm{observer}}(S.\mathrm{row.sourceWitness})
\]

be the actual pure-time payoff difference carried by the row.  The row
interface gives only

\[
S.\mathrm{gain}\le\Delta(S).
\tag{7}
\]

Let

\[
h(S)=\Pr_{q(S)}(\text{every opponent of the observer Continues}).
\]

The checked theorem
`quittingPureTimeDeviationPayoff_sub_rootThenContinuation_shift_one` gives the
exact literal transport law

\[
\boxed{\Delta_{\mathrm{shifted}}(S^+)=h(S)\Delta(S).}
\tag{8}
\]

Since joint survival includes the observer's own Continue event,

\[
c(S)\le h(S).
\tag{9}
\]

The constructor deliberately installs the conservative stored annotation

\[
S^+.\mathrm{gain}=c(S)S.\mathrm{gain}
\le h(S)\Delta(S).
\tag{10}
\]

Therefore (3) is exact for the **chosen annotation**, while (8) is exact for
the **literal behavioral payoff edge**.  A theorem claiming that the actual
paid edge itself scales by joint survival would be false unless an additional
condition forces the observer to Continue at the prefixed root.

This distinction strengthens rather than weakens the noncollapse conclusion:
along a ray the actual shifted edge is multiplied by
`prod h_k`, which is at least `prod c_k`.  But the two products must not be
identified.

## 3. Does a public recursive canonical ray now exist?

Only as a supplied structure.

PR #86 defines

```text
CanonicalMaximalPositiveRay initial resetOwner other
```

with fields `source : Nat -> QuittingPaidCapLiftedSource`, one positive
one-step record at every time, and the successor equation.  All subsequent
ray theorems take this structure as an argument.

There is no constructor

```text
Nonempty (CanonicalMaximalPositiveRay initial resetOwner other)
```

and no public exhaustive theorem combining a finite unique-cap stopping trace
with the infinite alternative.  The two declaration names asserted in the
response do not occur in PR #86.

### The missing theorem is nevertheless mathematically valid

The one-step alternative can be reapplied after every positive step because
(2), (4), and (5) preserve the same minimum, reset zero, and positive
incidence.  Classical dependent choice therefore gives the exact exhaustive
alternative

\[
\boxed{
\begin{array}{l}
\text{a finite coherent trace whose last source has unique all-Continue cap,}
\\[1mm]
\text{or one coherent infinite `CanonicalMaximalPositiveRay`.}
\end{array}}
\tag{11}
\]

This is not a new game-theoretic hypothesis.  It is missing packaging.  A
Lean-facing shape is:

```text
CanonicalMaximalTraceEndsUnique initial resetOwner other
  ∨ Nonempty (CanonicalMaximalPositiveRay initial resetOwner other)
```

where the trace stores the same one-step records, rather than only a list of
profiles.  This prevents an unrelated successor choice at each depth.

The underlying profile sequence is genuinely canonical: (1) forces it to be
the deterministic profile-indexed maximal-prefix sequence.  Proof fields and
returned reset witnesses may still be nonunique, but the actual profiles,
roots, observer, scalar, and shifted pure times are fixed by the source.

## 4. Sharp infinite-ray theorem

Assume a ray is supplied, and write

\[
c_n=c(S_n),
\quad a_n=1-c_n,
\quad
P_n=\prod_{k<n}c_k,
\quad
D_n=D(S_n),
\quad g_n=S_n.\mathrm{gain}.
\]

The public equations give

\[
\boxed{
D_n=P_nD_0,
\qquad
d_i(S_n)=P_nd_i(S_0),
\qquad
g_n=P_ng_0.}
\tag{12}
\]

If `D_*` is the stored positive global minimum, every `S_n` is an actual
profile, so

\[
D_*\le D_n=P_nD_0.
\]

Hence

\[
\boxed{P_n\ge\kappa:=D_*/D_0>0,}
\tag{13}
\]

and

\[
g_n\ge\kappa g_0>0.
\tag{14}
\]

Aggregate reset incidence obeys

\[
I_n\ge P_nI_0\ge\kappa I_0>0.
\tag{15}
\]

The positive-debt support and normalized debt vector are exactly constant:

\[
d_i(S_n)>0\iff d_i(S_0)>0,
\tag{16}
\]

\[
d_i(S_n)D_0=d_i(S_0)D_n.
\tag{17}
\]

The division-free form (17) is preferable in a public theorem.

### Actual paid edge

Let `h_n` be the observer-opponents survival at `q_n`, and let `Delta_n` be
the payoff difference between the literally shifted stored witnesses.  Then

\[
\boxed{
\Delta_n=\left(\prod_{k<n}h_k\right)\Delta_0,
\qquad
\prod_{k<n}h_k\ge P_n\ge\kappa.}
\tag{18}
\]

Thus both the conservative annotation and the actual payoff edge remain
uniformly positive, but generally with different exact products.

## 5. Summability and sharp block estimates

Because `0<c_n<1` and `P_n>=kappa`,

\[
\sum_n a_n<\infty,
\qquad a_n\to0.
\tag{19}
\]

For `m<n`, define the exact block survival and absorption

\[
C_{m,n}=\prod_{k=m}^{n-1}c_k
=\frac{P_n}{P_m}
=\frac{D_n}{D_m},
\tag{20}
\]

\[
A_{m,n}=1-C_{m,n}
=\frac{D_m-D_n}{D_m}.
\tag{21}
\]

The inequalities

\[
A_{m,n}\le\sum_{k=m}^{n-1}a_k
\le -\log C_{m,n}
=\log(D_m/D_n)
\tag{22}
\]

are sharp at first order.  Since the series tail tends to zero,

\[
\sup_{n>m}A_{m,n}\to0.
\tag{23}
\]

Thus every sufficiently late block formed solely from canonical ray roots has
vanishing total absorption.  This is stronger and more precise than merely
`a_n -> 0`.

### Law, payoff, and cap displacement

Assume `|r_i(T)|<=M`.  Let `nu_n,U_n,B_n` be the complete terminal law,
prescribed payoff, and unrestricted behavioral cap of `S_n`.  Composing the
literal prefix-law equations over the whole block gives the sharper bounds

\[
\boxed{\|\nu_n-\nu_m\|_1\le2A_{m,n},}
\tag{24}
\]

\[
\boxed{\|U_n-U_m\|_\infty\le2M A_{m,n},}
\tag{25}
\]

and, using `B=U+d` and `d_n=C_{m,n}d_m`,

\[
\boxed{\|B_n-B_m\|_\infty\le4M A_{m,n}.}
\tag{26}
\]

These improve the response's bounds with `sum a_k` by using the exact block
absorption.  They imply that all three packets are Cauchy.  PR #86 does not
currently state (24)--(26) as declarations.

## 6. Fixed causal atom

The PR proves only the aggregate incidence lower bound (15).  It does not
contain the marked-stage theorem claimed in the response.

Mathematically, if the initial actual profile has a fixed coalition `T` at a
fixed date `t` with mass `mu>0`, then the literal prefix identity (1) gives

\[
\boxed{
\operatorname{StageMass}(S_n,n+t,T)=P_n\mu
\ge\kappa\mu.}
\tag{27}
\]

This is the inherited contribution.  Fresh prefix absorption may add mass to
the same terminal-law coordinate but does not alter (27)'s marked shifted
event.

For the concrete Fin4 singleton-base source, no abstract selection is needed:
`FinFourSingletonBaseSameLawResetProducer.atom_mass_lower` already supplies a
fixed terminal coalition, and the persistent singleton owner Quits surely, so
the source absorbs at date zero.  The initial marked atom can therefore be
taken at `t=0` with the existing explicit positive mass floor.  A direct
adapter should expose (27) for that atom.

No declaration named `stageMass_eq_reach_mul` was found at current main or PR
#86.  The proof should use the existing live-root/profile prefix equations or
introduce that local transport lemma explicitly.

## 7. Actual Fin4 source adapter

The generic ray is not detached from the Fin4 project, but PR #86 does not
package the connection.

The checked route is:

```text
FinFourQuantitativeFullSupportHardResidual
  -> nonempty_resetRepairPaidChain
  -> chain.sourceCapLiftedSource
```

For this source choose

```text
resetOwner := chain.producer.resetOwner
other      := owner.
```

The producer fields give:

* resetOwner is free and hence has zero debt by `free_solved`;
* reset-owner/owner incidence is exactly one by `reset_incidence`;
* the residual supplies the terminal exploitability witness;
* the source minimum is positive and global;
* the initial paid scalar is the terminal gap; and
* the explicit source atom described in Section 6 is available.

Combining this adapter with (11) would give an actual hard-residual
alternative:

\[
\boxed{
\text{finite unique-all-Continue descendant}
\quad\lor\quad
\text{source-attached canonical Zeno ray with fixed paid/reset/atom floors}.}
\tag{28}
\]

That is the sharp source-facing theorem still to package.  It remains a
reduction, not a consumer.

## 8. Consumer and rank audit

The ray rules out several hoped-for conclusions rather than producing one.

1. **Debt-support rank is constant.**  Equations (16)--(17) exclude the
   existing positive-debt-support rank along these prefix steps.
2. **Late canonical charge vanishes.**  Equation (23) prevents late blocks of
   the same ray from supplying a fixed positive absorption floor.
3. **The descendants are not terminal approximants.**  In Fin4,

   \[
   \max_i d_i(S_n)\ge D_n/4\ge D_*/4.
   \tag{29}
   \]

4. **Cauchy is not recurrence.**  Equations (24)--(26) produce a semantic/law
   limit, but not a behavioral profile attaining it, a return to one earlier
   payoff, or a positive charged loop.
5. **The suffix atom is not prefix charge.**  Equation (27) remains behind the
   inserted roots; it does not make any `a_n` nonvanishing.
6. **The reset dispatch is not a chronological connector.**  Each step stores
   a fixed-law returned point, but exact cap-Nash against the returned cap does
   not imply exact Nash--Bellman admissibility against its prescribed payoff.

The existing charged-near-return consumer applies only after a new theorem
constructs a positive cumulative floor-admissible return.  The varying
paid-cap-port consumer is the wrong immediate target for this ray because its
fixed absorption-floor hypothesis is contradicted by (23).

A new rank would have to use data not constant under (12), such as a proved
finite change in binding/root strata or a source-preserving reset connector.
PR #86 supplies no such rank.

## 9. Boundary tests

### Scalar Zeno regression

Take

\[
c_n=\exp(-2^{-n-1}).
\]

Then every `a_n=1-c_n` is positive, `prod c_n>0`, `sum a_n<infinity`, all
product-scaled passports have uniform positive floors, and every late block
has vanishing absorption.  Hence no positive-return or finite-rank conclusion
follows from the scalar equations alone.

### Joint versus opponent survival

Let the observer Quit with positive probability at the prefix root while all
three opponents Continue surely.  Then

\[
h=1,
\qquad c<1.
\]

The literal shifted pure-time difference is unchanged, while the stored
annotation is deliberately reduced by `c`.  This falsifies identification of
the two gain factors.

### Zero-minimum regressions

Existing maximal-ray examples with zero global minimum show that Zeno prefix
geometry is behaviorally realizable.  They do not realize the complete
positive-minimum paid/reset state and are not counterexamples to Fin4.

No positive-minimum table realizing the infinite machine is supplied.

## 10. Formalization handoff

The missing or corrected declarations should be separated as follows.

```text
-- Exhaustive recursion, not merely the supplied ray interface
canonicalMaximalTraceEndsUnique_or_nonempty_positiveRay

-- Exact behavioral gain, distinct from stored annotation
CanonicalMaximalPositiveRay.actualPaidDifference_eq_opponentSurvival_mul
CanonicalMaximalPositiveRay.actualPaidDifference_eq_product_mul_initial

-- Exact block rather than additive-tail estimates
CanonicalMaximalPositiveRay.blockSurvival_eq_totalDebt_ratio
CanonicalMaximalPositiveRay.blockAbsorption_eq
CanonicalMaximalPositiveRay.outcomeLaw_dist_le_two_mul_blockAbsorption
CanonicalMaximalPositiveRay.payoff_dist_le_two_mul_bound_mul_blockAbsorption
CanonicalMaximalPositiveRay.cap_dist_le_four_mul_bound_mul_blockAbsorption

-- Literal source atom
CanonicalMaximalPositiveRay.stageMass_shift_eq_survival_mul

-- Fin4 actual-data entry
FinFourQuantitativeFullSupportHardResidual.uniqueCapDescendant_or_canonicalZeno
```

The first theorem must retain the one-step records in the finite trace and
infinite ray.  The last theorem should use the explicit singleton-base atom,
not reselect an unrelated positive law coordinate.

## 11. Gate conditions

### PASS for mathematical promotion/formalization

The package is worth integrating as a sharp conditional normal form after:

* PR #86 compiles and passes its import/trust checks;
* the response uses the actual public names and distinguishes a supplied ray
  from a produced one;
* the finite-stop/infinite-ray theorem (11) is added;
* the gain text distinguishes joint-survival annotation scaling from
  opponents-only actual payoff scaling; and
* the marked-atom claim is either formalized or clearly labeled ordinary
  mathematics.

The exact block estimates (24)--(26) and concrete Fin4 adapter (28) are useful
strengthenings but need not block merging the sound generic core if its
conditional status is explicit.

### FAIL for export as a completed Fin4 result

Do not export this as a terminal or descent answer while any of the following
remain true:

* the ray is only supplied rather than produced from the hard source;
* the unique-all-Continue finite branch remains unconsumed;
* the infinite branch has no positive charged return or renewable finite rank;
* the fixed-law reset output has no source-matched chronological seam;
* the marked suffix atom remains distinct from current prefix absorption; or
* no positive-minimum table realizes the infinite branch.

The strongest honest conclusion is (28): after the missing recursion and
adapter are packaged, the live obstruction is a genuine source-attached
canonical Zeno ray, not an arbitrary sequence of unrelated descents.  That is
strict boundary clarification, not a proof of uniform equilibrium.
