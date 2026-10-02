# Global semantic minimality excludes the singleton/Never chamber

**Author:** `CODEX_SOURCE_GATE`  
**Status:** proved ordinary mathematics from named checked declarations; not
Lean-checked; ready for independent review  
**Date:** 2026-08-31

## 1. Question and answer

The checked law-tight strict-minimum trichotomy has a singleton/Never arm.
That arm contains an owner whose displayed cap equals its own singleton
reward.  A law-tight hull minimum by itself can have this form; the exact
regression in
[`CODEX_SOURCE_GATE__SATURATION_FACE_UE_REGRESSION_AND_MARKED_TWO_PORT_AUDIT.md`](CODEX_SOURCE_GATE__SATURATION_FACE_UE_REGRESSION_AND_MARKED_TWO_PORT_AUDIT.md)
shows even a singleton canonical hull does not rule it out.

The actual Fin4 hard-residual construction retains one stronger datum: the
hull origin is a **global** minimizer of total terminal-semantic debt over the
entire semantic carrier.  This datum eliminates the singleton/Never arm
immediately.

The reason is exact.  Hull minimality and global minimality make the selected
hull minimum a global semantic minimizer as well.  The checked global
singleton-margin theorem then gives

\[
 D(z)\le z_i^{\mathrm{cap}}-r_i(\{i\}).                    \tag{1.1}
\]

At the singleton/Never owner, the right side is zero, while the hull minimum
has strictly positive debt.  This is a contradiction.  No chronological
edge, binding-cycle iteration, terminal exploitability toggle, or Fin4
cardinality argument is needed.

## 2. Self-contained theorem

Let $I$ be a finite player type, let $r$ be a finite quitting-game reward
table, and let

\[
 s,z\in
 \mathrm{QuittingTerminalSemanticLawPoint}(I).
\]

Write $D(x)$ for
`quittingTerminalSemanticDebtSum x`.  Assume:

1. $s$ belongs to `quittingTerminalSemanticLawCarrier r`;
2. the semantic pair $s.1$ is a global debt minimizer:

   \[
   D(s.1)\le D(y)
   \quad\text{for every }y\in
   \mathrm{quittingTerminalSemanticCarrier}(r);           \tag{2.1}
   \]

3. $z$ is an `IsQuittingLawTightCapNashSaturationMinimum r s z`;
4. $0<D(z.1)$; and
5. for some player $o$,

   \[
   z.1.2(o)=r_o(\{o\}).                                   \tag{2.2}
   \]

Then `False`.

Equivalently:

> A positive minimum of a law-tight cap--Nash hull whose origin is a global
> terminal-semantic debt minimizer has no cap coordinate equal to its own
> singleton reward.

This theorem is dimension-free.

## 3. Proof

### 3.1 The hull minimum is in the semantic carrier

By `IsQuittingLawTightCapNashSaturationMinimum.mem`, $z$ lies in the canonical
hull.  Since $s$ lies in the joint carrier,
`quittingLawTightCapNashSaturationHull_subset_carrier` gives

\[
 z\in\mathrm{quittingTerminalSemanticLawCarrier}(r).
\]

Applying `terminalSemanticLawCarrier_fst_mem_carrier` therefore gives

\[
 z.1\in\mathrm{quittingTerminalSemanticCarrier}(r).       \tag{3.1}
\]

This is the required carrier hypothesis for the singleton-margin theorem;
there is no silent identification of the hull with the semantic carrier.

### 3.2 The two minima have equal debt

The origin belongs to its hull by
`quittingLawTightCapNashSaturationHull_origin_mem`.  Hull minimality therefore
gives

\[
 D(z.1)\le D(s.1).                                        \tag{3.2}
\]

Conversely, (3.1) lets us apply the global source inequality (2.1) to $z.1$:

\[
 D(s.1)\le D(z.1).                                        \tag{3.3}
\]

Thus

\[
 D(z.1)=D(s.1).                                           \tag{3.4}
\]

For every semantic-carrier candidate $y$, equations (3.4) and (2.1) now give

\[
 D(z.1)=D(s.1)\le D(y).                                   \tag{3.5}
\]

Hence $z.1$ itself is a global terminal-semantic debt minimizer.

### 3.3 The checked singleton margin contradicts cap binding

Apply `minimumTerminalSemantic_singletonMargin` to $z.1$, using (3.1),
(3.5), and $0<D(z.1)$, at player $o$.  Its conclusion is exactly

\[
 D(z.1)\le z.1.2(o)-r_o(\{o\}).                           \tag{3.6}
\]

Substituting the cap-binding equality (2.2) into (3.6) gives

\[
 D(z.1)\le0,
\]

contradicting $0<D(z.1)$.  This proves the theorem.

The sign and coordinate orientation are essential: the checked margin is
**cap minus own singleton reward**, not prescribed payoff minus singleton
reward.  The singleton/Never chamber supplies exactly the cap equality needed
to make that margin zero.

## 4. Direct Fin4 hard-residual corollary

Inside the proof of
`finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber`, the source
declaration
`exists_finFourHardResidual_minimumLaw_causalSuffixAtom` supplies an origin
$s$ together with:

- joint-carrier membership;
- the global minimum property (2.1);
- equality of $D(s.1)$ with `quittingTerminalDebtSumInf r`; and
- positivity of that infimum.

The saturation construction then supplies a hull minimum $z$, proves
$0<D(z.1)$, and applies
`lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle`.
If the third disjunct occurs, its field
`QuittingSingletonNeverBindingCycleChamber.cap_binding` is precisely (2.2).
The theorem above gives `False`.

Therefore the source-attached Fin4 conclusion strengthens to the two-way
alternative

\[
 \boxed{
 \text{all four debts are positive}
 \quad\lor\quad
 \text{a reset-rigid same-law return exists}.}            \tag{4.1}
\]

All the origin, hull-minimum, positive finite atom, positive debt, and
minimum-face fields of the existing theorem can be retained unchanged.  Only
the impossible singleton/Never disjunct is deleted.

This does not settle either surviving branch and does not prove the Fin4
uniform-equilibrium conjecture.

## 5. The first global inequality that the exact regression fails

The rational regression in the linked note has

\[
 c=(0,0,0,1),\qquad
 r_i(\{i\})=c_i,\qquad D=\tfrac65.
\]

It is a positive minimum of its singleton canonical law-tight hull and of its
complete-law fibre.  If it were also a global semantic minimizer, the checked
margin would say, for every player $i$,

\[
 \tfrac65\le c_i-r_i(\{i\})=0,
\]

which is impossible.  Thus (1.1) is the first genuinely global inequality
that rules out the regression.  Its explicit stationary uniform equilibrium
is consistent with this: the game has other semantic carrier points below
the displayed hull point.

This comparison isolates the minimal missing source field sharply:

- same-law minimality is insufficient;
- canonical-hull minimality, even with a singleton hull, is insufficient;
- **global terminal-semantic debt minimality is sufficient** once one cap is
  singleton-tight.

The terminal exploitability witness is upstream justification for the
positive global minimum in the hard residual.  It is not separately used in
the branch-elimination proof.

## 6. Exact source/API audit

The proof uses the following checked declarations.

- `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`.
  Its conclusion is
  `debtSum pair <= pair.2 who - singletonReward who` under literal global
  semantic-carrier minimality and positive total debt.
- `quittingLawTightCapNashSaturationHull_origin_mem` and
  `quittingLawTightCapNashSaturationHull_subset_carrier` in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashSaturationHull.lean`.
- `IsQuittingLawTightCapNashSaturationMinimum.mem` and `.debt_le` in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashMinimumFace.lean`.
- `terminalSemanticLawCarrier_fst_mem_carrier`, used to pass from the joint
  law carrier to the semantic carrier.
- `QuittingSingletonNeverBindingCycleChamber.cap_binding` in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashStrictMinimum.lean`.
- `exists_finFourHardResidual_minimumLaw_causalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`.
- `finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourLawTightCapNashStrictMinimum.lean`.

There is one API presentation issue.  The current final Fin4 trichotomy
statement does not expose the origin's global-minimum field, although its
proof obtains and uses that field as `hsourceMinimum`.  A downstream proof
from the theorem statement alone therefore cannot eliminate the third arm.
The clean formalization is either:

1. add the dimension-free theorem of Section 2 and consume it inside the
   existing Fin4 construction before packaging the disjunction; or
2. expose the source global-minimum field and derive (4.1) downstream.

The first option is the smaller API and prevents an impossible branch from
escaping the source theorem.

## 7. Scope and formalization status

- The mathematical proof is a three-inequality argument using checked
  declarations with matching hypotheses.
- No compactness, attainment, behavioral strategy restriction, or law-fibre
  substitution is added.  The only attainment is the already checked global
  semantic minimizer supplied by the hard-residual source.
- The conclusion is dimension-free at the generic level and eliminates only
  the singleton/Never disjunct in the source-attached Fin4 theorem.
- The result is not yet Lean-checked and has not passed independent review.
- No export is proposed before review.

## 8. Concrete next step after review

Formalize the dimension-free exclusion lemma, then strengthen the Fin4 source
theorem to (4.1).  Research should resume only on the full-debt and reset-
rigid arms after that integration; the singleton/Never binding cycle is not a
live hard-residual chamber.
