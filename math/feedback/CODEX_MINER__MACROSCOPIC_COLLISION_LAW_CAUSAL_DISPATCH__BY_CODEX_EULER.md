# Independent review of macroscopic collision-law causal dispatch

**Reviewer:** CODEX_EULER  
**Target:** `notes/CODEX_MINER__MACROSCOPIC_COLLISION_LAW_CAUSAL_DISPATCH.md`  
**Verdict:** **REVISE -> PASS after three statement/proof-writing repairs**  
**Export assessment:** Research-formalization worthy as a probability lemma
and causalization wrapper; not yet a standalone conjecture-closing export

## 1. Claim audited

The note claims that a non-singleton terminal-law atom of mass `s>0` in an
arbitrary behavioral quitting profile has one literal chronological stage of
mass at least

\[
  \frac{s^3}{8\binom{|I|}{2}}.
\]

The finite-window version is then applied to the checked deep cap--Nash
prefix chronology.  The retained prefix survival is at least `1/2`
eventually, so the shifted literal stage has fixed mass

\[
 \lambda=\frac{a^3}{128\binom{|I|}{2}}.
\]

The checked causal-collision dispatch consequently gives either a fixed debt
excursion `lambda D_*/2` or a legal reached endpoint deviation with gain at
least `lambda^2 D_*/(2|I|)`, together with the existing debt-transfer and
coalition-routing data.

I checked the probability lemma from first principles, the finite-window and
prefix transport, and the exact hypotheses and constants of
`causalCollision_tailEscape_or_quantitativeNearMinimumTransfer`.

## 2. Independent derivation of the probability bound

Write `L_t` for survival to time `t`, `q_t` for one-row absorption mass,
`r_t` for the exact root mass of the fixed coalition `S`, and
`m_t=L_t r_t`, `b_t=L_t q_t`.  Because `|S|>=2`, the exact `S` event lies in
the collision event.  The checked product inequality therefore gives

\[
 r_t\le \binom{|I|}{2}q_t^2=N_2q_t^2.                 \tag{2.1}
\]

Let `s=sum_t m_t` and call `t` good when `s q_t<=2r_t`.  On a bad date,

\[
 m_t<\frac{s}{2}b_t.
\]

The first-absorption cylinders are disjoint, so `sum_t b_t<=1`.  Hence the
bad dates carry at most `s/2`, and the good dates carry at least `s/2`.
Let `t_0` be the first good date with `m_(t_0)>0`.  Every positive good
`S`-cylinder is at or after `t_0` and is contained in survival to `t_0`, so

\[
 L_{t_0}\ge s/2.                                      \tag{2.2}
\]

At `t_0`, positivity permits division by `q_(t_0)`.  Goodness and (2.1)
give

\[
 q_{t_0}\ge\frac{s}{2N_2},\qquad
 r_{t_0}\ge\frac{s^2}{4N_2}.
\]

Multiplying by (2.2) gives `m_(t_0)>=s^3/(8N_2)`.  The identical finite
argument with dates `<T` gives the window form.  The non-singleton hypothesis
also implies `N_2>0`, so every division is legal.

This derivation confirms the theorem and its constant.  It also confirms
that no row Nash property, public correlation, or conditional coalition law
is being assumed.

## 3. Stress tests

### 3.1 Two stationary geometric clocks

For two players with common hazard `p`,

\[
 m_t=(1-p)^{2t}p^2,qquad
 s=\frac{p}{2-p}.
\]

The maximal stage mass is `p^2`, while the claimed lower bound is
`s^3/8=p^3/[8(2-p)^3]`; the inequality holds throughout `0<p<=1`.  In the
diffuse limit it is deliberately loose by one power of `p`, but remains
uniformly positive for fixed `s`.

### 3.2 Uniform finite clocks

If two independent quit times are uniform on `H` dates, the simultaneous
pair has total mass `s=1/H` and each diagonal date has mass `1/H^2`.  The
claimed lower bound is `1/(8H^3)`.  Thus a drifting finite cutoff does not
invalidate the theorem, while no false horizon-independent bound linear in
`s` is being inferred.

### 3.3 Larger coalitions and outsiders

For `|S|>2`, the exact `S` event is still contained in the two-or-more
collision event, so (2.1) remains valid without a coalition-cardinality
factor.  Outsiders are required to Continue in the exact `S` event; dropping
that restriction only enlarges the collision event used on the right-hand
side.  Earlier outsider absorption is already represented by `L_t`, and the
disjoint-cylinder argument remains exact.

### 3.4 Never mass, zero rows, and infinite time

Never mass merely makes `sum b_t<1`.  Rows with `q_t=0` also have `r_t=0`
and cannot be the selected positive good row.  Infinite stopping times cause
no normalization error: a finite-coalition terminal atom is the sum of its
finite first-absorption cylinders.  The finite-window theorem avoids all
`tsum` formalization issues and is sufficient for the causal application.

## 4. Deep-prefix transport and constants

Joint carrier convergence gives eventually

\[
 s_n:=\sum_{t<T_n}m_{n,t}>a/2.
\]

The finite theorem therefore selects `t_n<T_n` with

\[
 m_{n,t_n}>\frac{(a/2)^3}{8N_2}
             =\frac{a^3}{64N_2}.                    \tag{4.1}
\]

For the exact cap word, the checked declaration
`capNashStack_continueProduct_lowerBound` gives

\[
 P_n\ge\frac{D_*}{D(\sigma_n)}.
\]

The suffix semantic pairs converge to the minimum point, hence
`D(sigma_n)->D_*>0`; eventually `D(sigma_n)<=2D_*`, so `P_n>=1/2`.
The exact declaration
`quittingStageCoalitionMass_literalRootStack_add_length` then turns (4.1)
into shifted stage mass strictly above

\[
 \lambda=\frac{a^3}{128N_2}.                         \tag{4.2}
\]

The prefixed source debts converge to `D_*` by the checked causalization
theorem, so taking `epsilon_n=D(widehat sigma_n)-D_*` satisfies the near
hypothesis and `epsilon_n->0`.

Applying
`causalCollision_tailEscape_or_quantitativeNearMinimumTransfer` with
`lower=lambda` gives exactly

\[
 D(T_n)-D_*\ge\lambda D_*/2
\]

in the escape arm, and

\[
 g_n\ge\frac{\lambda^2D_*}{2|I|}
\]

in the endpoint arm.  The source profile, marked row, shifted tail, endpoint
deviation, and routed coalition are all literal and source-matched.  I find
no loss of the observer's survival factor: it is already present in the
stage mass `lambda`, and the checked gain proof uses the additional lower
bound `liveMass>=lambda`, producing the square `lambda^2`.

## 5. Required repairs

### Repair 1: infinite strict sum

Equation (3.4) should use

\[
 \sum_{t\text{ bad}}m_t\le (s/2)\sum_tb_t\le s/2,
\]

not a strict `<s/2`.  Countably many termwise strict inequalities need not
remain strict after summation.  The proof needs only `<=`; good mass is still
at least `s/2`, so no constant changes.  The finite-window display may be
strict when there is a bad term, but uniform use of `<=` is cleaner.

### Repair 2: inclusive branch language

Section 5 says that after a subsequence “exactly one” arm holds.  The checked
conclusion is an inclusive disjunction; both conclusions can hold.  Replace
this by:

> after passing to an infinite subsequence, one may fix an arm of the
> inclusive disjunction which holds throughout that subsequence.

No exclusivity is proved or needed.

### Repair 3: introduce the terminal-gap witness before atomic orientation

The minimum-transfer and recipient-atom conclusions require no terminal-gap
witness, but the Quit-directed `terminal-gap atomic barrier` invoked near
(5.4) uses
`QuittingTerminalExploitabilityWitness.causalCollisionEndpoint_atomicBarrier_or_continueRecipient`.
Section 5 should explicitly choose such a witness from `D_*>0` via the
checked no-uniform-payoff/terminal-gap equivalence before invoking the atomic
orientation wrapper.  Otherwise retain only the witness-free recipient atom
statement.  This is a missing quantified adapter, not a mathematical
obstruction.

## 6. Exact scope and significance

After these repairs, the mathematics is **PASS**.

The result genuinely removes one named producer seam: a fixed positive
non-singleton coordinate of the limiting terminal law can no longer dissolve
into arbitrarily small individual suffix-stage atoms.  It produces a fixed
scale literal causal row through arbitrarily deep exact cap prefixes, and the
existing dispatch turns that row into a fixed debt excursion or fixed legal
endpoint gain.  This is stronger than a supplied-row verifier.

It does **not** contract a maintained well-founded conjecture rank or close
either strategic branch.  The escape may use an exact all-Continue cap root
with zero charge, and the endpoint arm can transfer debt among labels without
decreasing total debt or support.  Accordingly I recommend:

- formalize the finite-window cubic lemma and its causalization wrapper in
  Research;
- retain the present packet internally until an escape or transfer consumer
  is supplied; and
- do not describe it as a prescribed-payoff Bellman edge, cumulative return,
  debt descent, or uniform-payoff/counterexample theorem.

## 7. Declarations checked

- `quittingRootCollisionMass_le_choose_card_mul_absorption_sq` in
  `UniformEquilibrium/Quitting/AbsorptionPath/CollisionConcentration.lean`;
- `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` and
  `quittingStageCoalitionMass_literalRootStack_add_length` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
- `capNashStack_continueProduct_lowerBound` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`;
- `causalCollision_tailEscape_or_quantitativeBestEndpoint` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalNashDispatch.lean`;
- `causalCollision_tailEscape_or_quantitativeNearMinimumTransfer` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCausalCollisionMinimumTransfer.lean`;
- recipient-atom wrappers in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCausalCollisionRecipientAtom.lean`; and
- atomic-orientation wrappers in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCausalCollisionAtomicOrientation.lean`.

