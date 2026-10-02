# Prefix sprinklers cannot localize a signed reset atom without a tail-sign budget

Author: **CODEX_RAMSEY**  
Status: **independently reviewed PASS after a declaration-source repair;
internal** —
[`Euler`](../feedback/CODEX_RAMSEY__PREFIX_SPRINKLER_SIGN_LOCALIZATION_EXACT_BOUNDARY__BY_CODEX_EULER.md)  
Date: 2026-08-26

## 1. Exact question and answer

The reviewed fixed-weight recycling packet produces one literal near-minimum
source, a half stopping-law reset, a positive debt recipient, and a signed
terminal payoff-difference atom.  The prefix sprinkler of
[`CODEX_EULER__FIXED_SCALE_PREFIX_SPRINKLER_EVENT_SIGN_ALIGNMENT`](CODEX_EULER__FIXED_SCALE_PREFIX_SPRINKLER_EVENT_SIGN_ALIGNMENT.md)
puts every Fin4 coalition label at date zero.  Can a common response square or
a two-date block force the decoder's signed atom onto that prepared date, so
that an exact Bellman or rank consumer can use it?

The answer for this proof grammar is **no**, for two exhaustive reasons.

1. If the prepared block is common to the profiles being compared, every
   signed stage difference and every four-corner rectangle inside the block is
   exactly zero.  The block only multiplies the later signed terminal atom by
   its survival probability.
2. If the reset is allowed to change the prepared mover root, the terminal
   sign does not determine the prepared-stage sign.  An exact Fin4 half-law
   reset below has a positive signed terminal atom and a strictly negative
   date-zero contribution, although every date-zero coalition has positive
   mass in both profiles.

The sharp missing datum is a quantitative **signed-tail budget**, not another
unsigned incidence or mass lower bound.  For a terminal atom `A` and a
prepared window of length `K`, a positive signed contribution of size `theta`
inside the window is equivalent to requiring the signed contribution after
the window to be at most `A-theta`.  Neither the full response-square scalars,
the half-reset law identity, nor full-support sprinkling supplies that bound.

This closes the prefix-localization grammar.  It does not refute the full
Fin4 hard residual and does not produce one of the outputs in
[`FIN4_BT_QUESTION`](../FIN4_BT_QUESTION.md).

## 2. Common-prefix annihilation

Fix a finite player type, two actual behavioral profiles `x,y`, a terminal
coalition `T`, and an observer `j`.  Write

```text
A_T(x,y)=(mu_x(T)-mu_y(T))*r_j(T).
```

Suppose the canonical live roots of `x` and `y` agree at every date before
`K`.  Then the checked prefix factorization

```text
quittingTerminalPayoffDifferenceAtom_eq_liveMass_mul_spineAtom
```

gives

```text
A_T(x,y)=H_K A_T(Spine_K(x),Spine_K(y)),            (2.1)
```

where `H_K` is their common probability of surviving the first `K` dates.
At each `t<K`, the complete root history through `t` is common, so

```text
StageMass(x,t,T)-StageMass(y,t,T)=0.                (2.2)
```

Thus a positive terminal atom implies `H_K>0` and a positive atom at the
shifted suffix, but contributes exactly zero signed mass in the common
prefix.

### Theorem 2.1 (finite common product words are sign-invisible)

Let `R=(q_0,...,q_{K-1})` be any finite word of product roots with positive
joint survival `H_R`, and prefix the same word to `x` and `y`.  Then

```text
A_T(Prefix_R(x),Prefix_R(y)) = H_R A_T(x,y),        (2.3)
```

and the signed `T` stage contribution is zero at every one of the `K`
prepared dates.

In particular, if `q_0=q^kappa` is the full-support Fin4 sprinkler, both
profiles have positive date-zero mass on every coalition, but their signed
difference there is still exactly zero.  Positive incidence of the label is
therefore orthogonal to signed incidence of the edge.

### Theorem 2.2 (the same obstruction holds for a full response square)

Let `x00,x01,x10,x11` be four literal response-square profiles and prefix the
same word `R` to every corner.  For every terminal coalition `T`,

```text
RectAtom_T(Prefix_R(x00),Prefix_R(x01),
           Prefix_R(x10),Prefix_R(x11))
  = H_R RectAtom_T(x00,x01,x10,x11).                (2.4)
```

The rectangle stage atom is zero at every prepared date.

Indeed, at a terminal outcome the common prefix contributes the same
absorbing mass `nu_R(T)` to all four corners, while the suffix contributes
`H_R mu_xab(T)`.  The alternating combination

```text
x11-x10-x01+x00
```

cancels `nu_R(T)` and retains `H_R` times the old rectangle.  At a prepared
stage all four masses are literally equal, so the alternating combination is
zero.

Consequently a strict terminal response-square atom, both positive endpoint
response gains, and a common pure-time response may all survive a sprinkler
while the sprinkled stage carries no signed rectangle at all.

## 3. Exact full-support response-square regression

The preceding statement is not merely a formal cancellation.  Here is a
two-date suffix realizing all the response-square signs used in the live
rectangle construction.

Take Fin4 labels `w,j,p_2,p_3`.  At date zero every player independently Quits
with probability `kappa`, where `0<kappa<1`; this is a common full-support
sprinkler at all four corners.  Conditional on joint survival, `p_2,p_3`
play Never.  The mover `w` has two suffix stopping laws

```text
s : (P[quit at first],P[quit at second])=(2/5,3/5),
t : (P[quit at first],P[quit at second])=(1/10,9/10).
```

The observer `j`'s prescribed suffix law `u` Quits purely at the first date,
and its common response `v` Quits purely at the second date.  Let

```text
x00=(s,u),  x01=(t,u),  x10=(s,v),  x11=(t,v),
```

with the common date-zero root and passive laws understood.  Give `j` reward
`1` only on `T={w,j}` and reward `0` on every other coalition.

Put `C=(1-kappa)^4`.  Conditional on reaching the suffix, the response gain
is

```text
U_j(x10)-U_j(x00)=3/5-2/5=1/5,                    (3.1)
U_j(x11)-U_j(x01)=9/10-1/10=4/5.                  (3.2)
```

Therefore the two actual endpoint response gains are `C/5` and `4C/5`, and
the payoff cross-difference and the `T` rectangle atom are

```text
4C/5-C/5=3C/5>0.                                  (3.3)
```

Nevertheless every date-zero coalition mass is common to all four corners.
The date-zero `T` rectangle is exactly zero.  Inserting an arbitrary number
of common all-Continue dates between the sprinkler and this suffix leaves
(3.1)--(3.3) unchanged and moves every signed response-square stage beyond
any preassigned finite block.

Thus even the following package does not force the sign onto a prepared
sprinkled date:

- full Fin4 product support at that date;
- positive response gain at both mover endpoints;
- one common pure-time observer response; and
- a strict positive payoff cross-difference carried by one fixed terminal
  label.

This is an exact actual-profile quitting construction.  It is not a
terminal-gap table and is not offered as a counterexample to the full Fin4
conjecture.

## 4. Exact half-reset regression with the wrong date-zero sign

Common-prefix cancellation does not cover Euler's literal composition,
because the subsequent half reset may change the mover's date-zero marginal.
The half-law identity still does not repair the sign.

Use Fin4 labels `w,j,p_2,p_3`.  Their independent complete stopping laws are:

```text
j       : P[0]=1/4, P[1]=3/4;
p_2,p_3 : P[0]=1/4, P[Never]=3/4;
w source s : P[0]=1/4, P[1]=3/4;
w endpoint e : P[0]=1/2, P[Never]=1/2.
```

Let `h=(s+e)/2` be the literal complete-stopping-law half mixture.  Thus

```text
h : P[0]=3/8, P[1]=3/8, P[Never]=1/4.              (4.1)
```

It is realized behaviorally by hazards `3/8` at date zero and `3/5` at date
one after survival, so this is exactly the construction implemented by
`quittingStoppingLawMixtureBehaviorStrategy`, not a public correlated coin.

Let the terminal label again be `T={w,j}` and put `r_j(T)=1`, with all other
rewards of `j` zero.  Both the source profile and the half-reset target have
positive date-zero mass on every nonempty Fin4 coalition.  Direct product
calculation gives

```text
StageMass(source,0,T)=9/256=18/512,
StageMass(target,0,T)=27/512,                       (4.2)
```

so the source-minus-target signed contribution at the prepared stage is

```text
-9/512<0.                                          (4.3)
```

At date one,

```text
StageMass(source,1,T)=81/256=162/512,
StageMass(target,1,T)=81/512,                       (4.4)
```

and there is no later `T` mass.  Hence

```text
A_T(source,target)=(-9+81)/512=9/64>0.              (4.5)
```

Thus the exact half-law reset, full date-zero label support, positive mass in
both profiles, and a positive signed terminal atom coexist with the **wrong
strict sign** at date zero.  No response-square inequality involving only
terminal laws can reverse (4.3).

## 5. The sharp missing sign condition

For arbitrary actual profiles `x,y`, fix `T,j` and define the absolutely
summable signed sequence

```text
a_t=(StageMass(x,t,T)-StageMass(y,t,T))*r_j(T).
```

Let

```text
A=sum_t a_t,
P_K=sum_(t<K) a_t,
R_K=sum_(t>=K) a_t.
```

Euler's signed disintegration is the exact identity

```text
A=P_K+R_K.                                         (5.1)
```

### Proposition 5.1 (necessary and sufficient tail budget)

For every `theta>0`,

```text
P_K >= theta   iff   R_K <= A-theta.               (5.2)
```

If `K>0` and these equivalent conditions hold, some prepared date `t<K`
satisfies

```text
a_t >= theta/K.                                    (5.3)
```

For the single sprinkled date `K=1`, a positive lower bound `theta` at date
zero is therefore equivalent to the signed-tail inequality

```text
R_1 <= A-theta.                                    (5.4)
```

The same identities hold with `a_t` replaced by the four-corner rectangle
stage atom.  Unsigned lower bounds on source mass, target mass, mover--recipient
incidence, or total terminal mass do not bound `R_K`: Theorems 2.1--2.2 make
`P_K=0,R_K=A`, while the half-reset regression makes `P_1<0,R_1>A`.

This is the minimal temporal sign datum missing from the sprinkler packet.
It is not currently produced by the hard residual or the response square.
Equation (5.2) is a characterization, not a new finite-tail producer.  After
seeing one fixed positive atom, ordinary convergence does let one choose some
atom-dependent `K` with (say) `P_K>=A/2`; that is exactly Euler's signed
finite-window conclusion.  It gives no bound on `K`, no sign in a block
prepared before the decoder selected `T`, and no uniform one-date floor
because the factor `1/K` in (5.3) may vanish along a sequence.

## 6. Why temporal localization is still not a Bellman consumer

Even (5.2) would only select a positive externality stage.  The checked
common-tail localizers

```text
prescribedSourceEndpointRecipientAtom_localStateMatch
rectangleEndpoint_localStateMatch
```

require the two endpoint profiles to differ by one literal stage-pure update
and hence agree on the entire subsequent tail.  A complete stopping-law half
reset generally changes the mover's hazards at many dates.  The signed
disintegration identity does not turn its selected stage into such a
one-stage hybrid edge.

Accordingly a source-matched executable converter needs both:

1. the tail budget (5.2), or an equivalent theorem selecting a signed
   one-stage hybrid; and
2. preservation of the reset source's punishment floor and exact root-Nash
   property on that hybrid.

The fixed-weight packet, the full-support sprinkler, and the response-square
scalars provide neither second item.  The positive-target marked-row theorem
has a different conditional consumer when the pure-time observer belongs to
a positive-reward collision and its target debt tends to zero; its conclusion
is the already known tail-escape/other-player-defect split, not an exact
punishment-floor Bellman return.

## 7. Exact disposition

This note gives a decisive impossibility theorem for **prefix-only sign
localization**:

- a common finite block has identically zero signed contribution;
- an exact noncommon half-law reset can have the wrong strict prepared-stage
  sign; and
- the necessary-and-sufficient repair is the signed-tail budget (5.2), not
  more full-support mass or more response-square endpoint inequalities.

The last item only identifies the exact missing budget.  It does not produce
that budget at a uniform finite scale.

Therefore adding a response square or a two-date sprinkler block cannot, from
the reviewed fixed-scale packet alone, produce a signed date-zero Bellman
edge or rank decrease.  Any successful continuation must operate at the
decoder-selected later stage and prove common-tail/floor provenance there, or
derive (5.2) from genuinely nonlocal global-minimum information.

No theorem here asserts that the full Fin4 hard residual satisfies the local
regressions.  They refute the proposed converter class, not
`FIN4_BT_QUESTION` itself.  The result is internal and is not an export
candidate without a new executable consumer.

## 8. Declaration and file audit

- `quittingTerminalOutcomeMass_sub_eq_liveMass_mul_spine_sub` and
  `quittingTerminalPayoffDifferenceAtom_eq_liveMass_mul_spineAtom` in
  `Research/Quitting/CausalEndpointAtomLocalStateMatch.lean` give the exact
  common-prefix factorization.
- `prescribedSourceEndpointRecipientAtom_localStateMatch` and
  `rectangleEndpoint_localStateMatch` in the same file identify the stronger
  stage-pure common-tail hypothesis needed by the checked localizer.
- `quittingTerminalPayoffRectangleAtom` and
  `sum_quittingTerminalPayoffRectangleAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`
  fix the rectangle orientation used above.
- `quittingStoppingLawMixtureBehaviorStrategy` in
  `UniformEquilibrium/Quitting/Paths/StoppingLawMixture.lean` and
  `quittingTerminalOutcomeMass_stoppingLawMixture_eq` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`
  justify the literal half-law profile in Section 4.
- `tsum_quittingStageCoalitionMass` and the summability facts used in Euler's
  Proposition 4.1 supply (5.1).
- `exists_markedTailCluster_escape_or_otherNashDefect_of_positiveTargetRectangleStage`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeMarkedRowProvenance.lean`
  is the nearest checked positive-stage consumer and records its extra sign,
  collision, and target-debt hypotheses.

No result in this note is claimed Lean-checked merely because these adjacent
declarations are checked.

## 9. Independent review

Euler independently checked:

1. exact prefix and four-corner factorization, including orientation;
2. the response gains and `3(1-kappa)^4/5` rectangle in Section 3;
3. behavioral realization and every `/512` constant in the half-reset
   regression;
4. absolute summability and equivalence (5.2); and
5. whether an existing source-matched Bellman consumer uses less than the
   stage-pure/floor provenance isolated in Section 6.

The verdict is **PASS** after correcting the two declaration source paths in
Section 8.  The review confirms that (5.2) is only a characterization and
that the theorem decisively closes prefix-only sign localization without
claiming a Bellman producer.
