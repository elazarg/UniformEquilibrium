# Positive limiting roots enter the normalized-passport return/inert split

## Status

Ordinary mathematics, not checked in Lean and not independently reviewed.

The `PositiveLimitRoot` atlas node is not separate.  The strict maximal ray
and its retained forced-pair source produce an actual decorated family to
which the existing normalized-passport closure and minimization apply.  A
positive-absorption exact root at the limiting cap acts on the same decorated
limit, remains in the normalized slice, and strictly lowers its whole debt.
The slice minimizer therefore yields exactly the existing equality-return or
strict normalized-inert alternative.

The actual-data adapter is literal.  Its target is the canonical maximal word
followed by the source pure pair.  Its comparison profile is the same maximal
word followed by the preceding pure singleton.  Both use the same actual
near-minimum reference tail.  Arbitrary-prefix actualization later puts the
same additional root word on both profiles.

In fact the positive limiting root is only needed to show that the ray cluster
itself is not the normalized minimizer.  Strictness of the ray already gives
the positive limiting mass and gain needed to invoke normalized minimization.
Thus every strict maximal ray has a source-faithful transition to the
return/inert split; `PositiveLimitRoot`, `CardThreeRay`, and `FullBindingRay`
remain useful geometric refinements but need not be terminal completion nodes.

## 1. Input data

Fix one

```text
packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
```

over a positive global minimum source.  Write

* `j` for `returnSource.producer.owner`;
* `o` for `returnSource.forcedOwner`;
* `C={j,o}` for `packet.rayTerminal`;
* `z_0=packet.raySource` for the semantic pure-pair source;
* `tau_n=packet.rayTail n` for the retained reference tails;
* `q_0,...,q_(n-1)` for the canonical maximum-absorption exact-cap roots;
* `S_n` for their joint Continue product;
* `z_n` for the resulting semantic ray; and
* `L=lim D(z_n)` for the strict ray limit.

The strict branch has

$$
D_*<L\le D(z_0),
\tag{1}
$$

and the exact debt scaling identity gives

$$
D(z_n)=S_nD(z_0).
\tag{2}
$$

Consequently

$$
S_n\longrightarrow S_\infty:=\frac{L}{D(z_0)}>0.
\tag{3}
$$

The reference tails satisfy

$$
D(\operatorname{Sem}(\tau_n))\longrightarrow D_*.
\tag{4}
$$

Finally, the hard terminal witness and the forced-pair construction give the
fixed table gap

$$
\Gamma:=r_o(\{j,o\})-r_o(\{j\})
\ge\gamma>0.
\tag{5}
$$

## 2. Literal ray decoration

Define the date-zero comparison and target bases

$$
A_n:=\{j\}\triangleright\tau_n,
\qquad
B_n:=\{j,o\}\triangleright\tau_n.
\tag{6}
$$

Here the notation means a pure coalition root followed counterfactually by the
displayed literal tail.  Thus `B_n` is exactly `packet.rayBaseProfile n`.

Put the same canonical maximal prefix word on both:

$$
\widehat A_n=(q_0*\cdots*q_{n-1})*A_n,
\qquad
\widehat B_n=(q_0*\cdots*q_{n-1})*B_n.
\tag{7}
$$

The target `widehat B_n` is exactly `packet.rayFamily.rayProfiles n`.  Define a
decorated family by

```text
sourceProfile n := widehat A_n
profile       n := widehat B_n
mark          n := n
terminal        := {j,o}
markedOwner     := o
gainMover       := o
```

Every field is actual.

### Marked mass

The target base absorbs as `C` with probability one at its marked root.  The
outer word reaches it with probability `S_n`.  Hence

$$
\operatorname{MarkedMass}_n=S_n>0.
\tag{8}
$$

### Actual gain

The two bases differ only in player `o`'s action at the marked row.  Their
conditional payoff difference is the fixed gap `Gamma`.  Common prefix
absorption cancels, so

$$
U_o(\widehat B_n)-U_o(\widehat A_n)=S_n\Gamma>0.
\tag{9}
$$

This is a literal terminal-payoff difference, not a scalar annotation.

### Zero marked-owner defect

At the pair row, player `j` Quits surely and (5) makes Quit the exact best
endpoint for `o`.  The checked forced-owner identity gives

$$
\operatorname{Defect}_o(\tau_n,\{j,o\})=0.
\tag{10}
$$

The common outer word only shifts the marked date, so (10) remains the
decorated family's marked-owner field.

### Tail

Taking the all-Continue spine through the outer word and the marked root gives
literally

$$
\operatorname{Tail}_{n+1}(\widehat B_n)=\tau_n.
\tag{11}
$$

Thus the family retains the same actual near-minimum tails as the forced-pair
packet.

## 3. Convergent passport

The canonical decorated ambient is compact.  Pass to one subsequence on which
the complete base decorations converge to a point `P`.  This single selection
includes:

* the whole semantic pair and terminal law of `widehat B_n`;
* the complete tail semantic pair and law of `tau_n`;
* the marked mass; and
* the actual gain.

Equations (1)--(4), (8), and (9) give

$$
P.\operatorname{wholeDebt}=L>0,
\tag{12}
$$

$$
P.\operatorname{tailDebt}=D_*,
\tag{13}
$$

$$
P.\operatorname{markedMass}=S_\infty>0,
\tag{14}

$$
P.\operatorname{actualGain}=S_\infty\Gamma>0.
\tag{15}
$$

Therefore `P` is precisely a

```text
QuittingMarkedPairDecoratedFamily.ConvergentPassport family minimum
```

derived from the actual strict-ray source.

Choose the standard half densities

$$
m=\frac{P.\operatorname{markedMass}}
        {2P.\operatorname{wholeDebt}},
\qquad
g=\frac{P.\operatorname{actualGain}}
        {2P.\operatorname{wholeDebt}}.
\tag{16}
$$

Both are positive, and `P` satisfies the normalized inequalities strictly.

## 4. The positive limiting root acts on this same passport

Now suppose the `PositiveLimitRoot` node supplies a product root `r` with

$$
\operatorname{Abs}(r)>0
\tag{17}
$$

which is exact cap--Nash against the limiting cap of the semantic ray.

The whole semantic coordinate of `P` is a cluster point of `z_n`.  The cap
sequence has the specified limiting cap, so `r` is exact against
`P.whole.1.2`.  Since `P` belongs to the closed arbitrary-prefix orbit,
the checked prefix-closure theorem gives

$$
r*P\in\operatorname{NormalizedSlice}(m,g).
\tag{18}
$$

All four claims in (18) are exact:

* `r*P` is in the closed orbit because it is the limit of the actual profiles
  obtained by prefixing `r` to the selected `widehat B_n` and `widehat A_n`;
* its post-mark tail is still the same tail coordinate;
* its marked mass and actual gain are both multiplied by the same joint
  Continue probability; and
* exact cap--Nash prefixing multiplies whole debt by that same probability.

Writing `c(r)=1-Abs(r)`, equations (17)--(18) give

$$
(r*P).\operatorname{wholeDebt}
=c(r)L<L.
\tag{19}
$$

Thus the positive limiting root does not merely lower an unrelated semantic
point: it strictly lowers the same source-attached normalized passport.

## 5. Existing minimization gives the complete outgoing split

Let `Q` minimize whole debt on this nonempty normalized slice.  Since `r*P` is
admissible,

$$
D_*\le Q.\operatorname{wholeDebt}
\le c(r)L<L.
\tag{20}
$$

Apply

```text
exists_minimum_normalizedPassportSlice_eq_or_strict_inert
```

to the actual family and passport above.  Exactly one of the existing outputs
results.

### Equality arm

If

$$
Q.\operatorname{wholeDebt}=D_*,
$$

the checked minimum-return actualizer constructs actual profiles of the form

$$
(w_k*q_0*\cdots*q_{n_k-1})*B_{n_k},
\tag{21}
$$

and comparison profiles with the exact same additional word `w_k` and the
same maximal word on `A_(n_k)`.  It retains:

* the original minimum source and forced-pair packet;
* the literal pair and forced-owner label;
* the actual near-minimum tail;
* positive marked mass and actual payoff gain; and
* zero marked-owner defect.

Since the terminal has cardinality two, the existing endpoint-law consumer
gives the same three-role regeneration/ascent output used by the maintained
normalized-return branch.  No carrier point is substituted for an actual
profile.

### Strict arm

If

$$
D_*<Q.\operatorname{wholeDebt},
$$

the checked normalized minimizer theorem says

$$
\operatorname{Nash}(Q.\operatorname{wholeCap})
=\{\mathbf C\}.
\tag{22}
$$

Together with its actual family, passport densities, minimum tail, marked
pair, mass, gain, and owner-defect fields, this is precisely the existing
strict normalized-inert node.

Therefore

$$
\boxed{
\textsf{PositiveLimitRoot}
\longrightarrow
\textsf{ThreeRoleReturn/Ascent}
\quad\lor\quad
\textsf{NormalizedInert}.}
\tag{23}
$$

## 6. Stronger consequence: the root is not needed for the transition

The positive root proves the useful strict comparison (19), but the passport
itself used only the strict ray facts `L>D_*` and `S_infinity>0`.  Hence the
same normalized minimization can be applied before classifying the limiting
root or binding set:

$$
\boxed{
\textsf{StrictRay}
\longrightarrow
\textsf{ThreeRoleReturn/Ascent}
\quad\lor\quad
\textsf{NormalizedInert}.}
\tag{24}
$$

The positive-root, card-three, and full-binding classifications remain valid
geometric information, especially for attacking the strict inert output, but
they are not separate unconsumed exits of the completion graph once this
source adapter is installed.

This does not solve the conjecture: the normalized-inert output is still an
open terminal node, and the equality output can regenerate without preserving
the paid orientation.  It does remove the new positive-root node as an
independent obstruction.

## 7. Lean-facing adapter

A direct formalization can introduce:

```text
FinFourStrictRayNormalizedDecoratedFamily
FinFourStrictRayNormalizedOrigin
FinFourStrictRayNormalizedReturnOrInert
```

with source/target profiles defined by (6)--(7).  The proof should reuse:

* `quittingTerminalPayoff_sub_rootThenContinuation` for (9);
* the maximal-prefix survival and debt-limit theorems for (3), (8), and (12);
* `rayBaseProfile_ownerDefect_eq_zero` for (10);
* `rayProfiles_postMarkSpine_eq_reference` for (11);
* the existing compact subsequence construction used by
  `FinFourCanonicalPaidEndpointOrigin`;
* `prefixMap_mem_normalizedPassportSlice_of_isZeroNash` for (18); and
* `nonempty_quittingMarkedPairMinimumReturnActualizer` plus the existing
  nonsingleton endpoint-law consumer in the equality arm.

The structure must store the incoming strict-ray object and the subsequence
equations, so that the equality actualizer is visibly a literal extra root word
on the same canonical ray, not an independently selected family.

## Files inspected

* `Research/Quitting/NormalizedPassportPrefixOrbit.lean`
* `Research/Quitting/NormalizedPassportMinimizer.lean`
* `Research/Quitting/NormalizedPassportMinimumReturn.lean`
* `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`
* `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`
* `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean`
* `Research/Quitting/FinFourProducerAtlas/StrictEndpointNormalizedReturn.lean`
* `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`
* `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`

## Remaining check before export

The construction should be independently audited for the exact comparison
profile at (6) and for the identification of the compact whole-cap limit with
the cap supplied by `PositiveLimitRoot`.  Those are the only non-generic
source equations; the normalized closure and minimization are already checked.
