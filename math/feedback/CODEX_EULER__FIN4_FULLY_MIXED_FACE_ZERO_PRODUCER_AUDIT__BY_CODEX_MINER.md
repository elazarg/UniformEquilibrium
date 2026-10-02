# Independent review of the Fin4 fully mixed face-zero producer audit

**Reviewer:** CODEX_MINER  
**Target:**
[`CODEX_EULER__FIN4_FULLY_MIXED_FACE_ZERO_PRODUCER_AUDIT.md`](../notes/CODEX_EULER__FIN4_FULLY_MIXED_FACE_ZERO_PRODUCER_AUDIT.md)  
**Verdict:** **PASS.**  The fully mixed criterion, polynomial/coefficient
calculation, correspondence with the checked conditional-face-gap compiler,
and the limited nonproduction claim are correct.  The negative conclusion is
an audit of current fields and singleton-data independence, not an
independence theorem for the complete hard residual.

## 1. Necessity and sufficiency of the common zero

For fixed player `i`, `Q_i` is the pure Quit-now endpoint against the three
stationary opponent marginals, `A_i` is the unconditional absorbing part of
pure Continue, and `c_i` is the opponents' all-Continue probability.  Since
all opponent hazards are positive, `c_i<1`, and Never has value

```text
N_i=A_i/(1-c_i).
```

Thus the displayed identity

```text
F_i=(1-c_i)Q_i-A_i=(1-c_i)(Q_i-N_i)
```

has a strictly positive prefactor.

If the stationary profile is exact terminal Nash and `0<p_i<1`, compare its
date-zero mixture with two valid behavioral deviations: Quit now, and
Continue at date zero then resume the prescribed stationary strategy.  Each
pure endpoint is at most the prescribed value, while their mixture with
positive weights `p_i,1-p_i` is exactly that value.  Both endpoint values
must therefore equal the prescribed value.  The Continue endpoint is
`A_i+c_i U_i`, so

```text
U_i=Q_i,
U_i=A_i+c_i U_i,
Q_i=N_i,
F_i=0.
```

This proves necessity without a subgame-perfect assumption; Continue once
and resume is one initial-state unilateral behavioral deviation.

Conversely, a positive common zero is exactly the input of

```text
quittingConditionalFaceGapStationaryCertificateOfFaceNumeratorZero.
```

For a supplied `p in (0,1)^I`, choose for example positive lower coordinates
strictly below `p` and upper coordinates equal to one.  The compiler retains
the supplied hazard, proves the fixed point and exact endpoint Nash, and uses
joint/opponent contraction to obtain unrestricted behavioral terminal Nash
and the uniform-equilibrium payoff.  Theorem 2.1 is therefore an exact
equivalence.

## 2. Polynomial size and nonsingleton coefficient

For Fin4, `c_i,Q_i,A_i` are multilinear in the three opponent coordinates.
The product `(1-c_i)Q_i` has total degree at most six and individual degree at
most two; subtracting `A_i` does not enlarge these bounds.  No `F_i` depends
on `p_i`.

For `T` containing `i`, `r_i(T)` appears only in the `Q_i` summand indexed by
`T\{i}`.  Its coefficient in `F_i` is exactly

```text
(1-c_i(p))
 * product_(j in T\{i}) p_j
 * product_(j in I\T) (1-p_j).
```

At an interior hazard it is strictly positive.  Changing a nonsingleton
coordinate therefore moves `F_i(p)` through either sign without changing
any singleton reward or normalized-solo/LCP field.  On a box with positive
lower hazard bounds, taking `T=I` makes this coefficient uniformly positive,
so a large positive or negative change destroys the appropriate upper- or
lower-face sign uniformly.  This is a valid independence statement for the
singleton/LCP fields only.

## 3. Checked face-gap producer and derangement

The signs in (3.1) match the checked Poincare--Miranda theorem: strict
positive `F_i` on the lower `blocker(i)` face and weak nonpositive `F_i` on
the upper face give a common zero strictly above every lower coordinate and
weakly below every upper coordinate.  If all upper bounds are strictly below
one, the zero is fully mixed even when an upper face binds.  Strict upper
signs are needed only to place it strictly below the upper box.

If `blocker(i)=i`, the two relevant face points may be chosen with identical
opponent coordinates and different `p_i`.  Since `F_i` is independent of
`p_i`, the lower strict-positive and upper nonpositive requirements
contradict each other.  Hence any nonvacuous permutation assignment has no
fixed point; on Fin4 it is a derangement.

The finite range adapter has the stated content.  Its first two interval
families bound `i`'s Quit payoff without/with its blocker, while the third
bounds every nonempty Continue outcome.  The strict lower mixture inequality
and weak upper mixture inequality imply exactly the two face signs by
Bernoulli averaging.  Its checked assumption
`0<lower(blocker(i))`, together with permutation surjectivity, is equivalent
to positivity of every lower coordinate.

## 4. Current-source audit and exact scope

The normalized singleton matrix, its `ResidualHardClass` predicates, normal
core, and the packet's mixture/pinning data do not control the nonsingleton
coefficients above.  The complete hard residual additionally carries a
terminal witness, punishment-normal inequalities, and existentially selected
semantic sources.  The one-coordinate perturbation need not preserve those
extra fields, and the note explicitly does not claim that it does.  Therefore
the correct conclusion is:

```text
current named singleton/LCP fields do not produce a common zero or face box;
no checked joint implication from the complete hard residual is known.
```

It is not a theorem that such a joint implication is impossible.

The pair-base constrained Nash point supplies signs only at its selected
boundary root.  The checked lemmas have the stated orientations: a
nonsaturated coordinate gives `F_i<=0`, and a coordinate strictly above its
lower constraint gives `F_i>=0`.  They do not extend those signs to every
point on eight faces of one common box, and prescribed-owner constructions
may reselect different points and laws.

Finally, the minimum-fiber all-Continue tube is a tail-payoff exclusion.  A
fully mixed common zero uses its endogenous fixed-point value, which has not
been source-matched to that tube.  If it were in the tube, unique exact
all-Continue would exclude the positive root immediately; absent that
alignment, the tube neither produces nor refutes a common zero elsewhere.

The note's resulting obligation is therefore precise and appropriately
conditional.  Failure of the coarse range screen does not imply absence of a
zero, as the independently reviewed Gray contraction certificate illustrates.

