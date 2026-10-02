# Review of the cross-face and collision-tangent packet

Reviewer: `CODEX_CEDAR`

Reviewed note:
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md)

Scope: current Section 58, Propositions 56--60, with priority on the raw-gap
coercivity in Proposition 58, the universal forced-Quit expansion in
Proposition 59, and the probability-weighted correction in Proposition 60.
I refreshed the board and reread the current corrected version after the
earlier `eta<=epsilon` interpretation had been removed.  This is an independent
ordinary-mathematics falsification audit; it gives no Lean or export claim.

## Verdict

**Propositions 56--60 are VALID ordinary mathematics in their current stated
scope.**  I found no sign, orientation, remainder, endpoint-weighting, or
quantifier error.  In particular, Proposition 58 is only a raw-gap theorem;
Proposition 60 correctly weakens its semantic consequence to the one-sided
active collision-tangent inequality.

## 1. Cross-face normalization and semantic separation

For `(N2)`, direct multiplication gives

```text
M z=(1,0,1,0),       qbar+M z=0,
sum_i z_i=2.
```

Hence the projective packet is exactly

```text
c=1/3,    a=(1/9,2/9,1/9,2/9).
```

Matching singleton-to-cemetery odds forces
`p=(1/4,2/5,1/4,2/5)`, whose continuation, singleton, and collision masses are
respectively `81/400`, `162/400`, and `157/400`.  Thus the packet is not one
product row.  The support mismatch in Proposition 56(1) is also literal: a
cross-face solution has positive mass outside the actual zero-gap face, while
`NonnegativeBoundaryDirection.supported_on_zero` forbids it for a continuous
germ at that boundary.

For the collision-free schedule, deleting the first singleton term from the
whole-packet equality gives

```text
V_start(second)_j-s_j
  =a_first*(s_j-R_first_j)/(1-a_first).
```

Since positive mixing by the second owner requires its row-start value to be
`s_j`, every nonzero off-diagonal normalized singleton entry obstructs every
ordering.  This validates the three failures claimed in Proposition 56 and
does not exclude recurrent, collision-using blocks.

## 2. Exact alternating-pair separation

The four equations `(N12)` and inactive inequalities `(N13)` have the stated
orientation.  For a maximal hazard `T`, the inactive inequality gives

```text
1/(1-T)<=4-2T,
```

and the corresponding Bellman equation then gives
`T/(1-T)<2D`, while inactivity gives `T/(1-T)<=2(1-D)`.  Therefore `T<1/2`.

Subtracting paired equations gives `(N18)`.  On `(0,1/2)`,

```text
-1<1/(1-t)^2-2e<4,
```

so equal signs and opposite signs of the two differences both give the two
strict reciprocal inequalities claimed; zero in one difference forces zero
in the other.  After `a=b=r,u=v=s`, I independently expanded

```text
P(r,s)-P(s,r)=3(r-s)(2r+2s-2rs-1).
```

The diagonal case reduces to `1=2r^2(1-r)`, and on the other factor the
substitution `s=(1-2r)/(2(1-r))` gives exactly

```text
[2(1-r)]^2 P(r,s)=6r(1-r)(1-2r)>0.
```

Thus Proposition 57 excludes precisely the stated interior two-phase support,
not boundary, longer, or vanishing approximate blocks.

## 3. Proposition 58 constants

Raw activity at one row gives the tail error at most `2 eta`; mixing that row
and adding Bellman defect gives the current-value error at most
`beta+eta`.  Substitution in a nonactive Bellman equation costs

```text
beta + 2 eta + c*(beta+eta) <= 2 beta+3 eta,
```

so `(N28)` is correct.

With variables ordered `(u,v,a,b)`, the linearization is

```text
[[ 3,-1, 0,-1],
 [-1, 3,-1, 0],
 [ 0,-1, 3,-1],
 [-1, 0,-1, 3]],
```

namely `3I-adj(C4)`, with eigenvalues `1,3,3,5`.  Therefore
`||Lh||_2>=||h||_2>=A`.  Each coordinate remainder is bounded by

```text
2A^2+4A^2+4A^2=10A^2,
```

so the four-coordinate Euclidean remainder is at most `20A^2`.  At
`A<=1/40`, `||F||_2>=A/2`, hence `max |F_k|>=A/4`.  This yields
`2 beta+3 eta>=A/4` and then `max(beta,eta)>=A/20` exactly.

## 4. Propositions 59--60 and the semantic correction

For forced Quit by active `i`, the exact-one-opponent mass differs from
`alpha lambda_j` by total weighted mass at most `alpha^2`.  Since the row
difference from solo is bounded by `2M`, this costs `2M alpha^2`.  At least two
opponents Quit with probability at most `alpha^2/2`; its row difference from
solo costs at most another `M alpha^2`.  Thus

```text
|Quit_i-s_i-alpha C_i(lambda)|<=3M alpha^2
```

with the advertised constant.  Under raw activity,
`Quit_i-T_i=(1-p_i)(Quit_i-Continue_i)`, pinning and Bellman error give
`|Quit_i-s_i|<=eta+beta`, proving `(N37)`.  The conclusion `(N38)` is valid
for the fixed direction `lambda` quantified in Proposition 59; for varying
directions only the corresponding cluster-direction conclusion would follow.

For semantic endpoint Nash, the two inequalities really are

```text
(1-p_i)D_i<=epsilon,       p_i D_i>=-epsilon.
```

The first yields `(N44)`.  Multiplying the identity by `p_i` before using the
second gives exactly the factors in `(N45)`.  Dividing by `alpha` yields only
`C_i<=0` under `epsilon+beta=o(alpha)`.  Equality needs
`epsilon=o(alpha^2)` and `beta=o(alpha)` for each fixed positive
`lambda_i`, as stated.  The example `D_i=-kappa alpha` confirms sharpness:
the raw gap is first order while Continue regret is only order `alpha^2`.

## 5. Conjecture-facing scope

The checked pair-join residual and signed-pivot declarations named in the note
overlap the algebraic tangent, but they do not supply the missing strategy
producer.  The surviving obligation is exactly the corrected one: dispatch a
positive supported collision tangent, exploit or recurrently absorb negative
tangents, or retain a nonvanishing compact product block.  Nothing in
Propositions 56--60 proves `SCB`, a returned block, or the full conjecture.
