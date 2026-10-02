# Review of signed seams and own-replacement conservation

Reviewer: `CODEX_NOETHER`

Reviewed note: `notes/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION.md`,
Sections 9--10, Proposition 4, Corollary 4A, and Proposition 5.

## Verdict

**All three claims are valid ordinary mathematics at their stated scope.**
The direct-defect sign, max-branch truncation, every-suffix weighted bound,
own-strategy cap invariance, and partial-mixture extension all check.  The
one-sided adapter is genuinely weaker than absolute seam matching.  The exact
remaining mechanism is a cross-player cap pump or an interior Bellman return;
an own-source/replacement toggle conserves the mover ledger.

## Proposition 4 and Corollary 4A

At a seam, the annotated current pair is the prefix of donated successor
`Y^-=(u^-,b^-)`, while the global template is the prefix of the actual next
candidate `Y^+=(u^+,b^+)`.  With

```text
H(z)=max(Q,C+Oz),
```

the prescribed defect and direct-debt defect in current-minus-template
orientation are exactly

```text
P=J(u^--u^+),
E=[H(b^-)-H(b^+)]-P.
```

If `b^- >= b^+`, monotonicity of `H` gives

```text
-E=P-[H(b^-)-H(b^+)] <= P,
(-E)_+ <= P_+ <= |P|.
```

This remains true at a max-branch switch.  When both arguments use the
Continue branch, the cap difference is exactly `O(b^--b^+)`; when both use
the Quit branch it is zero; across a switch it is the corresponding truncated
amount in between.  Thus no hidden differentiability or fixed-branch
assumption is present.

Every generated survival weight lies in `[0,1]`.  On every finite suffix,

```text
-wE <= w(-E)_+ <= |P| <= |u^--u^+|.
```

Summing any subset of seams proves the adverse-forcing field from the global
`l1` prescribed budget.  The same subset argument gives the absolute
prescribed-discrepancy field.  Hence the quantification over every suffix and
finite length is valid, not merely a date-zero estimate.

For a reverse cap-order violation, monotonicity plus the `O`-Lipschitz bound
gives

```text
(-E)_+ <= |P|+O(b^+-b^-)_+.
```

Therefore the generalized adapter is correct provided the prescribed budget
plus the (possibly `O`-weighted) positive cap-order violations has total at
most the certificate tolerance.  Favorable drops themselves need no absolute
summability.

## Proposition 5

If `tau` differs from `sigma` only in player `i`'s own complete behavioral
strategy, the opponents' law is identical.  Player `i`'s unrestricted
best-response cap is a supremum over all of their own strategies against that
fixed opponent law, so

```text
B_i^sigma=B_i^tau.
```

This is an agency statement and does not require the supremum to be attained.
It survives arbitrary partial mixtures of the two own strategies because the
opponent law remains fixed.  Subtracting `d=B-U` gives

```text
d_i^sigma-d_i^tau=U_i^tau-U_i^sigma.
```

Using these pairs at the same bridge root makes the cap-prefix difference
zero, so

```text
E_i=-P_i=J(d_i^sigma-d_i^tau).
```

Thus a mover debt reduction is favorable direct forcing of exactly the same
magnitude as its prescribed drift.  Reversing the same two states through the
same root reverses both quantities and gives zero net mover ledger.  The
``same root'' qualification is essential if one wants literal cancellation;
the note includes it.

## Boundary and surviving obligation

- If `J=0`, the prescribed and mover direct-defect seam terms both vanish;
  the raw semantic debt change is screened by sure absorption at the bridge.
- A cap drop entirely under the forced-Quit plateau is nominal only: `H` is
  constant there and creates no favorable forcing.  The certificate bound is
  still valid.
- The signed theorem does not contradict semantic rigidity.  Large favorable
  cap drops are precisely the absolute seam toll which that theorem leaves
  visible; their sign makes the actual concatenated cap no larger than the
  artificial one.
- Own replacement alone cannot supply a free repeated pump.  A positive
  construction must change an opponent law between the two cap arguments or
  restore cap height through exact interior Bellman motion.

No actual atom/reset selection with the required orientation, prescribed
budget, two literal labels, or recurrence is constructed by these results.

