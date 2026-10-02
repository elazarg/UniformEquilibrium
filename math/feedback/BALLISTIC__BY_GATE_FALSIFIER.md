# Adversarial gate review of `BALLISTIC.md`

Reviewer: `CODEX_GATE_FALSIFIER`

## Verdict

**FAIL for export, but retain as a useful algebraic note.**

The weighted cocycle telescope is a sound and genuinely useful finite-
dimensional compression after two small repairs:

1. the alternatives are not exclusive, so “exactly one” must be replaced by
   “at least one”; and
2. failure of the boundary subsequence only gives an eventual uniform
   interior bound, not a bound at every finite index.  The proof must discard a
   finite prefix and take all blocks in the remaining tail.

With those changes, the theorem proves that every uniformly interior
normalized ballistic chain forces an interior fixed state of the *ambient
normalized relation*.  It does not produce an actual continuation cap,
product root, payoff, law, returned block, rank decrease, or terminal consumer.
It therefore falls exactly under the live strict-inert question's stated
nonanswer: “another ... ballistic ... split without consumers for every
output.”  The packet does not strictly close or narrow an accepted output of
that question.

## Exact claim audited

For finite `I`, fixed matrices `M,J`, and a sequence

```text
(lambda_n, Lambda_n, rho_n) in Delta(I) x Delta(I) x [eta,1]
```

satisfying

```text
Lambda_n = rho_n lambda_n + (1-rho_n) Lambda_{n+1},
W_n = M Lambda_n + rho_n J lambda_n <= 0,
lambda_{n,i} W_{n,i} = 0,
```

the intended conclusion is:

```text
(some current coordinate tends to zero along a subsequence)
or
(there exist r in [eta,1] and y in the interior simplex with
 (M+rJ)y=0).
```

This inclusive disjunction is correct.  The stronger phrase “exactly one” is
false.

## 1. Exact counterexample to exclusivity

Let `I={0,1}`, `M=J=0`, `eta=1`, and

```text
rho_n = 1,
lambda_n = Lambda_n = (1 - 1/(n+2), 1/(n+2)).
```

The renewal and complementarity equations hold identically.  Coordinate 1
tends to zero, so the boundary output holds.  But the fixed-state output also
holds: take `r=1` and any interior simplex point `y`, since `(M+rJ)y=0`.

Thus the theorem must say “at least one” or “if the boundary output fails,
then the fixed-state output.”  No natural uniqueness of the reduction is
available from the stated equations.

## 2. Finite-prefix gap in the proof

The proof says that failure of the boundary alternative gives

```text
lambda_{n,i} >= delta for every n and i.
```

This is not valid.  A coordinate may equal zero at one early index and equal
`1/2` at every later index.  There is then no strictly increasing subsequence
along which it tends to zero, but no positive lower bound valid at every
index.

The repair is straightforward.  For each coordinate, failure of a subsequence
tending to zero implies positive `liminf`.  Since `I` is finite, there are
`N` and `delta>0` such that

```text
lambda_{n,i} >= delta for every n>=N and every i.
```

Shift the chain to date `N`.  Any occurrence of `rho_n=1` and every recurrence
block used in the proof must then be chosen at dates at least `N`.

This repair is necessary also for the `rho_n=1` shortcut: an early state with
`rho_n=1` need not have interior `lambda_n`, whereas a tail occurrence does.

## 3. Audit of the weighted telescope

After the finite-prefix repair, the central calculation is correct.

Let `g_n=1-rho_n`, assume `g_n>0` on the selected block `[a,b)`, let

```text
q = (product_{a<=n<b} g_n)^(1/(b-a)),
r = 1-q,
alpha_a=1,
alpha_{n+1}=alpha_n g_n/q.
```

Then `alpha_b=1`.  With

```text
A = sum alpha_n Lambda_n,
B = sum alpha_n rho_n lambda_n,
Z = sum alpha_n,
```

renewal gives exactly

```text
B = r A + q(Lambda_a-Lambda_b),
```

and weighted work gives

```text
M A + J B = 0.
```

Consequently, for

```text
y = A/Z,
e = q(Lambda_a-Lambda_b)/Z,
```

one has

```text
(M+rJ)y = -J e.
```

The bounds are also correct:

- `eta <= r < 1`, because every `g_n <= 1-eta`;
- `y` is a simplex point;
- eventual `lambda_{n,i}>=delta` and renewal imply
  `Lambda_{n,i}>=eta*delta`, hence the same lower bound for `y_i`; and
- `||e|| <= ||Lambda_a-Lambda_b||`, since `Z>=1` and `q<=1`.

Compactness of the simplex gives arbitrarily close pairs in every tail.  The
proof should choose `a_k>=k` and `b_k>a_k`; this both repairs provenance and
shows that the limiting `y` lies in the asymptotic closed convex hull

```text
intersection_N closure(conv{Lambda_n : n>=N}).
```

Taking a convergent subsequence of the geometric means and weighted averages
then yields

```text
r in [eta,1],
y_i >= eta*delta > 0,
(M+rJ)y=0.
```

No interchange of an infinite sum with a limit is used.  Every telescope is
finite, and only finite-dimensional continuity is needed.

## 4. Strongest corrected theorem

The strongest rigorously supported statement is:

> Let `I` be finite and let the normalized ballistic equations hold with a
> fixed positive renewal-ratio floor `eta`.  Then either some current-hazard
> coordinate tends to zero along a subsequence, or there exist
> `r in [eta,1]` and an interior simplex point `y` in the asymptotic closed
> convex hull of the tail-average sequence such that `(M+rJ)y=0`.

The positive lower bound on `rho_n` is used essentially to keep the produced
`r` away from zero and to transfer eventual interiority of `lambda_n` to
`Lambda_n`.

This theorem is dimension-free and is stronger than merely extracting an
invariant occupation measure: it produces one scalar `r` multiplying the same
vector `y` in both matrix terms.

## 5. Source and provenance audit

The project does possess an actual-source adapter into the normalized input:

- `FinFourUniformlyBallisticNormalizedSource` in
  `Research/Quitting/FinFourProducerAtlas/BallisticNormalizedOmegaChain.lean`
  retains one actual strict ray, cutoff, full binding, and a positive renewal
  floor;
- `FinFourBallisticNormalizedOmegaChain` retains common finite-window source
  provenance; and
- `IsBallisticEdge` has exactly the renewal, work inequality, and
  complementarity equations used in the note, with the fixed normalized solo
  and collision matrices.

Applying the corrected theorem to the nonnegative half of such an omega chain
is legitimate.  Cofinal block selection retains the statement that `y` is an
asymptotic convex-block limit of tail-average states from that one source.

The output, however, is not itself source-realized:

- `y` is a limit of weighted block averages, not necessarily a coordinate
  limit of the selected chain;
- `r` is a limit of block geometric means, not necessarily a source renewal
  ratio;
- no actual absolute hazard vector is reconstructed;
- no terminal payoff or unrestricted behavioral cap is reconstructed;
- no actual product root is proved Nash against one continuation cap;
- no terminal law, marked atom, paid row, or reset provenance reaches the
  fixed state; and
- no finite chronological block returns to it.

The theorem is therefore a valid theorem about the ambient normalized
relation, not an actual-data output node of the Fin4 atlas.

The already checked `BallisticNormalizedOccupation.lean` constructs a
balanced occupation law supported on the same exact normalized relation.  The
new weighted telescope is not a duplicate of that statement: its useful new
content is the common-vector equation `(M+rJ)y=0`.  But it still has no
semantic consumer.

## 6. All-behavior and consumer audit

No hidden finite-horizon or stationary cap substitution appears in the
algebraic proof: caps are absent from its statement.  The source omega chain
was derived from exact cap-root data, but the output fixed state does not
inherit those unrestricted-cap semantics.  It must not be described as an
exact root, stationary profile, or Nash--Bellman state.

The document correctly observes that the hard residual excludes `My=0`, while
the theorem gives only

```text
My = -r Jy.
```

No sign, cancellation, or source theorem removes `Jy`.  Thus there is no
contradiction with the hard residual.

Likewise:

- the boundary output is only an asymptotically vanishing normalized current
  coordinate, not a regenerated minimum source or strict support-rank drop;
- the fixed-state output has no chronological return or UE compiler;
- neither output is a terminal atlas node; and
- no exhaustive downstream dispatch is supplied.

The sentence that the aperiodic selected dynamics “cease to be terminal data”
is too strong.  The selected orbit may still be essential for any
source-faithful absolute lift.  What ceases to be necessary is only recurrence
analysis for proving existence of an ambient normalized algebraic loop.

## 7. Export-gate assessment

The named live question
`questions/FIN4_STRICT_NORMALIZED_INERT_IMPOSSIBILITY_OR_MODEL.md` explicitly
lists as a nonanswer:

> another binding-cardinality, flow, ballistic, parity, or complementarity
> split without consumers for every output.

This packet supplies exactly such a ballistic reduction.  It does not prove
incompatibility, UE, a charged return, a renewable finite-rank descent, or a
positive-gap table.  Its source hypothesis remains the already open ballistic
branch, and neither output has a consumer.

Therefore it does not qualify under `exports/README.md`, even after the two
proof repairs.  Preserve the corrected theorem in `notes/` and formalize it
only if the project decides that the normalized algebraic interface itself is
worth maintaining.  Export becomes appropriate only after adding either:

1. a source-faithful absolute lift from `(M+rJ)y=0` to an actual returned
   Nash--Bellman block or another established consumer; or
2. a proof from the hard Fin4 collision geometry that every such interior
   fixed state is impossible, together with a consumed boundary branch.
