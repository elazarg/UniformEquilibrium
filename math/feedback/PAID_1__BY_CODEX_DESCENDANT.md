# Independent audit of `gpt/PAID_1.md`

Reviewer: `CODEX_DESCENDANT`

## Verdict

**REVISE.**  The central local obstruction is mathematically sound after one
correction: the raw softened roots retain a fixed root-Nash defect, whereas
every exact root in the relevant minimum tube is all Continue and has zero
absorption.  The literal last-root restart also retains a fixed defect.  This
is useful negative information about the proposed product-base path.

It is not a “no-consumer theorem” from the supplied hypotheses.  It excludes
the raw softened roots, local exactification, and the displayed naive restart;
it does not exclude a nonlocal consumer using the complete source, nor supply
one of the five requested outputs or the requested positive-gap table.  The
result should be recorded as a **local mechanism no-go**, not as an answer to
the question.

## 1. Closed homotopy and the exact-root tube

The calculation

```text
U_i-s_i >= D_*-d_i = sum_{j != i} d_j > 0
```

is correct under full positive debt.  The same strict lower bound persists on
the debt homotopy from `B` to `U`.

For `t<1`, the checked auxiliary-target budget gives

```text
(1-t) D_* Abs(root) <= D(z)-D_* = 0,
```

so every exact root is all Continue.  At `t=1`, the note misstates the
minimum-simplex equality alternative.  A nontrivial root requires a debt gate
with

```text
d_i(z) = D_*,
U_i = s_i,
```

and hence every other debt coordinate zero.  It does **not** require
`d_i(z)=0`.  Full debt and the already proved strict inequalities nevertheless
exclude the gate, so the unique-all-Continue conclusion on the closed segment
survives unchanged.

The open-tube and linear estimate

```text
Def(v,x) >= c_T Abs(x)
```

are valid.  Near all Continue, the uniform singleton gap gives the linear
bound; away from all Continue, compactness and the absence of exact roots give
a positive defect minimum.  This is also already represented by the checked
strict-all-Continue basin/linear-absorption-defect infrastructure, so it is
not a new consumer.

## 2. Cap-leakage ledger

For a unilateral replacement by mover `p`, the mover's unrestricted cap is
unchanged because its opponents are unchanged.  Hence

```text
d'_p-d_p = -g,
L = g + E'-E,
sum L = sum g + E_final
```

along a path starting on the minimum fibre.  These identities correctly retain
all spectator cap changes.  They show that paid gain can be balanced by
spectator debt creation.  They do not prove that this stored exploitability
cannot later be consumed by another source-attached construction.

## 3. Affine first exit

The affine classification is valid only because the question explicitly
supplies one fixed endpoint-polynomial cell.  Along one coordinate softening,
the prescribed payoff and selected caps are affine, so

```text
g(t)=beta*t,
D(t)=D_*+lambda*t,
```

with `beta>0` and `lambda>=0`.  If `lambda=0`, the short edge stays on the
minimum fibre; if `lambda>0`, every positive point is off minimum and the
excess/gain ratio is constant.  Continuity puts sufficiently short endpoints'
`U(t)` and `B(t)` inside the exact-root tube, so both local exact roots are all
Continue.  This is a correct inert-port description, not a chronological
return.

## 4. Uniform defect of the raw singleton path

At the original product root, a sure quitter `p` with another sure-quitting
opponent has

```text
ContinueValue_p - QuitValue_p = d_p(z)>0.
```

For all sufficiently small simultaneous softening parameters this comparison
stays at least `min_{p in K} d_p(z)/2`.  A softened player still Quits with
probability at least `1/2`, so replacing its root action by pure Continue gains
at least

```text
min_{p in K} d_p(z)/4.
```

This proves the fixed root-defect floor throughout the post-first-softening
path while another original sure quitter remains, including the terminal
one-sure-quitter root.  The singleton-mass formula is also correct.

For the displayed restart, soften the last sure quitter and resume the literal
minimum source on all Continue.  Holding one earlier softened player `p`
fixed, its endpoint comparison converges to the comparison with the last
quitter sure.  Thus the restart still has a fixed positive deviation gain.
This is a genuine source-faithful no-go for that particular restart and covers
unrestricted behavioral deviations because the pure root action is itself an
allowed complete response.

The note should avoid calling raw absorption “admissible charge”: the raw root
is uniformly defective.  Its absorption is physical root absorption only.
The text mostly respects this distinction, but the headline table and final
summary should state it explicitly.

## 5. Exact consequence and novelty

What is established is:

```text
local paid softening path
  -> positive physical absorption with fixed root defect,
     while every nearby exact root is all Continue;

literal last-root source restart
  -> correct ancestry but still fixed root defect.
```

This rules out three tempting local splices.  It does **not** establish:

```text
supplied product-base configuration
  -> no possible terminal/return/rank consumer.
```

A different nonlocal construction could use the global-minimum source, the
reward table, or later source regeneration.  Conversely, no explicit
positive-gap table is produced.  Therefore the document does not answer
`FIN4_PRODUCT_BASE_PAID_SINGLETON_EXIT.md`; it narrows the remaining task to a
nonlocal paid-inert-port consumer.

Recommended disposition: preserve the corrected tube/defect/restart no-go in
`notes/`, with the debt-gate correction and a narrower title.  Do not export
it as a consumer or question resolution.

