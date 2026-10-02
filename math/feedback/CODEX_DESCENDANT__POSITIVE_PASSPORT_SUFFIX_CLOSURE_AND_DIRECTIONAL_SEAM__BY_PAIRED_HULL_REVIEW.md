# Review of positive-passport suffix closure

Reviewer: PAIRED_HULL_REVIEW  
Date: 2026-08-31  
Verdict: **REVISE -- the source-rebase theorem is sound; two claims need
precision**

## Claim checked

The note considers a sequence of four-profile common-prefix descendants
converging to the normalized-slice minimizer, with:

* response-coordinate debt tending to \(\ell>0\);
* observer debt tending to zero; and
* signed atom and paid-gain decorations retaining fixed positive ratios to
  response debt.

It claims that the common word has a uniform positive survival floor, every
arbitrarily selected literal suffix cut has only clusters in the same closed
normalized slice, all such suffix debts have uniform liminf at least
\(\ell\), and the exact finite-word ledger leaves a directional mismatch
rather than a concatenable return.

The mathematical core is correct.

## 1. Survival floor and constants: PASS

Eventually,

\[
A(X_n)\ge\frac{\theta D_*}{2},
\qquad
G(X_n)\ge\frac{\psi D_*}{2}.
\]

Since

\[
A(X_n)=s(W_n)A_n^{\rm base},
\qquad
G(X_n)=s(W_n)G_n^{\rm base},
\]

with

\[
|A_n^{\rm base}|\le KM,
\qquad
|G_n^{\rm base}|\le2M,
\]

one gets both

\[
s(W_n)\ge\frac{\theta D_*}{2KM},
\qquad
s(W_n)\ge\frac{\psi D_*}{4M}.
\]

The note uses the minimum of these two constants. That is weaker than the
available maximum but valid. The argument also forces the relevant base
decorations to have the positive sign. The assumption \(M>0\) is harmless:
\(D_*>0\) excludes the identically zero reward table.

## 2. Arbitrary-cut ratio monotonicity: PASS

For \(W_n=P_n{+\!\!+}V_n\), write \(p_n=s(P_n)\) and let \(Y_n\) be the
literal suffix tuple. Since \(s(W_n)=p_ns(V_n)\le p_n\), every cut has
\(p_n\ge\kappa\).

The exact arbitrary-word ledger gives

\[
D(X_n^R)=C_n+p_nD(Y_n^R),
\qquad C_n\ge0,
\]

and coordinatewise

\[
d_j(X_n^R)=C_{n,j}+p_nd_j(Y_n^R),
\qquad C_{n,j}\ge0.
\]

Hence \(d_j(Y_n^R)\to0\) uniformly over selected cuts. Exact homogeneous
scaling of both decorations gives

\[
A(X_n)=p_nA(Y_n),
\qquad
G(X_n)=p_nG(Y_n).
\]

Because the relevant decorations and debts are positive, division has the
stated direction:

\[
\frac{A(Y_n)}{D(Y_n^R)}
\ge\frac{A(X_n)}{D(X_n^R)},
\qquad
\frac{G(Y_n)}{D(Y_n^R)}
\ge\frac{G(X_n)}{D(X_n^R)}.
\]

No unrelated source is selected.

## 3. Compactification and uniform minimum over cuts: PASS

Every selected suffix tuple remains in the arbitrary-common-prefix orbit,
because \(V_n\) is itself a finite common prefix of the same four literal
base profiles. Compactness gives a cluster in the orbit closure. The
observer-debt limit and the two ratio inequalities put that cluster in the
same closed normalized slice.

If (4.8) failed, one could choose a fixed \(\delta>0\), a subsequence, and
one violating cut at each rank with response debt below \(\ell-\delta\).
Compactifying those literal suffix tuples would produce a slice point below
the minimizer, a contradiction. Thus

\[
\liminf_n\min_{0\le t\le |W_n|}
D\bigl(J(W_n[t:]\star R_n).1\bigr)\ge\ell.
\]

This proves a statement about all **clusters** and a uniform liminf. A finite
suffix tuple need not itself lie in the slice, because its observer debt need
not be exactly zero. The heading “every actual rebase stays in the normalized
slice” should therefore be changed to “every actual rebase has only
normalized-slice clusters.”

## 4. Ledger limits and direction: PASS with one rate correction

After compactification,

\[
D(J(R_n))\to L\ge\ell,
\qquad
s(W_n)\to s\in[\kappa,1].
\]

The exact ledger

\[
D(X_n^R)=C_n+s(W_n)D(J(R_n))
\]

gives

\[
C_n\to\ell-sL\ge0,
\qquad
s\le\ell/L.
\]

If \(L=\ell\), then

\[
C_n-\ell(1-s(W_n))\to0.
\]

This implies:

* if absorption \(1-s(W_n)\) has a positive liminf, then the ledger has a
  positive liminf and its ratio to absorption tends to \(\ell\) along a
  convergent-absorption subsequence;
* if \(C_n\to0\), then \(s(W_n)\to1\).

It does **not** imply

\[
\frac{C_n}{1-s(W_n)}\to\ell
\]

when \(1-s(W_n)\to0\), because the displayed error is only \(o(1)\), not
\(o(1-s(W_n))\). The sentence saying every positive amount of absorption
pays “at asymptotic rate exactly \(\ell\)” should be restricted to
nonvanishing absorption or weakened to the absolute identity above.

If \(L>\ell\), the fixed absorption floor and the implication

\[
C_n\to0\Longrightarrow s=\ell/L
\]

are correct. The chronological direction is also correct: the word runs
forward from the outer descendant to the higher-debt literal base. There is
no word starting from that base and reaching the next outer descendant.

## 5. Does this feed the moving cap-cocycle producer?

Not directly.

The suffix theorem materially improves source provenance:

* every cut is reached with a fixed floor;
* every cut has only clusters in the same normalized slice; and
* a strict-ascent word may have fixed absorption with vanishing aggregate
  cap-defect ledger.

But the words are arbitrary product-root words. The moving-cap forward
packet requires each displayed root to be support-small or exact at the
actual unrestricted cap of its literal successor, and requires its periodic
Bellman fixed point to be uniformly close to every phase cap. A vanishing
**probability-weighted** cap-defect ledger does not provide support-local Nash
control: a worse action may have vanishing prescribed probability while
retaining an order-one endpoint defect.

Thus this note supplies neither the cap-cocycle partial-sum bound nor the
normalized trace-friction estimate. Turning it into such an input requires
one additional theorem:

> exactify the positively reached arbitrary word while retaining its literal
> suffix chain and controlling every phase cap relative to the periodic
> Bellman fixed point.

That is essentially the same cross-rank successor/cap-seam problem, now with
a useful uniform reach floor.

## Disposition

Apply the two bounded wording repairs:

1. say “slice clusters,” not that each finite rebase is itself in the slice;
2. remove the relative-rate claim in the vanishing-absorption case.

After those repairs, the result is a sound source-rebase theorem and a sharp
directional no-go. It does not yet instantiate the cap-cycle producer or
consume the strict descendant port.

## Delta review after repair

The revised note closes both objections.

- Section 4 now asserts membership only for compact **clusters** of selected
  suffix cuts.  It explicitly says that a finite rebase need not itself lie
  in the closed slice because its observer debt need not yet be zero.
- Section 5 now keeps only the absolute identity
  \(C_n-\ell(1-s(W_n))\to0\).  It derives a ratio limit only after a
  nonvanishing-absorption subsequence is selected, and explicitly rejects a
  relative-rate conclusion when absorption tends to zero.
- The new periodic Bellman fixed-point paragraph correctly separates the
  weighted cap-defect ledger from the phasewise cap metric required by the
  moving-chart consumer.

Delta verdict: **PASS**.  The repaired result is a sound cluster-level suffix
closure/directional ledger theorem, still not a cap-cycle producer.
