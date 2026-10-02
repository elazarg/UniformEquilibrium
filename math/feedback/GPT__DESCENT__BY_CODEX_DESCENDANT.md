# Audit of `gpt/DESCENT.md`

Reviewer: `CODEX_DESCENDANT`

Verdict: **REVISE; no new consumption of the paid-cap question.**  The note
correctly recognizes the finite-charge ballistic residual, but Section 2 is a
vacuous branch of the displayed positive-minimum cap orbit, Section 1
misdescribes one port as recursive applications of `QuantitativeDebtDescent`,
and the stationary repair proposed in Section 6 omits the normalized-solo
boundary.

## 1. The displayed recursion is one summable port

For the literal cap lift,

\[
 D_{k+1}=c_kD_k,
 \qquad
 D_k=\Bigl(\prod_{j<k}c_j\Bigr)D_0,
 \qquad D_k\ge D_*>0.
\]

Thus the successive `P_k` in Section 1 are the finite prefixes inside one
selected port.  They are not the limit descendants returned by repeated
applications of the `QuantitativeDebtDescent` constructor.  This distinction
matters: the port limit need not be an actual profile, whereas every finite
prefix is an actual source whose induced port is merely a tail of the same
orbit.

The same equations already imply

\[
 \prod_k(1-a_k)\ge D_*/D_0>0
 \quad\Longrightarrow\quad
 \sum_k a_k<\infty.
\]

Equivalently, the checked finite debt budget gives

\[
 D_*\sum_{k<N}a_k\le D_0-D_N\le D_0-D_*.
\]

Hence the hypothesis `sum a_k = infinity` in Section 2 is impossible before
compact recurrence is invoked.  The proposed first outcome is not an
additional branch of this construction.  Positive-charge/zero-displacement
near-return remains the already checked *finite-total-charge* branch of the
exact trichotomy.

There is also an orientation correction.  Since

\[
 B_{k+1}=F_{q_k}(B_k),
\]

the Bellman edge is directed from the later prefixed value `B_(k+1)` to the
tail value `B_k`.  A block with endpoints `n_j<n_l` is traversed
`B_(n_l) -> B_(n_j)`, not in increasing prefix index.  Endpoint closeness is
symmetric, so this alone would not invalidate a near-return, but the literal
chronology should be stated in the correct direction.

## 2. Paid-row transport uses opponent survival

The shifted pure-time payoff difference is multiplied by the product of the
observer-deleted Continue masses, not by the joint survival product `s_k`.
The former is at least the latter, so the useful conclusion

\[
 g_k\ge s_kg_0\ge (D_*/D_0)g_0
\]

is valid.  The equality `g_k=s_kg_0` asserted in Section 1 is not valid in
general.

With this repair, the finite-charge conclusions in Section 3 are sound:
caps, prescribed values, and terminal laws are Cauchy; positive-debt support
is unchanged; the shifted paid comparison has a fixed positive lower bound;
and remaining late absorption tends to zero.  These facts are already the
content of the checked summable port and the reviewed same-provenance
high-limit Zeno alternative.  They are not a new compression theorem.

## 3. The proposed stationary estimate is false without a properness input

For a positive-absorption root `q`, tail cap `b`, and successor
`b'=F_q(b)`, let `w` be the terminal payoff of repeating `q` forever.  The
affine identity is indeed

\[
 a(w-b)=b'-b,
 \qquad a=\operatorname{Abs}(q)>0.
\]

Thus normalized cap motion is exactly the stationary fixed-point
displacement.  This is the durable useful observation in the note.

It does **not** give the uniform estimate (14).  For player `i`, write
`beta_i` for opponent Continue mass and `h_i=1-beta_i`.  In the mixed exact
case the stationary Never value contains the quotient

\[
 N_i-b_i={a\over h_i}(w_i-b_i).
\]

Consequently stationary behavioral regret can stay order one while
`|w_i-b_i|=|(b'_i-b_i)/a|` tends to zero, whenever `h_i/a -> 0`.  This is the
normalized-singleton (deleted-law bubble) boundary.  It is exactly why the
period-one refusal formulas carry the denominator
`1 - normalizedSingletonMass_i`.

Therefore a valid stationary conclusion requires either a uniform properness
bound away from normalized singleton mass one, or a separate consumer of the
solo/deleted-law branch.  The paid-cap packet supplies neither.  Section 6
does not reduce the remaining problem without reopening that already known
boundary.

## 4. Exact durable delta

After correction, the only useful new formulation is:

> normalized cap motion equals the repeated-root stationary fixed-point
> displacement; under a supplied uniform non-solo/properness bound, its
> vanishing gives stationary approximate equilibria.

That is a conditional proper-clock consumer, not a consumer of
`QuantitativeDebtDescent` or `InertStall`.  The unconditional conclusion of
the note remains the already known finite-charge Zeno port.  No renewable
rank, source restart, or terminal consumer is produced.

