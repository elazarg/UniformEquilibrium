# Vanishing-reach suffix regeneration no-go

## Status

This is an exact law-level obstruction. It shows that positive-reach
conditioning cannot be promoted to an exact limiting successor after the
reach witness is forgotten.

Throughout,

$$
d_{\mathrm{TV}}(\mu,\nu)
=\sup_A|\mu(A)-\nu(A)|
=\frac12\|\mu-\nu\|_1.
$$

It does not rule out:

- a reach-weighted approximation of the original unconditioned profile;
- a finite-precision construction that never promotes the conditional limit
  to an exact source;
- an external phase rank that exits the operation before reach collapses; or
- a richer behavioral-provenance type retaining off-path code.

# 1. Conditioning with a positive reach floor

For a one-player stopping law \(\mu\) on
\(\mathbb N\sqcup\{\infty\}\), let

$$
q_d(\mu)=\mu(\{d,d+1,\ldots,\infty\}).
$$

When \(q_d(\mu)>0\), let \(S_d\mu\) be the conditional law after survival to
date \(d\), shifted back by \(d\).

If

$$
q_d(\mu)\ge\rho,
\qquad
q_d(\nu)\ge\rho,
$$

then

$$
d_{\mathrm{TV}}(S_d\mu,S_d\nu)
\le
\frac{2}{\rho}d_{\mathrm{TV}}(\mu,\nu).
\tag{1}
$$

Indeed, conditioning divides by a quantity at least \(\rho\), and both the
numerator and denominator change by at most total variation. The time shift
is an isometry.

There is no corresponding uniform modulus when the reach tends to zero.

# 2. Exact closure at depth one

Define

$$
\mathsf{CSR}_1
=
\overline{
\{(\mu,S_1\mu):q_1(\mu)>0\}
}^{\,\mathrm{TV}\times\mathrm{TV}}.
\tag{2}
$$

For \(p_n=2^{-n}\), put

$$
\mu_n^Q=(1-p_n)\delta_0+p_n\delta_1,
$$

and

$$
\mu_n^N=(1-p_n)\delta_0+p_n\delta_\infty.
$$

Both sequences are finitely supported, uniformly tight, and converge in
total variation to \(\delta_0\). Their reaches satisfy

$$
q_1(\mu_n^Q)=q_1(\mu_n^N)=p_n>0,
$$

but

$$
S_1\mu_n^Q=\delta_0,
\qquad
S_1\mu_n^N=\delta_\infty.
\tag{3}
$$

Hence

$$
(\delta_0,\delta_0)\in\mathsf{CSR}_1,
\qquad
(\delta_0,\delta_\infty)\in\mathsf{CSR}_1.
\tag{4}
$$

More generally, every stopping law \(\tau\) occurs in the fibre over
\(\delta_0\). Shift \(\tau\) forward by one date, multiply it by \(p_n\), and
put the remaining mass \(1-p_n\) at date zero. The resulting source tends to
\(\delta_0\), has positive depth-one reach, and has conditional suffix
\(\tau\). Therefore

$$
\{\delta_0\}\times\Delta(\mathbb N\sqcup\{\infty\})
\subseteq\mathsf{CSR}_1.
\tag{5}
$$

This gives the exact closure:

$$
\mathsf{CSR}_1
=
\{(\mu,S_1\mu):q_1(\mu)>0\}
\;\cup\;
\left(
\{\delta_0\}\times
\Delta(\mathbb N\sqcup\{\infty\})
\right).
\tag{5a}
$$

Indeed, if a limiting source has positive depth-one reach, (1) makes
conditioning continuous on a fixed positive-reach neighbourhood, so the
limiting target is its literal suffix. If the limiting reach is zero, a
one-player law is necessarily \(\delta_0\).

At the limiting source,

$$
q_1(\delta_0)=0.
$$

Thus none of the pairs in (5) is a legal positive-reach suffix execution from
the limiting source. The closed relation contains actual target laws, but
they are not actual executions of the named operation at that source.

# 3. Exact protected-source reconstruction fails

Mark the sole input stopping law as protected. Starting from \(\delta_0\),
any finite program made from:

- finite prefixing;
- finite concatenation; and
- positive-reach suffixing,

without replacement of the protected law, preserves almost-sure finite
stopping:

$$
\mu(\infty)=0.
\tag{6}
$$

This follows by induction over the finite program. In particular, no such
program reconstructs the closed-relation target \(\delta_\infty\), and every
faithful output \(\nu\) satisfies

$$
d_{\mathrm{TV}}(\nu,\delta_\infty)=1.
\tag{7}
$$

For the one-player quitting table

$$
r(\{1\})=1,
\qquad
r(\varnothing)=0,
$$

the suffix-level unrestricted cap is \(1\), while

$$
U(\nu)=1-\nu(\infty).
$$

Thus the output source \(\delta_\infty\) and every protected faithful recovery
have a unit payoff/exploitability discrepancy at the suffix level.

This unit discrepancy is conditional. In the original approximating profile,
the suffix is reached with probability \(p_n\to0\), so the corresponding
unconditional semantic effect may vanish. The theorem therefore obstructs
exact source regeneration, not every reach-weighted consumer.

# 4. Rank scope

The relation also contains the law-level self-loop

$$
(\delta_\infty,\delta_\infty)\in\mathsf{CSR}_1.
\tag{8}
$$

Consequently there is no law-intrinsic rank

$$
\mathcal R:
\Delta(\mathbb N\sqcup\{\infty\})\to\mathbb N
$$

that strictly decreases along every edge of \(\mathsf{CSR}_1\).

This does not exclude a proof-relevant external phase rank on enlarged nodes,
for example a rank that permits suffix regeneration only once. Such a ranked
producer is a different adapter and still needs a terminal consumer and a
backward compiler.

# 5. Conclusion

The graph closure of positive-reach suffixing is not a closed legal-execution
adapter once the reach and exact-source witness are forgotten.

A sound use of conditioning must instead retain at least one of:

1. a positive reach floor on the limiting edge;
2. finite-precision status, without promotion to a new exact source;
3. a summable source-faithful decoder with typed ancestry; or
4. an enlarged ranked producer that exits before the illegal limiting
   conditioning step.

At stopping-law level this records only distributions on the live spine. If
literal off-path behavioral code is required by later operations, that code
must be included separately in the provenance type.
