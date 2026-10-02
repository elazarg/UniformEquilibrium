# Recurrence architecture obstruction

There are two distinct notions of transition in the quitting-game project:

- a chronological transition executes a finite block and continues with the
  reached suffix; and
- a horizontal operation constructs, replaces, selects, normalizes, or
  compactifies a source.

Treating both as edges of one recurrent relation is unsound. Recurrence in
such a relation need not describe one executable play chronology.

## Complete actual profiles and discontinuous caps

The space

\[
\Sigma=([0,1]^4)^{\mathbb N}
\]

is a compact space of complete behavioral profiles in the product topology.
It determines every literal prefix and suffix operation. It also determines
every unrestricted unilateral cap set-theoretically: against fixed opponents,
an arbitrary behavioral response is a probability law on finite pure stopping
times and Never, so

\[
B_i(\sigma)
=
\sup_{t\in\mathbb N\cup\{\infty\}}
U_i(\sigma[i\leftarrow Q_i^t]).
\tag{1}
\]

This does not make the cap continuous.

Consider the rational table

\[
r_i(S)=
\begin{cases}
0,&i\in S,\\
1,&i\notin S,
\end{cases}
\qquad \varnothing\ne S\subseteq I.
\tag{2}
\]

Let \(\sigma^n\) prescribe that all four players Continue before date \(n\)
and Quit surely at date \(n\). Then \(\sigma^n\) converges coordinatewise to
all-Continue, while

\[
U_i(\sigma^n)=0,
\qquad
B_i(\sigma^n)=1.
\]

At all-Continue, both the solo reward and the Never reward are zero, so its
cap is zero. Hence there is no compact Hausdorff topology on the set of exact
profiles for which all finite hazard coordinates and all actual unrestricted
caps are continuous. The finite hazard coordinates already separate exact
profiles.

The safe distinction is:

- the actual-profile space is compact and set-theoretically sufficient; but
- the graph obtained by adjoining its actual caps, laws, and response data
  need not be closed.

Embedding that graph in a compact ambient product introduces boundary packets
that need not be actual or internally consistent. Possible responses include
noncompact operational states, compact semantic closures with explicit escape
states, semicontinuous envelopes, and two-tier actual/semantic architectures.
The obstruction does not select one of them.

## Untyped legal-operation recurrence is false

Let \(P_{\mathbf C}\) prefix one all-Continue row and let \(S\) remove the
first row. For every profile \(\sigma\),

\[
S(P_{\mathbf C}\sigma)=\sigma.
\tag{3}
\]

Thus any relation containing both operations has the two-cycle

\[
\sigma\longrightarrow P_{\mathbf C}\sigma
\longrightarrow\sigma,
\tag{4}
\]

with zero physical absorption charge. A relation containing complete-strategy
replacement has the still simpler identity edge \((\sigma,\sigma)\); removing
identity replacements destroys closedness, and its closure restores them.

For table (2), take \(\sigma\) to be immediate all-Quit and
\(\tau=P_{\mathbf C}\sigma\). Both have debt one in every coordinate, but
\(\{\sigma,\tau\}\) is a closed, serial, zero-charge recurrent class under
prefix and suffix operations. The same table nevertheless has the exact
all-Continue equilibrium.

This is not a counterexample to uniform equilibrium. It is a counterexample
to the inference

\[
\text{recurrence under arbitrary legal source operations}
\Longrightarrow
\text{executable chronological recurrence}.
\]

Source replacement, normalization, minimizer selection, compactification,
and regeneration must therefore remain horizontal unless a separate theorem
constructs a literal commuting seam into one chronology.

## Sure absorption and the off-path suffix

If a finite block \(B\) has prescribed joint survival \(c(B)=0\), its suffix
is not reached under prescribed play. This alone does not make the suffix
irrelevant to unrestricted caps: a unique sure quitter may deviate to
Continue and expose it.

The sufficient screening condition is

\[
c(B)=0,
\qquad
H_i(B)=0\quad\text{for every player }i,
\tag{5}
\]

where \(H_i(B)\) is the probability that all opponents of player \(i\)
survive the block. Then neither prescribed play nor any unilateral deviation
reaches the suffix, and a cemetery target is semantically sound.

A pure nonsingleton quitting row satisfies (5): after one player changes its
action, another sure quitter remains. A pure singleton row generally does not.

## Circular negative output

If the hypotheses already include a global positive minimum total debt
\(D_*>0\), then every profile satisfies

\[
\max_i d_i(\sigma)\ge D_*/4.
\tag{6}
\]

Thus returning the input table and the assumed lower bound is not an
independent counterexample certificate. It is only a reformulation of the
premise. Moreover, since a cap is a supremum, an actual deviation is guaranteed
at every fixed margin \(\gamma<D_*/4\), not necessarily at exactly
\(D_*/4\).

A noncircular negative result must give a concrete finite reward table and an
independently checkable proof of a positive exploitability lower bound.
