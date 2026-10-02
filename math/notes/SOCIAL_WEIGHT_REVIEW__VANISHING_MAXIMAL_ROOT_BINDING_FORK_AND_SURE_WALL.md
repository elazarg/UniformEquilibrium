# Vanishing maximal roots: binding fork and induced sure wall

## Status

Ordinary mathematics, not Lean-checked.  This is a conditional refinement of
a supplied coherent paired response/maximal-root packet.  It does not derive
that packet from one fixed outward ray, and it is not a terminal consumer.

The induced-Nash semantics used in the final normalization already exist in
checked form.  The incremental content is the alignment of a vanishing-root
binding label with one signed source/response atom and one literal root-time
fork, together with explicit constants.

## 1. Supplied packet

Let \(I=\operatorname{Fin}4\), let rewards be bounded by \(M>0\), and let
\(D_*>0\) be the global minimum of total terminal semantic debt.

Assume a full-debt global minimum

\[
x=(U,B),
\qquad
d_i(x)>0\quad(i<4), \tag{1.1}
\]

and actual same-source sibling profiles \(A_n,R_n\) such that:

1. \(A_n\) and \(R_n\) differ only in one fixed player \(j\)'s complete
   strategy;
2. \(A_n\to x\) in complete terminal semantics;
3. \(d_j(R_n)\to0\);
4. \(D(R_n)\) remains bounded, in particular \(D(R_n)\le8M\); and
5. \(q^n\) is a maximum-absorption exact product root against \(B(R_n)\),
   with absorption

   \[
   a_n=1-\prod_i(1-q^n_i)\longrightarrow0. \tag{1.2}
   \]

These are supplied outer-sequence hypotheses.  They must come from a coherent
paired packet.  They do not follow by iterating one fixed endpoint with small
positive \(j\)-debt: exact prefixing would scale that debt by the same positive
factor as total debt and would not make it vanish.

Write

\[
s_i=r_i(\{i\}),
\qquad
\alpha_i=U_i-s_i.
\]

The minimum singleton margin gives

\[
\alpha_i
\ge D_*-d_i(x)
=\sum_{h\ne i}d_h(x)>0. \tag{1.3}
\]

Put

\[
\alpha=\min_i\alpha_i>0. \tag{1.4}
\]

Since the siblings differ only in \(j\)'s strategy,

\[
B_j(R_n)=B_j(A_n)\longrightarrow B_j, \tag{1.5}
\]

and hence eventually

\[
B_j(R_n)-s_j\ge D_*/2. \tag{1.6}
\]

## 2. Binding label or uniform cap moat

For player \(i\), write

\[
\chi_{n,i}=\prod_{h\ne i}(1-q^n_h).
\]

Suppose \(q^n_k>0\).  For large \(n\), \(q^n_k<1\), so exact
complementarity makes \(k\) indifferent between Quit and Continue.  If
\(p^n_{-k}(A)\) is the probability that exactly the opponents in \(A\) Quit,
then

\[
\chi_{n,k}(B_k(R_n)-s_k)
=
\sum_{\varnothing\ne A\subseteq I\setminus\{k\}}
p^n_{-k}(A)
\bigl(r_k(A\cup\{k\})-r_k(A)\bigr). \tag{2.1}
\]

Therefore

\[
|B_k(R_n)-s_k|
\le
\frac{2M(1-\chi_{n,k})}{\chi_{n,k}}
\le
\frac{2Ma_n}{1-a_n}longrightarrow0. \tag{2.2}
\]

After a subsequence, one fixed active label \(k\) works.  Equation (1.6)
forces

\[
k\ne j. \tag{2.3}
\]

If instead the maximum-absorption root is all Continue eventually, it is
already the unique exact root at that cap.  After a subsequence, either one
fixed coordinate still satisfies

\[
B_k(R_n)-s_k\longrightarrow0, \tag{2.4}
\]

or all four gaps have a uniform positive lower bound.  The latter is the
strict cap-moat arm.

Thus the vanishing-root branch gives either:

\[
\boxed{
\text{uniform strict cap moat and unique all Continue}
\quad\text{or}\quad
\text{a fixed binding label }k\ne j.
} \tag{2.5}
\]

## 3. Binding produces an aligned signed atom

Assume the binding arm.  Since \(A_n\to x\),

\[
U_k(A_n)\longrightarrow U_k.
\]

Equations (1.3) and (2.2)/(2.4) yield eventually

\[
U_k(A_n)-B_k(R_n)\ge\alpha/2. \tag{3.1}
\]

Also

\[
U_k(A_n)-U_k(R_n)
=U_k(A_n)-B_k(R_n)+d_k(R_n)
\ge\alpha/2. \tag{3.2}
\]

Let \(\mu^A_n,\mu^R_n\) be their complete terminal laws.  Since the Never
outcome has reward zero,

\[
U_k(A_n)-U_k(R_n)
=\sum_{\varnothing\ne T\subseteq I}
(\mu^A_n(T)-\mu^R_n(T))r_k(T). \tag{3.3}
\]

There are fifteen nonempty coalitions.  After a subsequence, one fixed
coalition \(T\) satisfies

\[
(\mu^A_n(T)-\mu^R_n(T))r_k(T)
\ge\alpha/30. \tag{3.4}
\]

The same player \(k\) is therefore the binding cap coordinate, the recipient
of a fixed same-source payoff loss, and the observer of a fixed signed law
atom.

## 4. Literal reached curvature fork

If \(q^n_k>0\), exactness at the response cap gives

\[
Q_k(q^n_{-k})=C_k(q^n_{-k};B_k(R_n)). \tag{4.1}
\]

Against the actual response payoff,

\[
Q_k(q^n_{-k})-C_k(q^n_{-k};U_k(R_n))
=\chi_{n,k}d_k(R_n). \tag{4.2}
\]

Hence in the literal prefixed profile \(q^n::R_n\), changing \(k\)'s current
mixed action to pure Quit has exact gain

\[
g^R_{n,k}
=(1-q^n_k)\chi_{n,k}d_k(R_n)
=(1-a_n)d_k(R_n). \tag{4.3}
\]

At the same literal root against the source sibling, pure Continue has
conditional advantage

\[
C_k(q^n_{-k};U_k(A_n))-Q_k(q^n_{-k})
=\chi_{n,k}(U_k(A_n)-B_k(R_n))
\ge(1-a_n)\alpha/2. \tag{4.4}
\]

The fork is at date zero and has joint reach one.

If the selected root is all Continue and (2.4) holds, pure Quit from \(R_n\)
has gain

\[
s_k-U_k(R_n)
=d_k(R_n)-(B_k(R_n)-s_k). \tag{4.5}
\]

After a subsequence, either \(d_k(R_n)\to0\), so both fixed coordinates
\(j,k\) have asymptotically zero debt, or \(d_k(R_n)\ge\beta>0\), in which
case (4.3) or (4.5) supplies a fixed positive literal root-time gain.

## 5. Exact-prefix passport

Let \(w=x_0\cdots x_{m-1}\) be a finite word, where each \(x_t\) is exact at
the successive cap of the prefixed response endpoint.  Prefix the same word
to both siblings and put

\[
P(w)=\prod_{t<m}c(x_t).
\]

Root-absorption rewards cancel between the two branches, while exactness on
the response branch gives

\[
U_k(w::A_n)-B_k(w::R_n)
=P(w)(U_k(A_n)-B_k(R_n)). \tag{5.1}
\]

Also

\[
D(w::R_n)=P(w)D(R_n). \tag{5.2}
\]

Global minimality and \(D(R_n)\le8M\) imply

\[
P(w)\ge D_*/(8M). \tag{5.3}
\]

Consequently

\[
U_k(w::A_n)-B_k(w::R_n)
\ge\frac{\alpha D_*}{16M}. \tag{5.4}
\]

This is a renewable finite-prefix passport.  It is not a forward
extension-compatible chronology, because selecting new outer roots does not
by itself identify later descendants with reached suffixes of one source.

## 6. Induced sure-wall normalization

Fix \(k\) and let \(J=I\setminus\{k\}\).  In the finite three-player game on
\(J\), fix \(k\) to Quit and let the terminal coalition be
\(A\cup\{k\}\) when the free Quit set is \(A\subseteq J\).  Choose a mixed
Nash equilibrium \(y\) of this induced game and write

\[
p_0=\Pr_y(A=\varnothing).
\]

Make an actual profile \(W\) which plays this product root at date zero and
then Never.  Every \(\ell\ne k\) has exactly zero unrestricted debt: after any
replacement by \(\ell\), the sure quitter \(k\) still absorbs at date zero,
and the induced Nash inequalities cover the only relevant action.

For \(k\), Quit and Continue values are

\[
Q_k(y)=\sum_{A\subseteq J}p_y(A)r_k(A\cup\{k\}), \tag{6.1}
\]

\[
C_k(y)
=p_0\max\{0,s_k\}
+\sum_{\varnothing\ne A\subseteq J}p_y(A)r_k(A). \tag{6.2}
\]

Pure-time extremality is exact here, so

\[
D(W)=d_k(W)=[C_k(y)-Q_k(y)]_+. \tag{6.3}
\]

Global minimality gives \(D(W)\ge D_*\), hence

\[
p_0(-s_k)_+
+\sum_{\varnothing\ne A\subseteq J}
p_y(A)(r_k(A)-r_k(A\cup\{k\}))
\ge D_*. \tag{6.4}
\]

Therefore either

\[
p_0(-s_k)_+\ge D_*/2, \tag{6.5}
\]

which yields

\[
s_k\le-D_*/2,
\qquad
p_0\ge D_*/(2M), \tag{6.6}
\]

or one fixed nonempty \(A\subseteq J\) satisfies

\[
p_y(A)(r_k(A)-r_k(A\cup\{k\}))
\ge D_*/14. \tag{6.7}
\]

In the latter arm,

\[
r_k(A)-r_k(A\cup\{k\})\ge D_*/14,
\qquad
p_y(A)\ge D_*/(28M). \tag{6.8}
\]

This is a literal date-zero negative-singleton/Never wall or a positive-mass
member-leaving wall.

Appending \(A_n\) and \(R_n\) behind the same sure-\(k\) root gives two
profiles with identical prescribed payoff and terminal law.  If \(p_0>0\),
the earlier source/response discrepancy becomes a counterfactual one-coordinate
cap fork:

\[
B_k(W^A_n)-B_k(W^R_n)
\ge p_0\alpha/2. \tag{6.9}
\]

The original signed terminal-law atom is not preserved through the sure wall;
it has been converted into this cap fork.

## 7. Exact boundary

The conditional refinement is:

\[
\boxed{
\begin{array}{l}
\text{strict unique-all-Continue cap moat},\
\text{or two fixed asymptotically zero debt coordinates},\
\text{or a literal reached curvature fork with a finite-prefix passport},\
\text{or a negative-singleton/Never or positive-mass leave wall}.
\end{array}
} \tag{7.1}
\]

None is yet a terminal consumer.  The induced Nash point is reselected from
the reward table and is not reached from the incoming source.  The cap fork
is counterfactual rather than a Nash--Bellman temporal edge.  No uniform
payoff, charged near-return, or renewable finite-rank descent follows here.

## Checked dependencies and duplication

The final sure-base semantics substantially overlaps the checked declarations:

- `persistentBase_inducedNash_free_semantics` in
  `TerminalSemanticFinFourSoloWallDispatch.lean`;
- `singletonBase_inducedNash_floorExcess_semantics` and the stationary
  handoffs in `LargeBaseStationarySemanticHandoff.lean`;
- the generic paid-response maximal-root reduction for the coherent outer
  family and common-prefix survival floor.

The new part needing formalization, if useful, is Sections 2--5 and the
explicit wall constants in Section 6.  It should be packaged as a conditional
consumer of the existing coherent paired packet, not as a replacement
producer.

