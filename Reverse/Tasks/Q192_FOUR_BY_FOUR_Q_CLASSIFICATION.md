# Question 192: Full-core four-by-four zero-diagonal Q classification

## Matrix problem

Let \(M\in\mathbb R^{4\times4}\) have zero diagonal. Define a decreasing
sequence of index sets by

\[
I_0=\{1,2,3,4\},\qquad
I_{n+1}=\{i\in I_n:\exists j\in I_n,\ j\ne i,\ M_{ij}\leq0\},
\qquad
I_*=\bigcap_n I_n.
\]

Say that \(M\) is standard \(Q\) if, for every \(q\in\mathbb R^4\), there is
\(z\geq0\) such that

\[
w=q+Mz\geq0,\qquad z_iw_i=0\quad(1\leq i\leq4).
\]

Say that \(M\) has a homogeneous simplex solution if there is
\(z\geq0\), \(\sum_i z_i=1\), such that

\[
Mz\geq0,\qquad z_i(Mz)_i=0\quad(1\leq i\leq4).
\]

The branch of interest is

\[
I_*=\{1,2,3,4\},\qquad
M\text{ is standard }Q,\qquad
M\text{ has no homogeneous simplex solution}.
\tag{*}
\]

## Known finite classification boundary

For a zero-diagonal matrix on three indices, standard \(Q\) with no
homogeneous simplex solution is completely classified up to relabeling. Its
six off-diagonal entries have one of the two strict directed-cycle
orientations

\[
\begin{pmatrix}0&-a&b\\c&0&-d\\-e&f&0\end{pmatrix}
\quad\text{or}\quad
\begin{pmatrix}0&a&-b\\-c&0&d\\e&-f&0\end{pmatrix},
\qquad a,b,c,d,e,f>0,
\]

and its determinant is positive. In the first orientation this is
\(bcf>ade\), and the converse holds.

For a four-index zero-diagonal standard-\(Q\) corrected core, a nonempty core
has size three or four. The size-three branch is therefore covered by the
preceding classification. The full-core branch is nonempty: for example,

\[
\begin{pmatrix}
0&0&-1&2\\
0&0&-1&2\\
2&2&0&-1\\
-1&-1&2&0
\end{pmatrix}
\]

satisfies \((*)\).

## Question

Classify all matrices satisfying \((*)\), up to simultaneous permutation of
indices and positive diagonal row and column scalings.

## Acceptance criterion

A complete answer must give a finite collection of normalized sign/zero
patterns and explicit polynomial equalities and strict or weak inequalities
such that:

1. every matrix satisfying \((*)\) is equivalent to one listed region;
2. every matrix in a listed region is standard \(Q\), with a constructive LCP
   support certificate valid for every right-hand side \(q\), or an equivalent
   exact proof;
3. every listed region excludes homogeneous simplex solutions;
4. all boundary cases with zero off-diagonal entries are assigned correctly;
5. the transformations used in the normalization are proved to preserve the
   three properties in \((*)\).

A search over sampled matrices or a list of sufficient families is not a
classification. A useful partial answer may completely classify one fixed
sign chamber, but it should state explicitly which chambers remain.

# Answer

The useful observation is that the two difficult properties in ((*)) admit exact finite polyhedral encodings:

[
\text{no homogeneous simplex solution}
\iff
\text{positive independence of every complementary column set},
]

and

[
M\text{ is }Q
\iff
\text{the nonsingular complementary cones cover }\mathbb R^4.
]

In dimension four, positive independence and cone coverage can both be reduced to explicit Gram-determinant and adjugate inequalities. This gives a complete finite semialgebraic classification, including all singular and zero-entry boundaries. It is much larger than the two-pattern (3\times3) classification, so the natural form is a compressed finite atlas rather than a flat table.

---

# 1. Complementary matrices

Put (I={1,2,3,4}). For every (S\subseteq I), define the complementary matrix

[
B_S(M)=\bigl[b^S_1\ \cdots\ b^S_4\bigr],
\qquad
b^S_i=
\begin{cases}
-M_{\bullet i},&i\in S,\
e_i,&i\notin S.
\end{cases}
\tag{1}
]

Thus, for (x\geq0),

[
q=B_Sx
]

means precisely

[
z_i=
\begin{cases}
x_i,&i\in S,\
0,&i\notin S,
\end{cases}
\qquad
w_i=
\begin{cases}
0,&i\in S,\
x_i,&i\notin S,
\end{cases}
]

and hence

[
q=w-Mz,\qquad w=q+Mz,\qquad z,w\geq0,\qquad z_iw_i=0.
\tag{2}
]

Consequently,

[
M\text{ is standard }Q
\iff
\bigcup_{S\subseteq I}\operatorname{cone}B_S(M)=\mathbb R^4.
\tag{3}
]

After ordering (S) before (I\setminus S),

[
B_S=
\begin{pmatrix}
-M_{SS}&0\
-M_{I\setminus S,S}&I
\end{pmatrix},
]

so

[
\delta_S(M):=\det B_S(M)
=(-1)^{|S|}\det M_{SS}.
\tag{4}
]

In particular, because the diagonal is zero,

[
\delta_{{i}}=0.
]

The only potentially nonsingular complementary matrices are therefore indexed by

[
\mathfrak S
===========

{\varnothing}
\cup \binom I2
\cup \binom I3
\cup {I},
\qquad |\mathfrak S|=12.
\tag{5}
]

---

# 2. An explicit polynomial test for positive dependence

For vectors (v_1,\ldots,v_k\in\mathbb R^4), let

[
V=[v_1\ \cdots\ v_k],\qquad G(V)=V^{\mathsf T}V.
]

Define the positive-circuit predicate (\operatorname{Circ}(V)) as follows.

For (k=1),

[
\operatorname{Circ}(V)
\iff
v_1^{\mathsf T}v_1=0.
\tag{6}
]

For (2\leq k\leq5),

[
\operatorname{Circ}(V)
\iff
\det G(V)=0
\quad\text{and}\quad
\operatorname{adj}(G(V))_{ab}>0
\quad(1\leq a,b\leq k).
\tag{7}
]

All expressions in (6)–(7) are polynomials in the coordinates of the (v_i).

## Positive-circuit lemma

For a finite family (v_1,\ldots,v_m\in\mathbb R^4), the following are equivalent:

[
\exists,\lambda\geq0,\quad
\lambda\neq0,\quad
\sum_{i=1}^m\lambda_i v_i=0;
\tag{8}
]

[
\exists,J\subseteq{1,\ldots,m},
\quad
1\leq |J|\leq5,
\quad
\operatorname{Circ}\bigl([v_j]_{j\in J}\bigr).
\tag{9}
]

### Proof

Choose an inclusion-minimal support (J) of a nonnegative dependence. The corresponding coefficients are strictly positive. Minimality implies that the nullspace of (V_J) is one-dimensional: otherwise one could perturb the positive nullvector until one coefficient became zero.

Thus (\operatorname{rank}V_J=|J|-1), and necessarily (|J|\leq5). Since

[
\ker(V_J^{\mathsf T}V_J)=\ker V_J,
]

the adjugate has the form

[
\operatorname{adj}(V_J^{\mathsf T}V_J)
=c,\lambda\lambda^{\mathsf T},
\qquad c>0,
]

so it is entrywise strictly positive. The converse follows because an entrywise positive column of the adjugate is a strictly positive nullvector. ∎

For later use, write

[
\operatorname{PosDep}(v_1,\ldots,v_m)
:=
\bigvee_{\substack{\varnothing\neq J\subseteq{1,\ldots,m}\|J|\leq5}}
\operatorname{Circ}\bigl([v_j]_{j\in J}\bigr).
\tag{10}
]

This is a finite Boolean combination of polynomial equalities and strict inequalities.

Its negation is also explicit. For example, when (k\geq2),

[
\neg\operatorname{Circ}(V)
\iff
\det G(V)>0
\quad\vee\quad
\bigvee_{a,b}\operatorname{adj}(G(V))_{ab}\leq0,
\tag{11}
]

because (G(V)) is positive semidefinite.

---

# 3. Exact classification of the homogeneous condition

A nonzero homogeneous LCP solution is a pair (z,w\geq0) such that

[
w=Mz,\qquad z_iw_i=0.
]

It can be normalized to (\sum_i z_i=1), so this is exactly the homogeneous-simplex condition in the question.

For (S={i:z_i>0}), set

[
x_i=
\begin{cases}
z_i,&i\in S,\
w_i,&i\notin S.
\end{cases}
]

Then (x\geq0), (x\neq0), and

[
B_Sx=0.
]

Conversely, every nonzero (x\geq0) in (\ker B_S) gives a homogeneous complementary solution by (2). Such an (x) necessarily has a nonzero (z)-part, since a positive combination of distinct identity columns cannot vanish.

Hence the following is exact:

[
\boxed{
\Phi_{R_0}(M)
:=
\bigwedge_{S\subseteq I}
\neg\operatorname{PosDep}
\bigl(b^S_1,b^S_2,b^S_3,b^S_4\bigr).
}
\tag{12}
]

Then

[
\Phi_{R_0}(M)
\iff
M\text{ has no homogeneous simplex solution}.
\tag{13}
]

There are only

[
16(2^4-1)=240
]

positive-circuit blocks in (12). Rank drops, zero columns, two-dimensional nullspaces, and nonminimal supports are all covered by the smaller subsets (J).

---

# 4. Exact polynomial classification of the (Q) property

Let

[
D(M)={S\in\mathfrak S:\delta_S(M)\neq0}.
\tag{14}
]

Only these supports give full-dimensional complementary cones.

## 4.1 Singular cones can be discarded

A singular (B_S) has its cone in a proper linear subspace. Therefore

[
\bigcup_{S\subseteq I}\operatorname{cone}B_S=\mathbb R^4
\iff
\bigcup_{S\in D(M)}\operatorname{cone}B_S=\mathbb R^4.
\tag{15}
]

Indeed, if the nonsingular cones did not cover, their finite closed union would have a nonempty open complement. One can choose a point in that open set outside the finite union of the spans of the singular cones.

## 4.2 Polynomial facet covectors

For (S\in D(M)) and (k\in I), define the row covector

[
a_{S,k}(M)
:=
\delta_S(M),
e_k^{\mathsf T}\operatorname{adj}(B_S(M))
\in\mathbb R^{1\times4}.
\tag{16}
]

If

[
\alpha=B_S^{-1}q,
]

then

[
a_{S,k}q
========

\delta_S^2,\alpha_k.
\tag{17}
]

Consequently,

[
q\in\operatorname{cone}B_S
\iff
a_{S,k}q\geq0
\quad\text{for every }k.
\tag{18}
]

All coordinates of (a_{S,k}) are polynomials in the entries of (M).

## 4.3 Finite selector condition

Fix a possible nonsingularity set (D\subseteq\mathfrak S). For every selector

[
\phi:D\longrightarrow I,
]

consider the selected covectors

[
a_{S,\phi(S)},\qquad S\in D.
]

Define

[
\Phi_{Q,D}(M)
:=
\bigwedge_{\phi:D\to I}
\operatorname{PosDep}
\bigl(a_{S,\phi(S)}^{\mathsf T}:S\in D\bigr).
\tag{19}
]

This is an explicit finite conjunction: there are at most (4^{12}) selectors. Each positive-dependence test needs only subsets of at most five selected vectors.

The determinant-status condition for (D) is

[
\operatorname{Stat}*D(M)
:=
\left(
\bigwedge*{S\in D}\delta_S(M)^2>0
\right)
\wedge
\left(
\bigwedge_{S\in\mathfrak S\setminus D}\delta_S(M)=0
\right).
\tag{20}
]

The empty support must belong to every nonempty region, since (B_\varnothing=I).

## Cone-coverage theorem

On (\operatorname{Stat}_D(M)),

[
\boxed{
M\text{ is standard }Q
\iff
\Phi_{Q,D}(M).
}
\tag{21}
]

### Proof

Suppose first that the nonsingular complementary cones do not cover. Choose (q) outside all of them. For each (S\in D), choose an index (\phi(S)) for which

[
a_{S,\phi(S)}q<0.
]

Thus the strict system

[
A_\phi q<0
\tag{22}
]

is feasible, where the rows of (A_\phi) are the selected covectors.

By Gordan’s strict alternative, (22) is feasible exactly when there is no nonzero (\lambda\geq0) with

[
A_\phi^{\mathsf T}\lambda=0.
]

By the positive-circuit lemma, this means that the selected covectors are not positively dependent. Hence (\Phi_{Q,D}) fails.

Conversely, suppose (\Phi_{Q,D}) fails. For some selector (\phi), its selected covectors have no nonnegative dependence. Gordan’s theorem gives (q) satisfying (22). For every (S\in D), at least one cone inequality in (18) is then negative, so (q) belongs to no nonsingular complementary cone. By (15), (M) is not (Q). ∎

This is also a constructive LCP certificate. Given (q), enumerate (S\in D). Formula (19) guarantees an (S) satisfying

[
a_{S,k}q\geq0\qquad(k=1,\ldots,4).
]

Then

[
\alpha=B_S^{-1}q
================

\frac{\operatorname{adj}(B_S)q}{\delta_S}
\geq0,
\tag{23}
]

and (2) gives an exact complementary solution.

---

# 5. Full-core condition

For the particular iteration in the question,

[
I_*=I
\iff
\forall i\in I\ \exists j\neq i:\ M_{ij}\leq0.
\tag{24}
]

If the right-hand condition holds, (I_1=I_0), so the iteration is immediately stationary. If it fails for some (i), that index is removed at the first step and can never return.

Thus full core is determined entirely by the sign/zero pattern.

---

# 6. Normalization under row and column scalings

Let

[
M'=R,PMP^{\mathsf T}C,
\tag{25}
]

where (R,C) are positive diagonal and (P) is a permutation matrix.

## 6.1 Preservation of the three properties

Given (q'), put

[
q=P^{\mathsf T}R^{-1}q'.
]

If ((z,w)) solves (\operatorname{LCP}(q,M)), define

[
z'=C^{-1}Pz,\qquad w'=RPw.
]

Then

[
q'+M'z'
=======

# RP(q+Mz)

# RPw

w',
]

and

[
z'_iw'_i
========

# \frac{R_i}{C_i}(Pz)_i(Pw)_i

0.

]

Therefore

[
M\text{ is }Q\iff M'\text{ is }Q.
\tag{26}
]

The same transformation with (q=0) preserves nonzero homogeneous solutions. A transformed nonzero (z') can be rescaled to have coordinate sum (1). Hence

[
M\text{ has a homogeneous simplex solution}
\iff
M'\text{ does}.
\tag{27}
]

Finally, positive scalings preserve every entry’s sign and zero status, while (P) merely relabels indices. Thus

[
I_*(M)=I
\iff
I_*(M')=I.
\tag{28}
]

The zero diagonal is also preserved.

## 6.2 Forest normal form

Fix a sign/zero pattern

[
\epsilon=(\epsilon_{ij})*{i\neq j},
\qquad
\epsilon*{ij}\in{-1,0,1}.
]

Construct the bipartite graph (G_\epsilon) with row vertices (r_i), column vertices (c_j), and an edge (r_i c_j) whenever (\epsilon_{ij}\neq0).

Choose, once and for all, a canonical spanning forest (F_\epsilon) of this graph, for example the lexicographically first spanning forest.

Every matrix with sign pattern (\epsilon) is row/column-scalable to

[
N_\epsilon(x)_{ij}
==================

\begin{cases}
0,&\epsilon_{ij}=0,[1mm]
\epsilon_{ij},&r_ic_j\in F_\epsilon,[1mm]
\epsilon_{ij}x_{ij},
&r_ic_j\notin F_\epsilon,
\end{cases}
\qquad x_{ij}>0.
\tag{29}
]

To see this, write

[
\log |(RMC)_{ij}|
=================

\log|M_{ij}|+\rho_i+\kappa_j.
]

On a forest, the equations setting the selected magnitudes to (1) are consistent and can be solved recursively. The remaining (x_{ij}) are the multiplicative cycle invariants. Changing the free potential on a connected bipartite component adds a constant to all row potentials and subtracts it from all column potentials, so the remaining normalized magnitudes are unaffected.

For a dense (4\times4) zero-diagonal pattern, the bipartite graph has twelve edges and a spanning tree has seven, leaving five positive parameters.

---

# 7. The finite normalized classification

Let (\mathcal E) be the set of lexicographically least representatives of the simultaneous (S_4)-orbits of the (3^{12}) sign/zero patterns. Before imposing full core there are

[
\frac{
3^{12}
+6\cdot3^7
+3\cdot3^6
+8\cdot3^4
+6\cdot3^3
}{24}
=====

22,815
\tag{30}
]

such orbits.

Let (\mathcal E_{\mathrm{fc}}\subseteq\mathcal E) consist of those representatives satisfying

[
\forall i\ \exists j\neq i:\epsilon_{ij}\in{-1,0}.
\tag{31}
]

For (\epsilon\in\mathcal E_{\mathrm{fc}}) and (D\subseteq\mathfrak S), define

[
\boxed{
\begin{aligned}
\mathcal R_{\epsilon,D}
=======================

\bigl{
N_\epsilon(x):;&
x_{ij}>0,\
&
\operatorname{Stat}*D(N*\epsilon(x)),\
&
\Phi_{R_0}(N_\epsilon(x)),\
&
\Phi_{Q,D}(N_\epsilon(x))
\bigr}.
\end{aligned}}
\tag{32}
]

All the conditions in (32) are finite Boolean combinations of:

[
p(x)=0,\qquad p(x)>0,\qquad p(x)\leq0,
\tag{33}
]

where (p) is an explicitly specified polynomial obtained from determinants, Gram matrices, and adjugates.

The complete classification is

[
\boxed{
{M:M\text{ satisfies }(*)}/!\sim
\ =
\bigcup_{\epsilon\in\mathcal E_{\mathrm{fc}}}
\ \bigcup_{D\subseteq\mathfrak S}
\mathcal R_{\epsilon,D},
}
\tag{34}
]

where (\sim) is simultaneous permutation together with independent positive diagonal row and column scaling.

Some regions in (34) are empty. Empty regions may be deleted, but this is unnecessary for classification: membership of a given normalized matrix is decided by evaluating the displayed polynomial signs. If one insists that each region be a conjunction rather than a finite Boolean combination, expand (12) and (19) into disjunctive normal form. That produces a literal finite list of basic semialgebraic regions.

There are no quantified real variables left in (32): the only remaining conjunctions are over the finite sets of supports, selectors, and subsets of at most five selected covectors.

---

# 8. Verification against the five acceptance requirements

1. **Exhaustiveness.**
   Every matrix is permuted to one (\epsilon\in\mathcal E), then row/column-scaled to (N_\epsilon(x)). Conditions (24), (13), and (21) show that a matrix satisfying ((*)) lands in exactly one determinant-status family (D) and in one of the regions (32).

2. **Exact (Q) proof and certificate.**
   Formula (19) is equivalent to complementary-cone coverage by the cone-coverage theorem. For each (q), the support certificate is obtained by finding (S\in D) with all inequalities in (18) nonnegative and then using (23).

3. **Exclusion of homogeneous solutions.**
   Formula (12) excludes every nonnegative kernel vector of every complementary matrix. Conversely, any homogeneous solution produces such a kernel vector.

4. **All zero and singular boundaries.**
   Off-diagonal zeros are part of (\epsilon); singular principal/complementary matrices are assigned by (20); lower-rank and nonminimal positive dependencies are detected by the smaller circuit subsets. No genericity or strict-nondegeneracy assumption occurs.

5. **Invariance of the normalization.**
   Equations (25)–(28) prove preservation of all three properties. The forest construction proves that every equivalence orbit has a normalized representative of the form (29).

---

# 9. The displayed example

For

[
M=
\begin{pmatrix}
0&0&-1&2\
0&0&-1&2\
2&2&0&-1\
-1&-1&2&0
\end{pmatrix},
]

let

[
N=
\begin{pmatrix}
0&-1&2\
2&0&-1\
-1&2&0
\end{pmatrix}.
]

The (3\times3) matrix (N) is in the first strict cycle orientation and

[
\det N=8-1=7>0.
]

For arbitrary (q\in\mathbb R^4), define

[
\bar q=(\min(q_1,q_2),q_3,q_4).
]

Solve (\operatorname{LCP}(\bar q,N)), obtaining class variable (t) and variables (z_3,z_4). If (t=0), put (z_1=z_2=0). If (t>0), allocate all of (t) to an index attaining (\min(q_1,q_2)). Since rows (1) and (2) are identical and rows (3,4) depend on (z_1,z_2) only through (z_1+z_2), this gives an exact solution of (\operatorname{LCP}(q,M)).

The same reduction at (q=0), together with the (R_0) property of (N), forces

[
t=z_3=z_4=0,
]

and hence (z_1=z_2=0). Thus the example has no homogeneous simplex solution. Its full-core property is immediate from the negative entry in every row.

# Followup answer

The previous construction is only a quantifier-free decision procedure. It neither removes empty cells nor enumerates the surviving semialgebraic components, so it does **not** satisfy the stated acceptance criterion. The claim of a complete classification should be withdrawn.

A genuinely explicit partial classification can nevertheless be given for four strict sign chambers. These are the chambers in which exactly one sign occurs once in every row and every column. Up to simultaneous permutation, the exceptional entries form either a directed (4)-cycle or two directed (2)-cycles.

## 1. General permutation-chamber theorem

Let (\pi) be a fixed-point-free permutation of ({1,2,3,4}).

### Unique-negative chamber

Assume

[
M_{i,\pi(i)}<0,
\qquad
M_{ij}>0\quad(j\ne i,\pi(i)).
\tag{1}
]

Let (N) be the positive monomial matrix

[
N_{i,\pi(i)}=-M_{i,\pi(i)},
]

and put (P=M+N\geq0). Thus

[
M=P-N=N(A-I),
\qquad
A=N^{-1}P\geq0.
\tag{2}
]

Then

[
\boxed{
M\text{ satisfies }(*)\iff \rho(A)>1.
}
\tag{3}
]

### Unique-positive chamber

Assume instead

[
M_{i,\pi(i)}>0,
\qquad
M_{ij}<0\quad(j\ne i,\pi(i)).
\tag{4}
]

Let (P) be the positive monomial matrix supported on (\pi), let (N=P-M\geq0), and put

[
M=P-N=P(I-A),
\qquad
A=P^{-1}N\geq0.
\tag{5}
]

Then

[
\boxed{
M\text{ satisfies }(*)\iff \rho(A)<1.
}
\tag{6}
]

The spectral conditions below will be replaced by explicit polynomial inequalities.

---

## 2. Why the theorem is exact

Every row in either chamber contains a negative entry, so (I_*=I).

### 2.1 Homogeneous solutions

Let (S={i:z_i>0}) be the support of a nonzero homogeneous complementary solution.

In the unique-negative chamber, if (i\in S), (|S|\geq2), and (\pi(i)\notin S), then

[
(Mz)*i=\sum*{j\in S\setminus{i}}M_{ij}z_j>0,
]

contradicting ((Mz)_i=0). Thus (S) is (\pi)-invariant. A singleton support is impossible because the predecessor row (\pi^{-1}(i)) has a negative slack. If (\pi) consists of two (2)-cycles, one isolated cycle is also impossible because its active rows receive only their strictly negative exceptional term.

The same argument, with signs reversed, applies to the unique-positive chamber. Consequently, in all four strict chambers the only possible homogeneous support is the full set. Hence

[
\exists z>0,\ Mz=0
\iff
\exists z>0,\ Az=z
\iff
\rho(A)=1,
\tag{7}
]

where the last equivalence follows from Perron–Frobenius, since the displayed strict sign patterns make (A) irreducible. Therefore

[
M\text{ has no homogeneous simplex solution}
\iff
\rho(A)\ne1.
\tag{8}
]

### 2.2 The wrong side of the spectral threshold is not (Q)

In the unique-negative chamber, suppose (\rho(A)<1). Let (y>0) be a left Perron vector and choose (p<0). Set (q=Np<0). If (w=q+Mz\geq0) for some (z\geq0), then

[
N^{-1}w=p+(A-I)z\geq0.
]

But

[
y^{\mathsf T}\bigl(p+(A-I)z\bigr)
=================================

y^{\mathsf T}p+(\rho(A)-1)y^{\mathsf T}z<0,
]

a contradiction. Thus this (q) is not even feasible.

In the unique-positive chamber, if (\rho(A)>1), take (q=Pp) with (p<0). Feasibility would give

[
P^{-1}w=p+(I-A)z\geq0,
]

whereas

[
y^{\mathsf T}\bigl(p+(I-A)z\bigr)
=================================

y^{\mathsf T}p+(1-\rho(A))y^{\mathsf T}z<0.
]

Thus (M) is not (Q).

### 2.3 The correct side is (Q)

Use the complementarity map

[
F_M(x)=x^+ +Mx^-.
\tag{9}
]

The equation (F_M(x)=q) is equivalent to (\operatorname{LCP}(q,M)), with

[
w=x^+,\qquad z=-x^-.
]

Absence of nonzero homogeneous solutions makes (F_M) proper. On the orthant whose negative-coordinate set is (S), the Jacobian has determinant

[
\det M_{SS}.
\tag{10}
]

A nonzero Brouwer degree therefore proves surjectivity of (F_M), hence the (Q)-property. This is the standard degree route in LCP theory. ([JSTOR][1])

For the unique-negative (4)-cycle chamber, take (q=d>0). Any nonempty active support must be (\pi)-invariant, hence full. A full solution would imply

[
(I-A)z=N^{-1}d>0,
]

which is impossible when (\rho(A)>1), after multiplication by the left Perron vector. Thus (z=0) is the only solution and the degree is (+1).

For the unique-negative (2+2) chamber, at (q=d>0) there are exactly three solutions:

[
S=\varnothing,\qquad S={1,2},\qquad S={3,4}.
]

Their local indices are respectively

[
+1,\quad -1,\quad -1,
]

so the degree is (-1).

For either unique-positive chamber, take (q=-d<0). Feasibility forces every exceptional positive variable to be active, hence (z>0) and (w=0). Since (\rho(A)<1),

[
z=(I-A)^{-1}P^{-1}d>0
]

is the unique solution. Its local index is (\operatorname{sgn}\det M\ne0).

This proves (3) and (6).

---

# 3. Normalized (4)-cycle chambers

Every matrix in the unique-negative (4)-cycle chamber is row/column-scalable to

[
N_4(x,y,z,u,v)=
\begin{pmatrix}
0&-1&1&x\
y&0&-1&1\
1&z&0&-1\
-1&u&v&0
\end{pmatrix},
\qquad x,y,z,u,v>0.
\tag{11}
]

The unique-positive chamber is (-N_4(x,y,z,u,v)).

The associated nonnegative matrix is

[
A_4=
\begin{pmatrix}
0&u&v&0\
0&0&1&x\
y&0&0&1\
1&z&0&0
\end{pmatrix}.
\tag{12}
]

Define

[
\begin{aligned}
\phi_1&=1-y(u+v),\
\phi_2&=1-x(u+z),\
\phi_3&=1-v(y+1),\
\phi_4&=1-z(x+1),
\end{aligned}
\tag{13}
]

and

[
\begin{aligned}
\Phi
&=\det(I-A_4)\
&=1-u-v-z-u(x+y)-vy-xz+vxyz.
\end{aligned}
\tag{14}
]

Notice that

[
\det N_4=-\Phi.
\tag{15}
]

The four (\phi_i) are the four (3\times3) principal minors of (I-A_4). The only nontrivial (2\times2) principal minors are (1-vy) and (1-xz); they need not be listed separately because

[
1-vy\leq0\Longrightarrow \phi_3<0,
\qquad
1-xz\leq0\Longrightarrow \phi_4<0.
\tag{16}
]

For a nonnegative matrix (A),

[
\rho(A)<1
\iff
\text{all principal minors of }I-A\text{ are positive},
\tag{17}
]

and

[
\rho(A)>1
\iff
\text{some principal minor of }I-A\text{ is negative}.
\tag{18}
]

This is the principal-minor characterization of nonsingular and singular (M)-matrices.

## 3.1 Unique-negative (4)-cycle: five disjoint regions

The complete classification of this strict chamber is the following five-region list:

[
\begin{array}{ll}
\mathcal R_{4,1}:&
\phi_1<0,[1mm]
\mathcal R_{4,2}:&
\phi_1\geq0,\quad \phi_2<0,[1mm]
\mathcal R_{4,3}:&
\phi_1,\phi_2\geq0,\quad \phi_3<0,[1mm]
\mathcal R_{4,4}:&
\phi_1,\phi_2,\phi_3\geq0,\quad \phi_4<0,[1mm]
\mathcal R_{4,5}:&
\phi_1,\phi_2,\phi_3,\phi_4\geq0,\quad \Phi<0.
\end{array}
\tag{19}
]

Thus

[
\boxed{
N_4(x,y,z,u,v)\text{ satisfies }(*)
\iff
N_4\in\bigcup_{r=1}^{5}\mathcal R_{4,r}.
}
\tag{20}
]

Equivalently,

[
\phi_1<0\ \vee\ \phi_2<0\ \vee
\phi_3<0\ \vee\ \phi_4<0\ \vee\ \det N_4>0.
\tag{21}
]

All five regions are nonempty. Witnesses, in order, are

[
\begin{gathered}
(1/10,10,1/10,1/10,1/10),\
(10,1/10,1/10,1/10,1/10),\
(1/10,1/10,1/10,1/10,1),\
(1/10,1/10,1,1/10,1/10),\
(1/10,1/10,1/2,5,1/2).
\end{gathered}
\tag{22}
]

The last region is important: all proper listed principal minors are nonnegative, but the full determinant gives the (Q)-side.

## 3.2 Unique-positive (4)-cycle: one region

For the sign-reversed chamber,

[
\boxed{
-N_4(x,y,z,u,v)\text{ satisfies }(*)
}
]

exactly when

[
\boxed{
\phi_1>0,\quad
\phi_2>0,\quad
\phi_3>0,\quad
\phi_4>0,\quad
\Phi>0.
}
\tag{23}
]

Equivalently,

[
\phi_i>0\ (1\leq i\leq4),
\qquad
\det(-N_4)=\det N_4<0.
\tag{24}
]

The point (x=y=z=u=v=1/10) is a witness.

The homogeneous boundary in either sign chamber is precisely

[
\phi_1,\phi_2,\phi_3,\phi_4>0,
\qquad
\Phi=0.
\tag{25}
]

A determinant-zero point with some (\phi_i<0) is not homogeneous: it belongs to the unique-negative (Q)-region and to the unique-positive non-(Q) region.

---

# 4. Normalized (2+2) chambers

Every matrix whose unique negative entries form the two cycles
(1\leftrightarrow2) and (3\leftrightarrow4) is equivalent to

[
N_{22}(x,y,z,u,v)=
\begin{pmatrix}
0&-1&1&x\
-1&0&y&z\
1&u&0&-1\
1&v&-1&0
\end{pmatrix},
\qquad x,y,z,u,v>0.
\tag{26}
]

The unique-positive chamber is (-N_{22}).

The associated matrix has bipartite form

[
A_{22}=
\begin{pmatrix}
0&B\
C&0
\end{pmatrix},
\qquad
B=
\begin{pmatrix}
y&z\
1&x
\end{pmatrix},
\qquad
C=
\begin{pmatrix}
1&v\
1&u
\end{pmatrix}.
\tag{27}
]

Therefore

[
\rho(A_{22})^2=\rho(BC),
\tag{28}
]

where

[
BC=
\begin{pmatrix}
y+z&yv+zu\
1+x&v+xu
\end{pmatrix}.
\tag{29}
]

Define

[
\psi_1=1-y-z,
\qquad
\psi_2=1-v-xu,
\tag{30}
]

and

[
\begin{aligned}
\Psi
&=\det(I-BC)\
&=(1-y-z)(1-v-xu)-(yv+zu)(1+x)\
&=uxy-ux-uz-vxy+vz-v-y-z+1.
\end{aligned}
\tag{31}
]

Here

[
\det N_{22}=\Psi.
\tag{32}
]

## 4.1 Unique-negative (2+2): three disjoint regions

The explicit list is

[
\begin{array}{ll}
\mathcal R_{22,1}:&
\psi_1<0,[1mm]
\mathcal R_{22,2}:&
\psi_1\geq0,\quad\psi_2<0,[1mm]
\mathcal R_{22,3}:&
\psi_1,\psi_2\geq0,\quad\Psi<0.
\end{array}
\tag{33}
]

Thus

[
\boxed{
N_{22}(x,y,z,u,v)\text{ satisfies }(*)
\iff
N_{22}\in
\mathcal R_{22,1}\cup\mathcal R_{22,2}\cup\mathcal R_{22,3}.
}
\tag{34}
]

Equivalently,

[
y+z>1
\quad\vee\quad
v+xu>1
\quad\vee\quad
\det N_{22}<0.
\tag{35}
]

The weak inequalities in (33) assign equality boundaries correctly. For example, if (y+z=1), then (\Psi<0) automatically unless the second region already applies, because the off-diagonal entries of (BC) are strictly positive.

Witnesses for the three regions are

[
\begin{aligned}
&(1/10,2,1/10,1/10,1/10),\
&(1/10,1/10,1/10,1/10,2),\
&(100,1/10,1/10,1/1000,1/10).
\end{aligned}
\tag{36}
]

## 4.2 Unique-positive (2+2): one region

The sign-reversed matrix satisfies ((*)) exactly when

[
\boxed{
\psi_1>0,\qquad
\psi_2>0,\qquad
\Psi>0.
}
\tag{37}
]

Equivalently,

[
y+z<1,
\qquad
v+xu<1,
\qquad
\det(-N_{22})=\det N_{22}>0.
\tag{38}
]

Again (x=y=z=u=v=1/10) is a witness.

The homogeneous boundary is

[
\psi_1>0,\qquad \psi_2>0,\qquad \Psi=0.
\tag{39}
]

---

# 5. Why these are genuine normal forms

Positive diagonal row and column scalings preserve all three properties in ((*)). More explicitly, if

[
M'=R\Pi M\Pi^{\mathsf T}C,
\tag{40}
]

where (R,C) are positive diagonal and (\Pi) is a permutation matrix, then a solution of (\operatorname{LCP}(q,M)) is transported by

[
q'=R\Pi q,\qquad
z'=C^{-1}\Pi z,\qquad
w'=R\Pi w.
\tag{41}
]

Indeed,

[
w'=q'+M'z',
\qquad
z'_iw'_i
========

\frac{R_i}{C_i}(\Pi z)_i(\Pi w)_i.
\tag{42}
]

Signs and zeros are preserved, up to relabeling, so the full-core condition is also preserved.

In each of (11) and (26), the seven entries normalized to magnitude (1) form a spanning tree in the bipartite row-column incidence graph. The seven row/column scaling equations therefore have a solution, unique modulo the irrelevant common gauge.

For example, before normalization the (4)-cycle chamber has the form

[
\begin{pmatrix}
0&-a&b&c\
d&0&-e&f\
g&h&0&-i\
-j&k&l&0
\end{pmatrix},
\qquad a,\ldots,l>0.
\tag{43}
]

The normalized parameters in (11) are

[
\begin{aligned}
x&=\frac{ce}{bf},
&
y&=\frac{di}{fg},
&
z&=\frac{bfh}{aei},\
u&=\frac{bfgk}{aeij},
&
v&=\frac{fgl}{eij}.
\end{aligned}
\tag{44}
]

For the (2+2) chamber

[
\begin{pmatrix}
0&-a&b&c\
-d&0&e&f\
g&h&0&-i\
j&k&-l&0
\end{pmatrix},
\tag{45}
]

the normalized parameters are

[
\begin{aligned}
x&=\frac{clg}{bij},
&
y&=\frac{ej}{ld},
&
z&=\frac{fg}{di},\
u&=\frac{bjh}{alg},
&
v&=\frac{bk}{al}.
\end{aligned}
\tag{46}
]

The same formulas apply after reversing all signs.

Under row/column scaling, the matrix (A) changes only by positive diagonal similarity:

[
A';=;C^{-1}AC.
\tag{47}
]

Thus (\rho(A)), and consequently all the classifications above, are genuine invariants of the requested equivalence relation.

---

# 6. The zero stratum containing the displayed example

There is also a fully explicit lower-dimensional zero stratum:

[
D(a,b,c,d,e,f)=
\begin{pmatrix}
0&0&-a&b\
0&0&-a&b\
c&c&0&-d\
-e&-e&f&0
\end{pmatrix},
\qquad a,b,c,d,e,f>0.
\tag{48}
]

Define the (3\times3) quotient

[
\bar D=
\begin{pmatrix}
0&-a&b\
c&0&-d\
-e&f&0
\end{pmatrix}.
\tag{49}
]

Then

[
\boxed{
D(a,b,c,d,e,f)\text{ satisfies }(*)
\iff
bcf>ade.
}
\tag{50}
]

To prove this, aggregate

[
t=z_1+z_2.
]

For a right-hand side (q), set

[
\bar q=(\min(q_1,q_2),q_3,q_4).
]

A quotient solution ((t,z_3,z_4)) lifts as follows:

* if (t=0), set (z_1=z_2=0);
* if (t>0), allocate all of (t) to an index attaining
  (\min(q_1,q_2)).

Rows (3,4) depend on (z_1,z_2) only through (t), while rows (1,2) are identical. This gives an exact LCP solution of the four-dimensional problem. Conversely, taking (q_1=q_2), every four-dimensional solution aggregates to a quotient solution. The same aggregation and lifting work at (q=0), so homogeneous solutions are also equivalent.

The supplied example is

[
(a,b,c,d,e,f)=(1,2,2,1,1,2),
]

and

[
bcf=8>1=ade.
]

---

## Scope that remains

This is now an actual finite chamber list—ten nonempty polynomial regions for four strict sign orbits, plus the explicit duplicate zero stratum—but it is still not the requested full (4\times4) classification.

The unresolved part consists of:

[
\begin{gathered}
\text{strict sign chambers in which neither the positive nor negative}\
\text{entries form a derangement permutation,}
\end{gathered}
]

together with all other off-diagonal zero patterns, including the nonparallel versions of the zero pattern in (48). The earlier (22{,}815)-orbit construction does not resolve those cases and should not be represented as doing so.

[1]: https://www.jstor.org/stable/3690127 "Applications of Degree Theory to Linear Complementarity ..."


## Last followup

The correct status is a **partial chamber theorem**, not a classification of the full-core branch.

What has actually been established is:

[
\boxed{
\begin{array}{l}
\text{four strict sign orbits:}\
\quad\text{unique-negative and unique-positive derangement chambers,}\
\quad\text{with derangement type }(1234)\text{ or }(12)(34);[1mm]
\text{one special zero stratum obtained by duplicating a quotient row/column class.}
\end{array}}
]

Within those chambers, the result is genuinely explicit: there are normalized five-parameter representatives, finite nonempty polynomial regions, correct equality boundaries, and exact (Q)/homogeneous proofs.

It does **not** establish any of the following:

1. A classification of strict chambers where the negative entries—or the positive entries—do not form a permutation support.
2. A classification of chambers having several negative and several positive entries in a row or column.
3. A classification of zero patterns beyond the particular duplicate-class reduction.
4. A classification of all matrices with (I_*=I).
5. An enumeration or elimination of all surviving sign orbits in the full (4\times4) branch.

The obstruction to simply extending the spectral argument is structural. In the classified chambers, the exceptional-sign matrix is monomial, so one has

[
M=N(A-I)\qquad\text{or}\qquad M=P(I-A),
]

with (A\geq0), and every possible homogeneous support is forced to be invariant under one derangement. This reduces both the homogeneous condition and the (Q)-side to the single threshold (\rho(A)=1).

Outside those chambers, all of those features can fail simultaneously:

* a proper nontrivial support may carry a homogeneous solution;
* several different supports may become critical at unrelated polynomial hypersurfaces;
* no monomial factor produces a single nonnegative matrix (A);
* the Brouwer degree may receive contributions from many complementary supports;
* (Q)-membership need not be determined by the sign of one Perron threshold or one determinant.

Accordingly, the defensible theorem statement is:

> **Partial full-core classification.**
> Up to simultaneous permutation and positive diagonal row and column scaling, the branch ((*)) is completely classified in the four strict derangement sign chambers described above and in the displayed duplicate-class zero stratum. No claim is made for the remaining strict sign chambers or zero patterns.

The original full classification problem remains open after this partial result.
