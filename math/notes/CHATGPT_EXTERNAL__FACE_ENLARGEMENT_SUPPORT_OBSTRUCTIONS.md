# Face enlargement and support obstructions

Author: `CHATGPT_EXTERNAL`

Status: `PROOF_DRAFT`; classification and no-go analysis, not a complete Fin4
consumer.

Source: supplied as `ephemeral/FACE_ENLARGE.md` and moved here without rewriting
the mathematical body.

Three facts decide the proposed enlargement:

1. On a zero-diagonal face, mere nonnegative feasibility can always be tightened until at least one residual is zero.
2. Requiring such feasibility on every principal face is the classical completely-\(S_0\), equivalently semimonotone \(E_0\), condition.
3. A semimonotone \(R_0\) matrix is a standard \(Q\)-matrix; outside \(R_0\), the homogeneous LCP branch already makes the matrix projective \(Q\).

Together, these facts refute the strictness premise—but expose a better quantitative obstruction.

## 1. FaceTangent is exactly projective \(Q\)-bar

Write

$$
S_0(A)
\iff
\exists x\ge 0,\quad x\neq 0,\quad Ax\ge 0,
$$

and

$$
\operatorname{Completely}S_0(M)
\iff
\forall\,\varnothing\neq P,\quad S_0(M_P).
$$

### Tightening lemma

Let \(A\) have zero diagonal. Then

$$
S_0(A)
\iff
\exists \lambda\in\Delta:
A\lambda\ge 0
\quad\text{and}\quad
(A\lambda)_i=0
\text{ for some }i.
\tag{1}
$$

The reverse implication is immediate. For the forward implication, choose a feasible \(x\ge0\), \(x\neq0\), with support of minimum cardinality. Suppose \(Ax>0\) coordinatewise. Pick \(j\in\operatorname{supp}x\) and decrease \(x_j\):

$$
x(t)=x-t e_j.
$$

For rows with \(A_{ij}\le0\), the residual does not decrease. For rows with \(A_{ij}>0\), feasibility is retained while

$$
t\le \frac{(Ax)_i}{A_{ij}}.
$$

The row \(j\) never constrains \(t\), because \(A_{jj}=0\). Increase \(t\) until either a residual becomes zero or \(x_j\) becomes zero. In the second case, unless a residual simultaneously becomes zero, one obtains a feasible nonzero vector with smaller support, contradicting minimality. Normalizing \(x(t)\) proves (1).

Thus, on every zero-diagonal principal face, \(S_0\)-feasibility is already exactly the existing `PrincipalQDirection` information. The repository’s current direction constructor establishes the converse implication from projective \(Q\) on the face.  The normalized singleton matrix is indeed zero diagonal.

### Matrix-class identity

In fact, for every finite real matrix \(M\), without a diagonal assumption,

$$
\boxed{
\operatorname{Completely}S_0(M)
\iff
\operatorname{IsProjectiveQBarMatrix}(M).
}
\tag{2}
$$

For the easy direction, suppose every principal matrix \(A=M_P\) is projective \(Q\). Apply the projective LCP to \(q=-\mathbf 1\). If its cemetery mass is \(c\) and its singleton vector is \(z\), then

$$
Az-c\mathbf 1\ge0.
$$

The total-mass equation rules out \(z=0\), so \(z\neq0\), \(z\ge0\), and \(Az\ge0\). Hence \(A\in S_0\).

Conversely, if every principal submatrix of \(A=M_P\) is \(S_0\), then \(A\) is semimonotone \(E_0\). This is the classical characterization of semimonotone matrices by complete \(S_0\)-ness. If \(A\) is \(R_0\), Pang’s theorem gives \(A\in Q\). If \(A\) is not \(R_0\), it has a nonzero solution of \(\operatorname{LCP}(A,0)\); after normalization, that is exactly a homogeneous simplex solution. ([DOI][1])

The repository already proves the exact convention split

$$
\operatorname{ProjectiveQ}(A)
\iff
\operatorname{StandardQ}(A)
\ \lor\
\operatorname{HomogeneousSimplex}(A).
$$

Combining (1) and (2),

$$
\boxed{
\operatorname{FaceTangent}(M)
\iff
\operatorname{IsProjectiveQBarMatrix}(M)
}
\tag{3}
$$

for every finite zero-diagonal matrix.

Consequently, the requested rational example

$$
\operatorname{FaceTangent}(M)
\land
\neg\operatorname{IsProjectiveQBarMatrix}(M)
$$

does not exist—not for \(\operatorname{Fin}4\), and not in any finite dimension. Refactoring the clock construction through a face-direction provider may improve its API, but it cannot enlarge the theorem’s matrix class.

## 2. The right replacement is a strict dual blocker

The failed enlargement nevertheless has a useful exact dual.

For a nonempty face \(P\), define its tangent value

$$
\vartheta_P
:=
\max_{\lambda\in\Delta(P)}
\min_{i\in P}(M_P\lambda)_i.
\tag{4}
$$

Finite minimax gives the dual formula

$$
\vartheta_P
=
\min_{y\in\Delta(P)}
\max_{j\in P}(M_P^\top y)_j.
\tag{5}
$$

The face is feasible precisely when \(\vartheta_P\ge0\). If it is bad, then \(\vartheta_P<0\). Taking a dual optimizer and putting \(\eta_P=-\vartheta_P\) yields

$$
y\in\Delta(P),\qquad
\eta_P>0,\qquad
\sum_{i\in P}y_iM_{ij}\le-\eta_P
\quad(j\in P).
\tag{6}
$$

Call \((y,\eta_P)\) a **strict principal blocker**.

This gives the exact finite alternative

$$
\boxed{
\begin{aligned}
&\exists\lambda\in\Delta(P),\ M_P\lambda\ge0
\\
&\qquad\lor
\\
&\exists y\in\Delta(P),\ \eta>0,\ 
M_P^\top y\le-\eta\mathbf1 .
\end{aligned}}
\tag{7}
$$

The alternatives are mutually exclusive. For rational \(M\), \(y\) and \(\eta\) can be chosen rational, since (4)–(5) are rational linear programs.

Combining (3), (7), and the existing punishment-normal Snell consumer gives, in the current all-punishment-normal Fin4 chamber, the mathematically exact split

$$
\boxed{
\begin{aligned}
&\exists v,\quad v\text{ is a uniform-equilibrium payoff}
\\
&\qquad\lor
\\
&\exists\,\varnothing\neq P,\ y\in\Delta(P),\ \eta>0:
\quad
\forall j\in P,\ 
\sum_{i\in P}y_iM_{ij}\le-\eta .
\end{aligned}}
\tag{8}
$$

The first arm is exactly the existing Snell theorem.  The second arm is substantially more informative than “some principal matrix is nonprojective”: it gives a normalized rational covector and a positive margin.

## 3. The full-support packet forces a rank-increasing escape

Now use information specific to the present hard residual.

Let \(p\in\Delta(I)\) be the quantitatively full-support singleton packet. Full support and the packet’s target-pinning condition imply that its target equals each player’s own singleton payoff. Its mixture inequality therefore says

$$
Mp\ge0.
\tag{9}
$$

Take a bad face \(P\) with blocker \((y,\eta)\). Write

$$
p(P)=\sum_{j\in P}p_j.
$$

Using (6),

$$
\sum_{j\in P}p_j\,y^\top M_{P,j}
\le
-\eta p(P).
$$

But (9), tested against \(y\), gives

$$
0
\le
y^\top(Mp)_P
=
\sum_{j\in P}p_j\,y^\top M_{P,j}
+
\sum_{j\notin P}p_j\,y^\top M_{P,j}.
$$

Hence

$$
\boxed{
\sum_{j\notin P}p_j\,y^\top M_{P,j}
\ge
\eta p(P).
}
\tag{10}
$$

Several consequences follow immediately.

First, \(P\neq I\): the full face cannot be bad. Second, some outside owner \(j\notin P\) satisfies

$$
y^\top M_{P,j}
\ge
\eta\frac{p(P)}{p(P^c)}
>0.
\tag{11}
$$

Therefore some \(i\in P\) satisfies

$$
M_{ij}
\ge
\eta\frac{p(P)}{p(P^c)}
>0.
\tag{12}
$$

So every bad face has a quantitatively positive **outside singleton helper**.

This yields a finite matrix-level itinerary:

$$
P=P_0\subsetneq P_1\subsetneq\cdots\subseteq P_k,
\qquad
P_{\ell+1}=P_\ell\cup\{j_\ell\},
\tag{13}
$$

where every bad \(P_\ell\) carries a strict blocker and an outside helper \(j_\ell\), and \(P_k\) is good. The process stops after at most \(|I\setminus P|\) steps because the full face is good by (9).

This is the finite rank that the proposed hybrid program was missing:

$$
\boxed{
\text{good tangent}
\quad\lor\quad
\text{blocker-certified outside exit with }
|I\setminus P|\text{ strictly decreasing}.
}
\tag{14}
$$

For a bad three-player face in Fin4, the helper is necessarily the unique fourth player. For a bad pair, one of the two outside players satisfies (11). Thus the table-level helper ambiguity is already sharply bounded.

The important limitation is provenance: (10)–(14) are packet-level algebra. They do not attach the helper column to a literal minimum-law source. That is now the only reason this finite rank does not immediately compile into the strategic path.

## 4. A bad face imposes a first-order collision tax

The blocker also identifies exactly what a source-matched reset must pay.

Let \(x\ge0\) be singleton mass supported on \(P\), and put

$$
s=\sum_{j\in P}x_j.
$$

From (6),

$$
y^\top M_Px
=
\sum_{j\in P}x_j\,y^\top M_{P,j}
\le
-\eta s.
\tag{15}
$$

Suppose a collision/reset correction \(c\) and a coordinatewise error \(\delta\) make the step inward:

$$
M_Px+c\ge-\delta\mathbf1.
\tag{16}
$$

Multiplying by \(y\in\Delta(P)\) and using (15) gives

$$
\boxed{
y^\top c\ge\eta s-\delta.
}
\tag{17}
$$

Thus a bad face charges at least \(\eta\) units of blocker-weighted nonsingleton correction per unit of internal singleton clock mass. This is not an arbitrary Lyapunov function: it is the optimal dual obstruction to the failed tangent LP.

There is also a sharp small-hazard consequence. Split a local quit-rate vector into internal and outside masses,

$$
s=\sum_{j\in P}q_j,\qquad
o=\sum_{j\notin P}q_j,\qquad
h=s+o.
$$

Let

$$
B_P:=\max_{j\notin P}\max(0,y^\top M_{P,j}),
$$

and suppose the nonlinear collision/Bellman correction obeys

$$
y^\top c\le Ch^2
$$

while the local inward error is at most \(\delta\). Then

$$
\boxed{
\eta s\le B_Po+Ch^2+\delta.
}
\tag{18}
$$

Consequently:

* If \(o=0\) and \(\delta\le\eta h/2\), then either \(h=0\) or

  $$
  h\ge\frac{\eta}{2C}.
  $$

  An internal bad-face exit cannot occur at vanishing scale; it must be a macroscopic block.

* If

  $$
  h\le\frac{\eta}{4C},
  \qquad
  \delta\le\frac{\eta h}{4},
  $$

  then

  $$
  \frac{o}{h}
  \ge
  \frac{\eta}{2(B_P+\eta)}.
  \tag{19}
  $$

  A fixed positive fraction of first-order hazard must leak to outside players.

Hence the correct local hybrid alternative is

$$
\boxed{
\text{tangent direction}
\quad\lor\quad
\text{rank-increasing outside singleton leakage}
\quad\lor\quad
\text{linear-scale/macroscopic collision}.
}
\tag{20}
$$

The first-order versus quadratic distinction is important. The repository already contains the relevant uniform quadratic singleton-linearization estimates for bounded product roots and returned blocks.  A bad-face deficit is linear in \(h\), so an ordinary \(O(h^2)\) collision remainder cannot hide it.

## 5. The same blocker localizes the source-matching requirement to one scalar

Let

$$
b_i=r_i(\{i\}),
\qquad
\kappa_y(S)
:=
\sum_{i\in P}y_i\bigl(r_i(S)-b_i\bigr).
$$

For every active singleton \(j\in P\),

$$
\kappa_y(\{j\})\le-\eta.
\tag{21}
$$

Let \(\mu\) be an actual terminal law with expected payoff \(u\). Partition its outcomes into active singletons and all exits—outside singletons, nonsingletons, and Never. Then the exact identity gives

$$
\boxed{
\sum_{\text{exit }S}\mu(S)\kappa_y(S)
\ge
\eta\sum_{j\in P}\mu(\{j\})
+
y^\top(u_P-b_P).
}
\tag{22}
$$

Thus one does **not** need to attach the entire full-support packet to the literal source. It suffices to control the single scalar anchor defect

$$
y^\top(u_P-b_P).
\tag{23}
$$

If it is at least \(-\delta\), active singleton mass forces blocker-charged exit mass of at least \(\eta\mu_{\rm singleton}-\delta\). If outside singleton and Never exits do not supply this charge, a positively charged nonsingleton coalition must.

This is compatible with the newest checked machinery:

* nonsingleton terminal mass cannot diffuse away over time;
* a selected causal suffix atom retains an actual reached stage atom;
* at that same row, one gets either tail escape or a literal pure-endpoint gain;
* in the gain arm, the mover’s unrestricted behavioral debt drops exactly, another player receives a quantitative debt increase, and the routed coalition retains its mass;
* on a cofinal subsequence, mover, action, routed coalition, and recipient can all be fixed.

What those theorems do not yet prove is that their routed collision pays the blocker quantity \(y^\top c\), or activates the blocker-selected outside helper. The remaining finite-atom theorem can now be stated narrowly:

$$
\boxed{
\begin{array}{c}
\text{at a causal suffix row carrying a bad-face blocker,}
\\[2mm]
\text{outside helper activation}
\ \lor\
\text{tail escape}
\ \lor\
\text{positive blocker-weighted collision charge}.
\end{array}}
\tag{24}
$$

The first arm decreases \(|I\setminus P|\). The third arm accumulates the scalar charge from (17). Therefore uncharged cycling is excluded: rank can fall only finitely many times, while infinitely much bad-face clock mass forces divergent cumulative charge.

That is a substantially stronger target than an unrestricted “collision exit” theorem.

## Lean boundary

The natural formal declarations are now:

```lean
structure PrincipalS0Direction (M) (P)
structure PrincipalStrictBlocker (M) (P)

theorem principalS0Direction_or_strictBlocker
theorem principalQDirection_iff_s0Direction_of_diagonal_zero
theorem isProjectiveQBarMatrix_iff_completelyS0
theorem faceTangent_iff_projectiveQBar_of_diagonal_zero

theorem PrincipalStrictBlocker.outsideHelper_of_fullSupportDirection
theorem PrincipalStrictBlocker.collisionTax
theorem exists_uniformEquilibriumPayoff_or_punishmentNormalStrictBlocker_snell
```

The finite minimax alternative, zero-diagonal tightening, outside-helper theorem, and collision-tax inequality are elementary finite-dimensional targets. The equivalence with projective \(Q\)-bar additionally requires formalizing the semimonotone \(E_0\cap R_0\subseteq Q\) theorem or an equivalent LCP argument.

No source was edited or compiled in this turn. Under the project’s runbook terminology, the results above are mathematical derivations and a formalization plan, not yet Lean-checked declarations. 

[1]: https://doi.org/10.1016%2Fj.laa.2019.05.009 "https://doi.org/10.1016%2Fj.laa.2019.05.009"
