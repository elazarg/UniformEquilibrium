# The strict descendant port has one asymptotic passport and a prescribed-root equality gate

Identity: `CODEX_DESCENDANT`  
Date: 2026-08-31  
Status: **ordinary-mathematics sharpening, not a consumer.**  The tail-hull
projective identity, density minimization, root-defect barrier, and
prescribed-payoff equality classification are proved below.  An exact
four-player table shows that the exported local fields do not retain the
stronger common-response curl present before atom decoding.  The remaining
outputs are a one-host/full-screening passport-loss boundary or a
singleton-tight one-debtor gate; neither is currently a uniform-equilibrium
compiler or renewable finite rank.

## 1. Question

Start with the strict alternative in
`formalized/FOUR_PROFILE_DESCENDANT_SLICE_NEUTRALIZATION.md`.  Thus a closed
common-prefix descendant carrier contains four coordinates

\[
(R,Q,E,S),
\]

where:

* \(R,Q\) carry a positive signed terminal-law atom for observer \(j\);
* \(E,S\) carry a positive actual payoff gain for mover \(p\);
* \(R\) has zero \(j\)-debt;
* \(D(R)>D_*>0\); and
* all Continue is the unique exact product root at \(B(R)\).

A second unique-all-Continue point \(m\) is stored externally.  No equality
of laws, ancestry, or chronology between \(m\) and \(R\) is available and
none is used here.

Can the two positive passports consume this port?  The answer obtained here
is negative but sharper:

1. on the asymptotic tail descendant hull, the two passports are exactly
   proportional, so they provide only one normalized density;
2. repeated minimization of that density gives either complete passport loss
   or a global fixed-cap root-defect barrier; and
3. at a barrier point, every exact root against the prescribed payoff is
   either all Continue or an exact singleton-tight solo root carried by the
   unique debtor.

The final solo gate is already known as a difficult conditional chamber.  No
consumer is produced.

## 2. Exact small regression first

The following table realizes all displayed **target-side local fields** of
the strict four-profile port, with the stronger choice \(m=R\), and also
realizes the root-defect barrier derived later in Section 5.  It does not
realize the positive-minimum tangent-source provenance: its global minimum is
zero.  It therefore tests the exact local interface rather than the hard
residual.

Let the players be \(0,1,2,3\), put \(h=0\), \(p=2\), \(j=3\), and define
for \(i=0,1,2\)

\[
r_i(C)=
\begin{cases}
-1,&i\in C,\\
0,&i\notin C.
\end{cases}
\tag{2.1}
\]

Fix \(\kappa\in\{0,1\}\).  For player \(3\), put

\[
r_3(C)=
\begin{cases}
-1,&3\notin C,\\
-2-\kappa,&C=\{0,3\},\\
-2,&3\in C\text{ and }C\ne\{0,3\}.
\end{cases}
\tag{2.2}
\]

Take four date-zero pure profiles:

\[
S:\ \{0,2,3\}\text{ Quits},
\qquad
E:\ \{0,3\}\text{ Quits},
\qquad
Q:\ \{0,2\}\text{ Quits},
\qquad
R:\ \{0\}\text{ Quits}.
\tag{2.3}
\]

The observer's common response is Never: it changes player \(3\) from Quit
to Continue in both \(E\to R\) and \(S\to Q\).  The mover replacement
changes player \(2\) from Quit in \(S\) to Continue in \(E\), and the same
replacement takes \(Q\) to \(R\).

At \(R\),

\[
U(R)=(-1,0,0,-1),
\qquad
B(R)=(0,0,0,-1),
\qquad
d(R)=(1,0,0,0).
\tag{2.4}
\]

Thus \(D(R)=1\) and \(d_3(R)=0\).  Against \(B(R)\), Continue strictly
dominates Quit for every player at every pure opponent corner:

* for \(i=0,1,2\), joining any opponent coalition lowers payoff from \(0\)
  to \(-1\), and singleton Quit pays \(-1< B_i(R)=0\);
* for player \(3\), Continue pays \(-1\), while Quit pays \(-2\) except
  against the pure opponent coalition \(\{0\}\), where it pays
  \(-2-\kappa\).

Hence all Continue is the unique exact product root at \(B(R)\).
More precisely, if \(q_i\) is player \(i\)'s Quit probability, then the
total root defect is

\[
R(q;B(R))\ge\sum_iq_i
\ge 1-\prod_i(1-q_i)
=D(R)\operatorname{Abs}(q).
\tag{2.5}
\]

Thus the later fixed-cap barrier is already exact in this regression.

The two passports are both positive.  At terminal \(T=\{0,2\}\), the
unscaled signed atom is

\[
(\mu_R(T)-\mu_Q(T))r_3(T)=(0-1)\cdot(-1)=1,
\tag{2.6}
\]

The exported normalization in (3.1) uses \(K=16\), so its signed passport
in this regression is \(A=16\).  This harmless fixed factor does not affect
the comparison with the mover gain or any barrier conclusion.

while the mover gain is

\[
U_2(E)-U_2(S)=0-(-1)=1.
\tag{2.7}
\]

Nevertheless all Never is an exact terminal Nash profile and has debt zero.
The table is not a counterexample.

This regression proves two exact fences.

1. The strict port's target-side local data, even with \(m=R\) and the full
   root-defect barrier, do not imply a terminal contradiction without
   positive global-minimum source provenance.
2. The stronger common-response rectangle curl is

   \[
   [U_j(R)-U_j(E)]-[U_j(Q)-U_j(S)]
   =(1+\kappa)-1=\kappa.
   \tag{2.8}
   \]

   The \(\kappa=0\) table proves that the exported atom and gain passports do
   not imply the positive aggregate curl from the upstream
   `QuittingStoppingLawCommonResponseWitness`.  The \(\kappa=1\) table proves
   that adding that positive curl still does not yield a local contradiction,
   even in the presence of the exact barrier.  Both variants have
   \(D_*=0\); what they omit is positive-minimum source provenance.

## 3. The asymptotic tail hull

Return to the actual exported source.  At empty-word rank \(n\), write

\[
A_n=K(\mu_{R_n}(T)-\mu_{Q_n}(T))r_j(T),
\qquad
G_n=U_p(E_n)-U_p(S_n),
\tag{3.1}
\]

and suppose, on the common selected subsequence,

\[
A_n\longrightarrow A_\infty>0,
\qquad
G_n\longrightarrow G_\infty>0,
\qquad
D(R_n)\longrightarrow L>0.
\tag{3.2}
\]

The first convergence follows from convergence of the two laws and the fixed
terminal label; its positive limit follows from the uniform signed-atom
bound.  The second is
`fullReplacementPrescribedGain_tendsto_baseDebt` on the same strict rank
map.

For \(N\in\mathbb N\), let \(\mathcal O_N\) consist of the fourfold points
obtained from ranks \(n\ge N\) after an arbitrary finite common product-root
word, and put

\[
\mathcal K_\infty=
\bigcap_{N\ge0}\overline{\mathcal O_N}.
\tag{3.3}
\]

The sets in the intersection are nested nonempty compact sets, so
\(\mathcal K_\infty\) is nonempty and compact.  The empty-word cluster is in
every tail closure.  Prefixing by any fixed root preserves every
\(\overline{\mathcal O_N}\), hence preserves \(\mathcal K_\infty\).

### Theorem 3.1 (projective passport collapse)

Put

\[
\rho={A_\infty\over G_\infty}>0.
\]

Then every \(X\in\mathcal K_\infty\) satisfies

\[
\boxed{A(X)=\rho G(X).}
\tag{3.4}
\]

#### Proof

Approximate \(X\) by raw points with ranks \(n_k\ge k\) and common words
\(W_k\).  If \(c_k\in[0,1]\) is the joint survival of \(W_k\), exact common
prefix scaling gives

\[
A(W_k\star X_{n_k})-\rho G(W_k\star X_{n_k})
=c_k(A_{n_k}-\rho G_{n_k})\longrightarrow0.
\]

Continuity gives (3.4).  No division by the possibly vanishing \(c_k\) is
used.  \(\square\)

Thus the two positive coordinates are source-distinct but geometrically
one-dimensional on the asymptotic descendant hull.

## 4. One-density minimization without the zero-debt face

Let \(X_0\in\mathcal K_\infty\) be the empty-word cluster, and write

\[
A_0=A(X_0)>0,
\qquad D_0=D(X_0^R)>0.
\]

For any \(0<\alpha<A_0/D_0\), define

\[
\mathcal S_\alpha=
\{X\in\mathcal K_\infty:A(X)\ge\alpha D(X^R)\}.
\tag{4.1}
\]

This drops the equation \(d_j(X^R)=0\).  That loss is deliberate: it makes
the slice invariant enough to test every arbitrary root, not only roots with
zero observer defect.  The initial point lies in the slice, so it is compact
and nonempty.  Choose a minimizer \(Y_\alpha\), and write

\[
D_\alpha=D(Y_\alpha^R),
\quad A_\alpha=A(Y_\alpha),
\quad s_\alpha=A_\alpha-\alpha D_\alpha\ge0.
\tag{4.2}
\]

For a product root \(q\), let

\[
c(q)=\Pr_q(\mathbf C),
\quad a(q)=1-c(q),
\quad R(q)=\text{total root Nash defect against }B(Y_\alpha^R).
\]

The exact prefix identities give

\[
D(q\star Y_\alpha^R)=cD_\alpha+R(q),
\qquad
A(q\star Y_\alpha)=cA_\alpha.
\tag{4.3}
\]

Hence the prefixed point remains in \(\mathcal S_\alpha\) exactly when

\[
\alpha R(q)\le c s_\alpha.
\tag{4.4}
\]

Whenever (4.4) holds, minimality implies

\[
R(q)\ge a(q)D_\alpha.
\tag{4.5}
\]

Splitting on (4.4) yields the global inequality

\[
\boxed{
R(q)\ge
\min\left\{a(q)D_\alpha,{c(q)s_\alpha\over\alpha}\right\}.
}
\tag{4.6}
\]

If \(s_\alpha>0\), then every root with

\[
a(q)\le {s_\alpha\over A_\alpha}
\tag{4.7}
\]

satisfies the linear toll

\[
\boxed{R(q)\ge a(q)D_\alpha.}
\tag{4.8}
\]

Indeed, if \(R<aD_\alpha\), then
\(\alpha R<\alpha aD_\alpha\le(1-a)s_\alpha=cs_\alpha\),
where the middle inequality is equivalent to \(aA_\alpha\le s_\alpha\).
This makes (4.4) strict and contradicts minimality.

In particular every exact cap--Nash root at \(B(Y_\alpha^R)\) is all
Continue: for an exact root \(R(q)=0\), the prefixed point stays in the
slice, and minimality gives \(D_\alpha\le cD_\alpha\); positivity of
\(D_\alpha\) forces \(c=1\).  Finite root-game Nash existence shows that
all Continue itself is exact.

If \(s_\alpha=0\), the passport is saturated.  By (3.4), both passports are
saturated together.  For the canonical choice

\[
\alpha={A_0\over2D_0},
\]

saturation gives

\[
A_\alpha\le {A_0\over2},
\qquad
G(Y_\alpha)\le {G(X_0)\over2}.
\tag{4.9}
\]

This is not a finite rank: both positive real coordinates may be halved
indefinitely.

## 5. Density to zero

Let

\[
\alpha_n={A_0/D_0\over n+2},
\]

and choose a debt minimizer \(Y_n\) of each \(\mathcal S_{\alpha_n}\).  Put

\[
u_n={\alpha_nD(Y_n^R)\over A(Y_n)}\in(0,1].
\tag{5.1}
\]

After one common subsequence, use compactness of both factors to arrange

\[
Y_n\longrightarrow Y_\infty,
\qquad
u_n\longrightarrow u_\infty\in[0,1].
\]

There are two exhaustive cases.

### 5.1 Nonvanishing utilization

If \(u_\infty>0\), then \(u_n\ge\varepsilon>0\) eventually for some
\(\varepsilon\), and boundedness of debt gives

\[
A(Y_n)\le {\alpha_nD(Y_n^R)\over\varepsilon}\longrightarrow0.
\]

Thus, by (3.4),

\[
\boxed{A(Y_\infty)=G(Y_\infty)=0.}
\tag{5.2}
\]

The limiting point has lost both passports.

### 5.2 Vanishing utilization

If \(u_\infty=0\), equivalently \(u_n\to0\) on the selected subsequence,
the radius in (4.7) is

\[
{s_{\alpha_n}\over A(Y_n)}=1-u_n\longrightarrow1.
\]

For every fixed product root of absorption below one, (4.8) eventually
applies.  Continuity and then approximation of full-absorption roots give

\[
\boxed{
R(q;B(Y_\infty^R))
\ge D(Y_\infty^R)\operatorname{Abs}(q)
\quad\text{for every product root }q.
}
\tag{5.3}
\]

This is a fixed-cap barrier.  It says

\[
D(q\star Y_\infty^R)\ge D(Y_\infty^R)
\tag{5.4}
\]

for every one-date product prefix.  It is the opposite polarity from an
approximate Nash--Bellman chronology: positive absorption must be paid by at
least proportional root defect.

The minimum-fibre possibility must be dispatched before calling either case
inert.  If a selected cluster has debt \(D_*\) and retains a positive
passport, it re-enters the global minimum chamber classification.  The
argument here does not claim that it preserves the old zero observer.

### 5.3 Exact anatomy of passport loss

The first arm (5.2) is not an undifferentiated compactness loss.  Let raw
descendants of ranks \(n_k\to\infty\) and common words \(W_k\) converge to a
point with \(A=0\).  Write \(c_k\) for the joint survival of \(W_k\).  Since
the unprefixed signed atoms satisfy \(A_{n_k}\ge\gamma>0\),

\[
0\leftarrow A(W_k\star X_{n_k})=c_kA_{n_k}
\quad\Longrightarrow\quad c_k\longrightarrow0.
\tag{5.5}
\]

For player \(i\), let \(P_{i,k}\) be its own survival through \(W_k\), and
let

\[
H_{i,k}=\prod_{r\ne i}P_{r,k}
\tag{5.6}
\]

be its opponent-deleted survival.  Pass to a subsequence on which all four
\(P_{i,k}\) converge, and let \(Z\) be the nonempty set of coordinates whose
limits are zero.  There are exactly two forms.

* If \(|Z|\ge2\), then \(H_{i,k}\to0\) for every player \(i\).  Common-prefix
  coupling implies that all four prescribed-payoff vectors, all four cap
  vectors, and all four complete terminal laws coalesce.  The limiting
  four-profile point is diagonal.
* If \(Z=\{h\}\), then \(H_{h,k}\) has a positive limit and
  \(H_{i,k}\to0\) for \(i\ne h\).  The four laws and prescribed payoffs still
  coalesce, and every cap coordinate except possibly \(B_h\) coalesces.  All
  surviving four-profile variation is confined to one counterfactual cap
  coordinate.

Indeed, prescribed-payoff and terminal-law differences behind a common word
are multiplied by \(c_k\).  If rewards are bounded in absolute value by
\(M\), the unrestricted cap difference in coordinate \(i\) is at most
\(2M H_{i,k}\): after an arbitrary replacement of \(i\), the two tails can
be distinguished only if every opponent survives the word.  This is the
same deleted-survival estimate used by the checked actual-Zeno
coalescence modules.

The one-host arm also has a literal regeneration operation.  Force \(h\) to
Continue throughout \(W_k\), leaving the base four profiles untouched.  The
new common word has survival exactly \(H_{h,k}\), so both passports are
restored at a fixed positive scale:

\[
A(W_k^{-h}\star X_{n_k})=H_{h,k}A_{n_k},
\qquad
G(W_k^{-h}\star X_{n_k})=H_{h,k}G_{n_k}.
\tag{5.7}
\]

This is an actual source-attached quartet in the same arbitrary-word
carrier.  It is not a consumer: host clearing need not preserve debt
minimality, the zero-observer face, or exact-root rigidity.  In the
multi-clock arm, even absolute coalescence is not charge-relative
coalescence; \(H_{i,k}/c_k\) may diverge.  Thus neither arm supplies the
\(o(\text{charge})\) seam needed for replay.

## 6. Exact prescribed-payoff classification at the barrier

Let \(y=(U,B)\) be a semantic carrier point satisfying (5.3), put

\[
d_i=B_i-U_i,
\qquad D=\sum_i d_i>0,
\]

and let \(q\) be exact product-root Nash against the **prescribed payoff**
\(U\).  Write \(q_i\) for player \(i\)'s Quit probability,

\[
s_i=\prod_{h\ne i}(1-q_h),
\qquad
m_i=q_is_i,
\qquad
a=1-\prod_i(1-q_i).
\]

Here \(m_i\) is the probability that \(i\) is the unique quitter.

### Lemma 6.1

The total root defect against \(B\) obeys

\[
R(q;B)\le\sum_i m_i d_i\le D\sum_i m_i\le Da.
\tag{6.1}
\]

#### Proof

For player \(i\), changing the continuation vector from \(U\) to \(B\)
raises the Continue endpoint by exactly \(s_id_i\) and leaves the Quit
endpoint unchanged.  Exactness against \(U\) gives:

* zero defect against \(B\) if \(q_i=0\);
* defect \(q_is_id_i\) if \(0<q_i<1\); and
* defect at most \(s_id_i\) if \(q_i=1\).

Summing gives the first inequality.  The second uses \(d_i\le D\), and the
third uses that singleton-quitter mass is at most total absorption.  \(\square\)

The barrier (5.3) makes every inequality in (6.1) an equality.

### Theorem 6.2 (all Continue or singleton-tight unique debtor)

Every exact root against \(U\) is either all Continue, or there is one player
\(h\) such that

\[
q_h>0,
\qquad q_i=0\ (i\ne h),
\qquad d_h=D,
\qquad d_i=0\ (i\ne h),
\tag{6.2}
\]

\[
U_h=r_h(\{h\}),
\tag{6.3}
\]

and, for every \(i\ne h\),

\[
 (1-q_h)\bigl(U_i-r_i(\{i\})\bigr)
 +q_h\bigl(r_i(\{h\})-r_i(\{h,i\})\bigr)\ge0.
\tag{6.4}
\]

When \(q_h=1\), (6.4) reduces to
\(r_i(\{h,i\})\le r_i(\{h\})\).  For a genuinely mixed solo root, no
pointwise collision sign is asserted.

#### Proof

If \(a=0\), the root is all Continue.  If \(a>0\), equality
\(\sum_i m_i=a\) says there is no collision mass.  Independence then forces
at most one positive Quit probability, say \(q_h>0\).  Equality
\(\sum_i m_id_i=Da\) gives \(d_h=D\), hence all other debts vanish.

If \(0<q_h<1\), player \(h\)'s exact mixing against \(U\) gives
\(r_h(\{h\})=U_h\).  If \(q_h=1\), equality in the cap-root defect bound is

\[
B_h-r_h(\{h\})=D=B_h-U_h,
\]

which gives the same identity.  Every other player Continues against the
Bernoulli solo clock of \(h\); expanding its exact-root inequality gives
(6.4).  \(\square\)

Finite root-game Nash existence at \(U\) therefore gives the following
exhaustive, inclusive barrier alternative (both arms may hold):

\[
\boxed{
\begin{array}{c}
\text{all Continue is exact against both }U\text{ and }B,\\
\text{or the positive-debt support is the singleton }\{h\}\text{ and}\\
\text{an exact singleton-tight one-player-supported root exists against }U.
\end{array}}
\tag{6.5}
\]

If at least two debt coordinates are positive, the first arm is forced and
all Continue is the unique exact root against \(U\) as well as against \(B\).

### 6.3 Finite pure-coalition obstruction

The barrier also has a completely finite reward-table shadow.  For every
nonempty coalition \(C\), let \(\Phi_B(C)\) be the total positive unilateral
toggle gain at the pure root \(C\).  Explicitly, if \(|C|\ge2\),

\[
\Phi_B(C)=
\sum_{i\in C}\bigl(r_i(C\setminus\{i\})-r_i(C)\bigr)_+
+\sum_{i\notin C}\bigl(r_i(C\cup\{i\})-r_i(C)\bigr)_+,
\tag{6.6}
\]

whereas for a singleton \(C=\{h\}\),

\[
\Phi_B(\{h\})=
B_h-r_h(\{h\})
+\sum_{i\ne h}
  \bigl(r_i(\{h,i\})-r_i(\{h\})\bigr)_+.
\tag{6.7}
\]

The first term in (6.7) is nonnegative because all Continue is exact against
\(B\).  A pure coalition root has absorption one and root defect exactly
\(\Phi_B(C)\).  Therefore (5.3) gives the fifteen explicit inequalities

\[
\boxed{\Phi_B(C)\ge D\qquad(C\ne\varnothing).}
\tag{6.8}
\]

In particular every nonsingleton has a strict toggle of size at least
\(D/4\).  At a singleton \(\{h\}\), either

\[
B_h-r_h(\{h\})\ge D/2,
\tag{6.9}
\]

or one outsider has a strict join gain at least \(D/6\).  Iterating these
finite choices gives an exact alternative:

\[
\boxed{
\text{an executable singleton-owner response gain greater than }D/4,
\quad\text{or a strict nonempty toggle cycle with edge floor }D/6.}
\tag{6.10}
\]

In the first arm, choose a response within \(D/4\) of the cap.  It may be an
arbitrary behavioral response rather than a one-stage Quit action.  The second is the broader
singleton/pair-containing Boolean cycle, not the checked nonsingleton
monodromy leaf.  Such broader cycles are not ruled out by the existing
period-two argument, and their horizontal profiles are not successive dates
of one chronology.  Thus (6.10) is a finite falsifiable obstruction, not a
consumer.  Under the full Fin4 hard residual, the terminal-gap singleton
collision theorem already supplies a strict outsider join at every
singleton, so this specializes to the known broad all-nonempty toggle-cycle
obstruction, now with the additional barrier-derived quantitative floor.

## 7. The omitted common-response curl

The upstream theorem
`exists_quittingStoppingLawCommonResponseWitness_of_endpointDebtRise` stores
more than the exported rectangle sequence.  Before terminal-coordinate
decoding, its four literal profiles satisfy

\[
[U_j(R_n)-U_j(E_n)]-[U_j(Q_n)-U_j(S_n)]
\ge c-o(1)>0.
\tag{7.1}
\]

That aggregate curl is not a field of
`QuittingStoppingLawVanishingDebtRectangleSequence`; the structure retains
only one positive terminal coordinate and vanishing endpoint debt.  The
\(\kappa=0\) regression in Section 2 satisfies every displayed target-side
local field of the strict port while making (7.1) zero.  Consequently no
theorem from the exported port alone may use (7.1).

A source strengthening is mathematically available: retain the actual
`QuittingStoppingLawCommonResponseWitness` at the same ranks as the decoded
terminal atom.  Under common prefixing, the four payoff terms in (7.1) have
identical fresh-root contributions, so their rectangle curl scales by joint
survival just like \(A\) and \(G\).  This would yield a stronger
closed-descendant port carrying a positive response curl.  It would still
need a consumer; positivity of a static payoff square is not by itself an
ordered Nash--Bellman chronology.  The \(\kappa=1\) variant in Section 2
already realizes positive curl together with the exact root barrier and
unique all-Continue cap root at a zero-global-minimum table.  Any successful
curl consumer must therefore use the positive-minimum source provenance, not
only the strengthened local quartet.

## 8. Conclusion and next question

The strict four-profile port does not currently close.  Its sharpest proved
tail reduction is

\[
\boxed{
\begin{array}{c}
\text{minimum-fibre chamber return},\\
\text{or vanishing passports with one-host regeneration or full screening},\\
\text{or a fixed-cap barrier whose prescribed-payoff roots are}\\
\text{all Continue or singleton-tight unique-debtor solo roots.}
\end{array}}
\tag{8.1}
\]

The next concrete question is two-part.

1. Can positive-minimum source provenance exclude the vanishing-passport
   fully screened tail hull?  The one-host part already regenerates a
   positive-passport quartet, but does not preserve the minimizing face.
2. In the barrier arm, can the singleton-tight unique-debtor solo gate be
   consumed without assuming the induced-owner HOPF sign?  Existing exact
   regressions show that the forced pair and one-debtor data alone do not
   determine that sign.

A parallel source question is whether retaining (7.1) supplies a new
finite-rank response face or only a third scalar passport on the same
projective ray.

## 9. Proof audit and Lean handoff boundary

Three proof points were rechecked separately.

### 9.1 Arbitrary-root debt ledger

Equation (4.3) is not an inferred Bellman approximation.  It is the exact
checked identity
`prefixMap_wholeDebt_eq_continueMass_mul_add_capDefect`:

\[
D(q\star y)=\operatorname{Cont}(q)D(y)
 +\operatorname{RootDefect}(B(y),q).
\]

It holds for every product root, with no Nash hypothesis.  The law-difference
and payoff-gain passports have exact common-prefix scaling by the same joint
Continue factor.  Therefore (4.4)--(4.8) use one and the same root and one and
the same prefixed four-profile point; no semantic replacement is inserted.

### 9.2 Full-absorption roots

The limiting argument first proves (5.3) for roots with positive Continue
mass.  A root of Continue mass zero is approached by multiplying every Quit
probability by \(1-\varepsilon\).  Every approximant has positive Continue
mass and converges in the finite root simplex.  Both absorption and total
root defect are continuous there, so the inequality passes to the original
root.  This is exactly the tremble argument already checked in
`NormalizedPassportVanishingDensityBoundary.lean`; no division by Continue
mass occurs.

### 9.3 Equality classification

For an exact root against \(U\), changing only the continuation vector from
\(U\) to \(B=U+d\) raises player \(i\)'s Continue endpoint by precisely
\(s_i d_i\).  The three cases \(q_i=0\), \(0<q_i<1\), and \(q_i=1\) give the
first inequality of (6.1).  Combining it with the barrier gives

\[
Da\le R(q;B)\le\sum_i m_id_i\le D\sum_i m_i\le Da.
\]

Thus every inequality is equality.  Positive absorption and
\(\sum_i m_i=a\) exclude collision mass, hence leave one positive product
coordinate.  Equality in the debt-weighted average then forces that
coordinate to carry all debt.  The singleton-tight identity follows from
mixing indifference when \(q_h<1\), and from equality in the \(q_h=1\)
defect bound otherwise.  No collision sign is inferred in the mixed solo
case; only (6.4) is valid.

The following parts still require new Lean declarations if this line is to
be integrated:

1. the four-profile tail carrier and the asymptotic ratio identity (3.4),
   because the two base passports are only asymptotically proportional;
2. the adapter from that carrier to the checked single-density minimizer and
   vanishing-density boundary;
3. the equality classifier (6.1)--(6.5) and pure-coalition corollary
   (6.6)--(6.10); and
4. the Section 5.3 four-profile host/full-screening adapter.

The underlying debt ledger, one-density tent inequality, Continue-tremble
passage, arbitrary-word payoff/law scaling, and deleted-survival cap bounds
are already named checked results.  Section 7 is only a proposed stronger
source interface; no consumer or Lean theorem is claimed for it.

## 10. Sources inspected

* `formalized/FOUR_PROFILE_DESCENDANT_SLICE_NEUTRALIZATION.md`;
* `questions/FIN4_FULL_DEBT_CHAMBER_CONSUMER.md`;
* `notes/CODEX_RIEMANN__NORMALIZED_INERT_SINGLE_DENSITY_TOLL.md`;
* `notes/CODEX_ROOT__PRESCRIBED_PAYOFF_ROOT_LIFTING.md`;
* `notes/CODEX_CURIE__UNIQUE_DEBTOR_RECYCLE_DOES_NOT_PRODUCE_HOPF_SIGN.md`;
* `notes/CODEX_GATE__VANISHING_RESPONSE_MAXROOT_RESET_TRICHOTOMY.md`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/OffDiagonal/AtomRectangleSequenceAlternative.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PositiveTotalSlopeFullReplacement.lean`;
* `Research/Quitting/NormalizedPassportPrefixOrbit.lean`;
* `Research/Quitting/NormalizedPassportMinimizer.lean`;
* `Research/Quitting/NormalizedPassportVanishingDensityBoundary.lean`;
* `Research/Quitting/FinFourProducerAtlas/ActualZenoHostCompression.lean`;
* `Research/Quitting/FinFourProducerAtlas/ActualZenoFullyScreenedSiblingCoalescence.lean`;
* `notes/ATLAS_GATEKEEPER__SERIAL_NONEMPTY_TOGGLE_DISPATCH_NOT_MONODROMY.md`;
* `Research/Quitting/FinFourProducerAtlas/MonodromyImpossible.lean`; and
* `UniformEquilibrium/Quitting/Root/NashExistence.lean`.

The single-density minimization and density-to-zero barrier are established
generically in the normalized-passport modules.  The projective tail-hull
identity (3.4), needed because the present atom/gain ratio converges rather
than being pointwise constant, and its application to this four-profile
signed-atom quartet were not found in the inspected material.  Section 5.3
specializes the already checked host/full-screening survival algebra to this
four-profile carrier; it does not claim a new terminal consumer.
Section 6 is the direct fixed-barrier specialization of the reviewed
prescribed-payoff root classification: the barrier rules out that
classification's strict-debt-descent arm.  It is included with a direct proof
to make the exact equality conditions and remaining solo gate explicit.
