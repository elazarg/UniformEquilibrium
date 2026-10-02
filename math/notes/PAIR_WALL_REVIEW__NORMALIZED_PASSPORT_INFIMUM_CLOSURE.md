# Normalized-passport closure consumes support entry at a class minimizer

Author: PAIR_WALL_REVIEW

## Status

Complete ordinary-mathematics audit of the normalized-passport infimum idea.

The pointwise class of finite sources with weak density inequalities is not
preserved by an approximate support-entry prefix. The correct object is the
compact class of **limiting source-attached passport tuples**. That class is
closed by a diagonal witness argument, support-entry re-exactification
preserves its normalized mass and gain exactly, and continuous total debt
therefore has a minimizer in the class. At that minimizer every exact
positive-absorption cap root is impossible. Since all Continue is already
exact on a maximal-ray limit, it is the unique exact cap--Nash root.

This consumes the support-entry alternative into an invariant-density unique
all-Continue closure point. It does not consume that remaining inert point or
prove a uniform-equilibrium payoff.

## 1. Why the finite-source class is not closed

Let a source have debt \(D>0\), marked pair mass \(m\), and paid gain \(g\),
and suppose

\[
 m\ge\theta D,\qquad g\ge\phi D.                 \tag{1}
\]

Prefix a fixed root of joint Continue mass \(c>0\) which is only
approximately cap--Nash. If its total cap defect is \(E>0\), the exact
account is

\[
 D_Y=cD+E,\qquad m_Y=cm,\qquad g_Y=cg.           \tag{2}
\]

Consequently

\[
 {m_Y\over D_Y}={cm\over cD+E}<{m\over D},
 \qquad
 {g_Y\over D_Y}={cg\over cD+E}<{g\over D}.       \tag{3}
\]

A subsequent exact cap prefix multiplies all three displayed quantities by
the same survival factor, so it does not repair (3). Thus a source which
saturates either weak inequality in (1) leaves that exact finite-source class
whenever \(E>0\).

For example, take \(D=1\), \(c=1/2\), \(m=\theta\), and \(E_n=1/n\).
Then

\[
 {m_Y\over D_Y}={\theta/2\over1/2+1/n}<\theta
\]

at every finite rank, although the ratio tends to \(\theta\). This is a
counterexample to pointwise class preservation using only the exact identities
available in the proposed construction. Strictly smaller thresholds are
eventually preserved, but consuming fresh slack at every restart does not by
itself give an iteration theorem.

## 2. Limiting source-attached passports

Fix once and for all:

* the original positive global minimum source and its causal chronology;
* a pure pair \(C=\{j,o\}\), marked owner \(o\), and paid mover \(p\);
* the literal post-pair minimum-return requirement;
* the zero marked owner defect and the paid endpoint orientation; and
* positive density thresholds \(\theta,\phi\).

A limiting passport tuple is

\[
 P=(z,m,g),                                      \tag{4}
\]

where \(z\) is a terminal-semantic carrier point and there is a cofinal
source-attached sequence of actual profiles \(X_n\), marked dates \(t_n\),
and literal post-row tails such that:

1. \(\operatorname{Sem}(X_n)\to z\);
2. the marked root is the fixed pure pair \(C\);
3. its unconditional marked mass tends to \(m\);
4. the fixed literal mover gain tends to \(g\);
5. the marked owner defect is zero at every rank;
6. the complete post-row tails return to the original minimum fibre;
7. the retained original source ranks are cofinal; and
8. all Continue is exact cap--Nash against \(z^B\).

Require in addition

\[
 m\ge\theta D(z),\qquad g\ge\phi D(z).           \tag{5}
\]

Call the resulting class \(\mathcal P_{\theta,\phi}\). The gain coordinate is
redundant when it is literally the fixed pure-pair reward gap times the marked
mass, but retaining it makes the transport statement apply to the existing
paid-row wrapper without changing its interface.

The class is nonempty whenever one has an off-minimum canonical ray stall:
take a joint cluster of its actual finite prefixes, together with the limits
of the retained marked mass and gain. Exact maximal-prefix compactification
supplies item 8.

## 3. Sequential closure

The class \(\mathcal P_{\theta,\phi}\) is sequentially closed in

\[
 K_r\times[0,1]\times[0,G_{\max}],               \tag{6}
\]

where \(K_r\) is the compact terminal-semantic carrier and \(G_{\max}\) is
any table-dependent payoff-difference bound.

Indeed, suppose

\[
 (z^k,m^k,g^k)\longrightarrow(z,m,g)
\]

and each tuple has a witnessing source-attached sequence. From the \(k\)-th
witness choose one rank large enough that simultaneously:

* its semantic pair is within \(1/k\) of \(z^k\);
* its marked mass and gain are within \(1/k\) of \(m^k,g^k\);
* its post-row tail debt is within \(1/k\) of \(D_*\);
* every required limiting root-defect field is within \(1/k\) of its stated
  limit; and
* its retained original source rank is at least \(k\).

The diagonal profiles witness \((z,m,g)\). Literal pair labels, owner, mover,
orientation, and post-row equality are preserved because they were fixed
before taking the diagonal. Exactness of all Continue at the limiting cap is
closed under convergence of the cap-Nash inequalities. Finally (5) is closed
because total debt is continuous on \(K_r\) and \(D(z)\ge D_*>0\).

Thus \(\mathcal P_{\theta,\phi}\) is compact. In particular the continuous
map \(P\mapsto D(z_P)\) attains its infimum. This attainment is the step an
ordinary approximate-infimum argument lacks.

## 4. Exact support-entry transport on the limiting class

Let \(P=(z,m,g)\in\mathcal P_{\theta,\phi}\), put \(L=D(z)\), and suppose
there is an exact cap--Nash root \(q\) at \(z^B\) with positive absorption.
Write

\[
 c=\operatorname{Cont}(q)\in(0,1).              \tag{7}
\]

Apply \(q\) literally to a witnessing sequence \(X_n\). Its total cap defect
\(E_n\) at the actual caps tends to zero, so

\[
 D(q*X_n)=cD(X_n)+E_n\longrightarrow cL.        \tag{8}
\]

The marked pair mass and paid gain are exactly multiplied by \(c\):

\[
 m(q*X_n)\longrightarrow cm,\qquad
 g(q*X_n)\longrightarrow cg.                    \tag{9}
\]

Now prefix fresh exact cap--Nash roots at the changed actual caps and continue
outward along their maximal exact rays. Global minimality gives a positive
lower bound on every accumulated survival: if a resulting cluster has debt
\(L'\), then

\[
 D_*\le L'\le cL,\qquad
 \beta:={L'\over cL}>0.                          \tag{10}
\]

Exact cap-prefix scaling multiplies debt, marked mass, and paid gain by the
same \(\beta\). A diagonal maximal-ray cluster therefore has

\[
 (L',m',g')=(\beta cL,\beta cm,\beta cg),        \tag{11}
\]

and hence

\[
 \boxed{{m'\over L'}={m\over L},
 \qquad {g'\over L'}={g\over L}.}                \tag{12}
\]

The fixed pair, owner, mover, post-row tail, and original source cofinality
are unchanged by the common prefixes. The final maximal-ray cluster makes
all Continue exact at its limiting cap. Therefore

\[
 P'=(z',m',g')\in\mathcal P_{\theta,\phi},
 \qquad D(z')=L'\le cL<L.                       \tag{13}
\]

This is closure of the **limiting** passport class under support-entry
re-exactification. It does not assert the false finite-rank inequalities
ruled out in Section 1.

## 5. Minimum-class exclusion of support entry

Choose a minimizer

\[
 P_{\min}=(z_{\min},m_{\min},g_{\min})
 \in\mathcal P_{\theta,\phi}
\]

of total debt. If \(z_{\min}^B\) admitted a positive-absorption exact
cap--Nash root, Section 4 would construct another member of the same class
with strictly smaller debt, contradicting minimality.

But all Continue is exact at \(z_{\min}^B\) by definition of the class, and
a product root has zero absorption exactly when it is all Continue.
Therefore

\[
 \boxed{
 \operatorname{Nash}(z_{\min}^B)=\{\mathbf C\}.} \tag{14}
\]

There is a final exhaustive split. If \(D(z_{\min})=D_*\), its witnessing
actual profiles give whole-source return with the retained pair, minimum
tail, zero owner defect, and paid gain, so the maintained collision compiler
applies. Otherwise \(D(z_{\min})>D_*\), and (14) is the genuine remaining
off-minimum inert closure.

This is the valid infimum closure. It does not say that an arbitrary initial
support-entry point is already minimal. It says that closing the fixed
normalized-passport class under its source-faithful support-entry restart and
then minimizing produces a same-passport unique-all-Continue point.

## 6. Why an unclosed approximate-infimum proof fails

Without the sequential closure and attainment in Section 3, the statement

\[
 \forall P\in\mathcal P,\quad
 \exists P'\in\mathcal P,\quad D(P')<D(P)        \tag{15}
\]

does not contradict the existence of an infimum. The descent size is
source-dependent because it is \(a(P)D(P)\), where the support-entry
absorption \(a(P)\) may tend to zero near the infimum.

The numerical model

\[
 D(P_k)=D_*+{1\over k},\qquad P_k'=P_{k+1}       \tag{16}
\]

has strict descent at every point and fixed normalized passport densities,
but never goes below its infimum \(D_*\). Thus one may not first select an
approximate minimizer and then use the absorption of that selected source as
if the minimizer had been chosen within its own descent gap. Compact
attainment of the limiting passport class is essential.

## 7. Scope and formalization target

The result removes support entry as the terminal obstruction of the
normalized-passport restart architecture. Its honest conclusion is whole-
source return to the existing compiler, or a source-attached,
invariant-density, unique-all-Continue off-minimum cap point. Consuming the
latter point remains the difficult branch.

A Lean implementation should separate:

1. the finite identities, which include the additive defect \(E_n\) and do
   not preserve boundary density inequalities;
2. a source-attached limiting-passport structure with fixed labels and
   cofinal original ranks;
3. the diagonal sequential-closure theorem;
4. compact attainment of minimum debt in that class; and
5. support-entry re-exactification as a strict self-map below any minimizer
   admitting positive absorption.

No pointwise finite-source class should be advertised as invariant. No
uniform lower bound on support-entry absorption is required after compact
attainment is established.

## Sources inspected

* notes/FORCED_PAIR_REVIEW__APPROXIMATE_SUPPORT_ENTRY_REEXACTIFICATION.md.
* exports/FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md.
* Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean.
* UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean.
