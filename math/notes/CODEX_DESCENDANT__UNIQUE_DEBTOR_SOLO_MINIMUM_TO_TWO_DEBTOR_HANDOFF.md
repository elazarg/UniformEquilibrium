# A positive solo root at a descendant minimum reaches only the existing two-debtor handoff

Identity: `CODEX_DESCENDANT`  
Date: 2026-08-31  
Status: **ordinary-mathematics composition of checked inputs; valid but
frontier-subsumed, not a consumer.**  At a compact prefix-invariant debt
minimum, a positive-solo unique-debtor arm enters the checked actual
stationary two-debtor handoff.  However, the maintained hard residual already
constructs a same-table singleton-base paid/reset source for every prescribed
owner, without using this minimizer.  Because the handoff is not
chronologically connected back to the descendant point, the composition does
not remove an SCC or improve the available source interface.  The useful
surviving content is the exact local classification and the multi-debtor
linear seam moat.

## 1. Question

The prescribed-payoff equality gate in
`CODEX_DESCENDANT__ASYMPTOTIC_PROJECTIVE_PASSPORT_AND_ROOT_BARRIER.md`
allows a nontrivial exact root only in the following form.  There is one
debtor \(h\), all opponents Continue, the owner mixes with rate \(t>0\), and

\[
d_h(X)=D(X)>0,
\qquad d_i(X)=0\quad(i\ne h),
\qquad U_h=r_h(\{h\}).
\tag{1.1}
\]

Can this positive-solo arm persist at the bottom of the arbitrary-prefix
descendant carrier?  The answer is no: the source-native solo-wall theorem
turns it into either a lower-debt descendant or an actual stationary
two-debtor source.  At a descendant minimum the first output is impossible.

This does not consume a unique-debtor point at which all Continue is the only
prescribed-payoff root.  It also does not consume the resulting two-debtor
stationary source.

## 2. Prefix-invariant carrier minimum

Let \(\mathcal H\) be a nonempty compact subset of the terminal-semantic
carrier of a Fin4 quitting table.  Assume that it is invariant under finite
product-root prefixing:

\[
X\in\mathcal H, q\text{ a product root}
\quad\Longrightarrow\quad
\operatorname{Prefix}(q,X)\in\mathcal H.
\tag{2.1}
\]

The first-coordinate projection of the asymptotic arbitrary-word quartet
carrier in the preceding note is one example.  Equally, one can take the
closed arbitrary-prefix orbit of a single carrier point.

Choose \(X=(U,B)\in\mathcal H\) minimizing total semantic debt on
\(\mathcal H\), and assume

\[
D(X)>0.
\tag{2.2}
\]

### Lemma 2.1 (cap-root rigidity)

Every exact root against \(B\) is all Continue.

#### Proof

If \(q\) is exact against \(B\), exact semantic prefixing scales every debt
coordinate by the joint Continue probability \(c(q)\).  Hence

\[
D(\operatorname{Prefix}(q,X))=c(q)D(X).
\tag{2.3}
\]

The prefixed point lies in \(\mathcal H\).  Minimality and positivity imply
\(c(q)=1\), so \(q\) is all Continue.  Finite root-game Nash existence shows
that this root exists.  \(\square\)

### Lemma 2.2 (prescribed-root equality gate)

Every exact root against \(U\) is either all Continue or has exactly the
form (1.1): the unique debtor \(h\) is the only player who Quits with positive
probability.

#### Proof

For a root \(q\) exact against \(U\), the unrestricted-cap prefix formula
gives, coordinatewise,

\[
d_i(\operatorname{Prefix}(q,X))
\le
s_{-i}(q)d_i(X),
\tag{2.4}
\]

where \(s_{-i}(q)\) is the probability that every opponent of \(i\)
Continues at the root.

Suppose \(q_k>0\).  If some debtor \(i\ne k\) exists, then
\(s_{-i}(q)\le1-q_k<1\), while every other coordinate weakly contracts.
Thus (2.4), (2.1), and positivity give a strict decrease of total debt,
contradicting minimality.  Therefore any nontrivial exact root has only one
debtor, say \(h\), and no player other than \(h\) can have positive Quit
probability.  Owner mixing gives \(U_h=r_h(\{h\})\) whenever the rate is
strictly below one.

The rate cannot be one under the maintained Fin4 hard residual.  It supplies
an outsider \(c\ne h\) with

\[
r_c(\{h,c\})\ge r_c(\{h\})+\Gamma,
\qquad \Gamma>0.
\tag{2.5}
\]

If \(h\) Quits surely while every opponent Continues, then \(c\) strictly
prefers Quit, contradicting exactness.  Hence the owner rate belongs to
\((0,1)\), and the displayed singleton equality follows.  \(\square\)

The floor condition needed below is automatic.  For \(i\ne h\), zero debt
gives \(U_i=B_i\), and every behavioral cap dominates the punishment value.
For \(h\), singleton tightness and punishment normality give

\[
P_h\le r_h(\{h\})=U_h.
\tag{2.6}
\]

## 3. The positive-solo arm cannot be minimal

### Theorem 3.1 (solo minimum to two-debtor handoff)

Assume that the game has no uniform-equilibrium payoff and satisfies the
maintained Fin4 hard residual.  Let \(X\) minimize debt on a compact
prefix-invariant carrier \(\mathcal H\), with \(D(X)>0\).  If there is a
nontrivial exact prescribed-payoff root at \(X\), then the table admits one
of the actual stationary two-debtor sources in
`FIN4_SOLO_WALL_DEBT_DESCENT_OR_TWO_DEBTOR_HANDOFF.md`.

In particular, if that stationary handoff is excluded, all Continue is the
unique exact root against both \(U\) and \(B\).

#### Proof

By Lemma 2.2, write the nontrivial root as the solo root of owner \(h\) and
rate \(t\in(0,1)\).  Choose, for example,

\[
\alpha={t\over2}>0,
\qquad
d={1-t\over2}>0.
\tag{3.1}
\]

Then

\[
\alpha\le t\le1-d.
\tag{3.2}
\]

On this compact rate interval the checked Fin4 blocker theorem gives a
positive constant \(g_{\alpha,d}>0\): for every owner and every rate in the
interval, some outsider has the required strict solo-wall comparison.  The
proof is the punishment-completed solo alternative: if all three outsider
comparisons were nonpositive, the full singleton payoff vector would be a
uniform-equilibrium payoff.  Thus the input gate of the checked solo-wall
dispatch is satisfied at \(X\).  Equation (2.6) supplies its punishment-floor
hypothesis.

The solo-wall dispatch has two outputs.

1. It constructs finitely many exact semantic prefixes, followed by an exact
   root whose prefix strictly lowers total debt.  Every intermediate and
   final point belongs to \(\mathcal H\) by (2.1).  The wall prefixes preserve
   the unique-debtor debt vector, so the source of the final strict step still
   has total debt \(D(X)\).  The target therefore has debt strictly below
   \(D(X)\), contradicting minimality.
2. It constructs one of the literal stationary two-debtor handoffs described
   in the cited packet.

The first output is impossible, so the second holds.  Lemma 2.1 gives the
cap-root assertion.  Lemma 2.2 and finite Nash existence give the final
prescribed-root assertion when the handoff is excluded.  \(\square\)

## 4. Quantitative collider consequence

The exact solo inequality also gives a useful but already represented rate
bound.  Let \(c\) be the collider in (2.5).  Since \(c\) Continues in the
solo root,

\[
(1-t)\bigl(U_c-r_c(\{c\})\bigr)
\ge
t\bigl(r_c(\{h,c\})-r_c(\{h\})\bigr)
\ge t\Gamma.
\tag{4.1}
\]

With rewards bounded by \(M\), the left payoff difference is at most \(2M\),
and hence

\[
1-t\ge {\Gamma\over 2M+\Gamma}.
\tag{4.2}
\]

This excludes a sure singleton root and preserves every upstream passport by
a fixed positive factor for one prefix.  It does **not** give a lower bound on
\(t\), and therefore does not itself exclude a summable solo-clock sequence.
The same estimate already appears in the maintained codimension-one and
solo-wall analysis; it is recorded here only to make the boundary exact.

## 5. The complementary multi-debtor moat

The fixed-cap barrier from the strict descendant analysis gives more than
root uniqueness when at least two debts are positive.  Suppose a carrier
pair \(Y=(U,B)\) satisfies

\[
\operatorname{RootDefect}(q;B)
\ge D(Y)\operatorname{Abs}(q)
\quad\text{for every product root }q.
\tag{5.1}
\]

Put

\[
d_{\max}=\max_i d_i(Y),
\qquad
\kappa=D(Y)-d_{\max}.
\tag{5.2}
\]

For every root \(q\), raising the continuation coordinate from \(U_i\) to
\(B_i=U_i+d_i\) can increase player \(i\)'s root defect by at most
\(m_i(q)d_i\), where \(m_i(q)\) is the singleton-\(i\) root mass.  Therefore

\[
\begin{aligned}
\operatorname{RootDefect}(q;U)
&\ge
\operatorname{RootDefect}(q;B)-\sum_i m_i(q)d_i\\
&\ge
D(Y)\operatorname{Abs}(q)-d_{\max}\sum_i m_i(q)\\
&\ge
\kappa\operatorname{Abs}(q).
\end{aligned}
\tag{5.3}
\]

If at least two debt coordinates are positive, then
\(d_{\max}<D(Y)\), hence \(\kappa>0\).  Thus the prescribed-payoff root game
has a global linear absorption moat, not merely an isolated all-Continue
root.

The moat has an exact seam consequence.  Root defect is \(1\)-Lipschitz in
each continuation coordinate, so if \(q\) is exact against another vector
\(V\), then

\[
\kappa\operatorname{Abs}(q)
\le 4\lVert V-U\rVert_\infty.
\tag{5.4}
\]

Hence any exact positive-absorption escape from the multi-debtor barrier must
pay prescribed-payoff displacement proportional to its absorption.  This is
a sharp normalized obstruction, not a consumer: the four-profile gain and
signed-atom passports live on different profile pairs and do not supply a
continuation vector \(V\) with the required sign or chronology.

When there is a unique debtor, \(\kappa=0\), and (5.3) becomes exactly the
equality gate that permits solo roots.  Theorem 3.1 routes the positive-solo
case to the existing stationary handoff.  If no positive solo root exists, the
remaining unique-debtor all-Continue plateau has only the cap-side barrier;
the prescribed-payoff linear coefficient vanishes.

At an arbitrary off-minimum descendant plateau there is one further exact
finite split.  Apply the checked tight-coordinate dichotomy to the unique
all-Continue cap \(B\).  Let

\[
Z=\{i:B_i=r_i(\{i\})\}.
\tag{5.5}
\]

Either:

1. \(Z=\varnothing\), and compactness of the four coordinates gives a
   strict uniform singleton gap

   \[
   \delta=\min_i\bigl(B_i-r_i(\{i\})\bigr)>0;
   \tag{5.6}
   \]

   this is the open unique-cap basin; or
2. \(Z\) has at least two labels and contains a directed positive collision
   cycle.  For every vertex \(i\in Z\), some \(k\in Z\setminus\{i\}\)
   satisfies

   \[
   r_k(\{i,k\})>r_k(\{i\}).
   \tag{5.7}
   \]

At a unique-debtor all-Continue point the debtor \(h\) is not cap-tight,
because \(U_h\ge r_h(\{h\})\) and therefore

\[
B_h-r_h(\{h\})
=d_h+U_h-r_h(\{h\})
\ge D>0.
\tag{5.8}
\]

Hence the cycle in the second arm lies entirely
among the three solved coordinates.  This is a finite falsifiable
obstruction, but not a new consumer: the hard residual already supplies
positive singleton collisions and persistent-base stationary sources, while
the cycle carries no ancestry back to the descendant minimizer.

At a **global** positive-debt minimum, the second arm is impossible for a
simpler reason.  The checked global singleton moat gives

\[
B_i-r_i(\{i\})\geq D_*>0
\qquad(i\in I).
\tag{5.9}
\]

Thus the cap-tight set \(Z\) is empty at every global minimum point.  The
tight collision cycle is only an off-minimum descendant possibility; it is
not part of the global-minimum unique-debtor boundary.  The latter always
lies in the strict all-Continue cap basin.

There is a parallel prescribed-payoff split at a global minimum with unique
debtor \(h\).  Since all other debts vanish, (5.9) gives

\[
U_i=B_i\geq r_i(\{i\})+D_*
\qquad(i\ne h),
\tag{5.10}
\]

whereas the owner satisfies only \(U_h\geq r_h(\{h\})\).  Hence every exact
root against \(U\) is either all Continue or a solo root of \(h\).  If
\(U_h>r_h(\{h\})\), all Continue is unique against \(U\) as well.  If
\(U_h=r_h(\{h\})\), the strict outsider margins in (5.10) imply by continuity
that every sufficiently small positive solo-\(h\) rate is exact at the
initial point.  This recovers exactly the solo-prefix/support-wall lane; it
does not create a third root geometry.

## 6. What is and is not consumed

Theorem 3.1 gives the following local root configuration a same-table bypass:

```text
compact descendant debt minimum
  + singleton-tight unique debtor
  + positive exact solo root.
```

It redirects the table to the existing actual stationary two-debtor handoff.
That handoff has two unrestrictedly solved coordinates, debt on at most two
base coordinates, a fixed positive nonsingleton atom, and a literal paid
first-disagreement row.  It is not chronologically reached from \(X\).

This is **not** a new atlas contraction.  Under the same hard residual,
Theorem 4.2 and Corollary 4.3 of
`CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md` already
construct, for every singleton owner, an actual singleton-base stationary
source with unique debtor, paid row, strict-superset atom, solved reset owner,
and fixed-law reset dispatch.  The positive pair-premium branch in the solo
wall likewise produces the handoff without preserving ancestry from the
descendant minimum.  Theorem 3.1 supplies no missing backward compiler or
source relation, so it cannot consume the original branch merely by pointing
to that already-available source.

The remaining root-side state is sharper:

```text
compact descendant debt minimum
  + all Continue is the unique exact prescribed-payoff root
  + all Continue is the unique exact cap root.
```

This includes the isolated multi-debtor arm and a unique-debtor
all-Continue plateau.  Neither the positive signed-atom passport nor the
separate actual-gain passport is retained by the unconstrained minimization
used here.  Consequently this theorem does not consume the strict
descendant-neutral port itself.  A successful port consumer must still use
the incoming passports or chronology; unrelated same-table source existence
is insufficient.

The actual two-debtor handoff also remains nonterminal.  Its stationary
source is selected on the same reward table but is not an extension of the
incoming closed-descendant chronology.  Existing packets attach a positive
atom and paid row to it, but no uniform payoff, charged return, or renewable
finite-rank descent is currently obtained.

## 7. Exact no-go boundary

Dropping compact descendant minimality makes the strict-debt output of the
solo-wall theorem genuine and prevents the conclusion.  Dropping the hard
residual permits a sure solo root.  Dropping floor safety prevents use of the
punishment-completed solo compiler, although floor safety is automatic at the
unique-debtor singleton-tight gate considered here.

The local reward and root data alone do not contradict terminal equilibrium:
the regressions in
`CODEX_DESCENDANT__ASYMPTOTIC_PROJECTIVE_PASSPORT_AND_ROOT_BARRIER.md` and
`CODEX_MINER__FIN4_SINGLETON_BASE_ALLCONTINUE_RESET_WALL.md` realize the
corresponding unique-debtor/all-Continue geometry in tables with global
minimum debt zero.  Thus the remaining unique-all-Continue plateau must be
consumed using the positive-minimum source provenance or the actual
two-debtor handoff, not by a local root-game contradiction.

## 8. Lean handoff boundary

The mathematical inputs are already checked individually:

* exact cap-root debt scaling;
* exact prescribed-root deleted-survival debt contraction;
* Fin4 singleton collision and punishment normality;
* the compact positive blocker gap on a rate cell; and
* the complete solo-wall debt-descent/two-debtor dispatch.

If this local composition is useful as a diagnostic lemma, the missing Lean
declaration is only the compact prefix-invariant minimizer adapter composing
those inputs.  It should accept a compact carrier subset closed under
semantic prefixing and return:

```text
Nonempty stationaryTwoDebtorHandoff
or
forall q, IsExactRootNash U q -> q = allContinue.
```

The cap-root singleton conclusion is a separate one-line field from exact
debt scaling.  No actual-profile ancestry, law equality, marked date, or
source reach follows from the adapter.  Since the table-level handoff is
already available by a stronger unconditional producer, formalizing this
adapter is low priority.

## 9. Sources inspected

* `notes/CODEX_DESCENDANT__ASYMPTOTIC_PROJECTIVE_PASSPORT_AND_ROOT_BARRIER.md`;
* `formalized/FOUR_PROFILE_DESCENDANT_SLICE_NEUTRALIZATION.md`;
* `formalized/FIN4_OFF_MINIMUM_CHARGED_BLOCKER_GATE.md`;
* `formalized/FIN4_CHARGED_BLOCKER_COLLISION_OR_REPAYMENT_SPLIT.md`;
* `formalized/FIN4_SOLO_WALL_DEBT_DESCENT_OR_TWO_DEBTOR_HANDOFF.md`;
* `notes/CODEX_RAMSEY__UNIQUE_DEBTOR_FLOOR_ENTRANCE_AND_SOLO_RECYCLE.md`;
* `notes/CODEX_MINER__FIN4_STRICT_SOLO_REGENERATION_PLATEAU_BOUNDARY.md`;
* `feedback/CODEX_MINER__FIN4_STRICT_SOLO_REGENERATION_PLATEAU_BOUNDARY__BY_CODEX_EULER.md`;
* `notes/CODEX_ROOT__PRESCRIBED_PAYOFF_ROOT_LIFTING.md`; and
* `questions/FIN4_FULL_DEBT_CHAMBER_CONSUMER.md`.
