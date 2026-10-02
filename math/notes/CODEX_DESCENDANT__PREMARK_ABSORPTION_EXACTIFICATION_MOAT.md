# Through-mark absorption forces non-Nash work and cannot survive exactification

Identity: `CODEX_DESCENDANT`

Date: 2026-08-31

Status: **ordinary-mathematics reduction and exactification no-go, not a
consumer.**  The new opponent-absorption floor converts exactly into a fixed
weighted cap-defect ledger.  It cannot be preserved by an exact cap--Nash
rebuild over the same near-minimum post-mark tail.  Moreover, the floor is
inclusive of the marked row and may be paid entirely there; an exact Fin4
regression has an arbitrarily long exact all-Continue strict past and all its
absorption and paid work at the marked pair.  The surviving normalized
obstruction is a literal-defect occupation or a positive pre-mark singleton
law mass.

## 1. Question

Let \(z_*\) be a positive global minimum of total terminal semantic debt,

\[
D_*:=D(z_*)>0.
\]

Let \(\pi_n\) be actual profiles with marked dates \(m_n\), and let

\[
\tau_n=\operatorname{Spine}(\pi_n,m_n+1)
\]

be their literal post-mark tails.  Suppose

\[
D(\tau_n)\longrightarrow D_*.
\tag{1.1}
\]

For one fixed player \(i\), suppose the recently checked tight-coordinate
argument gives a constant \(h<1\) such that

\[
H_{n,i}:=
\prod_{t=0}^{m_n}
  \operatorname{OppCont}_i(q_{n,t})
\leq h
\tag{1.2}
\]

eventually.  Here \(q_{n,t}\) is the actual live root of \(\pi_n\) at date
\(t\).  Can this actual through-mark absorption be exactified, consumed
directly, or converted into a sharper normalized obstruction?

The answer obtained here is:

1. an exact or vanishing-error rebuild over \(\tau_n\) cannot retain the
   absorption floor;
2. the arbitrary word must instead carry a fixed cap-defect ledger, at
   asymptotic defect-per-absorption at least \(D_*\);
3. this ledger yields a finite dichotomy between actual literal endpoint
   work and a positive singleton terminal-law mass; but
4. without an additional strict-pre-mark floor, the result may merely
   reprice the already-known marked paid pair.

## 2. Exact finite-word account

Write

\[
c_{n,t}=\Pr_{q_{n,t}}(\mathbf C),
\qquad
a_{n,t}=1-c_{n,t},
\]

and let

\[
L_{n,0}=1,
\qquad
L_{n,t}=\prod_{s<t}c_{n,s}.
\]

The joint Continue product through the marked row is

\[
S_n=L_{n,m_n+1}
  =\prod_{t=0}^{m_n}c_{n,t},
\]

and its total absorption is

\[
A_n=1-S_n
  =\sum_{t=0}^{m_n}L_{n,t}a_{n,t}.
\tag{2.1}
\]

Because joint survival is at most every deleted-player survival,

\[
S_n\leq H_{n,i}\leq h,
\qquad
A_n\geq1-h=:a_0>0.
\tag{2.2}
\]

Let

\[
R_{n,t}=\operatorname{RootDefect}
  \bigl(B(\operatorname{Spine}(\pi_n,t+1)),q_{n,t}\bigr)
\]

be the total cap Nash defect of the actual root against the complete
behavioral cap of its literal successor.  Define the reached cap-defect
ledger

\[
C_n=\sum_{t=0}^{m_n}L_{n,t}R_{n,t}.
\tag{2.3}
\]

Iterating the exact arbitrary-root debt identity gives

\[
D(\pi_n)=C_n+S_nD(\tau_n).
\tag{2.4}
\]

Every \(\pi_n\) is an actual carrier point, so global minimality and (2.4)
give

\[
C_n\geq D_*-S_nD(\tau_n).
\tag{2.5}
\]

Writing \(e_n=D(\tau_n)-D_*\to0\), equations (2.2)--(2.5) imply

\[
\boxed{
C_n\geq a_0D_*-h e_n.
}
\tag{2.6}
\]

In particular,

\[
\liminf_n C_n\geq a_0D_*>0.
\tag{2.7}
\]

There is also a charge-normalized form.  Since \(A_n\geq a_0\),

\[
\boxed{
\frac{C_n}{A_n}
\geq D_*-\frac{e_n}{a_0},
}
\tag{2.8}
\]

and therefore

\[
\liminf_n\frac{C_n}{A_n}\geq D_*.
\tag{2.9}
\]

Thus the actual absorption is separated from exactness by a linear semantic
moat.  Pointwise root errors need not be bounded below: (2.9) permits the
charge to diffuse over increasingly many increasingly small roots.

The floor from tightness has the explicit asymptotic value

\[
a_0=\frac{\gamma}{2M+\gamma}
\]

when the tightness slack tends to zero.  With a fixed slack
\(0\leq\sigma<\gamma\), one may instead take

\[
a_0=\frac{\gamma-\sigma}{2M+\gamma}.
\]

## 3. Exactification no-go

Consider any finite word \(W_n\) of exact cap--Nash roots rebuilt over the
same literal tail \(\tau_n\).  Let \(\widehat S_n\) be its joint Continue
product.  Exact debt scaling gives

\[
D(W_n\star\tau_n)=\widehat S_nD(\tau_n).
\tag{3.1}
\]

Global minimality gives

\[
D_*\leq\widehat S_nD(\tau_n),
\]

so

\[
\widehat S_n\geq\frac{D_*}{D(\tau_n)}\longrightarrow1.
\tag{3.2}
\]

Hence

\[
\boxed{
\operatorname{Abs}(W_n)=1-\widehat S_n\longrightarrow0.
}
\tag{3.3}
\]

The same conclusion holds for an approximately exact rebuild whenever its
reached cap-defect ledger tends to zero, by (2.5).

This rules out absorption-preserving exactification over a near-minimum
tail.  More strongly, an exact rebuild cannot retain any terminal atom of
fixed positive mass inside the rebuilt word, because that atom is bounded by
the word's total absorption.

There is a precise fork when the marked atom and paid endpoint are retained.

* If the marked absorbing root is included in the exact rebuild, (3.3)
  forces its mass to vanish, so the atom and gain passports are destroyed.
* If the marked root is frozen and only the strict pre-mark past is rebuilt,
  the terminal suffix for the exact word is the **marked-root profile**, not
  \(\tau_n\).  Its debt need not tend to \(D_*\), so (3.2) supplies only the
  lower bound \(D_*/D(\text{marked profile})\), not convergence of survival
  to one.

Consequently the high-survival rebuilt profile does not asymptotically
dominate the old decoration inside the same normalized slice.  The argument
either loses the decoration or loses the near-minimum terminal debt.

## 4. The inclusive floor does not price the strict past

The checked floor (1.2) includes the marked row.  Factor it as

\[
H_{n,i}=H^-_{n,i}\,h^{\rm mark}_{n,i},
\tag{4.1}
\]

where \(H^-_{n,i}\) is opponent survival strictly before the mark.  An upper
bound on the product gives no upper bound below one on \(H^-_{n,i}\): the
marked factor alone may vanish.

Applying the same theorem at \(m_n-1\) would require a positive cap margin at
the suffix beginning **at** the marked row.  The source supplies the margin
only after the marked all-Continue branch, at \(m_n+1\).  A nonsingleton
marked coalition can screen that post-mark cap from every unilateral player,
so the missing margin is not automatic.

### Exact Fin4 regression

Let the players be \(0,1,2,3\), take observer \(i=0\), and define the only
nonzero reward coordinates by

\[
r_0(\{2\})=1,
\qquad
r_3(\{1\})=1.
\tag{4.2}
\]

Every other coordinate of every terminal reward is zero.  Let the post-mark
tail make player \(2\) Quit surely at its first row.  At the marked row make
the pure pair \(\{1,3\}\) Quit, and before it insert an arbitrary number of
all-Continue rows.

The observer's singleton reward is zero.  At the marked profile,

\[
B_0=U_0=0=r_0(\{0\}),
\]

because the sure pair screens the tail.  In the post-mark tail,

\[
B_0=1.
\]

Thus the tight-coordinate hypotheses hold with \(M=\gamma=1\), while
opponent survival through the mark is zero.  Strictly before the mark it is
one.

The marked pair is genuinely paid: player \(3\) gains one by Continuing,
which changes \(\{1,3\}\) to \(\{1\}\).  Every strict-past all-Continue root
is already exact cap--Nash.  The entire cap-defect ledger is the marked
player-\(3\) defect, equal to one.

Finally all Never is an exact terminal Nash profile, since every own
singleton reward is zero.  Hence the regression has global minimum debt
zero and is not a counterexample.  It proves the exact local limitation:
through-mark absorption, a post-mark cap margin, a paid pair, and an
arbitrarily long exact strict past can coexist, with no additional past
charge to exactify or consume.

## 5. Literal-work versus singleton-option decomposition

### A later marked-row moat removes time diffusion at the retained mark

The scratch theorem
fable_strictInert_markedRow_capDefect_floor supplies a stronger input at
the retained marked row than the aggregate through-mark floor.  If one
terminal coalition has stage mass at least \(\kappa>0\), and the post-mark
tail caps converge to a cap whose unique exact root is all Continue, then
there is \(r_0>0\) such that eventually

\[
r_0\le R_{n,m_n}.
\tag{5.0}
\]

Because the live mass \(L_{n,m_n}\) is at least the stage mass,

\[
\kappa r_0\le L_{n,m_n}R_{n,m_n}.
\tag{5.0a}
\]

Apply the coordinate inequality (5.1) at this one row only.  The resulting
option budget is bounded by \(2M\) times the total singleton stage mass at
the mark.  Therefore the marked row has the exact finite dispatch

\[
\boxed{
\begin{array}{c}
\text{some singleton has marked stage mass at least }
  \kappa r_0/(16M),\\
\text{or some one-date best-endpoint deviation has actual gain at least }
  \kappa r_0/8.
\end{array}}
\tag{5.0b}
\]

Indeed, either the option budget is at least half of (5.0a), and then the
four singleton cylinders give the first bound, or the literal-defect sum is
at least half, and the four player coordinates give the second.

This is genuinely stronger than the through-mark ledger for an impure marked
root: it eliminates diffusion over calendar dates.  It still yields a
singleton/concentrated packet or a paid endpoint, whose source-faithful
consumer is open because of cross-coordinate cap leakage.

At a pure nonsingleton marked row it is not new.  Every singleton option
coefficient is zero, continuation debt is completely screened, and
quittingTerminalSemanticDebtSum_pureNonsingletonRow_eq_totalDefect plus
global minimality gives the sharper pointwise floor

\[
D_*\le R_{n,m_n}=E_{n,m_n}.
\tag{5.0c}
\]

The existing pure-nonsingleton screening theorem then gives one actual
marked deviation of gain at least \(\kappa D_*/4\).  Thus the new moat is a
real impure-root localization theorem, but on the already forced pure-pair
branch it identifies the same marked-row charge and leaves the same leakage
obligation.

The cap-defect moat has one useful exact refinement.  Let

\[
P_{n,t,i}=
\operatorname{OppCont}_i(q_{n,t})\,
q_{n,t,i}(Q)\,
d_i(\operatorname{Spine}(\pi_n,t+1))
\]

be the own-Quit option budget, and let \(E_{n,t,i}\) be the coordinate root
Nash defect against the successor's prescribed payoff rather than its cap.
The checked one-row inequality is

\[
R_{n,t,i}-P_{n,t,i}\leq E_{n,t,i}.
\tag{5.1}
\]

After multiplying by live mass and summing, define

\[
Q_n=\sum_{t\leq m_n}L_{n,t}\sum_iP_{n,t,i},
\qquad
E_n=\sum_{t\leq m_n}L_{n,t}\sum_iE_{n,t,i}.
\]

Then

\[
\boxed{C_n\leq Q_n+E_n.}
\tag{5.2}
\]

If rewards are bounded by \(M\), every coordinate debt is at most \(2M\).
Moreover,

\[
L_{n,t}\operatorname{OppCont}_i(q_{n,t})q_{n,t,i}(Q)
\]

is exactly the stage mass of the singleton terminal \(\{i\}\) at date
\(t\).  Therefore, if \(P_n^{\rm sing}\) is the probability that the word
terminates in a singleton through the mark,

\[
Q_n\leq2M P_n^{\rm sing}.
\tag{5.3}
\]

Combining (2.7), (5.2), and (5.3), after discarding finitely many ranks one
gets the exhaustive quantitative split

\[
\boxed{
P_n^{\rm sing}\geq\frac{a_0D_*}{8M}
\quad\text{or}\quad
E_n\geq\frac{a_0D_*}{4}.
}
\tag{5.4}
\]

The constants use the eventual bound \(C_n\geq a_0D_*/2\).  In Fin4, the
first arm fixes one singleton owner on a subsequence with mass at least

\[
\frac{a_0D_*}{32M}.
\tag{5.5}
\]

This is aggregate law mass, not a one-date atom; owner-clock compression can
concentrate it, at the price and provenance already known for singleton
compression.

In the second arm, each summand

\[
L_{n,t}E_{n,t,i}
\]

is exactly the gain of one literal reached-row best-endpoint deviation.
There are again two exhaustive subcases:

1. some fixed row gain has a positive limsup, yielding an actual paid
   one-date endpoint after subsequence selection; or
2. the maximum row gain tends to zero while their sum stays above
   \(a_0D_*/4\).

In the second subcase, after fixing a player by Fin4 pigeonhole, the
normalized weights

\[
\nu_n(t)=
\frac{L_{n,t}E_{n,t,p}}
     {\sum_{s\leq m_n}L_{n,s}E_{n,s,p}}
\tag{5.6}
\]

form a diffuse probability occupation on actual pre-mark rows.  This is the
honest normalized obstruction left by failure of direct localization.  It is
not an exact Nash--Bellman chronology: the displayed roots are precisely the
nonexact roots whose defects carry the measure.

### The Continue-oriented part integrates into one legal response

The literal defect has a useful orientation which is lost by the scalar
notation above.  If \(Q_{n,t,i}\) and \(C_{n,t,i}\) are the two endpoint
values at the actual row, then

\[
E_{n,t,i}
=q_{n,t,i}(C)(Q_{n,t,i}-C_{n,t,i})_+
 +q_{n,t,i}(Q)(C_{n,t,i}-Q_{n,t,i})_+.
\tag{5.7}
\]

Call the two terms Quit-oriented and Continue-oriented, respectively.  Fix a
player \(p\), and let \(B_n\) be the finite set of through-mark dates on
which Continue is the better endpoint for \(p\).  Starting from the earliest
date in \(B_n\), successively force \(p\) to Continue at every date in
\(B_n\).  Earlier clears weakly increase the probability of reaching every
later selected date.  Conditional on reaching a later date, the root and
literal future from that date are still the original ones.  Hence the exact
one-row gain identity telescopes to

\[
U_p(\pi_n^{p,C})-U_p(\pi_n)
\ge
\sum_{t\in B_n}
 L_{n,t}q_{n,t,p}(Q)
 (C_{n,t,p}-Q_{n,t,p})_+.
\tag{5.8}
\]

This is one legal behavioral replacement, not a concatenation of different
players' deviations.  Its complete \(p\)-cap is unchanged because the
opponents are unchanged, and its literal post-mark tail is unchanged.  This
is the variable-gap version of the global refusal calculation.

Consequently, in the literal-work arm of (5.4), finite pigeonhole gives one
of two alternatives after a subsequence:

1. one player has a through-mark Continue-clearing response with actual gain
   at least \(a_0D_*/32\); or
2. the Quit-oriented literal defects have total reached mass at least
   \(a_0D_*/8\).

The constants come from splitting first between the two orientations and
then among four players.  The first alternative is a genuine paid behavioral
macro-edge, but is not by itself a return: changing one player's whole
prescription may raise the other three unrestricted caps.  The second
alternative does not admit the same integration.  Forcing Quit at an early
selected date screens the later selected dates, so the diffuse Quit-oriented
mass may fail to produce any one macroscopic deadline gain.  Thus the
unintegrated normalized obstruction can be sharpened to a Quit-oriented
occupation.

### Strict off-minimum normalization

Suppose additionally that the actual decorated profiles converge to a strict
descendant-neutral port of debt

\[
D(\pi_n)\longrightarrow\ell>D_*.
\tag{5.9}
\]

After a subsequence, take \(A_n\to A\in[a_0,1]\).  The exact ledger gives

\[
\frac{C_n}{A_n}
=D(\tau_n)+
  \frac{D(\pi_n)-D(\tau_n)}{A_n},
\tag{5.10}
\]

and therefore

\[
\boxed{
\frac{C_n}{A_n}
\longrightarrow
D_*+\frac{\ell-D_*}{A}
\ge\ell.
}
\tag{5.11}
\]

Equality with \(\ell\) occurs exactly when \(A=1\).  Thus a strict port has
one of two quantitative forms:

* asymptotically full joint absorption through the mark; or
* a cap-defect-per-absorption premium strictly larger than the port debt
  \(\ell\).

The pure-pair regression in Section 4 lies in the first form: the marked row
alone gives full absorption and carries the entire ledger.  Hence (5.11) is a
sharp normalized classification, not a contradiction.

### Exact leakage alternative for the Continue-clearing response

Let \(\rho_n=\pi_n^{p,C}\) be the response from (5.8), and write

\[
g_n=U_p(\rho_n)-U_p(\pi_n)>0.
\]

Because only \(p\)'s own strategy changes,

\[
B_p(\rho_n)=B_p(\pi_n),
\qquad
d_p(\rho_n)-d_p(\pi_n)=-g_n.
\tag{5.12}
\]

Therefore the total-debt change has the exact form

\[
D(\rho_n)-D(\pi_n)
=-g_n+\Lambda_n,
\qquad
\Lambda_n:=\sum_{k\ne p}
  \bigl(d_k(\rho_n)-d_k(\pi_n)\bigr).
\tag{5.13}
\]

In the Continue-oriented arm above, the constants may be retained relative
to the ledger:

\[
g_n\ge \frac{C_n}{16}.
\tag{5.14}
\]

Hence either

\[
D(\rho_n)\le D(\pi_n)-\frac{g_n}{2},
\tag{5.15}
\]

which is a genuine fixed one-step debt descent, or

\[
\Lambda_n>\frac{g_n}{2}\ge\frac{C_n}{32}.
\tag{5.16}
\]

In the second case one fixed recipient \(k\ne p\) may be selected in Fin4
with

\[
d_k(\rho_n)-d_k(\pi_n)>\frac{C_n}{96}.
\tag{5.17}
\]

Dividing by \(A_n\), (2.9) gives an asymptotic recipient-debt-transfer rate
at least \(D_*/96\); under (5.9), (5.11) improves it to \(\ell/96\).
This is the sharp obstruction left by failure of direct descent.  It is a
debt-transfer certificate, not necessarily pure cap rise: the recipient's
prescribed payoff may also fall.

Neither alternative is automatically renewable.  The four-profile
descendant slice is closed only under applying one common **outer prefix
word** to all four stored profiles.  The floor and the clearing set here run
through the retained mark and may change rows inside the stored base
profiles.  Such a change need not preserve the signed-atom pair, the separate
source/replacement gain pair, or the zero-observer face.  The regression in
Section 4 shows that all selected work may occur precisely in this unsafe
marked row.

If an additional hypothesis localizes (5.14) inside the common outer word,
then applying the same clear to all four coordinates weakly increases both
passport scales.  Descendant-slice minimality would then say more: a target
with debt strictly below \(\ell\) must enter positive observer debt, since a
zero-observer cluster would remain in the slice and contradict minimality.
Thus even the orbit-safe version yields the exhaustive obstruction

\[
\boxed{
\text{recipient debt transfer}
\quad\text{or}\quad
\text{entry into the formerly zero observer coordinate}.}
\tag{5.18}
\]

This is exactly the zero-face/cap-leakage obstruction already present in the
minimum-return program, now with a charge-normalized lower bound.  It is not
a new finite rank because a later response can erase the new coordinate and
recreate an old one.

Finally, feeding the macro-edge to the generic paid-cap lift does not connect
the two accounts.  The lifted exact roots see only the whole-profile cap
\(B(\pi_n)\), whereas \(C_n/A_n\) is computed from the sequence of literal
successor caps inside the arbitrary word.  The generic lift therefore returns
the known charged-return, real debt-descent, or inert-stall trichotomy, but
does not transport (5.11) or (5.17) into its exact-root absorption charge.

The recipient rise can nevertheless be attached to an actual **target-side**
port.  Equation (5.17) and nonnegativity of source debts give

\[
d_k(\rho_n)>\frac{C_n}{96}.
\tag{5.19}
\]

Using the eventual bound \(C_n\ge a_0D_*/2\), choose a complete behavioral
response of \(k\) at \(\rho_n\) with gain at least
\(a_0D_*/384\).  The pure-time mixture representation and the checked
first-disagreement extraction turn this into a source-matched paid row at
the literal target \(\rho_n\).  One may therefore build the usual exact
paid-cap port while storing the predecessor \(\pi_n\), the Continue-clearing
edge, and the through-mark ledger as external provenance.

This construction is renewable only as a **port object**, not as a decreasing
rank.  Its exact trichotomy again gives:

1. a charged return, which is consumed;
2. a strict real-valued debt descent from \(\rho_n\), whose endpoint need not
   re-enter the four-profile slice; or
3. an inert exact-cap stack, while the two paid horizontal edges remain
   trapped behind all-Continue roots.

In particular, the target-side exact roots do not inherit the predecessor's
ratio \(C_n/A_n\).  Thus (5.19) supplies a quantitative two-level paid
passport, but the second and third port outputs are exactly the existing
unconsumed paid-cap descent/inert-stall question.  Calling this wrapper a
renewable consumer would only rename that residual.

### 5.1 Comparison with the marked-row moat and multiplicity bound

The marked-row cap-defect theorem is stronger than the ledger argument at an
impure marked root.  If one fixed marked coalition has mass at least
\(\kappa\), and the post-mark caps converge to a cap with unique
all-Continue exact root, it gives a fixed lower bound on the total cap defect
of the marked root itself.  Applying the option-budget inequality at that
single row yields an actual one-date alternative:

\[
 \text{a fixed singleton cylinder}
 \quad\text{or}\quad
 \text{a fixed one-date endpoint gain}.
\tag{5.20}
\]

This removes the time-diffusion issue in (5.6) when its hypotheses apply at
the mark.  At the forced pure pair, however, the option budget is already
zero and the checked nonsingleton screening identity gives the sharper
defect floor \(D_*\).  Thus (5.20) is a genuine impure-root strengthening,
but on the forced-pair source it recovers the existing paid marked row and
does not control the other three caps after the update.

The companion multiplicity theorem says that, inside one actual profile,
there can be only finitely many \(\kappa\)-heavy marked dates whose post-date
caps lie in one such neighborhood.  Its proof is exactly the nonnegative
ledger summed over those dates.  It does not constrain the constructions in
this note, nor the attained persistent-product descendants: they select a
new profile for each rank or each root softening, and each profile carries
only one relevant mark.  Applying the multiplicity bound across those
profiles would silently assume the missing extension-compatible common
chronology.  Conversely, any future theorem placing infinitely many of these
marks in one literal play would close that branch immediately (or force the
reached masses to be summable).

### 5.2 Product-base pivot and its provenance limit

The zero-Never, zero-singleton source theorem gives an attained padded
product minimum with a sure-quitter core \(K\), \(|K|\ge2\).  At a positive
minimum the singleton option is strictly below every cap.  Comparing the
explicit padded and unpadded cap formulas therefore shows more directly that
the padding can be removed: the one-root-then-Never profile, and also the
stationary repetition of that root, have the same complete semantic pair and
terminal law as the padded profile.  The second sure quitter screens every
unilateral response from the continuation.

This simplification does not improve the consumer.  If the complement of
\(K\) is re-equilibrated in its induced finite game, then either all base
leave signs hold, giving the checked persistent-base uniform payoff, or some
base player has a paid leave response.  But the induced Nash point is a
newly selected stationary profile, not a literal descendant of the attained
minimum profile.  Its paid target is therefore another off-minimum paid port
with the minimum stored only as external provenance.  The marked-row ratio
and the old product-law passport do not transfer across this simultaneous
free-player reselection.

Working literally from the attained minimum avoids that loss, but gives
exactly the already exported sure-core softening descent: a flat small
softening is a minimum child with smaller sure core, while a strict
softening is an off-minimum paid target.  Hence the product-base pivot does
not turn (5.19) into a renewable rank or a terminal consumer.

## 6. What this changes

The pre-mark absorption floor does not support the hoped-for exact rebuild.
It gives a sharper and fully source-owned alternative:

\[
\boxed{
\begin{array}{c}
\text{positive through-mark actual absorption}\
+\ \text{near-minimum post-mark tail}
\end{array}
\Longrightarrow
\begin{array}{c}
\text{positive singleton law mass}\
\text{or positive literal-defect occupation.}
\end{array}}
\tag{6.1}
\]

The exactification failure is quantitative: every absorption-preserving
rebuild pays cap defect at asymptotic rate at least \(D_*\) per unit of
absorption.  However, the inclusive floor may be exhausted by the marked
paid row, and the diffuse literal-defect occupation has no current return
compiler.

A genuinely stronger next input would be one of:

1. a fixed strict-pre-mark absorption floor, excluding payment entirely at
   the retained marked root;
2. a theorem consuming the diffuse literal-defect occupation (5.6); or
3. a renewable use of the singleton mass in (5.5) which retains the incoming
   positive-minimum source rather than restarting the same forced-pair loop.

The current source does not supply item 1: the cap margin needed at the
marked suffix is screened by the marked nonsingleton collision.

After the orientation refinement, item 2 may be restricted further to the
Quit-oriented occupation.  The Continue-oriented occupation is already one
actual paid macro-response by (5.8), although the usual cross-coordinate cap
leakage still prevents treating that payment as a consumer.

Equations (5.12)--(5.18) make that last statement quantitative.  Failure of
a fixed one-step descent costs a fixed fraction of the through-mark cap ledger
in one recipient debt coordinate.  What is still absent is a source theorem
which makes this transfer preserve an old zero set or spend exact
chronological charge.

## 7. Checked inputs and Lean handoff

The following exact inputs were inspected:

* `fable_nearTight_coordinate_premark_opponentAbsorption_floor` and its
  eventual limit form in `fable/lean/FablePremarkAbsorptionFloor.lean` and
  `fable/lean/FableLimitTightAbsorptionFloor.lean`;
* `quittingTerminalSemanticDebtSum_literalRootStack_eq_weightedLedger_add`,
  `minimum_sub_transport_le_weightedLedger`, and the reached-positive-row
  interface in `Research/Quitting/FiniteWordWeightedCapDefectLedger.lean`;
* `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`;
* `quittingRootCapDefect_sub_quitOptionBudget_le_literalDefect`;
* `quittingTerminalSemanticDebt_mem_Icc_zero_two_mul`; and
* `quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect`.

The new Lean-sized adapters are:

1. compose the eventual opponent-survival floor with the exact weighted
   ledger to obtain (2.6)--(2.9);
2. state the exact-stack incompatibility (3.2)--(3.3); and
3. sum the option-budget inequality to obtain (5.2)--(5.5).

The diffuse occupation (5.6) is a normalized boundary object, not yet a
consumer theorem.
