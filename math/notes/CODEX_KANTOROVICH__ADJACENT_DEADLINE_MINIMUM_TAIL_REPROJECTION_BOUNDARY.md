# Adjacent deadlines: exact minimum-tail reprojection boundary

Author: `CODEX_KANTOROVICH`

## Status

Ordinary mathematics, not checked in Lean.  This note gives an exact
source-coherent positive/negative split for the adjacent-deadline packet.

* If the selected boundary observer has zero declared `Never` mass in the
  deadline-`N` Nash law, every opponent-hybrid `Q_N` gain and every
  common-response rectangle cross-difference is unchanged after grafting an
  arbitrary literal tail.  In particular it can be grafted to one supplied
  positive-minimum realizing chronology with no seam and no loss.
* If the observer has positive `Never` mass, Nash support identifies the hard
  `Q_N` gain exactly with opponent survival times the singleton reward.  On a
  punishment-normal positive-minimum fiber, the same `Q_N` plan is uniformly
  worse than the literal plan which passes through the finite word and resumes
  the minimum tail.  Away from the pure-spectator face, that pass plan is
  itself uniformly paid.
* In the near-pure-spectator arm, the adjacent boundary-participation mass can
  be reassigned to one participating player.  If the censored old laws are
  close to the previous deadline Nash law, moving that player's boundary mass
  back to `Never` is a literal paid own-law edge over the same positive-minimum
  tail, with exact mover-debt subtraction and an explicit Fin4 floor.  Hence
  the only unconverted adjacent arm is a macroscopic change in the
  **censored** stopping laws.

Thus the spectator is not a terminal obstruction.  The exact remaining
finite-deadline reprojection question is whether macroscopic censored
reshuffling itself has a source-faithful consumer.  The results here produce
actual positive-minimum-tail paid edges in every other arm, but do not yet
turn such an edge into terminal approximants, a minimum-fiber support drop, or
the Fin4 conjecture.

## 1. Finite data and deviation semantics

Let `I` be finite and nonempty and let all quitting rewards have absolute
value at most `R>0`.  Fix `N>=1`.  Let

\[
 p\in \operatorname{NE}_N
\]

be an independent mixed Nash law of the hard zero-tail timing game with pure
actions

\[
 \{0,\ldots,N-1,\infty\}.
\]

For player `i`, put

\[
 S_i=p_i(\infty),\qquad
 H_i=\prod_{j\ne i}p_j(\infty),\qquad
 M=S_iH_i.
\tag{1.1}
\]

Let `A_i` be player `i`'s equilibrium payoff in this finite game, let
`V_i(\infty)` be its payoff from the pure timing action `infinity`, and let
`V_i(N)` be the payoff from the newly exposed deterministic date `N`.  Write

\[
 g_i^0:=V_i(N)-A_i.
\tag{1.2}
\]

Let `tau` be an arbitrary actual behavioral tail.  Write

\[
 u_i^\tau=U_i(\tau).
\]

The literal graft `p*tau` first realizes the independent timing law and, only
if every sampled timing action is `infinity`, resumes `tau`.  All deviations
below are complete behavioral strategies.  In particular define

* `Q_N`: Continue through dates below `N` and Quit surely at `N`;
* `Pass_tau_i`: Continue through the whole finite timing word and then use
  `tau_i` literally in the retained tail.

No best response is assumed attained.

## 2. Exact last-date versus pass identity

The two displayed deviations are identical on every event on which an
opponent stops before the boundary.  On the event that every opponent passes
the word, of probability `H_i`, `Q_N` gives the singleton reward and
`Pass_tau_i` enters the literal tail.  Therefore

\[
\boxed{
 U_i((p*\tau)[i\leftarrow Q_N])
 -U_i((p*\tau)[i\leftarrow\operatorname{Pass}_{\tau_i}])
 =H_i\bigl(r_i(\{i\})-u_i^\tau\bigr).}
\tag{2.1}
\]

This identity quantifies over the complete post-word behavior in `tau_i`.
It remains valid when `tau_i` has infinite support or positive `Never` mass.

The prescribed graft payoff and the `Q_N` payoff give the separate exact
identity

\[
\boxed{
 G_i^\tau(N;p):=
 U_i((p*\tau)[i\leftarrow Q_N])-U_i(p*\tau)
 =g_i^0-Mu_i^\tau.}
\tag{2.2}
\]

Equation (2.2) is the single-column version of the retained-tail seam in the
reviewed adjacent-deadline packet.

## 3. Positive support of `Never` identifies the hard gain

Assume

\[
 S_i>0.
\tag{3.1}
\]

Because `infinity` lies in the support of player `i`'s finite mixed Nash law,
finite-game support indifference gives

\[
 V_i(\infty)=A_i.
\tag{3.2}
\]

The actions `Q_N` and `infinity` agree until all opponents have passed the
finite word.  The hard all-`infinity` outcome pays zero, whereas `Q_N` then
produces the singleton.  Hence

\[
 V_i(N)-V_i(\infty)=H_i r_i(\{i\}).
\tag{3.3}
\]

Combining (1.2), (3.2), and (3.3),

\[
\boxed{g_i^0=H_i r_i(\{i\}).}
\tag{3.4}
\]

Consequently a strictly positive exposed-boundary gain with `S_i>0` forces

\[
 H_i>0,\qquad r_i(\{i\})>0.
\tag{3.5}
\]

This is stronger than merely knowing that the gap witness has a profitable
late time.  It identifies the whole gain with one singleton cylinder.

## 4. Minimum-fiber isolation reverses the response order

Now specialize to Fin4 and assume the fixed hard residual.  Let

\[
 z=(u,b)
\]

belong to the positive global minimum-debt fiber.  The checked uniform
singleton-isolation theorem gives one `delta>0`, independent of `z` and `i`,
such that

\[
 u_i-r_i(\{i\})\ge\delta.
\tag{4.1}
\]

Let actual tails `tau_m` realize `z`, so `U(tau_m)->u`.  For all sufficiently
large `m`,

\[
 u_i^{\tau_m}-r_i(\{i\})\ge\delta/2.
\tag{4.2}
\]

Equations (2.1) and (4.2) imply the exact robust reversal

\[
\boxed{
 U_i((p*\tau_m)[i\leftarrow Q_N])
 -U_i((p*\tau_m)[i\leftarrow\operatorname{Pass}_{\tau_{m,i}}])
 \le-H_i\delta/2.}
\tag{4.3}
\]

If `S_i>0` and the hard boundary gain has floor `g_i^0>=gamma`, (3.4)
also gives

\[
 H_i\ge \gamma/R.
\tag{4.4}
\]

Thus the response-order reversal has the source-independent floor

\[
\boxed{
 U_i((p*\tau_m)[i\leftarrow Q_N])
 -U_i((p*\tau_m)[i\leftarrow\operatorname{Pass}_{\tau_{m,i}}])
 \le-\gamma\delta/(2R).}
\tag{4.5}
\]

Positive-minimum provenance therefore does not merely fail to repair the
hard response.  In the positive-`Never` arm it supplies a uniform response
of the opposite ordering.

There is nevertheless a useful replacement response before the spectator
limit.  Since `infinity` is a hard-game support action, its hard gain is zero.
After grafting `tau_m`, the exact gain of `Pass_(tau_(m,i))` is

\[
\boxed{
 G_i^{\tau_m}(\operatorname{Pass};p)
 =H_i(1-S_i)u_i^{\tau_m}.}
\tag{4.6}
\]

If `g_i^0>=gamma`, then (3.4) gives `H_i r_i({i})>=gamma`; for large `m`,
`u_i^(tau_m)>=r_i({i})`.  Hence

\[
\boxed{
 G_i^{\tau_m}(\operatorname{Pass};p)
 \ge (1-S_i)\gamma.}
\tag{4.7}
\]

Thus for every fixed `eta>0`, the whole subarm

\[
 0<S_i\le1-\eta
\]

does reproject to a literal source-attached paid response, now with response
label `Pass_tau_i` and gain at least `eta*gamma`.  The only way this
replacement charge can vanish is the projective spectator limit

\[
S_i\longrightarrow1.
\tag{4.8}
\]

The full unrestricted graft debt is also exact in this arm.  Because
`u_i^(tau_m)>0`, its tail cap is positive.  If `0<S_i<1`, both `infinity` and
some finite action lie in the hard Nash support, so both hard certificate
slacks vanish.  The zero-tail graft ledger therefore gives

\[
\boxed{
 d_i(p*\tau_m)
 =H_i\left[d_i(\tau_m)+(1-S_i)u_i^{\tau_m}\right].}
\tag{4.9}
\]

If `S_i=1`, the endpoint form is

\[
\boxed{d_i(p*\tau_m)=H_i d_i(\tau_m).}
\tag{4.10}
\]

Thus the positive-`Never` hard boundary contributes no hidden third kind of
debt after minimum-tail reprojection.  It becomes exactly:

* inherited minimum-tail debt, weighted by opponent passage; plus
* the paid pass response (4.6), which is weighted by finite participation.

When `S_i->1`, the second term vanishes.  If the boundary observer is active
at the selected minimum point, the first term remains inherited minimum debt.
If it is inactive there, both terms can vanish.  Taken alone, this leaves an
**inactive pure-Never spectator**; Section 5.1 shows that the adjacent
boundary-participation data reassign the paid role unless censored reshuffling
is already macroscopic.

### Pure-`Never` spectator

If in addition

\[
 S_i=1,
\]

then the prescribed player strategy in `p*tau_m` is already
`Pass_(tau_(m,i))`.  Hence (4.3) becomes

\[
\boxed{G_i^{\tau_m}(N;p)\le-H_i\delta/2<0.}
\tag{4.11}
\]

The hard source had `g_i^0>=gamma>0`; the literal minimum-tail graft has a
strictly unprofitable `Q_N` response.  The source profile, tail profile,
response date, and opponent laws are all the same literal objects.  No
subsequence or carrier reselection is involved.

This is the exact spectator obstruction to a universal

\[
 \text{hard paid }Q_N\text{ source}
 \Longrightarrow
 \text{minimum-source paid }Q_N\text{ source}
\]

adapter.

## 5. Zero `Never` mass gives lossless reprojection

The complementary case is equally exact.  If

\[
 S_i=0,
\tag{5.1}
\]

then `M=0`, so (2.2) gives

\[
\boxed{G_i^\tau(N;p)=g_i^0}
\tag{5.2}
\]

for every actual tail `tau`, with no approximation.

More generally, consider the opponent-hybrid part of the adjacent-deadline
chain.  Every column keeps player `i`'s own marginal equal to `p_i`; only one
opponent marginal changes at each edge.  If `p_i(infinity)=0`, every column
has joint pass mass zero.  Therefore for any two consecutive opponent
hybrids `A,B`,

\[
 G_i^\tau(N;A)=G_i^0(N;A),\qquad
 G_i^\tau(N;B)=G_i^0(N;B),
\tag{5.3}
\]

and hence

\[
\boxed{
 G_i^\tau(N;A)-G_i^\tau(N;B)
 =G_i^0(N;A)-G_i^0(N;B).}
\tag{5.4}
\]

Thus the first-crossing branch of the reviewed adjacent-deadline theorem
grafts literally to every tail with its full paid-source floor and rectangle
charge unchanged.  Taking `tau=tau_m` supplies one fixed positive-minimum
source chronology as the common literal post-word tail.  The profiles, finite
word, marked deadline, response plan, tail law, and all four rectangle corners
remain pointwise coherent.

This is a genuine source adapter, but not yet a minimum-*endpoint* adapter:
the grafted whole profiles need not themselves have debt `D_*`.  Accordingly
it does not by itself meet the hypotheses of the checked minimum-response
chord compiler.

### 5.1 Boundary participation is a reverse paid edge

There is a stronger role-reselection theorem in the near-spectator arm.  Let
`q in NE_(N+1)` be the adjacent Nash law and put

\[
 b_j=q_j(N),\qquad
 e_j=\operatorname{TV}(p_j,C_Nq_j).
\tag{5.5}
\]

Let `P^-` be the lifted all-censored law `L_N(C_Nq)`.  For one player `j`,
let `P^j` restore only the mass `b_j` from `infinity` to date `N`, leaving all
other marginals censored.  These are two literal independent finite timing
profiles and differ only in player `j`'s complete strategy.

No opponent has mass at date `N` in either profile.  If

\[
 H_j^c:=\prod_{k\ne j}(C_Nq_k)(\infty),
\]

then one-player linearity and the last-date/pass identity give

\[
\boxed{
 U_j(P^j*\tau)-U_j(P^-*\tau)
 =b_jH_j^c\bigl(r_j(\{j\})-u_j^\tau\bigr).}
\tag{5.6}
\]

For a sufficiently accurate minimum realizer, the reverse update therefore
has the actual whole-profile gain

\[
\boxed{
 U_j(P^-*\tau)-U_j(P^j*\tau)
 \ge b_jH_j^c\delta/2.}
\tag{5.7}
\]

This is an ordinary unilateral stopping-law edge.  It is not a comparison of
different players' rewards and it retains the minimum tail literally.  Since
only `j`'s prescribed strategy changes, `j`'s unrestricted best-response cap
against the fixed opponents is identical at the two endpoints.  Thus its debt
is subtracted by exactly the same amount:

\[
 d_j(P^-*\tau)
 =d_j(P^j*\tau)
  -\bigl[U_j(P^-*\tau)-U_j(P^j*\tau)\bigr].
\tag{5.7a}
\]

No corresponding sign is asserted for the other players' caps or debts.

The formula consumes the entire boundary-participation arm whenever censored
reshuffling is small.  Indeed, let `i` be the hard boundary witness with
`g_i^0>=gamma`, put

\[
 a:=\gamma/R,
\]

There are three exhaustive cases.  In cases 2 and 3, `S_i>0`, so (3.4)
implies `a<=1` and every opponent of `i` has
`p_k(infinity)>=a`.

1. If `p_i(infinity)=0`, use the lossless response adapter (5.2).
2. If `1-p_i(infinity)>=a/8`, the pass response has gain at least
   `a*gamma/8` by (4.7).
3. Otherwise `p_i(infinity)>1-a/8`.  If

   \[
   \sum_k e_k\ge a/8,
   \tag{5.8}
   \]

   retain the macroscopic censored-reshuffle residual.  If (5.8) fails, the
   reviewed finite-versus-Never alternative forces

   \[
   \sum_k b_k\ge a/8.
   \tag{5.9}
   \]

   Here is the complete constant calculation.  From
   `H_i=prod_(k!=i) p_k(infinity)>=a` and the fact that all factors lie in
   `[0,1]`, every opponent satisfies `p_k(infinity)>=a`.  Point-mass
   evaluation is bounded by total variation.  Since each `e_k<a/8`, for
   `k!=i`,

   \[
   (C_Nq_k)(\infty)>p_k(\infty)-a/8\ge7a/8,
   \]

   while

   \[
   (C_Nq_i)(\infty)>p_i(\infty)-a/8>1-a/4\ge3a/4.
   \]

   Thus every censored `Never` mass is at least `3a/4`.  Finite pigeonhole
   applied to (5.9) selects `j` with

   \[
   b_j\ge a/(8|I|).
   \]

   Equations (5.7)--(5.9) give the fixed reverse-edge floor

   \[
   \boxed{
   U_j(P^-*\tau)-U_j(P^j*\tau)
   \ge
   \frac{a\delta}{16|I|}
      \left(\frac{3a}{4}\right)^{|I|-1}.}
   \tag{5.10}
   \]

For Fin4 the right side is

\[
 \frac{27\delta a^4}{4096}>0.
\tag{5.11}
\]

The same hypotheses give a sharper floor.  For `k != i`,

\[
(C_Nq_k)(\infty)>p_k(\infty)-a/8
 \ge (7/8)p_k(\infty),
\]

while `(C_Nq_i)(infinity)>3/4`.  Hence, uniformly in the selected
participant `j`,

\[
H_j^c\ge \frac34\left(\frac78\right)^{|I|-2}a.
\]

The reverse-edge gain in (5.10) is therefore at least

\[
\boxed{
\frac{3\delta a^2}{64|I|}
  \left(\frac78\right)^{|I|-2}.}
\tag{5.12}
\]

For Fin4 this is

\[
\boxed{\frac{147\delta a^2}{16384}>0,}
\tag{5.13}
\]

which is stronger than (5.11).  The weaker bound remains a useful direct
consequence of the uniform coordinate floor.

Thus a pure-Never observer cannot remain the sole obstruction in the
boundary-participation/low-reshuffle chamber: the boundary participant itself
becomes a paid mover in the reverse direction.  The only adjacent-deadline
arm not converted to a literal positive-minimum-tail paid edge by this
argument is the already named macroscopic **censored reshuffle** (5.8).

## 6. Exact spectator hybrid formula and original-label regression

At the literal lifted source `L_N p`, no opponent has mass at the new date
`N`, so Section 4 applies directly.  Later opponent-hybrid columns may have
new-date mass.  Their correct formula contains collision terms which are not
controlled by singleton isolation.

Suppose the observer is still pure `infinity` in one such column `P`.  For
`T subset I\{i}`, let `zeta_P(T)` be the probability that:

* no opponent stops before `N`;
* exactly the opponents in `T` stop at `N`; and
* every remaining opponent chooses `infinity`.

The prescribed observer is exactly the pass-into-tail strategy.  Therefore

\[
\boxed{
\begin{aligned}
 G_i^\tau(N;P)
 ={}&\sum_{\varnothing\ne T\subseteq I\setminus\{i\}}
 \zeta_P(T)
 \left[r_i(T\cup\{i\})-r_i(T)\right]\\
 &+\zeta_P(\varnothing)
 \left[r_i(\{i\})-u_i^\tau\right].
\end{aligned}}
\tag{6.1}
\]

At `P=L_Np`, every nonempty `zeta_P(T)` vanishes and (6.1) is the strict
negative singleton term from (4.11).  After opponent replacements, the first
line can have either sign.  Hence a paid grafted source can reappear only
through a concrete same-date collision membership gain.  Neither finite
pigeonhole nor changing the name of the observer manufactures that sign.

### Small exact regression for retaining the original response label

The failure of the *same-observer `Q_N` response* already occurs with two
strategic players.  A four-player extension below additionally has one literal
exact tail with a strict singleton gap in every coordinate.  Importantly, the
example does have the reverse participant edge from Section 5.1; it therefore
illustrates why role reassignment is necessary rather than refuting that
reassignment theorem.

Call the players `i,j,k,l`.  The complete reward table is the following
membership formula, valid for every nonempty coalition `S`:

\[
r_i(S)=
\begin{cases}
2,&\{k,l\}\subseteq S,\\
2,&j\in S,\ i\notin S,\\
1,&i\in S,\ j\notin S,\\
0,&\text{otherwise},
\end{cases}
\tag{6.2}
\]

\[
r_j(S)=\mathbf 1_{\{k,l\}\subseteq S},
\tag{6.3}
\]

and

\[
r_k(S)=
\begin{cases}
1,&\{k,l\}\subseteq S,\\
-1,&k\in S,\ l\notin S,\\
0,&k\notin S,
\end{cases}
\qquad
r_l(S)=
\begin{cases}
1,&\{k,l\}\subseteq S,\\
-1,&l\in S,\ k\notin S,\\
0,&l\notin S.
\end{cases}
\tag{6.4}
\]

At deadline one, take

\[
 p_i=\delta_\infty,qquad
 p_j=\tfrac12\delta_0+\tfrac12\delta_\infty,qquad
 p_k=p_l=\delta_\infty.
\tag{6.5}
\]

Player `i` gets `1` from `infinity` and `1/2` from date zero.  Player `j`
gets zero from both actions.  Each of `k,l` gets zero from `infinity` and
`-1` from date zero, because the other one never quits.  Thus `p` is Nash.
The newly exposed response `Q_1` gives `3/2`, so

\[
 G_i^0(1;L_1p)=1/2.
\tag{6.6}
\]

At deadline two, take

\[
 q_i=\delta_\infty,qquad
 q_j=\tfrac12\delta_0+\tfrac16\delta_1+
      \tfrac13\delta_\infty,qquad
 q_k=q_l=\delta_\infty.
\tag{6.7}
\]

Player `i` gets `4/3` from both `infinity` and `Q_1`, and only `1/2` from
`Q_0`.  Player `j` gets zero from every timing action.  Each of `k,l` gets
zero from `infinity`, `-1` from `Q_0`, and `-1/2` from `Q_1`; the other one
never quits, while `j` preempts date one with probability `1/2`.  Hence every
displayed marginal is a best response, `q` is Nash, and

\[
 G_i^0(1;q)=0.
\tag{6.8}
\]

Moreover censoring date one in `q_j` gives `p_j` exactly.  Thus this is a
literal adjacent projective boundary carried by observer `i`; in the hard
zero-tail games the changed mover `j` is payoff-indifferent.

Now let the retained tail `tau` make exactly `k,l` Quit surely at its first
date.  This is an exact all-behavior terminal Nash profile: `i` and `j` are
indifferent to joining the sure pair, while if either `k` or `l` continues,
the other still quits surely and the deviator's payoff falls from `1` to `0`.
All later behavior is screened by the remaining sure quitter.  Its payoff
vector is

\[
 U(\tau)=(2,1,1,1),
\tag{6.9}
\]

while the singleton rewards are `(1,0,-1,-1)`.  Hence every coordinate has
a strict singleton gap, with common floor one.

For both grafted timing laws, prescribed player `i` receives `2` regardless
of whether `j` stops in the word or the word passes to `tau`.  Direct
calculation gives

\[
 G_i^\tau(1;L_1p)=-1/2,
\qquad
 G_i^\tau(1;q)=-2/3.
\tag{6.10}
\]

Thus the retained-tail cross-difference is still positive,

\[
 G_i^\tau(1;L_1p)-G_i^\tau(1;q)=1/6,
\tag{6.11}
\]

but **both `i`-response corners are unpaid**.  Complete profile, law,
deadline, response, and tail provenance are literal and exact.

On the other hand, after the tail is grafted the participant `j` is no longer
indifferent.  Removing its date-one mass gives the deadline-one graft and
raises its payoff from `1/3` to `1/2`, an actual reverse own-law gain of
`1/6`.  This is exactly (5.6)--(5.7), with `b_j=1/6`, `H_j^c=1`, and
`u_j^tau-r_j({j})=1`.  Thus the role-reselection theorem repairs precisely the
failure displayed by the original observer.

This table has global minimum debt zero because `tau` is exact.  It is not a
counterexample to a theorem using `D_*>0` through a new global carrier
inequality.  It is the smallest two-role mechanism, embedded in Fin4 with
all four strict singleton gaps, showing that:

\[
\boxed{
\text{paid hard `Q_N` square + literal tail + strict singleton isolation}
\not\Rightarrow
\text{a paid retained-tail `Q_N` square for the same observer}.}
\tag{6.12}
\]

The correct repair is to change the mover and the response label, as in
Section 5.1.  No additional global-minimality inequality is needed for that
repair when censored reshuffling is small.

## 7. Exhaustive boundary and required new producer

For a hard exposed-boundary witness `i`, the following dispatch is exhaustive.

1. **Zero-Never observer.**  `S_i=0`; the full opponent-hybrid rectangle is
   reprojected losslessly to any supplied positive-minimum tail by (5.2)--
   (5.4).
2. **Interior observer.**  `0<S_i<1`; the hard gain is the singleton cylinder
   (3.4), while the minimum-tail pass response beats `Q_N` by the fixed amount
   (4.5).  The pass response is itself paid by at least
   `(1-S_i)*gamma`; at any fixed distance from one this is a uniform actual
   edge.  Its floor can vanish only as `S_i->1`.
3. **Near-pure spectator.**  `S_i>1-a/8`, where `a=gamma/R`.  If the total
   censored-law displacement is below `a/8`, adjacent boundary participation
   produces the fixed reverse own-law edge (5.10).  This includes the exact
   pure-`Never` observer.  If the displacement is at least `a/8`, retain the
   macroscopic censored-reshuffle object.

Consequently the finite-deadline packet plus one supplied positive-minimum
realizing chronology always yields

\[
\boxed{
\begin{array}{c}
\text{a losslessly retained `Q_N` response/rectangle}\\
\lor\ \text{a paid pass-to-tail edge}\\
\lor\ \text{a paid reverse boundary-participant edge}\\
\lor\ \text{macroscopic censored-law reshuffling.}
\end{array}}
\tag{7.1}
\]

The first three outputs are literal, source-attached behavioral objects with
fixed positive floors.  They are not yet exact Nash--Bellman chronology or
minimum-fiber endpoints.  The exact next finite-deadline producer is therefore
narrower: consume the final censored-reshuffle arm, or show that one of the
three paid edges can be fed source-faithfully to an existing return/rank
consumer.  Preserving the original `Q_N` label in the spectator arm is neither
possible nor necessary: (4.11) and Section 6 give the exact obstruction and
(5.7) gives the replacement.

## 8. Sharp actual regression and its scope

The checked Fin4 hard-deadline table makes the distinction visible.  Its
finite timing Nash profiles carry an exposed late debt at player `0`, while
its same-table comparison family has payoff coordinate

\[
 u_0=1>r_0(\{0\})=1/2
\]

and is a uniform-equilibrium family with debt tending to zero.  Grafting the
favorable retained tail suppresses the hard boundary response exactly by the
mechanism above.  This actual table has global minimum debt zero, so it is not
a positive-gap counterexample.  Its role is to show sharpness of the
spectator formulas and that the response switch is not an artifact of an
abstract semantic model.

For a hypothetical positive-minimum Fin4 table, the checked isolation theorem
supplies (4.1) and therefore strengthens rather than weakens the response
reversal.  What positive minimum does **not** supply is alignment between the
finite timing witness and the positive-debt support of the retained minimum
tail.  Proving that alignment is additional mathematics; it is not contained
in the supplied law, cap, or causalization fields.

## 9. Exact overlap and source audit

The following were inspected directly.

* `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`.
* `quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU` in
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingGame.lean`.
* The finite timing recursion and literal hard-tail realization in
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`.
* The exact retained-tail payoff and cap interfaces in
  `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingNash.lean`.
* The hard-deadline table, unique timing law, late debt, and comparison family
  in `FinFourHardDeadlineTimingNashUniqueness.lean` and
  `FinFourHardDeadlineTimingNashBarrier.lean`.
* The reviewed adjacent boundary packet
  `exports/FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md`.
* The reviewed supplied-realizer response-menu transport
  `exports/SOURCE_FAITHFUL_MINIMUM_ENDPOINT_CAUSALIZATION_AND_RESPONSE_MENU_TRANSPORT.md`.
* The conditional minimum response-chord compiler in
  `exports/FIN4_MINIMUM_RESPONSE_CHORD_ACTUAL_LAW_REGENERATION.md`.

The exact zero-tail graft ledger in
`notes/CODEX_PASCAL__ZERO_TAIL_TIMING_NASH_RETAINED_CAP_LEDGER.md` already
proves the general cap formula for a fixed zero-tail Nash law followed by an
arbitrary tail.  Equations (2.1)--(2.2) are its two-response specialization.
The new content here is:

1. support-`Never` identification (3.4);
2. composition with the checked positive-minimum singleton isolation to get
   the quantitative reversal (4.5);
3. the zero-Never lossless adjacent-rectangle adapter (5.3)--(5.4);
4. the boundary-participant reverse-edge identity (5.6)--(5.7); and
5. the quantitative exhaustive reselection which leaves only macroscopic
   censored-law reshuffling, (5.8)--(5.11).

The boundary-participation atom in the reviewed adjacent-deadline export is
counterfactual and has no payoff sign.  Equation (5.7) is not that theorem
restated: positive-minimum singleton isolation orients an actual change of the
participant's complete stopping law and makes it uniformly profitable in the
reverse direction.  Conversely, the reviewed minimum-response-chord theorem
requires both endpoint clusters already to lie on the minimum fiber.  Nothing
here proves that for the grafted profiles, so the new paid edges do not yet
instantiate that consumer.  Source-faithful causalization can preserve these
contrasts after a supplied minimum endpoint exists; it does not supply the
missing endpoint equality.

### Lean-facing boundary

The mathematical adapter separates naturally into the following declarations.

```text
finiteDeadlineQuit_sub_pass_eq_opponentNever_mul_singleton_sub_tail

finiteDeadlineNeverSupport_boundaryGain_eq_opponentNever_mul_singleton

finiteDeadlineBoundaryParticipant_reverseGain_eq

adjacentDeadline_minimumTail_paidEdge_or_censoredReshuffle
```

The third declaration should return the two literal profiles `P^j*tau` and
`P^-*tau`, their equality off player `j`, their common retained tail, and the
exact identity (5.6), not merely an existential positive gain.  The capstone
should expose a four-constructor sum matching (7.1), so downstream code cannot
mistake a paid behavioral edge for an exact chronological edge or a
minimum-fiber endpoint.

## 10. Nonclaims

* The zero-Never grafted rectangle endpoints are not asserted to lie on the
  minimum fiber.
* The positive-`Never` pass response and reverse participant response are
  actual paid unilateral edges, but are not asserted to produce an admissible
  chronological edge, a return, or a support drop.
* The hard-deadline regression has global minimum zero.
* No positive-gap reward table is constructed.
* No existing minimum-response chord hypothesis is silently inferred.
* No Lean-checking claim is made.

## 11. Concrete next question

Suppose the last arm of (7.1) holds:

\[
 \sum_j\operatorname{TV}(p_j,C_Nq_j)\ge\gamma/(8R).
\]

After decomposing each censored displacement into its `Never`-coordinate
part and its conditional finite-date part, must one obtain either

* a literal paid own-law edge over the same minimum tail;
* a retained paid `Q_N` response square whose joint-pass seam is below half
  its hard charge; or
* an exact censor-compatible replacement Nash law at deadline `N`?

The last alternative is deliberately strategic rather than metric: large
reshuffling among payoff-equivalent finite best-response dates can have no
payoff consumer, but it may provide a compatible equilibrium selection.  A
counterexample must give literal adjacent Nash laws and a minimum-isolated
tail for which all three conclusions fail.
