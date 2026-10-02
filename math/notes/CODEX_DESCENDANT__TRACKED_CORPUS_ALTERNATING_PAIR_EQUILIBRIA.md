# The tracked exact-search corpus has alternating-pair equilibria

Author: `CODEX_DESCENDANT`

## Status

**Exact ordinary mathematics, independently reproducible from rational data;
not Lean-checked.**  Each of the four normalized rational tables currently
enumerated by the exact discovery campaign has an exact terminal Nash profile
of period two.  The two phases use the complementary active pairs

\[
  \{0,3\},\qquad \{1,2\}.
\]

The existence proof is a finite Poincare--Miranda certificate using rational
boxes, rational preconditioners, and exact rational interval arithmetic.  The
inactive endpoint inequalities are uniformly strict.  Thus the profiles are
Nash against the complete behavioral deviation class, not only against
stationary or bounded-clock deviations.

Consequently every table in the tracked campaign has

\[
  \eta(r)=0.
\]

In particular the lower-certificate branch cannot terminate on any of these
four exact tables.  Truncating the periodic equilibrium gives finite-clock
product profiles with exploitability tending geometrically to zero.  The
same Poincare--Miranda certificate persists throughout an explicit
coordinatewise reward ball of radius (10^{-7}) around each table.  This is
a complete upper witness for the present corpus and four small open
neighborhoods, not a statement about every future candidate table.

## 1. Exact question and inspected sources

The question was whether the tables selected by the local singleton-collision
and response-cycle screens survive a small genuinely chronological product
class.  A positive-gap candidate must defeat such profiles before an expensive
all-behavior lower search is meaningful.

The exact tables are the output of `load_tracked_candidates` in
`Experiments/fin4_exact_search/fin4_exact_search/candidate_campaign.py`, with
rationalization denominator (10000), applied to
`Experiments/singleton_collision_candidate_search/results.json`.  The
all-behavior certificate contract is the one in
`math/questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md` and the checked
quantile-clock hierarchy recorded in
`math/formalized/ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md`.

The four canonical table hashes are

\[
\begin{array}{c|c}
\text{candidate}&\text{canonical SHA-256}\
\hline
\text{seed}&
\texttt{f1ef6fea651f143cda1036180ba4d23f58381530ada9622e9603192311d57163}\\
\text{chain 40}&
\texttt{1d634c1a162c39b91485e5f9d2976d3923ef1a45a59f6baceb8751e4334c10c7}\\
\text{chain 41}&
\texttt{7abf4ff578bf63f701288dbdc12b37bf65e0e3488b11168d6436a69ad436a6ea}\\
\text{chain 42}&
\texttt{5e9c89bf03444bd36d02b70332bae2dc848cc6b11146d7c0e9a47416fbdb346f}.
\end{array}
\tag{1.1}
\]

Appendix A lists the exact rational reward rows, so the claim does not depend
only on these identifiers.

## 2. The two-periodic product profile

Let

\[
 q^A=(a,0,0,d),\qquad q^B=(0,b,c,0),
 \qquad 0<a,b,c,d<1.                       \tag{2.1}
\]

At phase (A), players (0,3) mix and players (1,2) Continue.  At phase
(B), players (1,2) mix and players (0,3) Continue.  Repeat the phases
forever.

For a product root (q), write

\[
 s(q)=\prod_i(1-q_i),\qquad
 A_i(q)=\sum_{\varnothing\ne S\subseteq I}
     \Pr_q(S)r_i(S),                       \tag{2.2}
\]

so the one-root transform is

\[
 T_q(V)=A(q)+s(q)V.                         \tag{2.3}
\]

Put (s_A=s(q^A)), (s_B=s(q^B)).  The two phase values are the rational
functions

\[
 V^A_i={A_i(q^A)+s_AA_i(q^B)\over1-s_As_B},
 \qquad
 V^B_i=A_i(q^B)+s_BV^A_i.                  \tag{2.4}
\]

The denominator is positive throughout every box used below.

Let (E_i(q;V)) denote Quit payoff minus Continue payoff for player (i) at
root (q) with next value (V).  Define

\[
 F(a,b,c,d)=
 \bigl(
 E_0(q^A;V^B),
 E_3(q^A;V^B),
 E_1(q^B;V^A),
 E_2(q^B;V^A)
 \bigr).                                   \tag{2.5}
\]

A zero of (F) makes the four active players indifferent in their respective
phases.  The four inactive endpoint differences are

\[
 E_1(q^A;V^B),\ E_2(q^A;V^B),\
 E_0(q^B;V^A),\ E_3(q^B;V^A).              \tag{2.6}
\]

## 3. Rational Poincare--Miranda certificate

The following elementary certificate is used four times.  Let (x_0\in
\mathbb Q^4), let (r>0), and put

\[
 Q=x_0+[-r,r]^4.
\]

Choose (A\in\mathbb Q^{4\times4}), set (G=AF), and bound all derivatives
of (G) on (Q) by exact rational interval arithmetic.  If

\[
 m_i=
 r\inf_Q\partial_iG_i-|G_i(x_0)|
 -r\sum_{j\ne i}\sup_Q|\partial_jG_i|>0       \tag{3.1}
\]

for every (i), then (G_i<0) on the negative (i)-face and (G_i>0) on
the positive (i)-face.  Poincare--Miranda gives (G(x)=0) for some (x\in
Q).  Condition (3.1) also makes the Jacobian of (G) strictly row-diagonally
dominant, so (A) is nonsingular.  Hence (F(x)=0).

For every candidate below take

\[
 r=10^{-5}.                                \tag{3.2}
\]

The centers are listed in variable order ((a,b,c,d)):

\[
\begin{array}{c|c}
\text{candidate}&x_0\\ \hline
\text{seed}&
(26547470883023/10^{14},26547470883023/10^{14},
25390254180870037/10^{17},25390254180870037/10^{17})\\
\text{chain 40}&
(252463270683174321/10^{18},138078811186281269/10^{18},
275438867868966939/10^{18},41864758369476139/(25\cdot10^{16}))\\
\text{chain 41}&
(84011086378602587/(2\cdot10^{17}),8994927047059821/(4\cdot10^{16}),
100196140494143077/(25\cdot10^{16}),261625632537410677/10^{18})\\
\text{chain 42}&
(179497493442466127/10^{18},58509148169910477/(5\cdot10^{17}),
33436371041247949/(25\cdot10^{16}),180029595329477163/10^{18}).
\end{array}                                             \tag{3.3}
\]

The rational preconditioners are:

\[
A_{\rm seed}=\begin{pmatrix}
154491/10^5&1044971/10^6&-16369/125000&1044971/10^6\\
-16369/125000&1044971/10^6&154491/10^5&1044971/10^6\\
134971/125000&-120583/10^6&422573/500000&1422587/10^6\\
422573/500000&1422587/10^6&134971/125000&-120583/10^6
\end{pmatrix},                                         \tag{3.4}
\]

\[
A_{40}=\begin{pmatrix}
1085419/10^6&817881/10^6&364291/10^6&209157/250000\\
-272973/500000&146287/250000&616077/500000&510283/10^6\\
1175293/10^6&249583/10^6&368289/250000&161551/100000\\
69107/250000&190697/250000&176067/200000&-81117/200000
\end{pmatrix},                                         \tag{3.5}
\]

\[
A_{41}=\begin{pmatrix}
961609/10^6&75779/62500&109689/10^6&1111503/10^6\\
-1034097/500000&1734193/10^6&1057243/500000&-213857/500000\\
250233/200000&-437369/10^6&486063/500000&66839/31250\\
-149821/250000&863621/500000&318921/250000&-1546213/10^6
\end{pmatrix},                                         \tag{3.6}
\]

\[
A_{42}=\begin{pmatrix}
821821/500000&222173/250000&467039/10^6&1273319/10^6\\
184063/10^6&169761/250000&117171/125000&40697/50000\\
1107851/10^6&53977/10^6&49173/62500&973/800\\
293599/250000&562681/500000&135329/125000&587681/10^6
\end{pmatrix}.                                         \tag{3.7}
\]

Direct exact interval evaluation gives, for all four coordinates of all four
certificates,

\[
 m_i>{9\over10^6}.                                     \tag{3.8}
\]

It also gives, throughout the same boxes,

\[
 \max\{E_1(q^A;V^B),E_2(q^A;V^B),
          E_0(q^B;V^A),E_3(q^B;V^A)\}
 <-{1\over100}.                                        \tag{3.9}
\]

All box coordinates lie strictly between zero and one.  Equations
(3.1)--(3.9) are a finite rational proof that every candidate has a point
((a,b,c,d)) at which the active coordinates mix and all inactive coordinates
strictly prefer Continue.

## 4. Upgrade to unrestricted terminal Nash

At the zero supplied by Section 3, each displayed root is an exact product
Nash root against the next phase value.  Equations (2.4) are the exact Bellman
recursion for the repeated profile.

This controls arbitrary behavioral deviations.  Fix a player (i).  Against
the other three periodic clocks, the two-phase dynamic programming operator is
a contraction: in one period every opponent has one active hazard in
((0,1)).  The endpoint inequalities state that the prescribed action attains
the Bellman maximum at each phase.  Iterating the contraction, or equivalently
using pure-time extremality, shows that no complete stopping law improves the
payoff.  Hence

\[
 B_i=U_i\qquad(i=0,1,2,3),                              \tag{4.1}
\]

and the two-periodic profile is an exact terminal Nash profile.

This is not a stationary-gap, pure-cycle, local-face, or bounded-deviation
claim.  It is an executable infinite behavioral profile and its cap is taken
over every unilateral behavioral replacement.

## 5. Finite-clock upper witnesses

The same certificate gives an elementary finite-clock approximation, useful
for the upper branch of the exact hierarchy.

Let

\[
 h_i=\prod_{j\ne i}(1-q_j),
 \qquad h=\max_i h_i,                                  \tag{5.1}
\]

where each (q_j) denotes the one nonzero hazard of player (j) in a full
two-phase period.  Exact interval evaluation on every certificate box gives

\[
 h<{2\over3}.                                           \tag{5.2}
\]

Truncate the periodic profile after (L) full periods by moving every later
finite stopping mass to Never.  The ordinary outcome changes only if all four
players survive (L) periods, and the payoff under an arbitrary replacement
of player (i) changes only if all three opponents survive.  Since rewards
are in ([-1,1]), coupling gives

\[
 |U_i^{(L)}-U_i|\le2h^L,
 \qquad
 |B_i^{(L)}-B_i|\le2h^L.                               \tag{5.3}
\]

Using (4.1),

\[
 \operatorname{Expl}_r(\sigma^{(L)})
 \le4h^L
 <4(2/3)^L.                                            \tag{5.4}
\]

Thus every tracked table has an explicit finite-clock product upper sequence.
The exact root can be algebraic rather than rational.  Rational hazard vectors
are dense, and all denominators in (2.4) stay uniformly away from zero on the
certificate boxes, so each finite-clock upper witness can in turn be
approximated by a rational finite-clock witness with arbitrarily small added
exploitability.  This is exactly the kind of upper object enumerated by the
escape-aware hierarchy.

## 6. Consequence for candidate generation

### 6.1 Explicit robust rejection balls

The certificates reject more than four isolated tables.  Let (r') be any
reward table satisfying

\[
 \lVert r'-r\rVert_\infty<{1\over10^7}                 \tag{6.1}
\]

for one of the four displayed tables (r).

Fixing the hazards, a periodic payoff is the expectation of one terminal
reward coordinate.  Hence changing every reward coordinate by at most
(\delta) changes each periodic value by at most (delta).  Each endpoint
difference is a difference of two such expected payoffs, and therefore

\[
 \lVert F_{r'}(x)-F_r(x)\rVert_\infty\le2\delta
 \qquad(x\in Q).                                        \tag{6.2}
\]

The maximum absolute row sum among all four preconditioners in
(3.4)--(3.7) is

\[
 {6344587\over10^6}<7.                                  \tag{6.3}
\]

Thus every signed face value of (A F) moves by less than

\[
 14\delta< {14\over10^7}< {9\over10^6}.                \tag{6.4}
\]

The strict Poincare--Miranda signs survive.  Each inactive endpoint
difference moves by at most (2\delta), so (3.9) also stays strictly
negative.  Therefore every (r') satisfying (6.1) has an exact alternating
pair terminal Nash profile in the same hazard box and has (eta(r')=0).

This robust conclusion is useful for candidate generation: exact rational
tables inside any of these four balls can be discarded by the same finite
certificate, without starting a lower-tree search.

### 6.2 Campaign implication

The current exact discovery campaign is logically sound, but its entire
tracked corpus lies on the upper branch.  Searching the lower tree on these
tables cannot produce a positive-gap certificate.

The smallest useful additional candidate screen is therefore:

1. enumerate the three partitions of four players into two pairs;
2. for each order of the two pair phases, solve the four active endpoint
   equations for a two-periodic product profile;
3. certify an interior zero and the four inactive signs by rational boxes; and
4. reject a table whenever such a certificate exists.

This screen is not a complete decision procedure.  Failure of the screen is
not evidence of a positive all-behavior gap.  It merely prevents expensive
lower-certificate work on tables already defeated by a very small exact
chronological product class.

The broader cross-vertex lesson is consistent with the cap-Jensen identity:
local pure response cycles can coexist with a product mixture that selects a
common alternating active face.  A credible hard-table generator should
penalize not only stationary and pure-clock escapes but also low-period
complementary-pair Bellman roots.

## 7. Exact nonclaims

This note does not provide:

* a positive-gap table;
* a lower certificate for any table;
* a decision procedure for arbitrary Fin4 tables;
* a proof that period two suffices outside the tracked corpus.

It does prove that the four tables presently prioritized by the exact campaign
cannot be counterexamples and supplies finite-clock product upper witnesses
approaching zero exploitability.

## Appendix A. Exact normalized reward tables

Rows are indexed by coalition mask (1,\ldots,15), with bit (i) denoting
player (i).

### Seed

\[
\begin{array}{c|rrrr}
1&1/4&1&0&0\\2&1&1/4&0&0\\3&1/4&1/4&1/4&1/4\\
4&0&0&1/4&1\\5&1/4&1/4&1/4&0\\6&0&1/4&1/4&1/4\\
7&1/4&0&0&0\\8&0&0&1&1/4\\9&1/4&0&1/4&1/4\\
10&1/4&1/4&0&1/4\\11&0&1/4&0&0\\12&1/4&1/4&1/4&1/4\\
13&0&0&0&1/4\\14&0&0&1/4&0\\15&-1/4&-1/4&-1/4&-1/4
\end{array}                                             \tag{A.1}
\]

### Chain 40

\[
\begin{array}{c|rrrr}
1&1543/9593&1&0&0\\2&1&2368/7843&-87/9820&0\\
3&1/4&1208/5793&2289/5030&976/3529\\
4&213/6746&0&1/4&8009/8180\\5&1/4&1/4&2857/9999&431/4566\\
6&-53/8001&765/4126&678/2731&1/4\\7&1/4&0&0&16/841\\
8&0&0&1&1/4\\9&1532/4919&-1243/9204&1/4&4397/7286\\
10&2933/8691&452/1693&190/8999&1/4\\
11&540/3493&455/1857&0&766/9693\\
12&943/6449&1/4&2111/8916&799/3976\\
13&596/7001&29/6720&0&4536/8977\\14&0&-561/5158&1/4&0\\
15&-1163/5539&-1/4&-1267/5028&-1/4
\end{array}                                             \tag{A.2}
\]

### Chain 41

\[
\begin{array}{c|rrrr}
1&268/7609&1&469/7326&0\\2&1&1/4&-139/7984&3961/9833\\
3&1097/5009&2534/8665&1/4&685/8158\\4&0&0&1/4&3437/4261\\
5&1/4&5108/8079&1/4&-466/7403\\6&-889/7845&1/4&904/6853&1/4\\
7&1/4&0&0&0\\8&-809/6637&0&1&1/4\\
9&1/4&0&747/3151&2287/8362\\10&3471/9064&1354/6587&0&1/4\\
11&-1269/8572&642/7895&0&0\\12&1/4&2443/7932&288/841&1/4\\
13&0&0&-216/4271&2254/9951\\14&0&0&2422/8983&44/3491\\
15&-655/2268&-47/446&-1/4&-2884/9039
\end{array}                                             \tag{A.3}
\]

### Chain 42

\[
\begin{array}{c|rrrr}
1&1/4&1&0&0\\2&1&1/4&-741/5878&-368/6713\\
3&2929/9134&1/4&373/1373&1/4\\4&557/5348&-538/9753&836/2699&1\\
5&1/4&1049/3748&313/1811&229/5726\\6&0&2131/7484&1/4&1254/4889\\
7&1144/6363&-145/8406&475/4969&-289/1839\\8&0&-539/4968&1&45/188\\
9&1/4&0&1810/7151&1754/5213\\10&776/2109&1/4&-165/5366&1790/6427\\
11&21/6086&2672/9075&252/3835&571/7198\\
12&1021/4024&626/3817&1/4&2227/3605\\
13&0&-1/4&-109/8161&1/4\\14&0&0&1/4&575/9816\\
15&-404/2135&-1/4&-1871/8228&-1113/8915
\end{array}                                             \tag{A.4}
\]
