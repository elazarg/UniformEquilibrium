# Certificate-aware thin slices and debtor-token rotation

## Status

Ordinary mathematics, not Lean-checked.  The thin-slice theorem below is
elementary and exact.  The finite model is a proposed candidate-generation
region for the existing escape-aware exact semidecision.  It is not a proof
that the region is inhabited, not an exhaustive description of every Fin4
counterexample, and not a replacement for the outer certificate.

The point of the construction is to include positive global minimality in the
model honestly.  Local reset-rigid equations do not certify it.

## Question

Can the remaining zero-Never, positive-singleton reset chamber be realized by
a rational four-player reward table with a uniform positive exploitability
gap?  If so, can one search a finite exact region which retains both:

1. the local timing/cap-face reset geometry; and
2. an independently checkable lower certificate against every behavioral
   profile?

The answer below gives such a finite region.  It also proves a useful collapse
when the displayed source and its response target lie in a sufficiently thin
total-debt slice above a certified exploitability floor.

## 1. Global certificate versus local debt

For a behavioral profile \(\sigma\), write

\[
d_i(\sigma)=B_i(\sigma)-U_i(\sigma),\qquad
D(\sigma)=\sum_{i<4}d_i(\sigma),
\]

and

\[
\eta(r)=\inf_\sigma\max_{i<4}d_i(\sigma),
\qquad
D_* = \inf_\sigma D(\sigma).
\]

Assume an exact outer certificate proves

\[
\eta(r)\ge\gamma>0. \tag{1}
\]

Then every actual behavioral profile satisfies

\[
\max_i d_i(\sigma)\ge\gamma, \tag{2}
\]

and therefore

\[
D_*\ge\gamma. \tag{3}
\]

Consequently, any actual profile with

\[
D(\sigma)\le\gamma+\varepsilon \tag{4}
\]

is automatically within \(\varepsilon\) of the global minimum of total debt:

\[
0\le D(\sigma)-D_*\le\varepsilon. \tag{5}
\]

This is the smallest honest way to put positive global minimality into a
finite reset model using the existing exact search.  Equation (1), not the
local chamber equations, is the authoritative global input.

## 2. Thin-slice debtor-token theorem

Assume

\[
0\le\varepsilon<\gamma
\]

and let \(\sigma\) satisfy (4).  Then there is a unique player \(p\) with

\[
d_p(\sigma)\ge\gamma. \tag{6}
\]

Moreover,

\[
\sum_{i\ne p}d_i(\sigma)\le\varepsilon. \tag{7}
\]

Indeed, existence follows from (2).  If two coordinates were at least
\(\gamma\), then \(D(\sigma)\ge2\gamma>\gamma+\varepsilon\).  Subtracting
\(d_p(\sigma)\ge\gamma\) from (4) proves (7).

Now replace one player \(m\)'s complete strategy by an exact behavioral best
response and call the resulting profile \(\rho\).  Since \(m\)'s opponents
are unchanged,

\[
B_m(\rho)=B_m(\sigma)
\]

and hence

\[
U_m(\rho)-U_m(\sigma)=d_m(\sigma),
\qquad
d_m(\rho)=0. \tag{8}
\]

There are two exact conclusions.

### Small responses

If \(m\ne p\), then by (7)

\[
U_m(\rho)-U_m(\sigma)=d_m(\sigma)\le\varepsilon. \tag{9}
\]

Thus every response of gain strictly larger than \(\varepsilon\) must be made
by the unique principal debtor \(p\).

### Token rotation or slice exit

Let \(m=p\).  If

\[
D(\rho)>\gamma+\varepsilon, \tag{10}
\]

then the response has made a quantitative exit from the certified thin slice.
Otherwise, (2) and \(d_p(\rho)=0\) give a unique \(q\ne p\) such that

\[
d_q(\rho)\ge\gamma,
\qquad
\sum_{i\ne q}d_i(\rho)\le\varepsilon. \tag{11}
\]

Thus a minimum-scale exact response has only two outcomes:

\[
\boxed{
\text{exit above }\gamma+\varepsilon
\quad\text{or}\quad
\text{rotate one }\gamma\text{-scale debtor token from }p\text{ to }q.
} \tag{12}
\]

At \(\varepsilon=0\) this is literal:

\[
d(\sigma)=\gamma e_p,
\qquad
d(\rho)=\gamma e_q,
\qquad p\ne q. \tag{13}
\]

The paid gain is exactly \(\gamma\).  This is a finite semantic response
machine on four debtor labels.  It can cycle, so (12) is not by itself a
chronological consumer or a rank decrease.

## 3. Debtor rotation is impossible in a sufficiently thin slice

The apparent rotation arm in (12) is itself inconsistent when the slice is
thin enough.  This uses the global **maximum-coordinate** certificate again,
not merely total-debt minimality.

Assume both

\[
D(\sigma)\le\gamma+\varepsilon,
\qquad
D(\rho)\le\gamma+\varepsilon, \tag{14}
\]

where \(\rho\) is an exact best-response replacement by the principal debtor
\(p\).  Let \(\sigma^\theta\), \(0\le\theta\le1\), be the actual profile in
which only player \(p\)'s stopping law is replaced by the convex mixture of
its source stopping law and its response stopping law.

This is an actual behavioral profile.  In a quitting game, a player's
behavioral strategy is represented by its distribution on
\(\mathbb N\cup\{\infty\}\), and a convex mixture of two such distributions is
again represented by behavioral hazards.

Player \(p\)'s opponents are fixed along the chord.  Its cap is therefore
constant, while its prescribed payoff is affine.  Since \(d_p(\rho)=0\),

\[
d_p(\sigma^\theta)
=(1-\theta)d_p(\sigma)
\le(1-\theta)(\gamma+\varepsilon). \tag{15}
\]

For every nonmover \(i\ne p\), the prescribed payoff is affine in the mixed
stopping law of \(p\).  The cap is the supremum, over all complete responses
of \(i\), of functions affine in that same law.  Hence
\(d_i(\sigma^\theta)\) is convex and

\[
d_i(\sigma^\theta)
\le
(1-\theta)d_i(\sigma)+\theta d_i(\rho). \tag{16}
\]

Let \(q\ne p\) be the target principal debtor from (11).  The thin-slice
bounds give

\[
d_q(\sigma^\theta)\le \theta\gamma+\varepsilon, \tag{17}
\]

while for \(i\notin\{p,q\}\),

\[
d_i(\sigma^\theta)\le\varepsilon. \tag{18}
\]

Indeed, at the source all non-\(p\) debts sum to at most \(\varepsilon\), and
at the target all non-\(q\) debts sum to at most \(\varepsilon\).

Choose

\[
\theta=\frac{\gamma}{2\gamma+\varepsilon}. \tag{19}
\]

Then the two upper bounds in (15) and (17) agree:

\[
(1-\theta)(\gamma+\varepsilon)
=\theta\gamma+\varepsilon
=\frac{\gamma^2}{2\gamma+\varepsilon}+\varepsilon. \tag{20}
\]

This common value is strictly smaller than \(\gamma\) precisely when

\[
\varepsilon^2+\gamma\varepsilon-\gamma^2<0,
\]

or equivalently

\[
\frac{\varepsilon}{\gamma}
<\frac{\sqrt5-1}{2}. \tag{21}
\]

Under (21), equations (15)--(18) imply

\[
\max_i d_i(\sigma^\theta)<\gamma,
\]

contradicting the global certificate (2).

Therefore:

\[
\boxed{
\begin{array}{c}
\eta(r)\ge\gamma,quad
D(\sigma)\le\gamma+\varepsilon,quad
\varepsilon/\gamma<(\sqrt5-1)/2,\\
\rho\text{ is an exact best-response replacement by the principal debtor}
\end{array}
\Longrightarrow
D(\rho)>\gamma+\varepsilon.
} \tag{22}
\]

In particular, the exact token rotation (13) is impossible.  More generally,
if \(D_*/\eta(r)<(1+\sqrt5)/2\), then sufficiently accurate minimum profiles
cannot have a principal-debtor best-response target on the same minimum fibre.
The response must make a quantitative off-minimum excursion.

This is an actual infeasibility inequality for the thin reset chamber.  It
does not yet consume the resulting off-minimum paid port.

## 4. Incorporating the sharpened reset residual

For the zero-Never, positive-singleton residual, impose additionally on the
source profile \(\sigma\):

\[
\Pr_\sigma(T=\infty)=0, \tag{23}
\]

and, for fixed \(j\),

\[
\Pr_\sigma(Q_T=\{j\})\ge\lambda>0. \tag{24}
\]

For a reset-rigid boundary source also fix an owner \(o\) with

\[
d_o(\sigma)=0. \tag{25}
\]

If \(\sigma\) lies in the thin slice, then \(o\ne p\).  An exact response by
the principal debtor either leaves the slice or rotates the principal debtor
to some \(q\ne p\).  The old zero coordinate \(o\) need not remain zero.  In
fact, when \(q=o\), the response is exactly the debtor-rotation obstruction:
the reset has reactivated the old zero at certificate scale.

This shows why a zero-preserving response lemma is genuinely stronger than
global minimality.  Global minimality confines the leakage to one new
certificate-scale coordinate in a thin slice; it does not forbid that
coordinate from being a former zero.

## 5. A finite exact candidate region

Fix rational parameters

\[
H,N\in\mathbb N,
\qquad
0<\varepsilon<\gamma,
\qquad
\lambda,g,\beta,\tau>0.
\]

The candidate variables are:

1. a rational normalized reward table
   \(r_i(S)\in[-1,1]\) for the fifteen nonempty coalitions;
2. four rational stopping laws for a source profile \(\sigma\), supported on
   \(\{0,\ldots,H\}\cup\{\infty\}\);
3. a player \(p\) and one pure stopping time
   \(t_p\in\{0,\ldots,H+1,\infty\}\) attaining \(p\)'s cap against the finite
   source opponents;
4. the literal response profile
   \(\rho=(t_p,\sigma_{-p})\); and
5. an independently verifiable outer certificate \(C_{N,\gamma}(r)\) proving
   (1) for every behavioral profile.

For finite-clock opponents, the unrestricted cap is the maximum over the
finite payoff-distinct pure-time menu.  Hence the source and target payoffs,
caps, debts, Never mass, and terminal coalition masses are rational functions
of these variables and can be compared exactly after clearing positive
denominators.

Impose the following exact constraints.

### Global positive-gap certification

The proof object \(C_{N,\gamma}(r)\) passes the independent escape-aware
verifier.  In the current exact search this may be produced by a finite-clock
lower tree plus the common-quantile transport allowance.  It is essential:
no finite list of displayed response times can replace it.

### Thin reset source

\[
D(\sigma)\le\gamma+\varepsilon,
\qquad
\Pr_\sigma(T=\infty)=0,
\qquad
\Pr_\sigma(Q_T=\{j\})\ge\lambda,
\qquad
d_o(\sigma)=0. \tag{26}
\]

The certificate and (17) force the unique principal debtor \(p\) and (7).

### Exact paid response

\[
t_p\in\operatorname*{argmax}_t V_p^\sigma(t),
\qquad
U_p(\rho)-U_p(\sigma)=d_p(\sigma)\ge g,
\qquad
d_p(\rho)=0. \tag{27}
\]

For the sharp token region one asks also

\[
D(\rho)\le\gamma+\varepsilon. \tag{28}
\]

Then a fixed new principal debtor \(q\ne p\) satisfies (11).  Requiring
\(q=o\) isolates literal reactivation of the reset zero; allowing arbitrary
\(q\) searches the whole debtor-rotation face.

### Optional strict all-Continue chamber

Unique all-Continue at the displayed cap is a quantified complementarity
condition.  A finite sufficient subchamber is strict pointwise Continue
dominance: for every player \(i\),

\[
B_i(\rho)\ge r_i(\{i\})+\beta, \tag{29}
\]

and for every nonempty opponent coalition
\(A\subseteq I\setminus\{i\}\),

\[
r_i(A)\ge r_i(A\cup\{i\})+\beta. \tag{30}
\]

Then Continue strictly dominates Quit at every product root against the cap,
so all Continue is the unique exact product root.  This is deliberately a
strong search filter, not an asserted consequence of the residual.

A supported member-leaving toggle remains compatible with (21): require some
\(h\in S\) with positive source-law incidence and

\[
r_h(S\setminus\{h\})
\ge r_h(S)+\tau. \tag{31}
\]

The opposite outsider-joining toggle is incompatible with global pointwise
Continue dominance and should be searched in a separate chamber without
(21).

All constraints except the certificate verifier are finite rational
polynomial inequalities.  The certificate itself is a finite exact proof
object.  Therefore a satisfying rational assignment is independently
checkable from a clean clone.

## 6. Search organization

The existing discovery campaign searches tables first and runs the global
certificate producer.  The residual model suggests an additional candidate
generator, not a change to certificate soundness:

1. enumerate or solve the local rational constraints (23)--(31);
2. normalize and hash each resulting reward table;
3. submit the table to the existing escape-aware lower/upper campaign;
4. accept it only if the produced lower certificate independently verifies.

The local system is valuable because it searches specifically for the only
thin-slice leakage pattern permitted by a positive global certificate.  A
solver witness without \(C_{N,\gamma}(r)\) is only a local regression.

## 7. Exact no-go for purely finite local models

No bounded response menu alone can certify this chamber as a counterexample.
For every fixed horizon, a table/profile can agree with all tested payoffs and
still admit a profitable deviation immediately after the last represented
date.  Likewise, finite stopping laws can move mass to infinity while their
finite coordinates converge to zero.

Therefore the smallest honest finite model has two logically separate parts:

\[
\boxed{
\text{finite rational reset/timing witness}
\quad+\quad
\text{escape-aware global lower proof object}.
} \tag{32}
\]

The first part locates the sharpened residual.  The second certifies positive
global minimum.  Conflating them would reproduce the finite-clock
incompleteness that the exact search hierarchy was designed to avoid.

## 8. What this does and does not achieve

The proved mathematical gain is the debtor-token reduction (12) together with
the chord obstruction (22).  Below the golden-ratio slice width, a
positive-minimum exact response cannot rotate the token at all: it must make a
quantitative off-minimum excursion.

The proposed finite region is suitable for exact semidecision and contains
the required positive-global-min proof object.  It does not show that the
region is nonempty.  Nor is the thin slice exhaustive: a counterexample could
have

\[
D_* - \eta(r)>0,
\]

in which case no profile need satisfy (4) for a certified
\(\gamma\le\eta(r)\).  Such a table remains in the broader full-debt/reset
chambers.

The next decisive test is computational and exact: search the rational region
(23)--(31), and either obtain a verified positive-gap table or prove one full
subchamber infeasible by a checkable rational/interval certificate.

## 9. A global quantitative separation between the two debt minima

The chord argument has a consequence which no longer assumes that the full
best-response target remains in the thin slice.

Assume rewards lie in \([-M,M]\), with \(M>0\), and define

\[
\eta=\inf_\sigma\max_i d_i(\sigma)>0,
\qquad
D_* = \inf_\sigma\sum_i d_i(\sigma).
\]

Then

\[
\boxed{
D_* - \eta
\ge
\sqrt{4M^2+\eta^2}-2M
=
\frac{\eta^2}{\sqrt{4M^2+\eta^2}+2M}>0.
} \tag{33}
\]

Thus a counterexample cannot have minimum total debt equal, or arbitrarily
close relative to the fixed reward scale, to minimum maximum-coordinate
debt.

### Proof

Put \(h=D_* - \eta\ge0\).  Suppose for contradiction that

\[
h^2+4Mh-\eta^2<0. \tag{34}
\]

Choose an actual profile \(\sigma\) with

\[
D(\sigma)\le D_*+\delta
=\eta+h+\delta, \tag{35}
\]

where \(\delta>0\) will be arbitrarily small.  Select \(p\) with maximum
debt \(a=d_p(\sigma)\).  Then

\[
\eta\le a\le\eta+h+\delta, \tag{36}
\]

and every non-\(p\) coordinate satisfies

\[
d_i(\sigma)
\le D(\sigma)-a
\le h+\delta. \tag{37}
\]

Choose a complete \(\zeta\)-best response by player \(p\), and mix its
stopping law with the source stopping law at weight \(\theta\).  Call the
actual mixed profile \(\sigma^\theta\).

The mover's cap is unchanged and its prescribed payoff is affine, so

\[
d_p(\sigma^\theta)
\le(1-\theta)(\eta+h+\delta)+\theta\zeta. \tag{38}
\]

For a nonmover \(i\), every response payoff is affine in player \(p\)'s mixed
stopping law.  All payoffs lie in \([-M,M]\).  Therefore both the prescribed
payoff and the supremal cap move by at most \(2M\theta\), giving

\[
d_i(\sigma^\theta)
\le h+\delta+4M\theta. \tag{39}
\]

Condition (34) is exactly

\[
\frac{h}{\eta+h}<\frac{\eta-h}{4M}. \tag{40}
\]

Choose \(\theta\) strictly between these two quantities.  Then choose
\(\delta,\zeta>0\) sufficiently small.  Equations (38)--(40) give

\[
d_i(\sigma^\theta)<\eta
\qquad(i<4),
\]

contradicting the definition of \(\eta\).  Hence

\[
h^2+4Mh-\eta^2\ge0.
\]

Since \(h\ge0\), solving the quadratic proves (33).

The proof uses no attainment of a best response or of either infimum.  The
parameters \(\delta\) and \(\zeta\) absorb both approximations.  It uses only
the exact stopping-law convexity available in quitting games and the complete
behavioral cap.

### Relation to the reset residual

Equation (33) eliminates the sharp token face \(D_*=\eta\) outright and gives
a quantitative moat above it.  It also explains why the off-slice target in
(22) is unavoidable: a counterexample needs enough total residual debt to
prevent a partial best response from lowering every coordinate below the
global maximum-debt floor.

This does not consume reset rigidity.  It moves the surviving chamber into
the genuinely multi-debtor regime

\[
D_*\ge \eta+\frac{\eta^2}
 {\sqrt{4M^2+\eta^2}+2M},
\]

where cross-coordinate leakage has a quantitatively necessary budget.

## 10. A fixed off-minimum paid port below the two-debtor threshold

There is a sharper connection to the existing off-minimum paid-port waist.
Continue to write \(\eta>0\) for the global minimum of maximum-coordinate
debt.

Let \(\sigma\) be an actual profile, put

\[
S=D(\sigma),
\qquad
a=\max_i d_i(\sigma),
\]

and select a maximizing player \(p\).  Assume

\[
\eta<S<2\eta. \tag{41}
\]

Let \(\rho\) be an exact best-response replacement by \(p\).  Then

\[
\boxed{
D(\rho)-S
\ge
\frac{a(2\eta-S)}{a-\eta}
\ge
\frac{S(2\eta-S)}{S-\eta}>0.
} \tag{42}
\]

This statement is conditional on exact best-response attainment and applies
directly to a finite-clock source.  A complete behavioral cap need not be
attained at one pure time in general; the carrier passage below uses
\(o(1)\)-best responses instead.

### Proof

First \(a>\eta\).  If \(a=\eta\), mix \(p\)'s source stopping law with its
exact response by any weight \(\theta>0\).  The mover debt becomes
\((1-\theta)\eta<\eta\), so the global exploitability floor forces some
other coordinate to have debt at least \(\eta\).  Letting \(\theta\downarrow0\)
and stabilizing that label would give two source debts at least \(\eta\),
contrary to \(S<2\eta\).

Along the response chord, the mover debt is

\[
d_p(\sigma^\theta)=(1-\theta)a.
\]

At

\[
\theta_0=\frac{a-\eta}{a}, \tag{43}
\]

the mover debt is exactly \(\eta\).  For every \(\theta>\theta_0\), it is
strictly smaller than \(\eta\), so another player has debt at least
\(\eta\).  By finiteness and continuity, at \(\theta_0\) some fixed
nonmover also has debt at least \(\eta\).  Therefore

\[
D(\sigma^{\theta_0})\ge2\eta. \tag{44}
\]

Every coordinate debt is convex along a one-player stopping-law chord:
the mover debt is affine, and a nonmover cap is a supremum of affine response
payoffs while its prescribed payoff is affine.  Hence total debt is convex,
so

\[
2\eta
\le D(\sigma^{\theta_0})
\le(1-\theta_0)S+\theta_0D(\rho). \tag{45}
\]

Solving (45) gives the first bound in (42).  Since \(a\le S\) and
\(a/(a-\eta)\) decreases in \(a\), the second follows.

### Exact-attainment minimum-fibre consequence

If an actual global minimum exists and

\[
\eta<D_*<2\eta,
\]

then a best response by any maximal debtor has gain at least \(\eta\) and
lands a fixed distance off the minimum fibre:

\[
D(\rho)-D_*
\ge
\Delta_{\mathrm{port}}
:=
\frac{D_*(2\eta-D_*)}{D_* - \eta}>0. \tag{46}
\]

### General actual/carrier passage

The same conclusion holds without response attainment.  Let \(x\) be a
carrier minimum with

\[
D(x)=D_*,
\qquad
\eta<D_*<2\eta. \tag{47}
\]

Choose actual realizers \(\sigma_n\to x\).  At each \(n\), select a
maximum-debt player and pass to a subsequence on which this player is one
fixed \(p\).  Write

\[
S_n=D(\sigma_n)\to D_*,
\qquad
a_n=d_p(\sigma_n)\to a=d_p(x). \tag{48}
\]

Then \(p\) maximizes debt at \(x\), so \(a\ge\eta\).  In fact

\[
a>\eta. \tag{49}
\]

If \(a=\eta\), then because \(D_*<2\eta\), every other debt at \(x\) is
strictly below \(\eta\).  A sufficiently small fixed mixture with an
\(o(1)\)-best response by \(p\) lowers the \(p\)-debt strictly below
\(\eta\), while the other debts remain below \(\eta\) by the uniform
\(4M\theta\) estimate (39).  This contradicts the definition of \(\eta\).

Choose \(\zeta_n\downarrow0\) and a \(\zeta_n\)-best response by \(p\), with
target \(\rho_n\).  Put

\[
e_n=d_p(\rho_n)\le\zeta_n. \tag{50}
\]

Along the literal one-player stopping-law chord, mover debt is exactly

\[
(1-\theta)a_n+\theta e_n.
\]

It crosses \(\eta\) at

\[
\theta_n=\frac{a_n-\eta}{a_n-e_n}
\longrightarrow
\theta_*:=\frac{a-\eta}{a}\in(0,1). \tag{51}
\]

Choose \(\widehat\theta_n>\theta_n\) with
\(\widehat\theta_n-\theta_n\to0\).  At this point mover debt is below
\(\eta\), so some nonmover has debt at least \(\eta\).  Mover debt tends to
\(\eta\), and hence

\[
\liminf_n D(\sigma_n^{\widehat\theta_n})\ge2\eta. \tag{52}
\]

Convexity gives

\[
D(\sigma_n^{\widehat\theta_n})
\le
(1-\widehat\theta_n)S_n
+\widehat\theta_nD(\rho_n). \tag{53}
\]

Taking lower limits,

\[
\liminf_n D(\rho_n)
\ge
\frac{\eta(2a-D_*)}{a-\eta}. \tag{54}
\]

Equivalently,

\[
\liminf_n(D(\rho_n)-D_*)
\ge
\frac{a(2\eta-D_*)}{a-\eta}
\ge
\Delta_{\mathrm{port}}>0. \tag{55}
\]

The response gain is at least \(a_n-\zeta_n\to a\ge\eta\), and every
\(\rho_n\) differs from \(\sigma_n\) only in player \(p\)'s literal complete
strategy.  Compactification therefore retains an actual same-opponents paid
sequence and produces an off-minimum response target.  No cap attainment is
asserted at the limit.

Thus the entire ratio chamber

\[
1< D_*/\eta <2 \tag{56}
\]

feeds a **quantitative off-minimum paid-response port**; it cannot support a
minimum-fibre debtor rotation.  This is the desired connection to the known
paid-cap waist.  The remaining unresolved step is still the consumer of that
off-minimum port.  The complementary chamber

\[
D_*\ge2\eta
\]

has enough total debt for two certificate-scale debtors and is the genuine
wide reset/full-debt residual.

## Inspected sources

- `questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`;
- `Experiments/fin4_exact_search/README.md`;
- `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashStrictMinimum.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/FinFourLawTightCapNashStrictMinimum.lean`;
- `UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumDebtSimplex.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumLawFiniteAtom.lean`.
