# Two-owner moment rigidity and a contact-rich actual replacement

Owner: CODEX_COORDINATOR. Ordinary mathematics.
This is a source-preserving normal form, not an equilibrium producer or an
exclusion of the I2 source. It requires the generic positive absorbing-gap
hypotheses used in the current I2 source reduction.

## Data and source

Four players have a finite native reward table Z, own singleton and Never
rewards zero. Players privately choose independent laws on Nat plus Never;
all unilateral replacement laws are allowed. Fix pivot p, partner i, and
quiet observers h,k. From a finite cut onward only p and i have finite
atoms, each infinitely many. All marginal Never masses are positive. The
whole profile is an actual global minimum of J_r=d_p+r nu on the carrier
with zero debts of the three observers; all full caps are attained by
Never. The generic positive absorbing full-debt gap supplies the uniform
tail dispersion bound

    D >= c (f_p+f_i)^2, c>0,

for every actual two-owner profile at this same table. The source bound
comes from the [uniform dispersion theorem](../exports/UNIFORM_THREE_OWNER_TAIL_DISPERSION.md),
not from assumed minimality of a conditional suffix. ALL-END and zero observer debts pass to every
conditional tail.

Work with the conditional pair tail once at the fixed cut. Let alpha_n,
beta_n be its unconditional atoms, P=sum alpha, I=sum beta, and
T=sum alpha_n beta_n. Put

    G=Z_i({p}), J=Z_i({p,i}), A=Z_p({i}), C=Z_p({p,i}), rho=G/J.

The established I2 contact argument gives J!=0, 0<rho<1 and
A-rho C>0. At every positive beta_n,

    alpha_n=rho P_n, P_n=sum_(m>=n) alpha_m.                 (1)

Let a=Pr(both finite and p first), b=Pr(both finite and i first).
Then a+b+T=PI, and (1) implies

    b=(1/rho-1)T, a=PI-T/rho.                             (2)

## Exact moment rigidity

For a quiet player j in {h,k}, write

    g_j=Z_j({p}), a_j=Z_j({i}), D_j=Z_j({p,i}),
    K_j=D_j-g_j/rho+a_j(1/rho-1).

Its Never payoff, also its cap, is

    B_j=g_j P+a_j I-a_j PI+K_j T.                         (3)

The active observer's cap is B_i=GP. The pivot cap and debt are

    B_p=A I,
    d_p=A PI-[C+A(1/rho-1)]T, nu=(1-P)(1-I).              (4)

Thus if

    a_h K_k-a_k K_h !=0,                                 (5)

the three observer caps determine P,I,T uniquely. Indeed B_i fixes P;
the determinant of the remaining linear system in (I,T) is
(1-P)(a_h K_k-a_k K_h), nonzero because P<1. Every other pair tail with zero observer debts, ALL-END, positive Never
masses, and these observer caps has the same pivot cap, debt and Never
mass.
This does not assume the two tails share a calendar.

Consequently a fixed-observer-cap variation confined to the same pair
cannot give a strict objective decrease under (5). A useful descent must
activate another owner, change a retained cap, or leave ALL-END. This is
an exact rigidity statement, not evidence against equilibrium existence.

## Actual replacement with many extra contacts

There exists another actual pair tail with exactly the same complete
(U,B,N) tuple, the same pivot law, and the following property. For every
finite physical-date interval W,

    number of positive partner atoms in W
       <= 2 + number of tied comparisons in W,            (6)

where tied comparisons are counted separately for each recipient in
{p,h,k}: its pure date-t Quit response equals its Never payoff. The
partner's own contacts are not counted. The modified whole profile is
therefore another actual global minimum, with the old head unchanged.
Statement (6) does not require the nondegeneracy (5).

To prove this, freeze alpha and its Never mass. Allow beta to vary only on

    L={n: J alpha_n=G P_n}.

Fix its total mass I, hence its Never mass 1-I, and tie moment T. Require
all pure-date comparisons of p,h,k to be no better than Never. These
requirements are affine closed inequalities in beta. Observer i's full
best-response cap depends only on the fixed pivot law, and its permitted
atoms and Never all attain it. The two quiet observers prescribe Never.
Thus each feasible beta has zero observer debt and is ALL-END; (2)--(4)
show the entire (U,B,N) tuple is fixed.

The feasible set F is nonempty, convex, and compact in total variation.
Here compactness requires proof: fixed total mass alone would allow escape
to infinity. For any member and any tail cut n, let f_p,f_i be the
conditional remaining finite masses. ALL-END coupling gives

    d_p <= 2M f_p f_i,

because replacing the pivot's draw by Never can change the outcome only
when both finite clocks are drawn. Together with uniform dispersion,

    c(f_p+f_i)^2 <=2M f_p f_i.

In particular f_i <= (2M/c)f_p. With N_p=1-P fixed,

    I_n <= f_i <= (2M/(c N_p)) P_n.                      (7)

Since P_n tends to zero, (7) gives uniform tightness of all feasible partner
laws. Coordinatewise subsequence extraction plus this bound gives total
variation convergence. The mass, moment and full comparison constraints
are closed in that topology, so F is compact.

Choose a maximizer on F of the strictly convex continuous function
sum_n beta_n^2. Every such maximizer is extreme: a nontrivial midpoint
representation would have strictly smaller squared norm than the average
of its endpoints, contradicting maximality.

Suppose (6) fails for this maximizer. Use its positive beta atoms in W as
variables. Impose homogeneous preservation of I,T and of each tied p,h,k
comparison in W. There are fewer equations than variables, so a nonzero
signed direction exists. All other atoms are fixed. For sufficiently
small steps of either sign the finitely many changed positive atoms stay
nonnegative and every strict comparison in W remains strict.

Every comparison outside W is unchanged. Before W, neither opponent's
current atom or survival probability changes, because the total partner
mass in W is fixed. After W, the remaining conditional pair law is
unchanged, again because its total mass is fixed; all prescribed Never
values are unchanged by (2)--(4). Equivalently the change of a date payoff
minus Never depends only on remaining tail atoms and vanishes after W.
The partner's comparisons do not depend on its own law. Hence both signed
steps lie in F, contradicting extremality and proving (6).

The pair remains infinite for both owners. If the partner law ended, a
later tail with the pivot alone would have zero debt for all players:
observers are still optimal and the sole pivot has payoff and cap zero.
Uniform dispersion would force its finite mass to vanish, contradicting
the fixed infinite pivot law. Positive Never masses were retained exactly.

## Consequence when late common support is forced

Suppose in addition that either A<0, or A>0 and the following raw screen
is empty. Write j in {h,k}, and set

    O={(x,lambda): lambda>0,
          0<=x<=rho if J>0, or rho<=x<=1 if J<0,
          Z_j({p})-x Z_j({j,p})+lambda Z_j({i})>=0
                                      for j=h,k}.        (8)

These conditions force common p/i support at every sufficiently late
occupied date, as in the existing I2 screen. For A<0, the pivot inequality
C beta_n<=A I_n makes beta_n>0 at every physical date, and (1) then makes
alpha_n>0. For A>0, infinitely many pivot-only atoms would give a point
of O: at such a date put x_n=alpha_n/P_n; the observer-i comparison bounds
x_n in the stated closed interval. Uniform pair-tail comparability lets
a subsequence of the conditional ratio f_i/f_p tend to lambda>0. Divide
the two quiet observers' Quit-versus-Never inequalities by f_p, use
q_p=x_n f_p, q_i=0, and let the remaining masses tend to zero. The
quadratic pair corrections vanish and give (8). Thus O empty excludes
infinitely many pivot-only atoms. Partner-only atoms are always impossible
by (1). The same raw screen therefore applies to the replacement law.

Then at least one of h,k has infinitely many finite responses tied with
Never in the replaced actual minimum.

Otherwise choose W after both quiet observers' last such contact. A pivot
contact cannot occur where beta_n=0, since its exact gap is

    C beta_n-A I_n,

and A!=0,I_n>0. Equation (6) therefore says that at most two partner atoms
after that cut fail to be pivot contacts. Eventually every occupied date
has both players active and both contact equalities. The pivot atom rate
is rho; the partner atom rate must be the constant s=A/C in (0,1).
Their successive finite-tail ratios are multiplied by

    (1-rho)/(1-s).

Uniform comparability from (7) and its symmetric inequality forces s=rho,
contrary to genericity GC-AJ!=0. If C=0, no pivot contact is possible and
(6) already contradicts infinite partner support.

This produces exact quiet contacts for a subsequent activation argument;
it does not prove that activating the quiet observer decreases the pivot
objective while preserving the other full caps. The sign and existence of
that compensated activation remain open.

## Sources and the remaining activation problem

The exact finite-splice full cap identity is
quittingContinuationBestResponseValue_rootThenContinuation_eq_max in
UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean. Its semantic pair
version is quittingTerminalSemanticPair_rootThenContinuation in
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean. No new Lean
check was run. The prior controlled-window export assumes all four hazards
positive and supplies strict concavity under a raw matrix test; it does not
supply the compact pair replacement or (6).

For a cap-changing replacement at a late cut, the original head must still
be retained. If N_p(head)>0 is its pivot Never mass and the original minimum
is ALL-END, the local objective at the source, after dividing by joint head
survival, has the active expression

    lambda B_p-U_p+r nu, lambda=1/N_p(head).

More generally the retained old-head cap is a maximum with its previous
finite-response branch. It cannot be dropped at a tie. Thus a prospective
three-owner activation at a produced quiet contact must preserve the other
full caps and lower this inherited maximum objective. Minimizing the
standalone tail expression d_p+r nu instead is not justified. The theorem
above avoids this issue by retaining the entire tuple exactly.
