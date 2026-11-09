# Arbitrarily long pair runs still force Never-mass saturation in a sign chamber

Owner: CODEX_ROOT.

Status: ordinary mathematics, independently reviewed; not checked in Lean.
This extends the fixed-word theorem to an entire eventual pair-star support
mode, with no bound on constant-run lengths. It does not eliminate saturation,
finite pivot cap contacts, or inactive-observer ties.

## Statement

Use a four-player native quitting game with finite rewards, own-singleton
and Never rewards zero. Complete stopping laws are independent, and every
behavioral deviation is priced. Fix pivot p; write O for the three observers.
Let Gamma and J be hollow singleton and participant-pair matrices. Assume

    Gamma invertible, v=Gamma^-1 e_p>0, S=sum_i v_i,
    G_i=Gamma_ip!=0 and J_ip/G_i>1    (i in O),
    Gamma_ij/G_i<0                    (distinct i,j in O).       (A)

No other entry of J, passive pair reward, or higher coalition reward is
restricted. Put lambda_i=1-G_i/J_ip, so 0<lambda_i<1.

Let P be an ACTUAL global minimum of J_r=d_p+r nu among all actual profiles
with zero observer debts, or on a carrier containing them, where r>0,
d=B-U and nu is the product of ORIGINAL marginal Never masses. Suppose
all marginal Never masses are positive, B=e (ALL-END), and no finite pivot
deadline attains its full cap. Suppose that after some finite date:

* each date has exactly the pivot and one observer with positive hazards;
* each inactive observer has strict Quit-versus-Never inequality Q_i<e_i;
* each of the three observer labels occurs infinitely often.

Then

    N_p(P)=1/(1+rS).                                        (B)

In particular, in the strict-mass case this entire eventual support mode
is excluded, including calendars with unbounded runs and no recurring fixed
physical-date word. No uniform strict-gap margin is assumed.

## Exact pair-run coordinates

Consider one maximal finite run of length L>=1 with active owners p,i.
Write E for its entrance Never-offer vector and b for its continuation
Never offers after the run. Every active i deadline attains E_i. Let
alpha_t be the pivot's conditional absolute stopping atoms within this
run, t=0,...,L-1, measured from its entrance. Its finite deadline offers to
i are

    G_i sum_(u<t) alpha_u + J_ip alpha_t.

Equating two consecutive offers gives

    alpha_(t+1)=lambda_i alpha_t, alpha_0=E_i/J_ip.        (1)

This holds exactly, not just to first order. For L=1 the second identity
still gives the entire pivot law. Let beta_t be observer i's conditional
absolute atoms, g=sum beta_t>0, and w_t=beta_t/g. Put

    theta=lambda_i^L in (0,lambda_i],
    m=sum_t w_t lambda_i^t in [0,1],
    f=sum_t alpha_t=(1-theta)E_i/G_i.                    (2)

Thus f is pivot finite mass in the run; g is observer finite mass. Both
are below one. Fix the original normalized weights w during a variation,
and vary g only. For any nearby E and g define the run laws by
alpha_t=E_i lambda_i^t/J_ip and beta_t=g w_t.

Let a,beta,c be the probabilities that the first head coalition is {p},
{i},{p,i}. Direct summation gives

    c=(E_i/J_ip)g m,
    a=f-(E_i/G_i)g(m-theta),
    beta=g-(E_i/G_i)g(1-lambda_i m).                    (3)

They obey a+beta+c=f+g-fg. The letter beta without a subscript in (3)
denotes an outcome probability, not an individual stopping atom.

Define the forward map from entrance caps E to terminal caps b by

    b_i=theta E_i/(1-f),
    b_p=(E_p-Gamma_pi g)/(1-g),
    b_j=[E_j-Gamma_jp a-Gamma_ji beta-Z_j({p,i})c]
                       /[(1-f)(1-g)]       (j outside{p,i}). (4)

These are exactly the Never-offer equations. The first follows from
E_i=G_i f+(1-f)b_i; the last is the passive two-owner outcome formula.
With b_i as in (4), every finite i deadline equals E_i, and its Never
offer equals E_i. Thus (1)--(4) preserve every active-observer contact.

All maps in (2)--(4) are analytic near E=g=0, uniformly over the compact
parameter set

    theta in [0,lambda_i], m in [0,1].                  (5)

The values theta=0 and moment endpoints are used only to obtain uniform
analytic bounds. Actual finite runs have theta>0 and their original
strictly positive weights w. No actual infinite run is substituted.

Write x=Gamma^-1 E. At zero data, the derivative of (4), with g as the
observer-mass control, is

    x_next=L_i(theta)x-e_i g,
    L_i(theta)=I-[(1-theta)/G_i]e_p Gamma_i.            (6)

Here and below e_i denotes a coordinate vector in matrix formulas. Put

    z_ij(theta_i)=(Gamma_ij/G_i)(theta_i-1)>0
                       for distinct observers i,j.    (7)

Then L_i e_p=theta_i e_p, L_i e_i=e_i, and
L_i e_j=e_j+z_ij e_p for j outside{p,i}. In addition L_i v=v because
Gamma_i v=0 for every observer.

## A uniformly invertible four-run chart

Take four consecutive runs whose labels are either i,j,k,i or i,j,k,j,
where i,j,k are the three different observers. Their lengths are arbitrary.
Denote the last label by l, their cap vectors by E_0,...,E_4, and their
controls by g_1,...,g_4. The four maps (4) recursively determine E_1,...,E_4
from E_0 and these controls, with the original theta and m fixed.

Change only the entrance pivot cap: E_0=E_0^old+t e_p. Impose four constraints:

    (E_4)_a=(E_4^old)_a for a!=l,
    (E_3)_l=(E_3^old)_l.                              (8)

For actual theta_l>0, the last equation implies the missing final equality
(E_4)_l=(E_4^old)_l exactly, because the last-run map in that coordinate is
theta_l E_l/[1-(1-theta_l)E_l/G_l], independent of g_4. This replacement
avoids differentiating a final-cap equation whose derivative tends to zero
when the last run is long.

The Jacobian of (8) with respect to the four controls is invertible at
zero data, uniformly over every parameter in (5). Here is a kernel proof
which includes theta=0. Set the entrance variation x_0=0 and denote the
control variations by u_1,...,u_4. The last reduced equality says
Gamma_l x_3=0, hence L_l x_3=x_3. Therefore x_4=x_3-e_l u_4 and
Gamma_l x_4=0. Together with the other three zero final-cap constraints
and invertibility of Gamma, this gives x_4=0, or x_3=e_l u_4.

For labels i,j,k,i, iteration of (6) gives

    x_3=-u_1 e_i-u_2 e_j-u_3 e_k
      -[u_1(z_ki+theta_k z_ji)+u_2 z_kj]e_p.

Thus u_2=u_3=0, u_4=-u_1, and

    u_1(z_ki+theta_k z_ji)=0.

The coefficient is at least
(-Gamma_ki/G_k)(1-lambda_k)>0, so every u vanishes.

For labels i,j,k,j, the same formula for x_3 applies. The equality
x_3=e_j u_4 gives u_1=u_3=0, u_4=-u_2, and u_2 z_kj=0. Again
z_kj>=(-Gamma_kj/G_k)(1-lambda_k)>0, so every u vanishes.

The first and last run parameters cause no degeneracy in this calculation.
All parameters lie in one fixed compact set; continuity of the reduced
four-by-four Jacobian and its nonzero determinant give a uniform inverse
bound. Its analytic maps have uniformly bounded derivatives in a fixed
neighborhood of zero data. The parameter-dependent inverse function theorem
therefore supplies an exact smooth curve solving (8) through every
sufficiently small original four-run window, with derivatives converging
uniformly to the zero-data derivatives as the original window data tend
to zero. Equivalently one may use finitely many inverse-function charts
covering the compact parameter set. No growing-dimensional inverse is used.

## Actual feasibility and derivative limits

In each individual original window, E_i/J_ip at its active run entrance
is positive, every finite run mass is strictly between zero and one, and
every weight w_t is positive. A sufficiently small two-sided interval in t
therefore gives proper positive pivot and active-observer atoms by (1)--(2).
All quiet hazards remain zero. There are finitely many dates in the window,
so its strict quiet-observer and pivot comparisons persist after further
restriction of the interval. Its size may depend on all run lengths and
strict margins. Uniform positive radius is unnecessary.

The unchanged actual continuation has B=e and optimal observers. The exact
contacts and retained strict comparisons give the full cap and prescribed
observer equalities throughout the new window, by the pure-deadline/END
characterization or backward Bellman recursion. Every entrance observer
cap and payoff is unchanged; the entrance pivot cap changes by exactly t.
The old finite head thus preserves observer optimality. Every earlier pivot
deadline is unchanged and strictly below the old END cap. There are only
finitely many, so they remain below the new END on a smaller two-sided
interval. The result is an actual observer-optimal comparison profile.

Let u be the window's prescribed pivot payoff, and c its joint survival.
Both have expressions involving only the four run outcome triples (3),
their masses, and the fixed continuation pivot payoff: recursively,

    u_before=Gamma_pi beta+J_pi c_pair+(1-f)(1-g)u_after,
    c=product_runs (1-f)(1-g).                        (9)

These finite aggregate expressions are uniformly analytic over (5).
At zero data, let a_total be the vector of first-order total stopping
masses across the four runs. The first-order Never recursion says

    dE_0-dE_4=Gamma a_total.

Since dE_0=e_p and dE_4=0, a_total=v. Therefore

    du/dt ->1, dc/dt ->-S                             (10)

uniformly as the original data tend to zero, independently of run lengths.
For the payoff, the linear term is Gamma_p a_total; for survival it is
-sum a_total. Uniform inverse and derivative bounds justify these limits.

Now let s_a and h_p,a be joint and opponent survival before the window,
and nu_tail the joint Never probability after it. The exact whole-profile
objective derivative is

    h_p,a-s_a du/dt+r s_a nu_tail dc/dt.               (11)

Minimality makes it zero. In an actual positive-Never law the conditional
remaining finite masses tend to zero at late cuts, so all four run masses
and entrance cap vectors tend uniformly to zero, regardless of their lengths.
The unchanged continuation's prescribed values tend to zero, nu_tail tends
to one, and h_p,a/s_a tends to 1/N_p(P). Using (10) in (11) gives (B).

## Why the required four-run windows always occur

Condense the eventual pair-label calendar into its maximal constant runs.
Every run is finite because all three labels recur infinitely, and adjacent
run labels differ. There are arbitrarily late triples of distinct run
labels: otherwise every sufficiently late triple would have its first and
third labels equal, forcing eventual alternation of two labels. Append the
following run. Since it differs from the third, its label is the first or
second. This gives precisely i,j,k,i or i,j,k,j. Their starting physical
dates tend to infinity, supplying the windows used in (11).

## Source correspondence and scope

The literal cap recursion is
quittingContinuationBestResponseValue_rootThenContinuation_eq_max in
UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean; the literal tuple
prefix identity is quittingTerminalSemanticPair_rootThenContinuation in
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean. Both statements
were inspected. They do not formalize the present uniform four-run chart.

The raw chamber (A) supplies compact contractive run parameters and the
noncancelling reduced determinant; it does not supply the actual global
minimum, eventual pair support, or strict quiet comparisons. The conclusion
removes the strict-mass conjunction of those actual source properties.
It proves no UE class by itself and leaves finite pivot contacts, equality,
other raw sign chambers, quiet ties, and the nonrealized source arm open.

The new theorem also permits unbounded runs, for which the old fixed-window
quantifiers give no uniform chart. No export admission is claimed here.

## One-negative-orientation boundary test

The ratio formulation is material to the source audit. In the all-positive
G_i orientation, the observer principal block has negative determinant;
the Schur complement equals 1/v_p>0. Hence det Gamma<0, which is already
an established UE exit. The following example instead has one negative
G_i, positive determinant, and every singleton column contains a negative
entry. It is an actual geometric source-shape test, not a claim to evade
every existing UE theorem or to realize a positive absorbing gap.

Take p=0 and

    Gamma=[0,1,1,1; -2,0,1,1; 2,-1,0,-1; 2,-1,-1,0],
    J=[0,-1,-1,-1; -6,0,-3,-2; 15/2,-5,0,-3; 13/2,-3,0,0].

Then det Gamma=6, v=(1/3,1/3,1/3,1/3), and (A) holds. Initially set
all remaining coordinates zero. Use four-date pair word 01,02,03,01,
rho=1/3, and the leading hazards

    a_0=(2,1,0,0), a_1=(1,0,1,0),
    a_2=(1,0,0,1), a_3=(1,1,0,0).

Put E=(6,-12,21/2,21/2). The identities Gamma sum a=(1-rho)E and
det F=1728 hold, where F is the eight-by-eight active-contact/entrance
Jacobian (entrance rows first, then chronological active contacts;
columns ordered by date and owner). The leading gaps are

    (-7,0,-1/2,-1/2), (-6,-1,0,-1),
    (-5,-1,-1,0), (-4,0,-2,-1).

Thus IFT gives a smooth exact four-date block q(t)=t a+O(t^2) with
entrance Never offers tE, terminal offers rho tE, all active observer
contacts, and all quiet/pivot gaps strict. Concatenate q(h rho^n) for
sufficiently small h>0. Summable proper hazards give positive original
Never masses. Assigned cap vectors match and tend to zero, so the exact
Never recursion telescopes to actual offers. Complete deadline comparisons
give B=e; active observer contacts give U_i=e_i. Every pivot finite
deadline is strict. The one negative conditional observer cap is permitted.

For a finite prefix making ALL entrance caps positive, fix such a small
h and set the following additional coordinates of this SAME game:

    Z_1(23)=Z_1(023)=2,
    Z_1(012)=Z_1(013)=Z_1(123)=Z_1(0123)=-10,
    Z_2(023)=21h/2-7/2, Z_3(023)=21h/2-11/2,
    Z_0(023)=4+2h.

Use root q=(1/2,0,1/2,1/2) before the actual tail. These additional
coordinates do not occur in the pair-only tail's actual outcomes. The
negative participant triples only lower its quiet forced-Quit offers,
so that tail and all its full-cap assertions remain valid. At the prefix,
the four END caps are exactly

    ((2+6h)/4, (4-12h)/8, (1+21h/2)/4, (1+21h/2)/4).

They are positive for small h. Observers2,3 have Q=C by the assigned
participant triple rewards; observer1 has Q=-51/8<C. Pivot0 has Q=C-h.
Therefore the full profile is ALL-END, observer-optimal, has positive caps
and positive original Never, and has no finite pivot cap attainer. Its
four pair labels recur indefinitely. The raw singleton matrix remains
unchanged, with det Gamma>0 and the strict inverse column.

The tail pivot debt is O(h^2), by summing q_p(C_p-Q_p)=O(h^2 rho^(2n)).
The prefixed pivot debt is h/2+O(h^2), and joint Never is at most1/8.
With r=1/4 one therefore has J_r<r for small h and
N_p<=1/2<3/4=1/(1+rS). This realizes every displayed source-shape
inequality used here except global minimality and a positive absorbing gap.
The saturation theorem implies that this profile is not a global minimum.
No such missing premise is claimed. The example has bounded runs; the
proof above, rather than this fixture, supplies uniformity for unbounded runs.
