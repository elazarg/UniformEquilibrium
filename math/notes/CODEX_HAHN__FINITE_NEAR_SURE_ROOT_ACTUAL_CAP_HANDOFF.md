# Finite near-sure roots already give an actual cap handoff

Author: `CODEX_HAHN`

## Status

**Ordinary mathematics; not Lean-checked and not proposed for export.**
The finite roots in the vanishing-survival branch are approximate
singleton-base Nash points, with an explicit error proportional to the
owner's residual Continue probability. More importantly, no approximate
version of the stationary prescribed-owner handoff is needed to preserve
finite ancestry: the complete owner-cap response already retained by the
first-root theorem produces a literal finite-source child with zero owner
debt and a new full-gap paid row.

This removes the compact-limit stationary source-entry seam from the local
handoff. It does not consume the resulting paid port, reconstruct a minimum
source, or give a renewable rank.

## Question

Let \(I=\operatorname{Fin}4\).  Assume a terminal exploitability witness of
fixed gap \(\Gamma>0\), and take the full vanishing-survival alternative B
of `FIRST_EXACT_ROOT_SURVIVAL_AND_UNIQUE_SURE_RESET`.  Thus
\(\tau_n\) are the actual stationary structured sources in that packet,
with semantic pairs \(X_n=(u_n,B_n)\), and \(q_n\) are exact independent
product Nash roots against \(u_n\).  Put

\[
 \rho_n=q_n::\tau_n,
 \qquad Y_n=\operatorname{Sem}(\rho_n).
\]

After the packet's subsequence, \(q_n\to q\), where \(q\) has a unique sure
quitter \(k\), and the finite prefixed sources satisfy

\[
 d_k(Y_n)\ge D_*/2>0
\]

eventually.  Crucially, item B.2 also supplies at every finite \(n\) a
literal complete cap-attaining response for \(k\): it forces Continue at
the new root and, conditional on opponent all-Continue, uses a stationary
Quit0-or-Never cap response in the actual tail \(\tau_n\).  This attained
response and its stationary-tail provenance are hypotheses of the result
below.  They do not follow from arbitrary actual profiles and exact roots:
for a general nonstationary tail, a complete pure-time cap need not be
attained.

Can the singleton-base handoff be realized before taking the stationary
limit, while retaining the literal profiles (\rho_n) and their source
ancestry?

## 1. Quantitative approximate induced Nash

Assume all terminal rewards and the supplied tail coordinates are bounded in
absolute value by (M). Write

\[
 \alpha_n=1-q_{n,k}\longrightarrow0.
\]

Let (widetilde q_n) be obtained from (q_n) by forcing (k) to Quit surely,
and let (z_n) encode the free marginals of (widetilde q_n) on
(F=I\setminus\{k\}).

For (i\in F), let (E_i(q;v)) be Quit payoff minus Continue payoff at the
root with all-Continue continuation (v_i). Couple (q_n) and
(widetilde q_n) so that only (k)'s action changes. On the event that (k)
Quits, the two endpoint differences are identical and the continuation is
irrelevant. The complementary event has probability (alpha_n). Each
endpoint difference lies in ([-2M,2M]). Therefore

\[
 |E_i(\widetilde q_n;0)-E_i(q_n;u_n)|
 \le 4M\alpha_n.                                             \tag{1}
\]

The own marginal of (i) is unchanged. Exact root complementarity for
(q_n) and (1) give

\[
 (1-q_{n,i})E_i(\widetilde q_n;0)\le4M\alpha_n,
 \qquad
 -q_{n,i}E_i(\widetilde q_n;0)\le4M\alpha_n.                 \tag{2}
\]

These are precisely the Quit and Continue regrets in the persistent
singleton-base binary game. Hence (z_n) is a (4M\alpha_n)-Nash point of
that induced game.

In particular, compactness implies that every limit of (z_n) belongs to
the exact induced Nash set. The prescribed-owner floor-excess functional is
continuous and has a uniform positive lower bound on that exact compact Nash
set under the terminal exploitability witness. Consequently its value at
(z_n) is eventually bounded below by half that uniform constant.

This is a valid robust entrance to the induced geometry. It does not by
itself preserve the finite source, because stationary repetition of
(widetilde q_n) is not (\rho_n).

## 2. Direct finite-source handoff

The first-root survivor theorem already retains more useful data. For every
large (n), player (k)'s complete cap at (\rho_n) is attained by a
behavioral response (\beta_{n,k}) which:

1. forces Continue at the new date-zero root; and
2. if all opponents Continue, uses an exact cap response in the literal tail
   (\tau_n).

Define the actual unilateral child

\[
 \chi_n=\rho_n[k\leftarrow\beta_{n,k}].                       \tag{3}
\]

Then the opponents of (k) are unchanged, so its complete best-response cap
is unchanged. Since (\beta_{n,k}) attains that cap,

\[
 U_k(\chi_n)-U_k(\rho_n)=d_k(Y_n)\ge D_*/2,
 \qquad d_k(\chi_n)=0.                                       \tag{4}
\]

Both statements concern unrestricted behavioral caps. The response in (3)
is not merely a root endpoint: its tail component is the exact stationary
Quit0-or-Never cap retained by the survivor theorem.

Now apply the terminal exploitability witness, of gap (Gamma>0), to the
literal profile (chi_n). It supplies some player (j_n) with

\[
 d_{j_n}(\chi_n)\ge\Gamma.                                   \tag{5}
\]

Equation (4) forces (j_n\ne k). After a finite-label subsequence, fix one
player (j\ne k). The checked pure-time averaging theorem then gives a
literal `QuittingPaidFirstDisagreementRow` of gain (Gamma) at the exact
source (chi_n).

With the reward bound (M), the stronger actual-reach selection can instead
be used at debt scale (Gamma). It gives a row of gain (Gamma/4) satisfying

\[
 \Gamma\le4M\,\operatorname{OwnSurvival},
 \qquad
 \Gamma\le8M\,\operatorname{OpponentLiveMass},               \tag{6}
\]

and retains support of the selected source stopping-time witness.

Thus the finite actual chain is

\[
 \tau_n
 \xrightarrow{\text{exact root prefix }q_n}
 \rho_n
 \xrightarrow{\text{cap-attaining response of }k}
 \chi_n,
\]

and (chi_n) carries the new paid row. No stationary repetition of the
limiting root is inserted.

## 3. Floor dispatch at the same finite child

For every actual opponent profile, the complete cap of a player dominates
its punishment value. Player (k)'s payoff at (chi_n) equals its complete
cap. Therefore

\[
 U_k(\chi_n)\ge \operatorname{Pun}_k.                         \tag{7}
\]

Consequently exactly one of the following holds:

1. every coordinate of (U(\chi_n)) is above punishment; or
2. a displayed player (i_n\ne k) is below punishment.

In the first arm,
`QuittingPaidRowMarkedExactOrbit.nonempty_of_floorSafe` starts the generic
marked exact-prefix construction at the literal semantic pair of \(\chi_n\).
The arbitrary-orbit consequences in
`Capacity/InfiniteOrbitConsequences.lean` imply, under the same terminal
exploitability witness, that the resulting root absorptions are summable and
hence tend to zero.  The unchanged paid suffix retains positive limiting
reach along each fixed orbit; its resulting delayed gain is proportional to
that orbit's reach limit, with no uniform lower bound as \(n\) varies.  Every
fixed positive charged-payoff recurrence premise is therefore unavailable
from these data. In the second arm, the under-floor player is source-matched
and distinct from the killed owner.

The convenience declaration for a repaired singleton-base exact orbit cannot
be applied directly: (chi_n) is not generally a stationary singleton-base
handoff. The claim instead uses the underlying generic exact-prefix orbit and
punishment-floor infinite-orbit structures. The construction is point-generic
after supplying the actual carrier membership and the floor inequality, so
the same fields can be assembled at (Sem(chi_n)). This is a small adapter, not
an already named theorem specialized to this child.

This is the same formal floor alternative as in the stationary singleton
handoff, but now it begins at an actual finite descendant of the tropical
source.

## 4. What this does and does not repair

The compact-limit stationary source-entry seam is avoidable. The finite
profiles already give the cap-attaining owner reset, killed owner debt,
distinct full-gap debtor, paid row, and floor alternative with literal
ancestry.

What remains is the established paid-port waist:

- the child (chi_n) need not be a singleton-base stationary profile;
- the new paid observer need not retain the tropical cap pin;
- the all-player floor arm enters the known vanishing-absorption exact orbit;
- the under-floor arm has no packet-preserving repair;
- the tropical genealogy is still not a complete regenerated minimum source;
  and
- neither arm gives a charged Nash--Bellman return or renewable finite rank.

Thus this is a stronger source adapter, not a consumer of
`FIN4_QUANTITATIVE_PAID_PORT_CONSUMER`.

## Boundary checks

### The approximate induced estimate is not exact membership

At finite (n), the owner is not generally sure. The continuation payoff can
enter a free player's endpoint comparison on the event that the owner
Continues, so exact induced Nash membership is not justified. Equation (1)
is the correct quantitative loss.

### The cap response must include the tail strategy

Forcing (k) to Continue at the new root is not by itself cap-attaining. On
opponent all-Continue, it must use the exact cap response in (\tau_n). The
finite child (3) includes that strategy, so (4) is a whole-profile identity.

### The repaired child is not a new singleton-base source

After (k) Continues, there is no sure quitter at date zero. A different
player may become indebted, exactly as in the unique-sure reactivation
regression. The conclusion is a source-attached paid port, not renewal of the
unique-sure chamber.

### Absolute convergence is not a return seam

Even if (chi_n) has a compact semantic limit, this does not identify it
with the original source, a minimum-fibre point, or the endpoint of an exact
Nash--Bellman block. The construction makes no such claim.

## Checked ingredients and Lean handoff

The exact root complementarity input and prefix debt formula are already
used in `FIRST_EXACT_ROOT_SURVIVAL_AND_UNIQUE_SURE_RESET`. The approximate
induced statement (1)--(2) needs a small endpoint-difference stability lemma
for replacing one opponent marginal by pure Quit.

The finite cap response is item B.2 of that survivor theorem. Once exposed as
an actual updated profile, the remaining pieces are existing declarations:

- the invariance of a player's cap under replacement of its own strategy;
- `HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at`;
- `positiveDebt_exists_actualReach_paidRow_withSupport`;
- `quittingPunishmentValue_le`; and
- the terminal-semantic exact-prefix orbit and its no-uniform absorption
  consequences, after assembling the generic infinite-orbit structure at the
  supplied child.

The useful new declaration should package (3)--(6) while retaining the
original finite prefix and tropical ancestry. A separate declaration can
record the approximate induced-Nash estimate (1)--(2); it is not needed for
the direct cap handoff.
