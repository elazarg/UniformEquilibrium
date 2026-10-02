# Zero-Never sources contract to an off-minimum port or a screened unique debtor

Identity: `SOCIAL_WEIGHT_REVIEW`

Status: **ordinary-mathematics proof draft.**  The finite-game construction
and unrestricted-deviation estimate below are exact.  The compact
minimum/off-minimum dispatch is standard carrier mathematics.  The whole
composition has not been checked as one Lean declaration.  Sections
7.8--7.16 add an ordinary-mathematics connection from the all-player escape
profile to a strict all-Never suffix and, in the minimum equality branch, to
the reviewed moving singleton-to-pair support descent.  This is a strict
contraction of the response-seam problem, not a terminal consumer of the
off-minimum or earlier-paid outputs.  The independent review currently covers
through Section 7.13; the explicit product-source construction and phase rank
in Sections 7.14--7.15 await delta review.

## 1. Question

Let \(I=\operatorname{Fin}4\), let terminal rewards lie in \([-M,M]\), and
let \(D_*>0\) be the global minimum of total unrestricted terminal debt.
Suppose actual profiles \(\sigma_n\) converge semantically to a global
minimum and their terminal Never probabilities tend to zero:

\[
 \operatorname{Sem}(\sigma_n)\longrightarrow z_*,
 \qquad
 \Pr_{\sigma_n}(\mathsf{Never})\longrightarrow0.
\tag{1.1}
\]

Can one avoid the one-player response seam, where killing one debtor may
reactivate a previously zero coordinate?

The answer is yes for three coordinates simultaneously.  The fourth player
is retained as an exogenous asymptotically sure finite clock.  The remaining
boundary is a minimum source at which that same player is the unique debtor.

## 2. Selecting the screening clock

For each player \(i\), let \(\zeta_{i,n}\) be the Never mass of its complete
behavioral stopping-time law in \(\sigma_n\).  Private behavioral
randomization gives the exact product identity

\[
 \Pr_{\sigma_n}(\mathsf{Never})
 =\prod_{i<4}\zeta_{i,n}.
\tag{2.1}

After a subsequence, there is one fixed player \(k\) such that

\[
 \zeta_{k,n}\longrightarrow0.
\tag{2.2}

Indeed, at every index some factor in (2.1) is no larger than the fourth root
of the product, and finite pigeonhole fixes its label cofinally.

Put \(F=I\setminus\{k\}\).  Player \(k\)'s entire behavioral strategy will
remain literally unchanged in the construction.

## 3. Screened finite timing game

Choose numbers \(\varepsilon_n\to0\) with
\(\zeta_{k,n}<\varepsilon_n\); for example, after the selected subsequence
one may take

\[
 \varepsilon_n=\max\{\sqrt{\zeta_{k,n}},1/n\}.
\]

Choose a finite cutoff \(H_n\)
such that

\[
 \Pr_{\sigma_{n,k}}(T_k>H_n)\le\varepsilon_n.
\tag{3.1}

Here \(T_k=\infty\) is included in the event on the left.  Such a cutoff
exists by (2.2).

For every free player \(i\in F\), use the finite pure-clock action set

\[
 A_n=\{0,1,\ldots,H_n\}\cup\{\infty\}.
\tag{3.2}

Define a finite three-player normal-form game on \(F\): a pure action vector
in \(A_n^F\) is interpreted as the corresponding pure quitting clocks,
player \(k\) keeps its literal strategy from \(\sigma_n\), and payoffs are
the exact infinite-horizon quitting payoffs of that actual profile.  Choose a
mixed Nash equilibrium of this finite game.  Independent mixing over pure
clocks is a probability law on \(\overline{\mathbb N}\), hence is realized by
an ordinary behavioral quitting strategy.  Let \(\rho_n\) be the resulting
actual four-player profile.

Thus \(\rho_n\) differs from \(\sigma_n\) only in the three complete
strategies indexed by \(F\).  It has a literal ancestry of at most three
unilateral complete-strategy replacements.  No step of that ancestry is
claimed profitable or Nash--Bellman.

## 4. The finite Nash point solves all three unrestricted caps

Fix \(i\in F\) and a pure response time \(s\in\overline{\mathbb N}\).
If \(s\le H_n\) or \(s=\infty\), this response is one of the actions of the
finite game.  If \(s>H_n\), compare it with Never.  The two induced outcomes
can differ only if player \(k\) survives beyond \(H_n\): every other free
player's realized finite action is at most \(H_n\), and otherwise that player
uses Never.  Therefore

\[
 \left|
 U_i(\operatorname{QuitAt}(s),(\rho_n)_{-i})
 -U_i(\operatorname{Never},(\rho_n)_{-i})
 \right|
 \le 2M\varepsilon_n.
\tag{4.1}

Finite-game Nash optimality and (4.1) imply

\[
 U_i(\operatorname{QuitAt}(s),(\rho_n)_{-i})
 \le U_i(\rho_n)+2M\varepsilon_n
 \qquad(s\in\overline{\mathbb N}).
\tag{4.2}

Every complete behavioral response is a mixture of pure stopping times.
Taking expectations and then the supremum gives the complete unrestricted
debt bound

\[
 \boxed{d_i(\rho_n)\le2M\varepsilon_n\qquad(i\in F).}
\tag{4.3}

The proof does not replace complete caps by finite-horizon caps.  The retained
clock of player \(k\) is what makes the omitted late actions uniformly close
to Never.

The target law also has

\[
 \Pr_{\rho_n}(\mathsf{Never})
 \le \zeta_{k,n}\longrightarrow0,
\tag{4.4}

because player \(k\)'s stopping law is unchanged.

## 5. Global-minimum dispatch

Compactify the terminal semantic pairs and terminal laws of \(\rho_n\).
Let \(y=((U',B'),\nu)\) be a selected joint cluster and write

\[
 L=D(U',B')\ge D_*.
\]

There are two cases.

### 5.1 Strict cluster

If \(L>D_*\), sufficiently late actual targets \(\rho_n\) are off minimum.
The ordinary terminal-gap actual-reach theorem supplies the standard outgoing
paid first-disagreement row.  Together with the literal finite replacement
ancestry from \(\sigma_n\), this is an actual off-minimum paid port.

### 5.2 Minimum cluster

If \(L=D_*\), (4.3) gives

\[
 d_i(y)=0\qquad(i\ne k).
\tag{5.1}

Since total debt is \(D_*>0\), necessarily

\[
 \boxed{d_k(y)=D_*,
 \qquad
 \operatorname{supp}^+d(y)=\{k\}.}
\tag{5.2}

Equation (4.4) also gives \(\nu(\mathsf{Never})=0\).  More importantly than
that terminal-law fact, the realizing sequence retains the actual stopping
law of the unique debtor \(k\), with marginal Never mass tending to zero.
Thus the result is source attached, not merely an abstract unique-debtor
semantic pair.

This output can be regenerated as a complete minimum source without changing
the realizing profiles.  Since \(\nu(\mathsf{Never})=0\), one of the fifteen
finite nonempty coalition coordinates has positive \(\nu\)-mass.  Stabilize
such a coalition and apply source-faithful minimum causalization to the exact
sequence \((\rho_n)\).  It selects only a subsequence, finite exact cap--Nash
prefixes, and marks.  The supplied suffixes remain these same \(\rho_n\).
Moreover the debtor's marginal Never mass remains vanishing after prefixing:
for any finite prefix word \(W_n\),

\[
 \Pr_{W_n\triangleright\rho_n,k}(T_k=\infty)
 =\Pr_{W_n,k}(\text{Continue through }W_n)\,\zeta_{k,n}
 \le\zeta_{k,n}\longrightarrow0.
\tag{5.3}

Thus the minimum output carries a full source chronology, positive finite
atom, exact response transport, unique-debtor semantic limit, and the same
vanishing-marginal clock passport.

It also carries a quantitative paid row for the same label \(k\).  Eventually
\(d_k(\rho_n)>D_*/2\).  Apply the complete actual-reach
first-disagreement theorem with that fixed floor, then shift both displayed
pure clocks through the selected causal prefixes.  The prefix joint and
player-deleted Continue products tend to one at the positive minimum, so a
fixed fraction of the gain and both actual-reach floors survives.  Thus the
regenerated source does not merely name the unique debtor: it retains a
literal source-matched cap response for that debtor.  This is still a
horizontal behavioral response, not a temporal Nash--Bellman edge.

Combining the cases gives

\[
\boxed{
 \text{zero-Never minimum source}
 \Longrightarrow
 \text{actual off-minimum paid port}
 \ \lor\ 
 \text{source-attached zero-Never unique-debtor minimum}.}
\tag{5.4}

## 6. Relation to zero-face preservation

At the source, a one-player best response by a debtor \(p\) can kill
\(d_p\) while reactivating an old zero coordinate.  The construction above
does not ask for one response which preserves the old face.  It re-equilibrates
all three players other than \(k\) simultaneously, so every one of those
coordinates is asymptotically zero by (4.3).  This absorbs all debtor rotation
inside that three-player face.

This is stronger than the coordinatewise reached-suffix inequality in
[`SOCIAL_WEIGHT_REVIEW__ZERO_NEVER_SINGLETON_LITERAL_TAIL_RENEWAL.md`](SOCIAL_WEIGHT_REVIEW__ZERO_NEVER_SINGLETON_LITERAL_TAIL_RENEWAL.md):
that inequality preserves existing zeros only until a paid opponent changes;
the screened Nash construction restores the entire three-coordinate zero
face after all such changes.

The construction is also an asymptotic extension of the finite-host
complementary-Nash theorem in
[`CODEX_AMPERE__FINITE_FIXATION_SPECTATOR_COMPRESSION_AND_HOST_ROTATION.md`](CODEX_AMPERE__FINITE_FIXATION_SPECTATOR_COMPRESSION_AND_HOST_ROTATION.md).
That theorem assumes one literal deterministic deadline \(T\) and uses the
exact finite alphabet through \(T\).  Here the supplied host has only
vanishing marginal Never mass, its cutoff \(H_n\) may escape, and the
late-versus-Never coupling (4.1) yields asymptotically zero rather than exact
free debts.  The global minimum dispatch (5.3) is the additional conclusion.

The construction is not the same as the checked stationary singleton-base
producer.  That producer installs a new sure date-zero owner chosen from the
reward table.  Here the screening clock is selected from the supplied actual
zero-Never source, remains literally unchanged, and may escape to arbitrarily
late dates.  The new conclusion is therefore a source-provenance contraction,
not a new existence theorem for the abstract unique-debtor chamber.

## 7. Exact remaining boundary

The construction cannot include player \(k\) among the re-equilibrated
coordinates.  Its unrestricted-deviation estimate uses \(k\)'s unchanged
finite clock to screen every omitted late response.  Once \(k\) is allowed to
replace its strategy, it may choose Never and the estimate (4.1) disappears.

Accordingly, the only unconsumed minimum output is exact:

> one source-attached player has asymptotically zero marginal Never mass and
> carries all debt \(D_*\), while the other three players are solved against
> unrestricted behavioral deviations.

This is a projective boundary, not a local cap-leakage ambiguity.  Consuming
it requires either:

1. a response of \(k\) whose target keeps the three free coordinates solved;
2. a chronological use of \(k\)'s actual finite clock before its profitable
   response destroys that clock; or
3. an incompatibility between unique debt \(D_*\), marginal finite stopping,
   and the Fin4 hard residual.

Finite-game Nash existence alone cannot perform the last step: allowing all
four players into the finite timing game removes the exogenous clock which
made late deviations uniformly negligible.  This is the same
late-versus-Never boundary that obstructs projective finite-deadline Nash
limits, now localized to the unique debtor.

### 7.1 Exact cap menu and the signed Never split

The unique-debtor sequence carries a little more finite structure.  At
\(\rho_n\), every free player mixes over \(A_n\).  Let

\[
 a_n=\prod_{i\ne k}\Pr_{\rho_{n,i}}(T_i=\infty)
\tag{7.1}
\]

be the probability that all three free clocks are Never, and put
\(s_k=r_k(\{k\})\).  Against these opponents, all finite stopping times
strictly after \(H_n\) have the same payoff.  If \(V_n(t)\) is player
\(k\)'s payoff from pure time \(t\), then

\[
 \boxed{V_n(H_n+1)-V_n(\infty)=a_ns_k.}
\tag{7.2}

Consequently player \(k\)'s complete cap is attained on the finite menu

\[
 \{0,1,\ldots,H_n+1,\infty\}.
\tag{7.3}

Select a cap-attaining action \(q_n\) from this menu.  Since
\(d_k(\rho_n)\to D_*\), there is an exact split.

1. If \(q_n<\infty\) cofinally, replacing \(k\) by
   \(\operatorname{QuitAt}(q_n)\) is an actual finite-clock response of gain
   \(D_*+o(1)\) and leaves its target debt zero.
2. If \(q_n=\infty\) and \(a_n(-s_k)\to0\), the late finite action
   \(H_n+1\) is \(o(1)\)-optimal by (7.2).  It is therefore an actual finite
   response of gain \(D_*+o(1)\) whose target \(k\)-debt tends to zero.
3. Otherwise, after a subsequence there is \(\delta>0\) with

   \[
    s_k<0,
    \qquad
    a_n(-s_k)\ge\delta.
   \tag{7.4}
   \]

   Replacing \(k\) by Never is the exact cap response, and the target law has
   Never mass \(a_n\ge\delta/M\).  This is the strict signed-Never host
   barrier, now source attached to the unique-debtor minimum sequence.

In the finite-response arms, freeze the new pure clock of \(k\) and solve the
finite complementary timing game once more.  All three free debts then
vanish exactly.  Compactification again yields an off-minimum port or a
minimum unique-debtor source, now with a literal deterministic finite host.
If the selected host deadlines stay bounded, a fixed deadline and the finite
mixed opponent strategies compactify to an attained finite-host minimum.  If
they diverge, the only remaining loss is a source-attached deadline escape.

This does not yet prove a deadline rank.  Re-equilibrating the free players
can make the host's next best response occur earlier, at the next date, or at
Never, and a later re-equilibration can reverse that move.  The exact progress
is the localization:

\[
\boxed{
 \text{unique-debtor clock boundary}
 \Longrightarrow
 \text{off-minimum port}
 \ \lor\ 
 \text{finite-host response/re-equilibration}
 \ \lor\ 
 \text{strict signed Never barrier}
 \ \lor\ 
 \text{deadline escape}.}
\tag{7.5}

The last three outputs are the established finite-host/projective
host-rotation waist; none is called a Nash--Bellman chronology here.  In
particular, a finite-host unique-debtor profile is not automatically a Nash
equilibrium of the deadline game just before its next best-response date:
the host may also have profitable earlier actions.  Therefore the deadline
escape above does not by itself instantiate the checked adjacent-deadline
Nash source.  A further simultaneous host/free Nash selection would be
needed, and that selection is precisely where literal minimum-source
alignment can be lost.

### 7.2 The strict-Never host and the provenance-sensitive escape

Under the maintained Fin4 hard residual, the signed arm (7.4) can be returned
to the existing positive-Never late-release packet.  This does not by itself
give a literal-tail contraction to the off-minimum paid-port waist.

Replace \(k\) by its exact Never cap response.  If the target semantic cluster
is strict, it is already an off-minimum paid port.  Otherwise its joint-law
cluster is a global minimum with positive Never mass at least
\(\delta/M\).  The reviewed positive-Never late-release construction at that
joint point selects a player \(a\) satisfying the table-level sign

\[
 r_a(\{a\})\ge\Gamma>0
\tag{7.6}

and installs a literal sure finite deadline for \(a\), with a fixed positive
singleton-\(a\) atom and a source-matched gain on its selected realizing
sequence.  Again a strict semantic cluster is the off-minimum port.  In an
attained minimum cluster, apply Sections 2--5 with the screening label
prescribed to be this same sure-clock player \(a\).  The output is strict, or
it is a unique-debtor minimum with debtor \(a\).

At that latter minimum, equation (7.2) and (7.6) show that the late finite
action \(H_n+1\) weakly dominates Never.  Hence a cap-attaining response can
be selected finite.  If one now permits the general finite-replacement
ancestry of the arbitrary-clock purification theorem, its target contracts to
the actual off-minimum paid port.  That conclusion is valid but forgets the
literal debtor marginal and reached-suffix ancestry being preserved here.

With only literal-clock/source provenance retained, weak compactification of
the marginal stopping laws has an additional honest output.  If all four
selected first-disagreement dates escape, the product reconstruction gains
positive Never mass while the displayed terminal law still has Never mass
zero.  This is the checked all-player escape account.  Under the additional
minimum/sign hypotheses of its social consequence it yields a quantitative
positive-social-surplus escape, whose general consumer remains open.

Thus there are two conclusions, according to the provenance one requires:

\[
\boxed{
 \text{zero-Never positive minimum source}
 \Longrightarrow
 \begin{cases}
  \text{actual off-minimum paid port},&
    \text{after arbitrary finite replacement ancestry},\\
  \text{off-minimum paid port or all-player escape account},&
    \text{with the literal clock passport retained}.
 \end{cases}}
\tag{7.7}

Neither line of (7.7) is a new terminal consumer.  The first is the maintained
arbitrary-clock purification theorem.  The second preserves more source
information but retains the positive-social all-player-escape waist in
addition to the off-minimum paid-cap waist.  Three-player simultaneous
Nashification removes debtor rotation; it does not consume either downstream
output.

### 7.3 A fixed reached port or an all-player projective escape

The literal debtor marginal gives one further source-level dichotomy which
does not require replacing it by a pure-clock minimum.

Work on the minimum branch and discard finitely many indices so that

\[
 d_k(\rho_n)\ge {3D_*\over4}.
\tag{7.8}
\]

Write \(\pi_n\) for the prescribed stopping law of \(k\),
\(C_n=B_k(\rho_n)\), and \(V_n(t)\) for the payoff of the pure clock \(t\)
against the literal
opponents of \(\rho_n\).  Define

\[
 \mathcal B_n=
 \{t:C_n-V_n(t)\ge D_*/2\}.
\tag{7.9}
\]

Since every payoff lies in \([-M,M]\), stopping-law disintegration gives

\[
 {3D_*\over4}
 \le \sum_t\pi_n(t)(C_n-V_n(t))
 \le {D_*\over2}+2M\pi_n(\mathcal B_n).
\]

Thus

\[
 \pi_n(\mathcal B_n)\ge {D_*\over8M}.
\tag{7.10}
\]

Because \(\pi_n(\infty)\to0\), eventually the positive-mass finite bad clocks
have total mass at least \(D_*/(16M)\).  Let \(p_n<\infty\) be their
earliest positive-\(\pi_n\)-mass member, and let
\(q_n\in\{0,\ldots,H_n+1,\infty\}\) be an exact cap-attaining clock,
whose existence was proved in (7.3).  Then

\[
 V_n(q_n)-V_n(p_n)\ge D_*/2.
\tag{7.11}
\]

Put \(a_n=\min\{p_n,q_n\}\), with the usual order below Never.  The two pure
clocks agree before \(a_n\).  Their payoff difference can be nonzero only if
every opponent survives to \(a_n\), and its conditional magnitude is at most
\(2M\).  Consequently

\[
 H_{-k,n}(a_n)\ge {D_*\over4M}.
\tag{7.12}
\]

The prescribed \(k\)-survival to \(a_n\le p_n\) is at least the total finite
bad mass, since \(p_n\) was its earliest time.  Hence the literal joint reach
of the first-disagreement row obeys

\[
 J_n(a_n)\ge {D_*^2\over64M^2}.
\tag{7.13}
\]

After a subsequence there are exactly two possibilities.

* **Fixed reached port.**  The dates \(a_n\) are bounded and hence may be
  made equal to one fixed calendar date.  Equations (7.11)--(7.13) give a
  source-attached pure-time cap row at that literal date with fixed payoff
  and reach floors.  Moreover, every free player's one-row regret at that
  reached history tends to zero: changing only its action there and then
  using its prescribed continuation is a complete behavioral deviation,
  whose unconditional gain is joint reach times the conditional root gain;
  use (4.3) and (7.13).

* **All-player projective escape.**  The dates \(a_n\to\infty\).  Both
  \(p_n\) and \(q_n\) then escape to infinity.  Equation (7.13) is already a
  fixed all-four joint-survival floor.  After common weak compactification,
  the reconstructed product profile has Never mass at least
  \(D_*^2/(64M^2)\), while (4.4) says that the displayed limiting terminal
  law has Never mass zero.  This is exactly the input of the checked
  all-player escape account.  In particular, Fin4 pigeonhole fixes one free
  player \(j\ne k\) whose marginal survival satisfies

  \[
   S_{j,n}(a_n)\ge
   \left({D_*\over4M}\right)^{1/3}
  \tag{7.14}
  \]

  cofinally, but the full all-player escape statement is stronger.

The fixed-date arm still is not an exact Nash--Bellman edge.  Although the
three free coordinates are asymptotically locally optimal before changing
\(k\), switching \(k\)'s action can change all three endpoint comparisons by
order one.  The escaping arm is consumed only in the checked social-sign
chambers; in general its positive-social-surplus output remains open.

### 7.4 Reached-suffix reduction and exact-root boundary

Both arms of Section 7.3 can be sharpened without changing the literal
debtor clock.

In the fixed-date arm, let \(T_n\) be the actual suffix beginning at the
common first-disagreement date \(a\), and let \(R_n=J_n(a)\).  For every
player \(i\), copy its prescribed strategy until \(a\) and then use an
arbitrarily accurate suffix best response.  This gives the coordinatewise
inequality

\[
 d_i(\rho_n)\ge R_n d_i(T_n).
\tag{7.15}
\]

Since \(R_n\) has the fixed floor (7.13), every free suffix debt tends to
zero.  At a joint semantic/law cluster of \((T_n)\), therefore, either:

1. its total debt is strictly greater than \(D_*\), giving a literal reached
   off-minimum source; or
2. it is a global minimum and \(k\) is again its unique debtor, now with the
   selected cap row at date zero.

The second alternative explains why recomputing a finite one-row product
Nash does not finish the fixed branch.  At any positive global-minimum
semantic point, an exact cap--Nash root \(x\) scales total debt by its joint
Continue probability \(c(x)\):

\[
 D(x\triangleright T)=c(x)D_*.
\]

Global minimality forces \(c(x)=1\).  Thus every exact cap root there is
all-Continue.  The paid date-zero switch is necessarily a horizontal complete
response, not a positive-absorption exact temporal root.  Re-solving the
one-row cap game erases the paid action instead of Nashifying it.  This is an
exact obstruction to the most direct fixed-row consumer, not just a missing
selection argument.

Thus the exact consumer map for the fixed-date arm is

\[
\boxed{
 \text{reached suffix}
 \Longrightarrow
 \text{off-minimum paid-cap port}
 \ \lor\ 
 \text{minimum unique-debtor all-Continue horizontal port}.}
\tag{7.15a}
\]

The first output is the universal off-minimum paid-port waist.  The second is
the zero-absorption inert output of the exact-root trichotomy; it is not
accepted by the Nash--Bellman or punishment-floor chronology consumers.  No
additional consumer is obtained merely from moving the paid row to date
zero.

### 7.5 The escaping arm supplies a checked two-cut input

In the escaping arm there is, nevertheless, a genuine finite hazard block.
Put

\[
 \beta={D_*\over16M},
 \qquad
 J_0={D_*^2\over64M^2}.
\tag{7.16}
\]

The finite bad clocks at or after \(p_n\ge a_n\) have total prescribed
\(k\)-mass at least \(\beta\).  Choose a finite \(e_n\ge p_n\) which captures
at least \(\beta/2\) of that mass.  Conditional on \(k\)'s survival to
\(a_n\), its probability of stopping in \([a_n,e_n]\) is at least
\(\beta/2\); hence its sum of behavioral Quit hazards on that interval is at
least \(\beta/2\).  The whole block is entered with literal joint probability
at least \(J_0\).

Let

\[
 H^F_n=\sum_{a_n\le t\le e_n}\sum_{i\ne k}q_{n,t,i}
\tag{7.17}
\]

be the raw free-player hazard in the same window.  After a subsequence:

* if \(H^F_n\ge1/2\), one fixed free player \(j\) has hazard sum at least
  \(1/6\) on the same uniformly reached block.  This is a literal two-label
  hazard packet, with \(k\)-hazard at least \(\beta/2\);
* if \(H^F_n<1/2\), the union bound gives conditional probability greater
  than \(1/2\) that all three free players survive through \(e_n\).  By
  independence of the four private clocks, the original prescribed profile
  then has a singleton-\(k\) terminal atom inside the block of unconditional
  mass at least

  \[
    J_0\,{\beta\over4}.
  \tag{7.18}
  \]

Thus deadline escape cannot hide the debtor's bad mass merely as positive
survival:

\[
\boxed{
 \text{escaping unique-debtor port}
 \Longrightarrow
 \text{uniformly reached two-label hazard block}
 \ \lor\
 \text{uniformly positive singleton-debtor atom}.}
\tag{7.19}

The two outputs remain actual-source data.  They are not exact
Nash--Bellman blocks: \(k\)'s prescribed hazards are precisely where its
positive debt may be spent, and the free players' small global debts do not
control conditional root errors after the joint reach has decayed inside the
long block.  The singleton output re-enters the source-attached singleton
lane, while the two-label output needs a renewal theorem before a persistent-
clock consumer applies.

The block itself already meets the checked uniformly reached two-cut
hypotheses after adding only a terminally silent mark before \(a_n\).  Take

\[
 \chi=\beta/2,\qquad r_0=J_0,
\]

and put

\[
 K_\chi=(1-e^{-\chi})D_*,
 \qquad
 \delta_\chi={e^\chi-1\over2}D_*.
\]

The exact checked output is

\[
\boxed{
 D(\operatorname{suffix}_{e_n+1}\rho_n)
   \ge D_*+\delta_\chi
 \quad\lor\quad
 \text{a source-attached paid suffix splice of gain }>
   {J_0K_\chi\over16}.}
\tag{7.20}
\]

In the paid arm the reached payer has entry debt \(>K_\chi/8\), while the
three free entry debts tend to zero by (7.15).  Hence the payer is eventually
the same label \(k\), and its reached target debt is at most \(K_\chi/16\).
Every root and cylinder strictly before the entry cut is retained.

The first output of (7.20) is the quantitative off-minimum exit-tail waist.
The second is the source-faithful paid-response waist with an aligned payer
and small target debt.  Neither is an exact Nash--Bellman edge, a renewable
minimum child, or a terminal consumer.  Thus the finite hazard block maps
exactly into checked producers, but does not close their remaining
source-reprojection/response seam.

Combining Sections 7.3--7.5 gives the honest literal-passport frontier:

\[
\boxed{
 \begin{gathered}
  \text{zero-Never unique-debtor minimum source}
  \\[1mm]
  \Longrightarrow
  \\[1mm]
  \text{off-minimum exit or paid-response port}
  \\
  \lor
  \\
  \text{all-player escape account}
  \\
  \lor
  \\
  \text{minimum all-Continue horizontal inert port}.
 \end{gathered}}
\tag{7.21}
\]

The two-cut theorem and the all-player escape account are checked consumers
of their respective input data, but their displayed outputs in (7.21) remain
live Fin4 waists.  In the additional sign chamber the escape account gives
the checked strict positive-social output; without those signs one retains
the account itself, not an unconditional positive-social conclusion.  What
remains is not another producer for a reached row: it is a source-reprojected
temporal consumer for the paid/off-minimum port, a consumer of the applicable
escape-account output, or a contradiction/rank for the zero-absorption
horizontal port.

### 7.6 Exact escape account on the unique-debtor face

The unique-debtor hypothesis does not, by itself, consume the all-player
escape.  It does give a sharper coordinatewise account which identifies the
missing sign.

Let \(z=(u,b)\) be the limiting minimum point, let \(\bar\rho\) be the product
profile reconstructed from the weak marginal limits, and write

\[
 E_i=\sum_{S\ne\varnothing}e(S)r_i(S),
 \qquad
 \Delta_i=b_i-B_i(\bar\rho).
\]

The checked escape identities give

\[
 u_i-U_i(\bar\rho)=E_i.
\]

Consequently, coordinate by coordinate,

\[
 d_i(\bar\rho)=d_i(z)+E_i-\Delta_i.
\tag{7.22}
\]

On the present face this reads

\[
 d_i(\bar\rho)=E_i-\Delta_i\ge0\quad(i\ne k),
 \qquad
 d_k(\bar\rho)=D_*+E_k-\Delta_k\ge0.
\tag{7.23}
\]

Global minimality gives only

\[
 \sum_i(E_i-\Delta_i)=D(\bar\rho)-D_*\ge0.
\tag{7.24}
\]

If \(s_i=r_i(\{i\})\ge0\) for a free player, the checked compact-law cap
bound gives \(\Delta_i\ge0\), and hence (7.23) forces \(E_i\ge0\).  It is
strict whenever either that free reconstructed debt or its cap drop is
strictly positive.  Thus nonnegative singleton signs on the free coordinates
localize any such strict escape surplus to the three free players.

Without those signs, however, \(\Delta_i\) may be negative by the exact
late-finite/Never correction.  Equations (7.23)--(7.24) then allow the escaped
reward moments, cap jumps, and debt coordinates to compensate.  Even if
\(D(\bar\rho)=D_*\), free debt may be created while the \(k\)-debt falls.
Therefore unique-debtor geometry alone supplies no sign-free contradiction
and no monotone debt-support rank.  This is the algebraic reason the checked
escape account, rather than merely the existence of escaped mass, is the
honest remaining output.

### 7.7 A sign-free contraction with an exact provenance cost

If preservation of the original literal clock, tail, law, and deleted-law
passport is not required, the sign-free escape account does contract to the
universal off-minimum paid-port waist.

Indeed, the reconstructed product profile \(\bar\rho\) is an actual behavioral
profile.  Global minimality gives \(D(\bar\rho)\ge D_*\).  If the inequality
is strict, \(\bar\rho\) itself is an actual off-minimum source; choosing a
maximal debt coordinate and applying the checked actual-reach selector gives
the standard source-supported paid row.

If \(D(\bar\rho)=D_*\), use the constant realizing sequence
\(\bar\rho,\bar\rho,\ldots\) in the checked arbitrary-clock minimum
purification theorem.  It produces a finite literal replacement ancestry
from \(\bar\rho\) to an actual profile \(\tau\) with

\[
 D(\tau)>D_*,
\]

together with the uniform max-debt and source-supported paid-row passport.
For Fin4 its debt floor is \(D_*/4\), its certified gain floor is \(D_*/16\),
and it retains the checked one-sided and joint-reach floors.

Thus, as a statement about existence of a fresh actual source,

\[
\boxed{
 \text{sign-free all-player escape account}
 \Longrightarrow
 \text{actual off-minimum paid port}.}
\tag{7.25}
\]

This is a composition of checked results, not a new consumer of that port.
It is also not a literal-passport theorem.  The first step replaces the
original approximating family by its canonical reconstructed product profile;
the purification then uses arbitrary finite one-player replacement ancestry.
This canonical restart is not an unrelated game profile: from every original
realizer one may replace the four marginal strategies, one player at a time,
by the four reconstructed strategies, reaching \(\bar\rho\) after at most
four literal unilateral replacements.  These replacement edges need not be
profitable or Nash--Bellman admissible, and the intermediate semantic seams
may be macroscopic.  The original moving dates, terminal law, deleted laws,
marked atom, and post-tail need not survive.  Therefore (7.25) is sufficient
for an atlas which retains only finite replacement ancestry, while (7.21)
remains the honest frontier for an extension-compatible or literal-tail
construction.

### 7.8 The reconstructed profile has a uniformly reached all-Never tail

The reconstructed full marginal-law packet gives a more source-oriented
version of (7.25) *inside* \(\bar\rho\).  Let \(\mu_i\) be its four stopping
laws and put

\[
 p_i=\mu_i(\{\infty\}),
 \qquad
 q=\prod_i p_i.
\]

In the all-player escape arm, \(q\ge J_0>0\).  Let \(S_T\bar\rho\) be the
literal continuation profile conditional on all players surviving through
date \(T\).  For every player \(i\), the finite mass of its residual stopping
law is

\[
 {\mu_i(\{t\in\mathbb N:t\ge T\})
  \over
  \mu_i(\{t\in\overline{\mathbb N}:t\ge T\})}
 \longrightarrow0.
\tag{7.26}
\]

Hence the residual law converges in total variation to Never.  Product
coupling, uniformly over one player's arbitrary replacement, gives

\[
 \operatorname{Sem}(S_T\bar\rho)\longrightarrow
 \operatorname{Sem}(\mathsf{Never}^I),
\tag{7.27}
\]

and the ordinary law and every one-player-deleted law converge to their
all-Never counterparts.  At the same time the literal outer reach satisfies

\[
 \Pr_{\bar\rho}(\text{all survive through }T)
 \longrightarrow q\ge J_0.
\tag{7.28}
\]

Write \(s_i=r_i(\{i\})\).  The all-Never semantic point is explicit:

\[
 U_i(\mathsf{Never}^I)=0,
 \qquad
 B_i(\mathsf{Never}^I)=\max\{0,s_i\},
 \qquad
 D_N=\sum_i(s_i)_+.
\tag{7.29}
\]

Global minimality gives \(D_N\ge D_*\).  In fact equality is impossible.
The checked theorem
`not_allNever_positiveMinimumTerminalSemanticDebt` says exactly that the
literal all-Never profile cannot attain a positive global minimum of total
terminal semantic debt.  Since \(D_*>0\), necessarily

\[
 D_N>D_*.
\tag{7.29a}
\]

Thus all sufficiently late literal suffixes in (7.27) are quantitatively off
minimum while retaining the outer reach floor \(J_0/2\).  No arbitrary-clock
purification or equality branch is needed.

Thus the complete sign-free packet admits the sharper canonical-child map

\[
\boxed{
 \begin{gathered}
  \text{reconstructed all-player escape profile}
  \\
  \Longrightarrow
  \\
  \text{uniformly reached literal off-minimum suffix}.
 \end{gathered}}
\tag{7.30}
\]

This uses the full stopping-law packet rather than a social sign.  It still
does not turn the reached off-minimum suffix through the arbitrary earlier
prefix into an exact Nash--Bellman chronology.  Moreover, the reconstructed
profile itself is a canonical compact-law child, not a literal suffix of the
original zero-Never approximating family.  Therefore (7.30) supplies a
canonical fresh source for the off-minimum waist but does not repair the
original extension-compatible trace seam.

### 7.9 A literal late-cut response removes Never

There is a stronger source-attached alternative inside the reconstructed
profile.  It avoids the arbitrary replacement ancestry in Section 7.7.
This is the direct compact-law form of the independently reviewed
positive-Never late-release construction in
`CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY.md`; that note's
finite-support compression and exact root-prefix version retains more
chronological data than the argument below.

Let \(\nu\) be the finite-outcome part of the terminal law of \(\bar\rho\).
Thus its complete law is

\[
 \nu+q\,\delta_{\mathsf{Never}},
 \qquad q>0.
\tag{7.31}
\]

By (7.29a), \(D_N=\sum_i(s_i)_+>D_*>0\), so fix a player \(i\) with
\(s_i>0\).  For every finite \(T\), replace only player \(i\)'s stopping
time \(X_i\) by

\[
 X_i^T=\min\{X_i,T\}.
\tag{7.32}
\]

Write \(\bar\rho^T\) for the resulting actual profile.  This is a
literal complete behavioral replacement.  The two strategies agree at
every date strictly before \(T\), and the target has zero Never probability
because player \(i\) Quits surely by \(T\).

The probability that the source reaches \(T\) converges to \(q\).  On that
event, the conditional residual law of every player converges in total
variation to Never.  Reward boundedness therefore gives

\[
 U_i(\bar\rho^T)-U_i(\bar\rho)
   \longrightarrow q s_i>0.
\tag{7.33}
\]

More precisely, all source terminal mass at finite dates at least \(T\)
tends to zero, while the target coalition at date \(T\) converges in law to
the singleton \(\{i\}\).  Hence the complete target laws converge to

\[
 \nu+q\,\delta_{\{i\}}.
\tag{7.34}
\]

Because the opponents of \(i\) are unchanged, its unrestricted behavioral
cap is unchanged exactly:

\[
 B_i(\bar\rho^T)=B_i(\bar\rho).
\tag{7.35}
\]

Consequently the mover's debt drop equals the actual payoff gain at every
finite \(T\).  After compactifying the other three caps, let \(w_i\) be a
target semantic/law cluster.  Equations (7.33)--(7.35) give

\[
 d_i(w_i)=d_i(\bar\rho)-q s_i,
 \qquad
 \operatorname{law}(w_i)=\nu+q\delta_{\{i\}}.
\tag{7.36}
\]

If \(\bar\rho\) itself is off minimum, it is already a canonical actual
off-minimum source.  Otherwise \(D(\bar\rho)=D_*\), and global minimality
gives the exhaustive dispatch

\[
\boxed{
 \begin{array}{c}
  D(w_i)>D_*:
   \text{ a literal late-cut paid response has an eventually off-minimum
   target},\\[1mm]
  D(w_i)=D_*:
   \text{ a zero-Never global-minimum law has singleton mass }q>0.
 \end{array}}
\tag{7.37}
\]

In the strict branch, sufficiently late actual targets have gain at least
\(q s_i/2\) and total debt bounded strictly above \(D_*\).  In the equality
branch, the same literal targets supply the realizing sequence for the
zero-Never minimum point; no unrelated law realizer is selected.

This is a genuine source improvement over (7.25): the earlier prefix and the
one-player response edge are literal.  It is not a terminal consumer.  The
zero-Never singleton minimum in the second branch is exactly the source class
treated by Sections 2--7, so without a monotone passport across another
escape reconstruction the argument can return to the same chamber.

### 7.10 Boundary-debt budget and flat minimum chords

The late-cut responses impose an additional quantitative restriction on the
hard equality branch.  For every \(i\) with \(s_i>0\), (7.33) is a sequence
of legal unilateral gains and therefore

\[
 q s_i\le d_i(\bar\rho).
\tag{7.38}
\]

Summing over the positive singleton coordinates gives

\[
 qD_N=q\sum_i(s_i)_+
   \le D(\bar\rho).
\tag{7.39}
\]

In particular, if the reconstructed profile remains on the minimum fibre,

\[
 qD_N\le D_*<D_N,
 \qquad q\le {D_*\over D_N}<1.
\tag{7.40}
\]

There is also no hidden cap curvature along a late-cut direction whose two
endpoints both remain at the minimum.  Fix a positive-solo player \(i\).
For \(0\le\theta\le1\), interpolate only that player's complete stopping law
between its source law and the forced-at-\(T\) law from (7.32).  The two laws
agree before \(T\).  For fixed \(T\):

1. every prescribed payoff is affine in \(\theta\);
2. player \(i\)'s cap is constant, because its opponents are unchanged; and
3. every other cap is convex in \(\theta\), being the supremum over complete
   responses of functions affine in the one changing opponent law.

The cap functions are uniformly Lipschitz on \([0,1]\), with a bound depending
only on the reward bound.  Pass to one subsequence in \(T\) on which they
converge uniformly.  This supplies a carrier chord \(w_i(\theta)\), with
prescribed payoff and law

\[
 U(w_i(\theta))=U(\bar\rho)+\theta q r(\{i\}),
 \qquad
 \operatorname{law}(w_i(\theta))
   =\nu+q\bigl((1-\theta)\delta_{\mathsf{Never}}
                    +\theta\delta_{\{i\}}\bigr).
\tag{7.41}
\]

Suppose both endpoints have debt \(D_*\).  Total debt is convex on this
chord, while global minimality bounds it below by \(D_*\).  Hence

\[
 D(w_i(\theta))=D_*
 \qquad(0\le\theta\le1).
\tag{7.42}
\]

Moreover, the sum of the four convex cap coordinates is affine on the chord.
Every individual Jensen gap is nonnegative and their sum is zero, so each cap
coordinate is itself affine.  Thus every debt coordinate is affine as well.
The equality branch of (7.37) is therefore a genuine flat minimum chord, not
a cap-switching-curvature branch.

This observation separates two possible consumers.  Strictness at any chord
endpoint supplies the source-attached off-minimum paid port.  Complete
flatness supplies a finite boundary-debt budget (7.38)--(7.40) and affine cap
transport, but still permits other coordinates to acquire exactly the debt
lost by the mover.  Affineness alone does not preserve old zero coordinates
and therefore does not yet give the required renewable rank.

### 7.11 The flat chord has only four spectator cap slopes

The affine conclusion in Section 7.10 is not an abstract convexity label.
It reduces every spectator cap displacement to a finite terminal-reward
menu.

Fix \(j\ne i\), put

\[
 q_{-j}=\prod_{h\ne j}p_h,
 \qquad
 \Delta_j=B_j(w_i)-B_j(\bar\rho),
\tag{7.43}
\]

and retain the equality case in which the whole chord is minimum.  At the
midpoint of the finite-\(T\) chord, choose an arbitrarily accurate pure-time
cap response of player \(j\).  Equality of the convex cap with its endpoint
chord implies that the same response is asymptotically optimal at both
endpoints.  Indeed, its two endpoint regrets are nonnegative and their sum is
twice its midpoint regret.

After a subsequence, the selected pure response time is in one of four
positions relative to \(T\): strictly before \(T\), equal to \(T\), strictly
after \(T\), or Never.  Conditional on all opponents of \(j\) surviving to
\(T\), every residual clock converges in total variation to Never.  The four
possible endpoint payoff slopes are therefore respectively

\[
 0,
 \quad
 q_{-j}\bigl(r_j(\{i,j\})-r_j(\{j\})\bigr),
 \quad
 q_{-j}\bigl(r_j(\{i\})-r_j(\{j\})\bigr),
 \quad
 q_{-j}r_j(\{i\}).
\tag{7.44}
\]

Since the response is asymptotically optimal at both endpoints, its payoff
difference converges to the cap difference.  Hence

\[
\boxed{
 \Delta_j\in
 \left\{
 0,
 q_{-j}(r_j(\{i,j\})-s_j),
 q_{-j}(r_j(\{i\})-s_j),
 q_{-j}r_j(\{i\})
 \right\}.}
\tag{7.45}
\]

For the mover, \(\Delta_i=0\).  Equality of total debt at the two endpoints
also gives the exact social balance

\[
 \sum_{j\ne i}\Delta_j
   =q\sum_j r_j(\{i\}).
\tag{7.46}
\]

Thus a hard equality branch must solve one finite system obtained by choosing
one of four timing types for each of the three spectators.  A nonzero cap
slope has a common asymptotically optimal response whose clock is aligned
with the release date; it cannot be caused by a fixed earlier response.

This is not yet an active-face rank.  The selected timing type can change
after passing to the zero-Never child, and (7.45) permits a formerly
zero-debt spectator to acquire positive debt.  A consumer would have to show
that the hard-residual singleton/collision signs exclude every type choice
satisfying (7.46), or that a nonzero late type supplies an accepted temporal
edge rather than another horizontal cap witness.

### 7.12 Hard-residual collision enters the repaired moving pair chord

The hard residual does consume more of the equality branch than (7.45) alone
shows.  Choose the release owner \(i\) from the terminal exploitability
witness, so that for its terminal gap \(\Gamma>0\),

\[
 s_i\ge\Gamma.
\tag{7.47}
\]

Punishment normality supplies a fixed \(j\ne i\) with the literal singleton
collision inequality

\[
 r_j(\{i,j\})-r_j(\{i\})\ge\Gamma.
\tag{7.48}
\]

Use the reviewed common-quantile finite-support compression on the actual
positive-Never profile \(\bar\rho\).  It gives actual profiles converging in
complete semantics and law to \(\bar\rho\), while preserving the marginal
Never atoms.  Choose \(T_n\) beyond every finite support.  Capping player
\(i\)'s clock at \(T_n\) then produces an **exact** singleton-\(i\) row of
mass converging to \(q\), not merely the asymptotic singleton row in (7.34).
The first replacement has gain converging to \(q s_i\ge q\Gamma\).

At this target row, cap player \(j\)'s clock at the same \(T_n\).  The second
replacement changes the exact singleton \(\{i\}\) to the exact pair
\(\{i,j\}\), with gain converging to

\[
 q\bigl(r_j(\{i,j\})-r_j(\{i\})\bigr)
\ge q\Gamma.
\tag{7.49}
\]

Both replacements retain the complete earlier source calendar and the same
post-row tail.  Suppose the singleton endpoint from the first replacement is
the minimum endpoint \(w_i\) in (7.37).  It has a positive moving singleton
atom and a literal singleton-to-pair response of fixed gain.  These are
exactly the supplied-sequence hypotheses of Section 17 of
`PAIRED_HULL_REVIEW__ORIENTED_PAIR_TO_SINGLETON_OR_RENEWABLE_CHORD.md`.
That repaired moving-row theorem gives, after one common refinement, the
exhaustive dispatch

\[
\boxed{
 \begin{array}{c}
  \text{a uniformly paid supported row strictly before }T_n,\\
  \text{or a literal quantitatively off-minimum pair endpoint},\\
  \text{or a regenerated minimum child with strict positive-debt-support
  drop}.
 \end{array}}
\tag{7.50}
\]

In the third arm the source and pair target are separately causalized using
their literal profile families and moving marks; the common prescribed-prefix
backward-edge theorem retains the actual suffix replacement.  The support
drop is therefore a genuine entry into the existing renewable tangent lane,
not the invalid date-zero normalization of an arbitrary screened endpoint.

This connection removes the unstructured zero-Never equality output **after
\(\bar\rho\) has been accepted as the current actual minimum source**.  It
does not repair the preceding all-player-escape reconstruction seam:
\(\bar\rho\) is the canonical product profile built from the selected
marginal-law limits, not a literal unilateral descendant or suffix of the
original zero-Never realizing family.  Nor does (7.50) consume its earlier
paid-row or off-minimum outputs.  Thus it is a real chamber contraction, but
not yet the requested terminal consumer.

### 7.13 Exact finite reconstruction phase and its typing limit

The word "canonical" in the preceding paragraph can be made more precise.
Let \(\sigma_n\) be the original common realizing sequence in the escape
account, and fix an order of the four players.  For \(k=0,\ldots,4\), form
\(\sigma_n^k\) by replacing the first \(k\) players' complete stopping laws
by their selected compact limits.  Then

\[
 \sigma_n^0=\sigma_n,
 \qquad
 \sigma_n^4=\bar\rho,
\tag{7.51}
\]

and every adjacent pair is a literal one-player behavioral replacement.
Jointly compactify the four intermediate semantic/law sequences.  If any
intermediate limit has debt strictly above \(D_*\), the reconstruction cube
already supplies an actual off-minimum target with at most four replacement
ancestors from the original source family.

If no intermediate limit is off minimum, every vertex lies on the global
minimum fibre.  Interpolate the one changed marginal on each adjacent edge.
Exactly as in Section 7.10, convexity plus global minimality makes every one
of the four interpolation edges a flat minimum chord, and every cap coordinate
is affine on it.  Thus the complete equality branch has the finite form

\[
\boxed{
 \text{at most four literal flat minimum marginal chords}
 \longrightarrow
 \text{the singleton-to-pair dispatch (7.50)}.}
\tag{7.52}
\]

This gives a legitimate one-use reconstruction phase: the number of
unreplaced marginal laws decreases from four to zero, after which the strict
support child in (7.50) enters the ordinary tangent-support rank.  It is
useful source provenance for a regenerated producer.

It is still not an accepted temporal or payoff chronology.  A marginal
replacement in (7.51) can be unprofitable for its mover, and flatness of total
debt does not change that sign.  Therefore (7.52) cannot be concatenated with
a Nash--Bellman or punishment-floor consumer unless one additionally orients
each flat chord, or proves that the un-oriented reconstruction phase may be
used only as nonrecursive ancestry before the one paid pair edge.  This is the
remaining typing issue, not a compactness gap.

### 7.14 The product minimum is independently an accepted source

The qualification at the end of Section 7.13 is necessary only for a
compiler which intends to transport the **old** escape passport through the
four marginal replacements.  It is not an obstruction to starting the
downstream positive-Never construction at \(\bar\rho\) itself.

Assume the equality branch

\[
 D(\bar\rho)=D_*.
\tag{7.53}
\]

Then

\[
 \bar z=
 \bigl(\operatorname{Sem}(\bar\rho),
       \operatorname{Law}(\bar\rho)\bigr)
\tag{7.54}
\]

is an **actual** joint-law carrier point at the global minimum.  The escape
construction gives

\[
 \operatorname{Law}(\bar\rho)(\mathsf{Never})=q>0.
\tag{7.55}
\]

The Fin4 hard residual is a table-level hypothesis, so it is retained at
\(\bar z\).  The checked theorem
`exists_positive_finiteLawAtom_of_finFourHardResidual_minimum`, applied to
this exact point, supplies a finite coalition \(S\) with

\[
 m=\operatorname{Law}(\bar\rho)(S)>0.
\]

This point admits an explicit causal source whose literal suffix is
\(\bar\rho\) itself.  Choose a finite cutoff \(K\) such that the total
\(S\)-mass before \(K\) exceeds \(m/2\), and choose one date \(t<K\) with
positive \(S\)-mass.  For rank \(n\), use the constant suffix profile
\(\bar\rho\) and prefix it by \(n+1\) literal all-Continue rows.

The global singleton moat gives

\[
 B_i(\bar\rho)-r_i(\{i\})\ge D_*>0
 \qquad(i<4).
\]

Hence all Continue is an exact cap--Nash root against \(B(\bar\rho)\).
Its prefix leaves the complete terminal semantics and law unchanged, so the
same statement iterates through the whole word.  The prefix Continue product
is one, its debt is exactly \(D_*\), and the chosen atom appears with the
same positive mass at the shifted date \(n+1+t\).  Thus the constant suffix,
constant cutoff and mark, and silent words explicitly inhabit the causal
minimum-source fields at \(\bar z\).  No newly selected joint-law realizer is
needed.

Now apply the reviewed positive-Never construction
`CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY.md` at \(\bar z\).
It produces actual profiles

\[
 P_n=R_n\star\widehat\rho_n,
 \qquad
 Q_n=R_n\star\widehat\rho_n^{[i,T_n]},
\tag{7.56}
\]

where \(R_n\) is an exact cap--Nash prefix over the literal suffix
\(\widehat\rho_n\), \(D(P_n)\to D_*\), and \(Q_n\) is one complete
unilateral late release of \(P_n\).  For a fixed positive-solo owner \(i\),
the gain has a fixed positive lower bound, the old finite atom occurs before
the release, and the release creates a positive singleton atom at the moving
date.  The hard-residual collision partner then gives the same-date
singleton-to-pair move used in Section 7.12.

Consequently the hypothesis in Section 7.12 that \(\bar\rho\) has been
"accepted as the current actual minimum source" is automatic in the equality
branch: it is accepted by the explicit constant-suffix source above, and all marked rows,
atoms, exact cap--Nash prefixes, and paid moves used downstream are freshly
generated there.  No field of that downstream packet refers to the original
zero-Never realizing sequence.

This gives the honest branch reduction

\[
\boxed{
 \begin{array}{c}
  \text{all-player escape reconstruction}\\
  \Longrightarrow\\
  \text{actual off-minimum product source}\\
  \quad\text{or}\quad\\
  \text{fresh source-attached positive-Never late-release packet}.
 \end{array}}
\tag{7.57}
\]

There is still no profitable or Nash--Bellman ancestry from the original
family to \(\bar\rho\).  Thus (7.57) does **not** permit one to spend the old
escape charge after the restart, prove an extension-compatible trace, or
transport an old marked row.  What it proves is narrower and sufficient for
the conditional two-release contraction: that construction uses only the
new positive-Never source and freshly generated paid rows.  Its remaining
outputs are the already named earlier-paid, off-minimum, and strict-support
waists; this section supplies no terminal consumer for them.

### 7.15 A one-way reconstruction phase cannot reset the support rank

The restart in Section 7.14 can be incorporated into one finite rank without
pretending that the original-to-product step is a profitable response or a
Nash--Bellman edge.  This is a rank on the **producer state machine**, not on
temporal game play.

Let \(B=5\), one larger than the number of players.  Use four nonterminal
state constructors:

1. `escapeOrigin`, the original all-player-escape packet;
2. `productMinimum`, the accepted positive-Never product minimum from
   Section 7.14;
3. `singletonMinimum`, the zero-Never positive-singleton endpoint of the
   minimum arm of the late release; and
4. `tangentMinimum`, the ordinary renewable strict-support node produced by
   the moving pair chord.

For a minimum point \(w\), write

\[
 s(w)=|\{i:d_i(w)>0\}|.
\]

Since \(D(w)=D_*>0\), one has \(1\le s(w)\le4\).  Define

\[
 \rho(\mathsf{exit})=0,
 \qquad
 \rho(\mathsf{tangentMinimum}(w))=s(w),
\tag{7.58}
\]

\[
 \rho(\mathsf{singletonMinimum}(w))=B+s(w),
 \quad
 \rho(\mathsf{productMinimum}(w))=2B+s(w),
 \quad
 \rho(\mathsf{escapeOrigin}(w))=3B+s(w).
\tag{7.59}
\]

Restrict the transition constructors to the ones actually proved above and
in the reviewed downstream packets:

\[
\begin{array}{rcl}
 \mathsf{escapeOrigin}&\longrightarrow&
   \mathsf{productMinimum}\ \text{or exit},\\
 \mathsf{productMinimum}&\longrightarrow&
   \mathsf{singletonMinimum}\ \text{or exit},\\
 \mathsf{singletonMinimum}&\longrightarrow&
   \mathsf{tangentMinimum}\ \text{with strict support drop, or exit},\\
 \mathsf{tangentMinimum}(w)&\longrightarrow&
   \mathsf{tangentMinimum}(w')\ \text{with }s(w')<s(w),\ \text{or exit}.
\end{array}
\tag{7.60}
\]

Every arrow strictly decreases \(\rho\).  Indeed, the largest rank in a
lower phase is smaller than the smallest rank in the phase immediately above
it, and the final recursive arrows strictly decrease support cardinality.
There is no constructor returning to `escapeOrigin`, `productMinimum`, or
`singletonMinimum` after its phase has been consumed.

This prevents the familiar rank-reset error: reconstruction is not invoked
afresh after every support child.  After at most three one-way phase changes,
all recursion lies in the ordinary strict-support lane, which has at most
three further nontrivial drops in Fin4.

The qualification is essential.  The first arrow in (7.60) is the canonical
compact-law restart of Section 7.14, not an executable chronological edge.
Thus \(\rho\) proves finite **producer control** and is enough to justify that
the reconstruction seam cannot recur inside this lane.  It does not charge
the original escape, create a payoff return, or consume any nonrecursive
exit.  If a downstream theorem requires every rank edge itself to be a
profitable or Nash--Bellman move, (7.58)--(7.60) do not meet that stronger
interface.

### 7.16 A null backward reconstruction seam is impossible

The missing original-to-product ancestry cannot be repaired by a vanishing
semantic/law seam.  This follows from one coordinate of the retained law.

Let \(\sigma_n^0=\sigma_n\) be the original escape realizers and let
\(\sigma_n^4=\bar\rho\).  Insert any four-step marginal-replacement path

\[
 \sigma_n^0,\sigma_n^1,\ldots,\sigma_n^4
\]

which replaces one complete player law at each edge.  Write

\[
 N_n^k=\Pr_{\sigma_n^k}(\mathsf{Never}).
\]

The escape arm gives \(N_n^0\to0\), whereas \(N_n^4=q>0\).  Therefore

\[
 q-o(1)
 =|N_n^4-N_n^0|
 \le\sum_{k<4}|N_n^{k+1}-N_n^k|.
\tag{7.61}
\]

After a fixed-edge subselection, some \(k<4\) satisfies

\[
 |N_n^{k+1}-N_n^k|\ge q/4-o(1).
\tag{7.62}
\]

Since total variation dominates the difference of the probability of one
event, the ordinary terminal laws at that edge remain separated by at least
\(q/4-o(1)\) in total variation.  This statement is independent of the order
of replacement and of all payoff signs.

Nor can source causalization hide this edge behind a null prefix.  If one
common finite word has joint Continue probability \(c_n\), the prefixed
Never mass is exactly \(c_nN_n^k\).  Hence for \(c_n\to1\),

\[
 |c_nN_n^{k+1}-c_nN_n^k|
 \ge q/4-o(1).
\tag{7.63}
\]

The same conclusion holds for two different prefixes whose absorption
probabilities both tend to zero, by two triangle inequalities.  Thus no
complete-law seam with error \(o(1)\) can turn the original escape family
into the product source.

Equation (7.62) does not orient the edge in payoff.  The mover's cap is fixed,
but its prescribed payoff may rise, fall, or remain unchanged, and the other
three caps may move by order one.  Therefore the macroscopic law toll is not
by itself an accepted chronological charge.  It proves the exact boundary:

\[
\boxed{
 \text{backward reconstruction must consume a macroscopic law change,}
 \quad\text{or use the one-way producer phase of Section 7.15}.}
\tag{7.64}
\]

In particular, asking only for a subtler compactness diagonal or a
high-survival common prefix cannot solve this seam.

## 8. Boundary checks

1. **Escaping deadline.**  The cutoff \(H_n\) may tend to infinity.  The
   proof is per-profile and uses no common horizon.
2. **Never action.**  Never is explicitly included in \(A_n\).  Only finite
   times strictly after \(H_n\) are approximated by it.
3. **Date zero.**  The action set includes zero, so immediate Quit is not
   omitted.
4. **Other free clocks.**  On the event that no free player stops by \(H_n\),
   every nondeviating free player chose Never.  This is why the comparison in
   (4.1) depends only on player \(k\)'s tail.
5. **No positive minimum.**  If \(D_*=0\), the minimum cluster in Section 5
   need not have a unique debtor.  Positivity is essential for (5.2).
6. **No source chronology claim.**  The three replacements from
   \(\sigma_n\) to \(\rho_n\) are actual profile ancestry, not an ordered
   temporal or Nash--Bellman path.

## 9. Sources checked and Lean handoff

The proof uses the stopping-law representation and pure-time completeness of
the unrestricted behavioral cap recorded in:

- `formalized/ARBITRARY_CLOCK_MINIMUM_PURIFICATION_TO_OFF_MINIMUM_PAID_PORT.md`;
- `formalized/FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md`;
- `notes/CODEX_AMPERE__FINITE_FIXATION_SPECTATOR_COMPRESSION_AND_HOST_ROTATION.md`;
  and
- `notes/CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY.md` for the
  stronger reviewed finite-support/root-prefix form of Section 7.9;
- `notes/PAIRED_HULL_REVIEW__ORIENTED_PAIR_TO_SINGLETON_OR_RENEWABLE_CHORD.md`,
  Section 17, for the moving singleton-to-pair minimum-chord dispatch used in
  Section 7.12;
- `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`,
  especially `exists_terminalGap_collision_at_singleton`, for (7.48);
- `formalized/FIN4_SINGLETON_BASE_SAME_LAW_RESET_PRODUCER.md` for comparison
  with the already checked stationary unique-debtor source; and
- `UniformEquilibrium/Diagnostics/Quitting/PureTimePositiveMinimumAllNever.lean`,
  especially `not_allNever_positiveMinimumTerminalSemanticDebt`, for the
  strict all-Never debt inequality in (7.29a);
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`,
  especially `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum`,
  for the finite atom at the exact product point in Section 7.14; and
- `Research/Quitting/SourceFaithfulRetainedResolution.lean` and the checked
  silent-prefix semantics for the all-Continue source construction in
  Section 7.14.

A narrow formalization can be split into:

1. selection of a fixed marginal-Never label from (2.1);
2. a finite mixed-Nash game on the three free stopping-time alphabets
   \(A_n\);
3. the late-time-versus-Never coupling bound (4.1);
4. conversion of finite Nash to the complete cap bound (4.3); and
5. the joint carrier strict/minimum dispatch (5.3).

No declaration currently packages this source-selected screened free-Nash
contraction.  Section 7.2 distinguishes the provenance-forgetting
arbitrary-clock contraction from the provenance-preserving
off-minimum/all-player-escape dispatch.  Sections 7.3--7.5 refine the latter
to a fixed reached port or the checked all-player-escape and two-cut outputs.
None of those downstream waists is claimed consumed.
