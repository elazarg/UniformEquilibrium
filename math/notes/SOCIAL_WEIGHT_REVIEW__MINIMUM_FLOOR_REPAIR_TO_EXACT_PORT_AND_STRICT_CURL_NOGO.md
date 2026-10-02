# Minimum-floor repair enters the exact port; a strict curl does not

Identity: `SOCIAL_WEIGHT_REVIEW`

Date: 2026-08-31

Status: **ordinary mathematics proved below; genuine reduction, not a
terminal consumer.**  In the all-player punishment-normal hard residual, a
source-attached positive global-minimum limit always yields actual
punishment-floor-safe paid profiles.  This includes the unique-debtor
boundary, where a vanishing best-response softening repairs the only possible
floor deficit.  The checked exact-port theorem then gives a uniform payoff or
the familiar summable all-Continue semantic port.  The latter remains open.

By contrast, a response curl at a strictly off-minimum endpoint gives no
punishment-floor control.  Section 6 gives an exact four-player regression in
which the curl and both exact response edges are present while a third
player's prescribed payoff is zero and its punishment value is one.

## 1. Question

Can the absolute signed seam or the common-response curl at the current Fin4
port be fed into an existing terminal consumer?

The closest checked consumer is
`QuittingPaidRowFloorSafeSource.exists_markedExactOrbit_alternative_of_witness`.
Its additional hypothesis is not cap switching or a second paid edge.  It is
the all-player inequality

\[
 \operatorname{Pun}_i\le U_i(\sigma)\qquad(i\in I)
\tag{1.1}
\]

at the **same actual profile** carrying the paid row.

The answer separates cleanly.

* At a source-attached global-minimum landing, punishment normality repairs
  (1.1), including at a unique-debtor boundary.  This enters the exact port.
* At a strict off-minimum curl landing, the local rectangle does not imply
  (1.1).  The signed seam/curl therefore does not enter the floor-safe orbit
  directly.  Its paid row can still enter the separate checked cap-lifted
  trichotomy, which stops at charged return, quantitative real debt descent,
  or literal inert stall.

## 2. Every positive global minimum is weakly floor-safe

Let \(z=(U,B)\) be a global minimizer of terminal-semantic debt and put

\[
 d_i=B_i-U_i,\qquad D_*:=\sum_i d_i>0,
 \qquad s_i:=r_i(\{i\}).
\]

The checked singleton margin says

\[
 B_i-s_i\ge D_*.
\]

Therefore

\[
 U_i-s_i\ge D_*-d_i=\sum_{k\ne i}d_k\ge0.
\tag{2.1}
\]

The maintained Fin4 hard residual is punishment-normal for every player:

\[
 \operatorname{Pun}_i\le s_i.
\tag{2.2}
\]

Combining (2.1)--(2.2) gives

\[
 \boxed{\operatorname{Pun}_i\le U_i\quad(i\in I).}
\tag{2.3}
\]

This is a carrier statement.  It is not yet an actual input to the checked
exact-port theorem when \(z\) is only a limit point.

If at least two coordinates of \(d\) are positive, (2.1) is strict for every
player.  With

\[
 m:=\min_i\sum_{k\ne i}d_k>0,
\tag{2.4}
\]

every actual profile whose prescribed payoff is sufficiently close to \(U\)
is floor-safe with margin at least \(m/2\).  This extends the familiar
full-debt punishment moat: full support is unnecessary; debt-support
cardinality at least two suffices.

## 3. The unique-debtor floor repair

The only boundary not covered by the strict moat is

\[
 d_p=D_*>0,\qquad d_i=0\quad(i\ne p).
\tag{3.1}
\]

Let actual profiles \(\sigma_n\) have semantic pairs converging to \(z\).
Write \(U^n,B^n,d^n\) for their semantic coordinates and

\[
 f_n=(\operatorname{Pun}_p-U^n_p)_+.
\]

Equations (2.1)--(2.2) imply \(f_n\to0\).  For \(i\ne p\), (3.1) gives the
strict limiting floor margin

\[
 U_i-\operatorname{Pun}_i\ge D_*.
\tag{3.2}
\]

Choose errors \(\varepsilon_n\downarrow0\) and a pure stopping time
\(q_n^+\in\mathbb N\cup\{\infty\}\) satisfying

\[
 V^n_p(q_n^+)\ge B^n_p-\varepsilon_n.
\]

After discarding finitely many terms, put

\[
 a_n:=V^n_p(q_n^+)-U^n_p\ge D_*/2.
\tag{3.3}
\]

If \(f_n=0\), set \(\theta_n=0\).  Otherwise set

\[
 \theta_n={2f_n\over a_n}.
\tag{3.4}
\]

For all late \(n\), \(0<\theta_n<1\) and \(\theta_n\to0\).  Let
\(\widetilde\sigma_n\) be obtained by replacing player \(p\)'s stopping law
by the convex stopping-law mixture

\[
 (1-\theta_n)\sigma_{n,p}+\theta_n q_n^+.
\]

This notation means the **complete stopping-law** mixture, realized as an
actual behavioral strategy by
`quittingStoppingLawMixtureBehaviorStrategy`.  It is not the pointwise
mixture of the two behavioral hazards.  The latter would repeatedly spend
the mixing weight along a long window and would not give the affine
identities used here.  The checked realization theorem identifies the
induced stopping law with the binary PMF mixture above.

Complete stopping-law mixture is affine in every prescribed terminal payoff.
Hence

\[
 U_p(\widetilde\sigma_n)
 =U^n_p+\theta_na_n
 \ge \operatorname{Pun}_p.
\tag{3.5}
\]

For every \(i\ne p\), the payoff change tends to zero because
\(\theta_n\to0\); the strict margin (3.2) therefore gives

\[
 U_i(\widetilde\sigma_n)\ge\operatorname{Pun}_i
\tag{3.6}
\]

for all late \(n\).  Thus \(\widetilde\sigma_n\) is an **actual floor-safe
profile**.

The repair retains the **full** incoming terminal-semantic limit, not only
the prescribed payoff and law.  Let \(M\) be the checked absolute reward
bound.  The prescribed profile and every profile obtained by an arbitrary
behavioral replacement of a nonmover \(i\ne p\) differ between the source
and repaired versions only through the same Bernoulli choice of player
\(p\)'s complete stopping law.  Therefore, uniformly over every behavioral
replacement of \(i\),

\[
 \left|U_i(\tau_i,\widetilde\sigma_{n,-i})
       -U_i(\tau_i,\sigma_{n,-i})\right|
 \le 2M\theta_n.
\tag{3.7}
\]

Taking suprema gives

\[
 |B_i(\widetilde\sigma_n)-B_i(\sigma_n)|\le2M\theta_n
 \qquad(i\ne p).
\tag{3.8}
\]

For the mover, the opponents are unchanged, so

\[
 B_p(\widetilde\sigma_n)=B_p(\sigma_n)
\tag{3.9}
\]

exactly.  Prescribed payoffs satisfy the same \(2M\theta_n\) bound, and the
complete terminal-outcome law is the exact convex mixture of the source and
endpoint laws; in particular its total-variation distance from the source
law is at most \(\theta_n\).  Since \(\theta_n\to0\), the repaired profiles'
entire prescribed-payoff/cap/law packets converge to the same incoming
minimum packet.

This repair also retains a fixed paid pure-time row.  Player \(p\)'s original
stopping law is a probability law on \(\mathbb N\cup\{\infty\}\), and its
payoff is the average of the pure-time values.  Hence one supported pure time
\(q_n^-\) satisfies

\[
 V^n_p(q_n^-)\le U^n_p.
\]

The opponents are unchanged by the softening, so at
\(\widetilde\sigma_n\)

\[
 V_p(q_n^+)-V_p(q_n^-)
 \ge a_n\ge D_*/2.
\tag{3.10}
\]

The checked pure-time first-disagreement decoder therefore supplies a
`QuittingPaidFirstDisagreementRow` on the same floor-safe actual profile,
with any fixed gain below \(D_*/2\).

There is a stronger kernel-checked **scratch-lane** selection in
`fable/lean/FableDebtActualReach.lean`.  Since

\[
 d_p(\widetilde\sigma_n)
 =d^n_p-\theta_na_n\longrightarrow D_*,
\]

apply
`positiveDebt_exists_actualJointReach_paidFirstDisagreementRow` with, for
example, \(\Delta=D_*/2\).  It selects the row so that its gain is
\(D_*/8\) and

\[
 {D_*^2\over4}
 \le32M^2\Pr_{\widetilde\sigma_n}
       (\text{all players survive strictly before the row start}).
\tag{3.11}
\]

More precisely, the underlying theorem
`positiveDebt_exists_actualReach_paidFirstDisagreementRow` gives the two
division-free inequalities

\[
 \Delta\le4M\,\Pr(\text{the observer survives to the row start}),
 \qquad
 \Delta\le8M\,\operatorname{liveMass}_{-p}(\text{row start}),
\tag{3.12}
\]

and their product is (3.11).  Since \(D_*>0\) forces \(M>0\), (3.11) may be
divided to give the explicit joint-reach floor

\[
 \Pr(\text{all players survive strictly before the row start})
 \ge {D_*^2\over128M^2}.
\tag{3.13}
\]

The strengthened scratch theorem
`positiveDebt_exists_actualJointReach_paidRow_withSupport` in
`fable/lean/FableActualReachSupport.lean` selects a row with the same gain
constant and joint-reach bound while also retaining the exact support
disjunction (writing its source witness as \(q_n^-\))

\[
 \begin{array}{c}
 q_n^- = t<\infty\text{ and player }p\text{ has positive stopping mass at }t,
 \\
 \text{or}\quad
 q_n^- = \infty\text{ and player }p\text{ has positive Never mass}.
 \end{array}
\tag{3.14}
\]

The support clause concerns the decoder's **source witness** \(q_n^-\), not
the receiving witness \(q_n^+\).  The probability in (3.11)--(3.13) is joint
survival to the row start; it is not a lower bound on any particular terminal
coalition atom at that row.  Thus the floor repair is compatible with the
stronger actual-reach fork, not only with the opponents-only `liveMass` field
of the generic paid row.

Both named actual-reach theorems, and the support wrapper, are presently
kernel-checked only in `math/fable/lean/`; no production file imports them.
By contrast, `QuittingPaidRowFloorSafeSource` and its exact-port alternative
used below are production declarations.  The adapter from the minimum
sequence to the floor-safe source remains ordinary mathematics and has not
yet been packaged as a Lean declaration.

No attainment of the unrestricted cap is used.  Approximate pure-time
attainment and support averaging suffice.  The case \(q_n^+=\infty\) and the
case \(q_n^-=\infty\) are both literal parts of the decoder.

## 4. Universal minimum-landing entrance to the exact port

The preceding argument gives a two-case theorem.

> **Minimum-floor paid entrance.**  Let a source-attached actual profile
> sequence converge in full prescribed-payoff/cap semantics to a positive
> global minimum of a Fin4 hard residual.  Then, after a subsequence and
> modifications tending to zero in complete stopping-law total variation,
> there are actual profiles which
>
> 1. lie above every behavioral punishment value;
> 2. retain the incoming limiting semantic pair and full terminal law; and
> 3. carry a pure-time paid first-disagreement row with one fixed positive
>    gain floor.

When the limiting debt support has cardinality at least two, no modification
is needed: use the strict floor moat and select a fixed positive debtor.  When
the support has cardinality one, use Section 3.

Applying the checked source-facing exact-port theorem and the terminal-gap
witness gives

\[
 \boxed{
 \text{uniform-equilibrium payoff}
 \quad\lor\quad
 \text{source-matched summable all-Continue semantic port with positive
 suffix reach}.}
\tag{4.1}
\]

Consequently a global-minimum landing of the response-curl minimizer is not a
new terminal chamber.  It enters the already known summable-port waist.  The
response curl is useful upstream to produce the landing, but it is not needed
for the floor repair once source-attached minimum approximants are available.

This does not solve that waist.  The exact roots are added by outward
prefixing:

\[
 q_{N-1}\star\cdots\star q_0\star\widetilde\sigma_n.
\]

Increasing \(N\) changes the earliest root.  These finite profiles are not
initial segments of one forward chronology.  Summability retains positive
reach to the paid suffix but supplies neither a forward exact spine nor a
completely absorbing sequentially-perfect family.  It therefore does not by
itself instantiate AGKRS branch S.3.

## 5. What the absolute seam and curl do supply

At a full-response edge \(S\to E\) of mover \(p\), exact cap invariance for
the mover gives

\[
 D(E)-D(S)
 =-[U_p(E)-U_p(S)]
   +\sum_{i\ne p}(d_i(E)-d_i(S)).
\]

At a global minimum this forces compensating leakage.  In Fin4, some
nonmover has a cap rise or payoff loss of at least one sixth of the mover
debt plus the off-minimum excess.  A finite exact-response cycle strengthens
this to one source-attached common-response rectangle with a fixed positive
curl.  The checked full-chord theorem then turns a first-order response
switch into a paid first-disagreement row plus deleted-clock survival.

None of these outputs includes (1.1).  The only present route from such a row
to an exact **prescribed-payoff punishment-floor orbit** is therefore:

\[
 \text{actual paid row}
 +\text{same-profile punishment floor}
 \longrightarrow
 \text{exact-port alternative}.
\tag{5.1}
\]

Sections 2--4 provide the missing floor only at a global-minimum landing.
They do not provide it at a strict off-minimum curl port.  Independently, a
paid row plus the retained positive global minimum can be packaged as a
`QuittingPaidCapLiftedSource`, since that structure imposes no prescribed-
payoff floor on the paid profile.  Its checked exact trichotomy gives:

\[
 \text{charged cap near-return and UE}
 \quad\lor\quad
 \text{quantitative total-debt descent}
 \quad\lor\quad
 \text{literal all-Continue inert stall}.
\tag{5.2}
\]

The last two arms are not terminal consumers, and the debt decrease is not a
renewable well-founded rank.  Thus (5.2) is an honest reduction of the strict
curl row, not a contradiction and not an entrance to the floor-safe orbit.

There is one exact chronological consequence which still falls short of a
consumer.  Suppose the paid row compares two finite pure times \(t<u\).  On
the event that no opponent stops from \(t\) through \(u\), both plans stop
alone and receive the same singleton reward.  Coupling the two plans therefore
gives

\[
 |V_i(t)-V_i(u)|
 \le 2M\Pr(\text{an opponent stops between }t\text{ and }u
              \mid\text{opponents reach }t).
\tag{5.3}
\]

Multiplying by the row's opponents-only live mass shows that a paid gain
\(g\) yields a literal **observer-deleted** two-cut opponent-absorption event
of mass at least \(g/(2M)\).  This is unconditional in the three-opponent
marginal law; it is not actual joint reach, because the observer's prescribed
strategy may stop before \(t\).  If the later witness is Never, the same coupling
leaves an additional no-opponent term equal to the singleton-versus-Never
payoff difference.  Thus the full chord supplies the positive-hazard part of
a two-cut passport, or a singleton/Never boundary.

It does not supply actual entry reach, near-minimum debt at either cut, exact
Nash--Bellman rows inside the receiving profile, or renewable child-source
ancestry.  Those are the missing fields in the current two-cut and AGKRS
consumers.

## 6. Exact strict-port regression

The failure is local and exact.  Take players \(o,m,\ell,k\), fix
\(0<d<1\), and define terminal rewards as follows:

\[
 r_o(S)=\mathbf 1_{\{o,m\}\subseteq S},
\]

\[
 r_m(S)=
 \begin{cases}
 d,&m\in S,\ o\notin S,\\
 1,&o\in S,\ m\notin S,\\
 0,&\text{otherwise},
 \end{cases}
\]

\[
 r_\ell(S)=
 \begin{cases}
 1,&\ell\notin S,\\
 1,&S=\{\ell\},\\
 0,&\ell\in S\text{ and }S\ne\{\ell\},
 \end{cases}
 \qquad r_k(S)=0.
\tag{6.1}
\]

Never pays zero.  At date zero let \(\ell\) Quit surely and \(k\) Never.
Let \(o,m\) use the four pure choices

\[
 X=(N,N),\quad E=(N,Q),\quad Y=(Q,N),\quad Z=(Q,Q).
\]

The displayed outcomes are respectively

\[
 \{\ell\},\quad\{m,\ell\},\quad\{o,\ell\},\quad
 \{o,m,\ell\}.
\]

For observer \(o\),

\[
 U_o(X)=U_o(E)=U_o(Y)=0,\qquad U_o(Z)=1,
\]

so the common-response curl is exactly one:

\[
 [U_o(Z)-U_o(E)]-[U_o(Y)-U_o(X)]=1.
\tag{6.2}
\]

The mover edge \(X\to E\) is an exact best response of gain \(d\), and the
observer edge \(E\to Z\) is an exact best response of gain one.  Thus the
rectangle has both literal paid edges, zero observer debt at \(Z\), and a
finite paid first-disagreement row.

Nevertheless the receiving endpoint \(E\) is not floor-safe.  Against any
opponent profile, let \(T\in\mathbb N\cup\{\infty\}\) be the first opponent
stopping time.  If \(\ell\) uses pure time \(q\), its payoff under (6.1) is

\[
 1-\Pr(T=q).
\tag{6.3}
\]

Every probability distribution on the countably infinite set
\(\mathbb N\cup\{\infty\}\) has atoms with arbitrarily small mass.  Hence
\(\ell\)'s unrestricted cap is one against every opponent profile.  Since
rewards are bounded above by one,

\[
 \operatorname{Pun}_\ell=1.
\tag{6.4}
\]

At both \(E\) and \(Z\), player \(\ell\) Quits simultaneously with at least
one other player, so

\[
 U_\ell(E)=U_\ell(Z)=0<1=\operatorname{Pun}_\ell.
\tag{6.5}
\]

Thus both receiving corners fail the same \(\ell\)-floor.  Even an exact
finite response rectangle with a unit curl and exact best-response edges need
not yield a `QuittingPaidRowFloorSafeSource`.
This table is an interface regression, not a counterexample to uniform
equilibrium existence or to any theorem using positive global-minimum
provenance.

## 7. Relation to current consumers

### Hard-principal geometry

The signed seam and curl identify one behavioral cross-effect.  They do not
identify the response row with the separately selected punishment-normal
hard principal, nor do they make the other coordinates exact at the retained
cap.  The plateau regressions show that a positive curl is compatible with a
unique all-Continue cap root because the mover or a third player can carry a
fixed root defect.

### Cap-switch full chord

`TerminalSemanticCapSwitchFullChord` consumes first-order curvature into a
paid row and deleted-survival floors.  Its row can be inserted directly into
a `QuittingPaidCapLiftedSource` with the retained positive global minimum,
and hence enters (5.2).  What is still absent is either a consumer of the
quantitative-descent/inert arms, or the same-profile punishment floor needed
to enter (5.1).

### AGKRS S.3

The curl supplies a profitable deviation, whereas S.3 needs a completely
absorbing sequence whose prescribed rows are asymptotically sequentially
perfect.  The exact-port construction repairs row exactness only in an
outward-prefix orbit.  Its summable arm has the wrong chronological
orientation and does not supply complete absorption.  Therefore the signed
seam/curl does not furnish the upstream AGKRS condition.

## 8. Exact remaining waist

The global-minimum branch now lands in one already isolated object:

\[
 \boxed{\text{summable outward exact-prefix port retaining a positive paid
 suffix reach}.}
\tag{8.1}
\]

The strict off-minimum branch now enters the cap-lifted trichotomy (5.2), but
its quantitative descent and inert outputs have no terminal consumer.  A
genuine next consumer must do at least one
of the following:

1. reverse or re-anchor (8.1) into one extension-compatible forward exact
   chronology;
2. turn the positive retained suffix reach into a completely absorbing
   sequentially-perfect family; or
3. derive a same-profile punishment floor or exact-cap compatibility at the
   strict curl endpoint from the positive-minimum ancestry.

The regression in Section 6 rules out item 3 from local rectangle fields
alone.

## 9. Sources inspected and Lean boundary

Named checked inputs:

* `minimumTerminalSemantic_singletonMargin`;
* `FinFourQuantitativeFullSupportHardResidual.all_punishmentNormal`;
* pure-time extremality of the unrestricted behavioral cap;
* `quittingStoppingLawMixtureBehaviorStrategy`, its exact stopping-law
  realization, and stopping-law-mixture payoff/law affinity;
* `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`;
* `QuittingPaidRowFloorSafeSource.exists_markedExactOrbit_alternative_of_witness`;
* `exists_quittingCapSwitchFullChordPaidRow_of_firstOrderRectangle`; and
* the exact cap-prefix debt-scaling identities.

Production-checked inputs in the list above include the minimum margin,
punishment normality, stopping-law realization/affinity, paid-row decoder,
and exact-port alternative.  The declarations in
`fable/lean/FableDebtActualReach.lean` and
`fable/lean/FableActualReachSupport.lean` are kernel-checked scratch results,
not production imports.  The minimum-floor paid entrance of Sections 3--4,
including the uniform cap-continuity argument, has not been packaged as a
Lean declaration.  The resulting exact-port alternative is checked once the
floor-safe paid source is supplied.  No claim is made that the summable port,
the strict curl port, or Fin4 uniform equilibrium has been consumed.
