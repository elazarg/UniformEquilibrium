# CODEX adversary: the off-minimum paid exit has a low-limit capacity slice, not a complete consumer

**Status (2026-08-30).** Ordinary mathematics, not Lean-checked as new
theorem groups.  Sections 1--5 prove a source-faithful special-case transition
from the third canonical renewal exit into the finite-hazard capacity
mechanism.  The transition requires the selected paid source's cap-port limit
to return a fixed fraction of the way toward the global debt minimum.  Section
6 audits the complementary high-limit branch without reselecting an endpoint
row: the exact cap-prefix sources form one literal tail system and retain a
fixed positive paid gain, but their remaining charge tends to zero and the
paid disagreement moves ballistically to infinity.  The branch either becomes
literally inert at finite depth or, under hypothetical nonexistence of a
uniform payoff, gives quantitative descents with vanishing size.  Thus this
note gives a genuine low-limit adapter and a sharp high-limit no-go, not a
completion of the Fin4 proof.  Section 8 directly tests deadline, clock
deletion, punishment, transverse-root, and finite-capacity consumers.  Exact
clock deletion recovers a fixed old suffix, and one new maximal-prefix orbit
gives a fixed-toll-or-inert-omega contraction.  Neither operation supplies the
history-compatible admissible return required by the checked terminal
consumers.  The finite-capacity conclusion (47) of Attempt 1 consequently
remains conditional on a single composable source-provenant chronology.
Section 9 consumes a positive exact root at the omega-source into an exact
joint-law debt return: equality with the minimum regenerates a minimum-law
source, while a strict off-minimum returned point and the unique-all-Continue
omega-source remain open.

This note continues
[`CODEX_ADVERSARY__FIN4_STRICT_RAY_RECURRENCE_INSUFFICIENCY.md`](CODEX_ADVERSARY__FIN4_STRICT_RAY_RECURRENCE_INSUFFICIENCY.md),
especially its Theorem 4 and Sections 7--8.

## Question

For one of the three terminal exits of the checked canonical support-renewal
rank, can the current source data produce either

1. a terminal uniform-equilibrium consumer, or
2. a literal exact parent-to-child block whose positive hazard charge is
   debited from the same history capacity?

I choose the off-minimum paid-first-disagreement exit because it already
contains actual behavioral profiles and its cap lift supplies literal exact
prefixes.

## 1. The three exact exit interfaces

For a `FinFourRenewableMinimumSourceNode` `node`, the definition
`FinFourRenewableTerminalExit` in
`Research/Quitting/FinFourProducerAtlas/CanonicalPairRenewableSourceRank.lean`
is exactly the following disjunction.

1. **Positive total tangent slope:**
   \[
     \exists m,\qquad 0<\sum_j T(m,j).
   \]

2. **Flat tangent plus support entry:**
   \[
     (\forall m,\ \sum_jT(m,j)=0)\quad\text{and}\quad
     \operatorname{HasFlatSupportEntry}(b,S,T).
   \]
   Expanding `HasQuittingStoppingLawFlatSupportEntry` from
   `ExhaustiveTangentAlternative.lean`, with \(\bar T\) the extension of the
   active-support tangent by zero, the second conjunct is
   \[
     \exists m\in S\ \exists j,qquad d_j(b)=0
       \quad\text{and}\quad 0<\bar T(m,j).
   \]

3. **Off-minimum paid first disagreement:** there are an active mover
   \(m\in S\) and a `FullReplacementCluster` endpoint \(z\), including an
   actual subsequence \(n_r\) with
   \[
      x_r:=\operatorname{fullReplacementPair}(m,n_r)\longrightarrow z,
   \]
   such that `HasOffMinimumPaidFirstDisagreement` holds.  Expanding that
   definition gives
   \[
      D_*:=D(b)<D(z)
   \]
   and fixed \(j\ne m\), \(G>0\) for which, eventually in \(r\), the literal
   profile producing \(x_r\) carries a nonempty
   `QuittingPaidFirstDisagreementRow reward profile j G`.

These are alternatives of the terminal node reached after at most three
strict positive-debt-support descents.  The support rank itself supplies no
consumer for any of them.

## 2. A necessary strengthening of the current paid dispatch

Put
\[
  g=D(z)-D_*>0.
\tag{1}
\]
Because `FullReplacementCluster.fullReplacement_tendsto` gives
\(x_r\to z\), and `continuous_quittingTerminalSemanticDebtSum` makes \(D\)
continuous,
\[
  D(x_r)\longrightarrow D(z)=D_*+g.
\tag{2}
\]
The paid-row property is eventual along the *same* ranks.  Intersecting the
two eventual sets therefore gives a rank \(r\) with both
\[
  D(x_r)>D_*+\frac{3g}{4}
\tag{3}
\]
and an actual paid row of the fixed gain \(G\).  Applying
`paidFirstDisagreement_capPortTrichotomy` to that row gives a
`QuittingPaidCapLiftedSource` \(s\) whose literal profile realizes \(x_r\),
whose minimum is \(b\), and hence whose initial debt satisfies (3).

This late choice is not what the checked theorem
`separated_and_paidCapPortDispatch_of_offMinimumPaidFirstDisagreement`
currently records.  Its proof uses only `hrows.exists`, so its selected rank
may be an early paid rank and the conclusion stores no lower bound on
`source.initialDebt`.  The endpoint separation carried beside the dispatch
does not imply separation of that arbitrarily selected source.  Any consumer
using the cluster gap must first add the late-selection strengthening above.

This is a quantifier issue, not a topological gap: the strengthened statement
follows immediately by intersection of two eventual predicates.

## 3. Low-limit paid exit gives an exact charged history child

Let \(p\) be a `SummablePort` of the late-selected source \(s\), and write
\[
 D_0=s.\mathrm{initialDebt},\qquad
 L=D(p.\mathrm{semanticPort.limit}).
\]
Let \(s_N\) be the actual literal profile
`quittingCapLiftedPrefixProfile reward s.profile N`, and put \(D_N=D(s_N)\).
The roots used in this profile are exact cap--Nash roots at their actual
successive suffixes.

### Theorem (off-minimum low-limit capacity slice)

Assume
\[
  L\le D_*+\frac g2.
\tag{4}
\]
Let \(D_{\max}>0\) be any uniform upper bound for total semantic debt on the
terminal semantic carrier.  Such a bound exists by compactness and continuity.
Then there is a finite \(N\) such that the literal exact block from `s.profile`
to \(s_N\) has unweighted absorption charge, and hence total marginal-hazard
charge, at least
\[
  \kappa=\frac{g}{8D_{\max}}>0.
\tag{5}
\]
Moreover `s.finitePrefixSource p N` is a paid cap-lifted source with

- profile exactly \(s_N\);
- the same global minimum \(b\);
- a strictly positive paid gain; and
- a suffix literally equal to the old source profile.

Thus it is a history-compatible child, not a freshly causalized carrier
point.  Write \(H(B)\) for the charge used by the history capacity: either
the sum of row absorption masses or the (larger) sum of all marginal quit
probabilities.  For every history potential satisfying the genuine extension law
\[
  \Phi(\tau)\ge H(B)+\Phi(\tau B),
\tag{6}
\]
this transition gives
\[
  \Phi(\tau B)\le\Phi(\tau)-\kappa.
\tag{7}
\]

### Proof

The checked `SummableSemanticPort.semantic_tendsto`, followed by continuity
of total debt, gives \(D_N\to L\).  Choose \(N\) so that
\[
  D_N<L+\frac g8\le D_*+\frac{5g}{8}.
\tag{8}
\]
By (3),
\[
  D_0-D_N>\frac g8.
\tag{9}
\]
Finite exact cap prefixing scales total debt by the joint survival product:
\[
  D_N=P_ND_0,
\tag{10}
\]
which is exactly
`quittingCapLiftedPrefixProfile_debt_eq_suffixReach_mul` (and equivalently
the finite stack identity
`quittingTerminalDebtSum_capNashRootStack_eq`).  Since \(D_0>0\),
\[
  1-P_N=\frac{D_0-D_N}{D_0}
    >\frac{g}{8D_{\max}}=\kappa.
\tag{11}
\]
If \(a_t\) is the absorption mass of row \(t\), then
\(P_N=\prod_{t<N}(1-a_t)\), and the elementary union bound gives
\[
  1-P_N\le\sum_{t<N}a_t=H(B).
\tag{12}
\]
This proves (5).
For each row, absorption (the probability that at least one player quits) is
at most the sum of the players' marginal quit probabilities.  Thus the same
lower bound applies if `hazard capacity` uses marginal rather than absorption
charge.

The source claims follow directly from
`QuittingPaidCapLiftedSource.finitePrefixSource`,
`finitePrefixSource_profile`, and `finitePrefixSource_minimum` in
`FinFourPaidResetDescentRegeneration.lean`.  Its paid gain is
`source.reachFloor * source.gain`, positive by `reachFloor_pos` and
`gain_pos`, and its row is the exact shifted row from the port.  Because its
profile is the literal cap-prefix profile, any further exact block at this
child concatenates to the old block.  Applying (6) and (12) gives (7).
`QED`

### What this theorem does and does not consume

It consumes the complete subcase (4) of the paid exit by an exact transition
into the capacity-slice mechanism.  The constant \(\kappa\) depends only on
the fixed endpoint gap and a game-wide carrier bound, not on the chosen block
length.

It does **not** prove a global natural-valued rank.  Reapplication would need
every later returned source either to retain the same positive gap or to have
its own gap bounded uniformly below.  `finitePrefixSource` retains the paid
row and the minimum, but no `FullReplacementCluster` and no lower bound on a
future cluster gap.  Therefore (7) is one certified capacity debit, not an
infinite-regeneration termination theorem.

The already checked `ChargedNearReturn` arm is independently terminal:
`ChargedNearReturn.uniformEquilibriumPayoff` supplies a uniform-equilibrium
payoff.  The theorem above is useful in the remaining cap-port arms whenever
their limit satisfies (4).

## 4. Exact residual and sharp no-go

If (4) fails, the port remains on the high-debt side
\[
  L>D_*+g/2.
\tag{13}
\]
Nothing in `QuantitativeDebtDescent` rules this out.  That structure proves
only \(L<D_0\) and quantitative inequalities in terms of its possibly
arbitrarily small cap displacement.  It supplies no fixed fraction of the
cluster gap.  `InertStall` supplies zero total absorption and zero cap
displacement, so it certainly cannot satisfy a positive capacity debit.

There is also a selector-independent terminal obstruction.  If the actual
paid source satisfies `HasUniqueAllContinueAtCap`, then
`capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap` and
`capNashStackAbsorptionSum_eq_zero_of_unique_terminalCap` prove that every
finite exact cap--Nash block is the all-Continue block, fixes the semantic
pair, and has charge zero.  The stronger joint version
`exactCapPrefix_joint_eq_self_of_unique_allContinue` also fixes the complete
terminal law.  Hence no exact history-compatible transition at that same cap
can enter a *positive* capacity slice.

This no-go is fully exact: choosing a different exact root, taking a longer
finite block, or repackaging it as a punishment-floor finite prefix does not
help (`QuittingPunishmentFloorFinitePrefix.constant_of_unique_allContinue_anchor`).
An escape from this plateau must change the cap/state, use nonexact roots
with a paid error budget, or provide an independent source-matched return.

## 5. Verdict and next exact question

**Special-case verdict: PASS.**  After late-row selection, an off-minimum
paid exit whose cap-port limit returns at least halfway across its endpoint
gap supplies a literal exact child with charge at least
\(g/(8D_{\max})\).  This is a valid capacity-slice transition.

**Full-exit verdict: OPEN / not exportable as a completion.**  Current source
data neither forces the halfway-return condition nor excludes a high-debt
unique-all-Continue plateau.  The latter has a checked exact-prefix no-go.

The next concrete question is:

> For the late-selected off-minimum paid source, can the endpoint's fixed
> paid gain and source-matched full-replacement provenance either force
> \(D(p.limit)\le D_*+g/2\), or produce a cap-changing returned source from
> the high-debt plateau (13)?

A merely strict cap displacement is insufficient; the required conclusion
must retain either a fixed fraction of \(g\) or another uniform positive
charge.

## 6. The high-limit tail is an exact Zeno paid phantom

This section continues with the *same* late-selected source \(s\), its same
port \(p\), and its same row.  No new full-replacement rank and no arbitrary
eventual paid row is selected.  Assume the residual inequality
\[
  L>D_*+\frac g2.
\tag{14}
\]

Let
\[
 \sigma_n=\operatorname{quittingCapLiftedPrefixProfile}(s.profile,n),
 \qquad D_n=D(\sigma_n),
\]
and let \(r_n\) be the selected exact cap root at \(\sigma_n\).  Put
\[
 a_n=\operatorname{Abs}(r_n)=1-c(r_n),
 \qquad h_n=\sum_{i\in\operatorname{Fin}4}q_i(r_n).
\]

### Theorem (same-provenance high-limit Zeno alternative)

The following assertions hold.

1. The literal profiles form an exact tail semigroup:
   \[
      \operatorname{Prefix}^{m}(\sigma_n)=\sigma_{n+m}.
   \tag{15}
   \]
   Their debts obey
   \[
      D_{n+1}=(1-a_n)D_n,qquad D_n\downarrow L.
   \tag{16}
   \]

2. For every \(n<N\),
   \[
     \sum_{t=n}^{N-1}a_t
       \le \frac{D_n-D_N}{L}
       \le \frac{D_n-L}{L},
   \tag{17}
   \]
   and, because there are four players,
   \[
     \sum_{t=n}^{N-1}h_t
       \le 4\frac{D_n-L}{L}.
   \tag{18}
   \]
   Consequently the entire future absorption and marginal-hazard capacities
   after depth \(n\) tend to zero.

3. Let
   \[
     s_n:=s.\mathrm{finitePrefixSource}(p,n).
   \]
   Every \(s_n\) has the literal profile \(\sigma_n\), the same minimum
   \(b\), the same observer, and the same positive displayed gain
   \[
      \bar G=s.\mathrm{reachFloor}\,s.\mathrm{gain}>0.
   \tag{19}
   \]
   Its row is the exact shift of the original row.  In particular its
   orientation and relative delay are unchanged, but
   \[
      \operatorname{start}(s_n.row)=n+\operatorname{start}(s.row).
   \tag{20}
   \]

4. Exactly one of the following subcases occurs.

   - **Finite inert landing:** for some \(n\), \(D_n=L\).  Then every later
     \(a_t=0\), every selected root is all Continue, and the induced tail
     port of \(s_n\) is an `InertStall`.  No positive capacity debit remains.

   - **Strict Zeno tail:** \(D_n>L\) for every \(n\).  Give \(s_n\) its
     induced cap port, whose orbit is the literal tail
     \((\sigma_{n+m})_m\) and whose semantic limit is the same limit as
     \(p\).  Its total debt drop is \(D_n-L>0\), while
     \[
       s_n.\mathrm{totalAbsorption}
          \le \frac{D_n-L}{L}\longrightarrow0,
       \qquad
       s_n.\mathrm{capDisplacement}\longrightarrow0.
   \tag{21}
     \]
     If the game has no uniform-equilibrium payoff, every one of these
     induced tail ports lies in `QuantitativeDebtDescent`, but the strict
     descent sizes tend to zero.

Thus neither subcase supplies a repeated uniform capacity slice.  More
strongly, for every \(\kappa>0\), all sufficiently late literal exact blocks
confined to this same source tail have absorption charge less than \(\kappa\)
and marginal-hazard charge less than \(\kappa\).

### Proof

The prefix construction is iteration of the deterministic map
\[
 \sigma\longmapsto
   \operatorname{root}(\sigma)\mathbin\|\sigma.
\]
The ordinary iterate identity proves (15) by induction.  The checked
one-step debt identity
`quittingCapLiftedPrefixProfile_debt_succ` gives the first part of (16), and
`SummableSemanticPort.semantic_tendsto` plus continuity of total debt gives
the second.

Since \(D_t\ge L>0\), (16) gives
\[
  a_t=\frac{D_t-D_{t+1}}{D_t}
      \le\frac{D_t-D_{t+1}}{L}.
\]
Summing telescopes and proves (17).  Each marginal quit event is contained in
the event that somebody quits, so \(q_i(r_t)\le a_t\).  Summing over four
players proves (18).  Letting \(N\to\infty\), and then \(n\to\infty\), proves
vanishing remaining capacity.

The fields in (19) are definitionally those of `finitePrefixSource`; its row
is `p.shiftedRows n`.  The exact provenance statements (20) are
`ShiftedPaidRow.receivingEarlier_eq`, `ShiftedPaidRow.start_eq`, and
`ShiftedPaidRow.later_eq`.  Notice the decisive distinction: the *gain* is
uniform, but the marked first disagreement is not at uniformly bounded
chronological distance.  It is pushed one stage farther away by every prefix.

If \(D_n=L\), monotonicity and convergence force \(D_t=L\) for every
\(t\ge n\).  Equation (16) and \(L>0\) force \(a_t=0\); zero absorption of a
product root means all marginal quit probabilities are zero.  Hence the tail
is literally all Continue, and `inertStall_of_totalAbsorption_eq_zero`
applies.

Suppose instead that \(D_n>L\) for all \(n\).  By (15), the canonical orbit
of the actual profile \(s_n.profile=\sigma_n\) is exactly the tail of the
original orbit.  Its summable semantic port therefore converges to the same
limit; uniqueness of limits removes any dependence on how the port structure
is packaged.  Formula (17) with \(N\to\infty\) is the first estimate in (21).
The cap coordinates of \(\sigma_n\) converge to the limit cap, so the
definition of `capDisplacement` gives the second convergence in (21).

For each \(n\), \(D_n>L\) forces positive total tail absorption: otherwise
(16) would keep the debt constant.  If its cap displacement were zero,
`chargedNearReturn_of_totalAbsorption_pos_of_capDisplacement_zero` would give
a `ChargedNearReturn`, whose checked field `uniformEquilibriumPayoff` would
contradict hypothetical nonexistence.  Hence cap displacement is positive,
and `quantitativeDebtDescent_of_capDisplacement_pos` gives the claimed
quantitative descent.  Its debt drop is exactly \(D_n-L\to0\). `QED`

### Exact interface regression

The vanishing is not an artifact of the estimates.  Fix \(D_*>0\), \(g>0\),
choose
\[
  D_0>D_*+\frac{3g}{4},qquad
  D_*+\frac g2<L<D_0,
\]
and define
\[
  D_n=L+(D_0-L)2^{-n},qquad
  a_n=\frac{(D_0-L)2^{-(n+1)}}{D_n}.
\tag{22}
\]
Then (16) holds exactly, every descent is strict, the limit stays uniformly
off the minimum, and
\[
  \sum_{t\ge n}a_t\le
    \frac{(D_0-L)2^{-n}}{L}\longrightarrow0.
\tag{23}
\]
Attach the same positive paid label \(\bar G\) at every state and shift its
date by \(n\).  This satisfies every scalar, semigroup, fixed-gain, and
chronological-provenance consequence used above while admitting no repeated
positive slice.  Taking \(D_0-L\) arbitrarily small also shows that the fixed
endpoint gap \(g\) alone cannot lower-bound even the *first* high-limit debit.

This is an exact regression of the source interface, not a claim that (22)
is independently realized by a Fin4 reward table.  The actual theorem above
is conditional on occurrence of the checked high-limit residual; the
regression proves that its currently exposed numerical and provenance fields
cannot exclude Zeno behavior.

## 7. Updated verdict

The off-minimum exit now has the exact dichotomy:

- a low cap-port limit gives the history-compatible debit of Section 3; or
- a high cap-port limit produces the same-source paid phantom of Section 6.

In the second branch, repeated use of the canonical cap port is provably
incapable of supplying a uniform capacity slice.  The remaining possible
escape must be genuinely transverse: a different exact-root branch with a
source-matched return, a cap-changing operation, or a terminal consumer of
the ballistic fixed-gain paid mark.  Merely redispatching the same row through
later finite prefixes cannot work.

## 8. Direct attack on the ballistic paid phantom

The high-limit object of Section 6 is stronger than a bare semantic
self-loop, but weaker than an executable recurrent source.  This section
states its exact data and tests the three plausible consumers: finite
deadlines, compact time shifts / punishment, and a transverse maximal-root
chronology.

### 8.1 Exact source-attached data

In the strict Zeno subcase, retain the notation of Section 6 and let
\(X_n=\operatorname{Sem}(\sigma_n)\), \(X_\infty=p.semanticPort.limit\).
The same one source and one port give:

\[
 X_n\longrightarrow X_\infty,qquad
 D(X_n)\downarrow L>D_*+g/2;
\tag{24}
\]

\[
 A_n:=\sum_{t\ge n}\operatorname{Abs}(r_t)\longrightarrow0,qquad
 \rho_n:=\operatorname{dist}(X_n^{cap},X_\infty^{cap})\longrightarrow0;
\tag{25}
\]

and actual profiles \(\sigma_n\) with rows of one fixed observer, orientation,
relative delay, and gain \(\bar G>0\).  If the original row witnesses are
\(u,v\in\mathbb N\cup\{\mathrm{Never}\}\), then the witnesses at depth \(n\)
are exactly
\[
  n+u,\qquad n+v,
\tag{26}
\]
with the convention \(n+\mathrm{Never}=\mathrm{Never}\).  Their first
disagreement is \(n+s_0\).

The complete terminal-outcome laws also have compact provenance.  A single
prefix of absorption \(a_n\) changes the finite outcome law in \(\ell^1\) by
at most \(2a_n\).  Therefore the summability in (25) makes these laws Cauchy.
The limit is a joint semantic/law carrier point, and the old suffix law is
retained there with at least the positive survival fraction \(L/D_0\).
This compactness forgets terminal *dates*: the terminal outcome law records
only the quitting coalition or Never.

Thus the packet has a genuine actual finite-depth ancestry, a compact joint
semantic/law limit, a fixed paid amount, and vanishing outer cap motion.  What
it lacks *without recentering* is a fixed finite location of the paid
comparison.  Section 8.5 records the exact recentering available for this
literal prefix family and why it is not a returned capacity child.

### 8.2 Exact local regression first

The regression in
`CODEX_EULER__FIN4_INERT_PAID_ROW_FULL_REACH_NONCONVERSION.md` realizes the
entire local obstruction with rational Fin4 rewards.  Write the players as
\(o,p,a,b\), and set, for every nonempty coalition \(S\),
\[
 r_o(S)=\mathbf 1_{\{o,p\}\subseteq S},
 \qquad
 r_p(S)=-\mathbf 1_{p\in S},\quad
 r_a(S)=-\mathbf 1_{a\in S},\quad
 r_b(S)=-\mathbf 1_{b\in S}.
\tag{27}
\]
In the actual profile \(\sigma\), player \(p\) Quits at date zero, \(o\)
Quits at date one, and \(a,b\) Never quit.  Then
\[
 U(\sigma)=(0,-1,0,0),\qquad B(\sigma)=(1,0,0,0),
 \qquad D(\sigma)=2.
\tag{28}
\]
Observer \(o\)'s comparison `Quit at 0` versus `Quit at 1` is a paid row of
gain one, with full opponent and own survival to its start.  At the cap in
(28), Continue strictly dominates Quit for \(p,a,b\); after they Continue,
Continue strictly dominates Quit for \(o\).  Hence all Continue is the unique
exact cap--Nash root.

After \(n\) all-Continue prefixes, the actual paid witnesses are exactly
\(n\) and \(n+1\), their gain is still one, the semantic pair is still (28),
and the complete exact-root capacity is zero.

This table has an exact terminal equilibrium elsewhere and global debt
minimum zero.  It is not a counterexample to the positive-minimum theorem.
It proves that every *local* field in (24)--(26), even with zero rather than
vanishing cap charge and with full live reach, is compatible with the
ballistic obstruction.  A successful theorem must use the positive global
minimum or hard source provenance to constrain other profiles; it cannot be
a local conversion of paid gain into exact-root charge.

### 8.3 Fixed deadlines erase the marked comparison

Let \(C_T\) censor a complete pure time to the deadline-\(T\) action space:
times below \(T\) are retained and all later times, including Never, map to
Never.  This is the iterated form of
`quittingFiniteDeadlineTimingActionCensor`.

For every fixed \(T\), (26) gives, eventually in \(n\),
\[
  C_T(n+u)=C_T(n+v)=\mathrm{Never}.
\tag{29}
\]
Thus every fixed finite-deadline quotient eventually identifies the two
witnesses whose uncensored payoff difference is at least \(\bar G\).  The
paid mark is invisible in every fixed projective coordinate.

Choosing moving deadlines \(T_n>n+s_0\) merely follows the escaping mark.  It
does not produce the current deadline consumer:

1. the two witnesses are unilateral pure-time comparisons on \(\sigma_n\),
   not mixed Nash laws of the finite timing game;
2. independently choosing a finite Nash law at each \(T_n\) gives no censor
   equation; and
3. a boundary law \(\delta_{T_n-1}\) censors to Never at the preceding
   deadline rather than to the earlier boundary law.

The checked structure `QuittingFiniteDeadlineCompatibleNashFamily` requires
an exact Nash law at *every* deadline and literal `censor_succ` compatibility.
Only that strong input makes adjacent TV tend to zero and activates
`QuittingFiniteDeadlineCompatibleNashFamily.exists_uniformEquilibriumPayoff`.
The repository correctly exposes finite-chain realizability as the separate
hypothesis `HasFiniteCompatibleQuittingTimingNashChains`; ordinary finite-game
Nash existence supplies only `HasDeadlinewiseQuittingTimingNash`.

Therefore the ballistic row is not a producer for the deadline compiler.

### 8.4 Shift compactness collapses the two witnesses

For deterministic stopping laws, the failure is quantitative.  If
\(k_n\to\infty\) and \(\lambda\) is any fixed probability law on
\(\mathbb N\cup\{\mathrm{Never}\}\), then
\[
  d_{TV}(\delta_{k_n},\lambda)
    =1-\lambda(\{k_n\})\longrightarrow1.
\tag{30}
\]
Indeed the atoms \(\lambda(\{k_n\})\) tend to zero.  In particular, the
moving witnesses have no total-variation convergent subsequence.  Also
\[
 d_{TV}(\delta_{n+u},\delta_{n+v})=1
\tag{31}
\]
whenever both offsets are distinct finite times; the same equality holds
between a finite time and Never.

In the one-point compact / finite-cylinder topology, both shifted witnesses
instead converge to Never.  That compactness is too weak: it identifies the
two sides of the paid comparison and does not make terminal payoff continuous.
In the regression (27), the delayed profiles converge pointwise to all Never,
while every finite profile retains the unit comparison.  The favorable
collision has escaped to infinity.

The exact repair would be a finite-tail tightness passport for the marked
stopping laws, or an error-controlled decoder which charges the escaped mass.
Neither is a field of `ShiftedPaidRow`, `SummablePort`, or the off-minimum
endpoint.  The particular literal prefix family does admit the exact clock
clearing below, but that operation discards rather than composes its incoming
history.

### 8.5 Exact clock clearing returns to the old suffix, not to a new source

There is one important positive fact.  Let \(s_0\) be the first-disagreement
date of the original row and define the reached suffix
\[
  \tau:=\operatorname{quittingAllContinueProfileSpine}
        (s.profile,s_0).
\tag{32}
\]
Because \(\sigma_n\) is a literal root stack of length \(n\) over
`s.profile`,
`quittingAllContinueProfileSpine_literalRootStackProfile_length` and the
additivity of the all-Continue spine give the exact identity
\[
  \operatorname{Spine}(\sigma_n,n+s_0)=\tau
  \qquad\text{for every }n.
\tag{33}
\]
Deleting the common clock from the shifted paid row therefore gives one
actual time-zero row on the *fixed* profile \(\tau\), with the same observer,
orientation and relative delay and with a positive gain at least \(\bar G\).
No compactness or subsequence is needed.

This does not consume the phantom.  The direction of (33) is conditioning on
the all-Continue live history and deleting the entire outer exact block.  The
profile \(\tau\)

- is the already-known postmark suffix, not an exact prefix child above
  \(\sigma_n\);
- need not have semantic pair \(X_\infty\) or debt near \(L\);
- does not inherit the spent capacity as an extension-compatible debit; and
- carries only a time-zero paid deviation comparison, not a Nash root.

Feeding \(\tau\) into a paid-cap port merely restarts the same
charged/descent/inert trichotomy.  In the regression (27), clock clearing
recovers the original time-zero unit row, but its displayed cap still has
unique all Continue and zero charge.  Thus exact clock deletion solves the
location problem while leaving the participant-Nash and renewable-history
problems untouched.

This is also exactly short of the checked payoff-near-return endpoint.
`QuittingPositiveAdmissiblePayoffClosure` requires a positive
punishment-floor-admissible edge and admissible paths whose endpoint payoffs
return arbitrarily close to that edge's tail payoff.
`PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer` assumes that such a
family can be produced from every separated eventual paid-row telescope.  The
source file explicitly records that it does **not** construct this output from
a paid row.  Equation (33) supplies neither its admissible charged edge nor its
return path.  Thus the fixed suffix \(\tau\) cannot be passed to that consumer
without adding precisely the seam still absent here.

### 8.6 A paid event is not a punishment-safe Nash row

The same regression rules out a vanishing-error punishment conversion.  If a
candidate current root assigns probability \(q>0\) to player \(p\)'s Quit
event which creates observer \(o\)'s collision premium, then \(p\)'s payoff
from its mixed action is \(-q\), while pure Continue gives zero.  Hence the
root Nash defect is at least \(q\).  Observer \(o\)'s collision benefit is at
most \(q\).  Therefore
\[
  \text{retained paid benefit}\ge\gamma
  \quad\Longrightarrow\quad
  \text{root Nash defect}\ge\gamma.
\tag{34}
\]
There is no sequence of approximate roots with Nash error tending to zero
which realizes a fixed fraction of this paid event.

This pinpoints the missing condition.  `QuittingPaidFirstDisagreementRow`
controls one observer's two unilateral timing values after survival to a
date.  It does not assert that the opponents' prescribed actions *at that
date* satisfy their own Nash or punishment inequalities.  Exact cap Nash can
erase the paid event while preserving its value as a counterfactual
deviation comparison.

Finite hazard capacity does not contradict this: capacity charges the exact
roots, while the drifting row is only a marked deviation pair.  The zero-charge
all-Continue self-loop in (27) can carry the mark outward forever.

### 8.7 The one valid transverse contraction

There is a genuine noncanonical operation available from the same initial
actual paid source: iterate the maximal-absorption exact cap root, producing
`quittingMaximalCapPrefixProfile reward s.profile n`.  This is one literal
composable chronology, not a family of unrelated one-step roots.  Positive
global minimum makes its absorption and marginal hazard summable, and the
same pure-time splice identity transports the original paid comparison with
a positive survival floor.

Put \(\delta=g/2\).  Exactly one of the following happens.

1. Some finite maximal-prefix profile has debt at most \(D_*+\delta\).
   Since the starting source has debt above \(D_*+3g/4\), the finite exact
   block spends at least \(g/(4D_{\max})\) weighted absorption.  It is a
   literal same-history capacity debit.

2. Every maximal-prefix profile stays above \(D_*+\delta\).  Summability
   forces the maximal root absorptions to zero.  Compactness and closedness
   of endpoint Nash then produce an off-minimum omega-source at which all
   Continue is exact.  If a positive finite suffix atom is separately
   supplied, the checked theorem
   `exists_offMinimum_retainedLaw_allContinue_or_supportEntry` retains a
   positive fraction of that atom and sharpens the endpoint to
   unique-all-Continue or a positive-absorption support-entry root.

The paid row alone does not supply the theorem's positive finite suffix atom:
it is a deviation comparison, not prescribed terminal-law mass.  Even when
the atom is present, the omega-source is a joint carrier point, not a
behavioral limit carrying the ballistic paid clocks.  A positive transverse
root at that point gives a one-step semantic/law prefix, but no checked map
embeds a freshly causalized realization back into the incoming history.

This contraction is therefore valid and useful, but its second arm is an
off-minimum inert/support-entry omega-source rather than a terminal consumer.

### 8.8 Audit of Followup 1, equations (42)--(47)

The numerical argument in `gpt/NONZERO_PERSIST_ATTEMPT_1.md` is correct under
its stated extra premise of **one composable source-provenant chronology**.

- A high-to-near-minimum return spends a fixed toll, so a finite-capacity
  chronology contains only finitely many such returned rows; equation (42)
  is correct.
- On one remaining infinite undercharge chronology, summability gives
  absorption tending to zero.  The singleton-gap bound (44), compactness,
  and closed endpoint Nash give (45); closedness of the debt floor gives
  (46).  Thus the off-minimum all-Continue omega-source conclusion is valid.

What is not currently produced is the common chronology to which all of
those selected maximal-return rows belong.

`FinFourUniformEscapePacket` supplies actual tails of one source origin and
literal `drop` reindexing.  At each rank,
`exists_maximalCapNash_halfFloorDispatch` selects a maximal root and
`returnedProfile` realizes its one-step prefix.  But `drop` is not that prefix:
there is no field identifying the returned profile at rank \(n\) with the
tail/source at rank \(n+1\).  Hence the selected hazards are separate
one-step branches, not charges on one path, and equation (42) cannot be
applied to them as a sum.  The file
`SourcePreservingCompletionConsumers.lean` states this limitation explicitly.

Conversely, the paid cap port of this note supplies one composable canonical
orbit, but its separately selected maximal root at \(\sigma_n\) need not be
the canonical root whose prefix equals \(\sigma_{n+1}\).  Replacing it by the
maximal root breaks that displayed edge.  Along the canonical orbit itself,
equations (43)--(46) do apply and yield exactly the all-Continue semantic port
already recorded in Section 6; they do not produce a return or a terminal
profile.

The maximal-prefix construction of Section 8.7 repairs composability by
building a new single orbit from the initial source.  It proves one fixed-toll
crossing or the off-minimum omega-source alternative.  It still does not
reproject a low returned profile as a renewable high source, and it does not
actualize the ballistic row at the omega-limit.  Therefore boxed conclusion
(47) is a correct **conditional reduction**, not a current unconditional
consumer of the actual off-minimum paid exit.

### 8.9 Direct verdict

All three direct consumers fail on the currently exposed packet.

- **Deadline:** fixed deadlines erase the comparison; moving deadlines lack
  Nash and projective compatibility.
- **Shift / punishment:** weak limits collapse both clocks to Never, TV
  compactness fails, and Nashifying the paid event can cost its full gain.
- **Finite capacity / transverse root:** the maximal orbit gives a valid
  fixed-toll-or-omega-source contraction, but the omega-source has no
  source-faithful paid-clock actualizer and the return has no renewable
  reprojection.

The ballistic paid phantom is therefore a real residual, not a hidden
terminal compiler.  The smallest adequate new input is one of:

1. finite-tail tightness for the marked source and deviation laws;
2. a punishment-safe paid-event certificate controlling every participant's
   root regret; or
3. an exact history map identifying a maximal returned profile with the next
   source of one composable capacity chronology.

## 9. The off-minimum omega-source split

Section 8.7 left a second outcome besides the ballistic marked profile: a
joint semantic/law omega-source at which all Continue is exact and either it
is the unique exact cap--Nash root or some exact cap--Nash root has positive
absorption.  The latter alternative has a complete one-step consumer, but its
name must not be confused with the tangent support-entry exit of Section 1.

### 9.1 The positive-root alternative is not a tangent support entry

The last disjunct of
`exists_offMinimum_retainedLaw_allContinue_or_supportEntry` says only

\[
  \exists x,\qquad x\text{ is exact Nash against }X^{cap},
  \qquad a:=\operatorname{Abs}(x)>0.
\tag{35}
\]

It supplies no active support, normalized reset tangent, zero-debt recipient,
or positive tangent column.  In particular it does not instantiate
`HasQuittingStoppingLawFlatSupportEntry`, whose conclusion is about entry of
a *tangent coordinate* into a zero-debt coordinate at a minimum-fibre base.
The two uses of “support entry” are mathematically different.

### 9.2 Exact positive-root return theorem

Let \((X,\mu)\) be the joint omega-source, let \(D_*>0\) be the global
minimum, and assume
\[
  D(X)>D_* ,\qquad \mu(\{S\})>0
\tag{36}
\]
for the retained finite atom.  If (35) holds, define the exact affine-prefixed
joint point
\[
  (Y,\nu):=
  \bigl(T_xX,\operatorname{LawPrefix}_x\mu\bigr).
\tag{37}
\]

Then:

1. \((Y,\nu)\) remains in the joint semantic/law carrier.
2. The exact cap--Nash account is
   \[
     D(Y)=(1-a)D(X)=D(X)-aD(X),
     \qquad D_*\le D(Y)<D(X).
   \tag{38}
   \]
   Thus the positive-root arm is a genuine second exact root and a strict
   one-step semantic-debt descent inside the closed joint carrier.  Its
   one-step weighted charge is
   \(aD(X)\ge aD_*>0\).
3. Its Continue mass is positive.  Otherwise (38) would give \(D(Y)=0\),
   contradicting \(D_*>0\).  Consequently the old atom survives:
   \[
      \nu(\{S\})
      \ge (1-a)\mu(\{S\})>0.
   \tag{39}
   \]

The carrier statement is
`quittingTerminalSemanticLawPrefix_mem_carrier`; the debt identity is
`capNashPrefix_tailEscape_exact_account` (equivalently sum the coordinate
identity
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`).
The atom inequality is the nonnegative old-law term in the affine law-prefix
formula.

At this stage \((Y,\nu)\) is a point of the closed joint carrier, not
necessarily the semantic/law point of one supplied behavioral profile.  Thus
(37) is source-coupled at the carrier level but is not by itself an
extension-compatible history child.  The minimum-equality causalization
described next is a genuinely stronger conclusion available from the
hard-residual packet.

This proves the exact dichotomy

\[
  D(Y)=D_*
  \quad\text{or}\quad
  D_*<D(Y)<D(X).
\tag{40}
\]

In the hard-residual Fin4 strict-ray packet, this entire construction is
already checked more strongly.  `FinFourStrictRayPositiveRootReturn` attaches
the root to a joint-law cluster selected from the same actual ray;
`returnedDebt_eq_limit_sub_charge` proves (38), and
`nonempty_minimumLawHandoff_or_offMinimumDescent` implements (40).  In the
equality arm it causalizes the returned minimum law and creates a fresh
`FinFourMinimumAtomProducer` with the same residual.  That object can re-enter
the minimum-source atlas and hence is the correct gateway toward the checked
minimum-fibre support rank.

The strict arm of (40) is only `FinFourStrictRayOffMinimumDescent`.  It has no
renewable rank or consumer.  The number \(a\) belongs to the selected root and
has no source-uniform lower bound, so repeated returns can again make a Zeno
sequence above \(D_*\).  Therefore the positive-root alternative is completely
consumed only when its returned debt equals the minimum; otherwise it replaces
the inert omega-source by a strictly lower off-minimum source.

### 9.3 Conditional fixed-law reset adapter

There is a narrower adapter which should be kept separate.  Suppose the joint
omega-source itself has a reset coordinate \(o\),
\[
  d_o(X)=0,
\tag{41}
\]
and its retained law has positive opponent incidence for some \(j\ne o\).
For example, a positive atom containing \(j\) supplies this incidence.  Under
a terminal exploitability witness,
`QuittingTerminalExploitabilityWitness.exists_fixedLaw_resetFace_dispatch`
may then be applied with the global minimum as source and \((X,\mu)\) as
target.  It returns a same-law reset-face minimizer and either

- a positive-survival absorbing exact prefix with strict debt descent and
  retained incidence; or
- an all-Continue fixed reset face.

Neither (41) nor the required incidence follows from exact all-Continue
uniqueness.  Exact cap prefixing also preserves the zero pattern of debt when
Continue mass is positive, so the positive-root return of Section 9.2 does
not manufacture a missing reset coordinate.

The pair-base theorem does not remove these hypotheses for the omega-source.
`exists_finFour_pairBasePaidResetDispatch` constructs a *different*
stationary target with its own law, reset owner, and unit incidence.  Its
returned reset face is not identified with \(X\), and no cap or law equality
transports uniqueness at \(X\) to that returned point.  Even the exact payoff
alignment in `PairBasePaidResetPayoffAlignment.lean` reaches a uniform payoff
only after supplying `QuittingFixedLawResetAdmissibleClosureSeam`, which is
precisely an additional charged edge and return path.

### 9.4 Uniqueness does not instantiate the normalized passport

In the other branch every exact cap--Nash root at \(X^{cap}\) is all Continue.
Together with the already known all-Continue exactness this gives the same
root-uniqueness formula appearing as the last field of
`FinFourNormalizedStrictInertSingleDensityToll`.  It does not construct that
object.  The latter also stores

- one particular forced-pair decorated family and its selected compact
  passport;
- a minimizer in the enlarged normalized passport slice;
- positive marked-mass and gain densities and their exact single-density
  identity; and
- the comparison of that minimizer with the original minimum source.

The omega-source supplies none of the decorated gain data: its retained law
atom is a prescribed-law fact, while the ballistic paid comparison is not
actualized at \(X\).  Moreover the normalized strict-inert file explicitly
retains no terminal consumer even when the full passport is present.  Thus
root uniqueness alone cannot enter, much less consume, that route.

The checked rational table
`FinFourEventualAllContinueLocalRegression` is an exact local regression.
Its `pairProfile` is actual, `exactRoot_eq_allContinue` proves cap-root
uniqueness, and `maximalPrefixOrbit_pairSemantic_eq` makes the maximal orbit
literally constant; the table also has a paid endpoint and the advertised
hard local matrix fields.  Nevertheless `neverPair_globalMinimum` and
`neverUniformEquilibriumPayoff` show that its global minimum is zero and it
already has a uniform equilibrium.  Hence the local uniqueness, paid, and
pair-base-looking fields do not themselves give a contradiction or the
missing consumer.  Positive global minimum is indispensable, but its only
unconditional effect here is the finite-capacity account of Section 9.2.

### 9.5 Omega-source verdict

- **Positive exact root:** a checked one-step joint-law return and strict debt
  descent.  Equality with \(D_*\) regenerates a minimum source in the actual
  hard-residual strict-ray packet; strict off-minimum return remains open.
- **Unique all Continue:** neither the normalized strict-inert passport nor
  the pair-base fixed-law reset is produced from this source.  This is still
  an unconsumed inert omega-source.
- **Tangent support rank:** the positive-root disjunct is not its support-entry
  hypothesis.  The route to that rank begins only after the returned joint
  law lands exactly on the minimum fibre and is causalized as a fresh minimum
  atom producer.

## Source declarations inspected

- `FinFourRenewableTerminalExit`, `terminalExit_or_nonempty_supportDescent`,
  `descentCount_lt_support_card` in
  `Research/Quitting/FinFourProducerAtlas/CanonicalPairRenewableSourceRank.lean`.
- `HasQuittingStoppingLawFlatSupportEntry` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/ExhaustiveTangentAlternative.lean`.
- `FullReplacementCluster`, `FullReplacementCluster.fullReplacement_tendsto`
  in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/MinimumFiberSupportDrop.lean`.
- `HasOffMinimumPaidFirstDisagreement` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FlatCirculationSupportRankElimination.lean`.
- `paidFirstDisagreement_capPortTrichotomy`, `PaidCapPortDispatch`,
  `separated_and_paidCapPortDispatch_of_offMinimumPaidFirstDisagreement` in
  `Research/Quitting/PaidRowCapPortDispatch.lean`.
- `QuittingPaidCapLiftedSource.initialDebt`,
  `quittingCapLiftedPrefixProfile`,
  `QuittingPaidCapLiftedSource.absorption_summable`,
  `quittingCapLiftedPrefixProfile_debt_eq_suffixReach_mul`,
  `quittingCapLiftedPrefixProfile_debt_succ`,
  `SummableSemanticPort.semantic_tendsto`, `reachFloor_pos`,
  `ShiftedPaidRow.receivingEarlier_eq`, `ShiftedPaidRow.start_eq`, and
  `ShiftedPaidRow.later_eq` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`.
- `QuantitativeDebtDescent`, `ChargedNearReturn`,
  `QuittingPaidCapLiftedSource.totalAbsorption`,
  `QuittingPaidCapLiftedSource.capDisplacement`,
  `chargedNearReturn_of_totalAbsorption_pos_of_capDisplacement_zero`,
  `quantitativeDebtDescent_of_capDisplacement_pos`,
  `inertStall_of_totalAbsorption_eq_zero`, and
  `chargedNearReturn_or_quantitativeDebtDescent_or_inertStall` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`.
- `QuittingPaidCapLiftedSource.finitePrefixSource`,
  `finitePrefixSource_profile`, `finitePrefixSource_minimum` in
  `Research/Quitting/FinFourPaidResetDescentRegeneration.lean`.
- `HasUniqueAllContinueAtCap`,
  `maximalOneStepPaidResetRegeneration_or_uniqueAllContinue` in
  `Research/Quitting/PaidCapMaximalOneStepRegeneration.lean`.
- `exactCapPrefix_joint_eq_self_of_unique_allContinue`,
  `QuittingPunishmentFloorFinitePrefix.constant_of_unique_allContinue_anchor`,
  `capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap`, and
  `capNashStackAbsorptionSum_eq_zero_of_unique_terminalCap` in
  `Research/Quitting/UniqueAllContinueCapStackNoGo.lean`.
- The current status summary for the canonical lane in `docs/TOOLKIT.md`.
- `QuittingFiniteDeadlineCompatibleNashFamily`,
  `QuittingFiniteDeadlineCompatibleNashFamily.exists_uniformEquilibriumPayoff`
  in
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineProjectiveCompatibility.lean`;
  `HasFiniteCompatibleQuittingTimingNashChains` and
  `HasDeadlinewiseQuittingTimingNash` in
  `Research/Quitting/FiniteDeadlineCompatibleNashChains.lean`.
- `QuittingPositiveAdmissiblePayoffClosure`,
  `PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer`, and
  `paidFirstDisagreementUniformPayoffConsumer_of_admissiblePayoffNearReturn`
  in
  `UniformEquilibrium/Diagnostics/Quitting/PaidFirstDisagreementPayoffNearReturn.lean`.
- `quittingAllContinueProfileSpine_literalRootStackProfile_length` in
  `UniformEquilibrium/Quitting/Root/SelfTailClosure.lean` and
  `quittingAllContinueProfileSpine_add` in
  `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`.
- `exists_maximalCapNash_returnSelection_or_sameTailUndercharge`,
  `summable_maximalCapPrefix_absorption`, and
  `exists_offMinimum_retainedLaw_allContinue_or_supportEntry` in
  `Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean`.
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
  `capNashPrefix_tailEscape_exact_account` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticStrictTailEscapeReturn.lean`;
  `quittingTerminalSemanticLawPrefix_mem_carrier` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`.
- `FinFourStrictRayPositiveRootReturn`,
  `FinFourStrictRayPositiveRootReturn.returnedDebt_eq_limit_sub_charge`,
  `FinFourStrictRayPositiveRootReturn.nonempty_minimumLawHandoff_or_offMinimumDescent`,
  `FinFourStrictRayMinimumLawHandoff`, and
  `FinFourStrictRayOffMinimumDescent` in
  `Research/Quitting/FinFourProducerAtlas/StrictRayPositiveRootReturn.lean`.
- `QuittingTerminalExploitabilityWitness.exists_fixedLaw_resetFace_dispatch`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`;
  `QuittingTerminalExploitabilityWitness.exists_finFour_pairBasePaidResetDispatch`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetAlignment.lean`;
  `QuittingFixedLawResetAdmissibleClosureSeam` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetPayoffAlignment.lean`.
- `FinFourNormalizedStrictInertSingleDensityToll` and
  `FinFourNormalizedStrictInertSingleDensityToll.slack_eq_zero_or_positive_with_local_toll`
  in
  `Research/Quitting/FinFourProducerAtlas/NormalizedInertSingleDensityToll.lean`.
- `FinFourEventualAllContinueLocalRegression.exactRoot_eq_allContinue`,
  `FinFourEventualAllContinueLocalRegression.maximalPrefixOrbit_pairSemantic_eq`,
  `FinFourEventualAllContinueLocalRegression.neverPair_globalMinimum`, and
  `FinFourEventualAllContinueLocalRegression.neverUniformEquilibriumPayoff`
  in `Research/Quitting/FinFourEventualAllContinueLocalRegression.lean`.
- `FinFourUniformEscapePacket`, `FinFourUniformEscapePacket.drop` in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionAtlas.lean`;
  `exists_maximalCapNash_halfFloorDispatch`, `returnedProfile`, and
  `semanticPair_returnedProfile_eq_prefix` in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionConsumers.lean`.
- The exact local regression in
  `notes/CODEX_EULER__FIN4_INERT_PAID_ROW_FULL_REACH_NONCONVERSION.md`.
