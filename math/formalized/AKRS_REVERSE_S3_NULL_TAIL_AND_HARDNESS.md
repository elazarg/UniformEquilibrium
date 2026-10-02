# Reverse S.3: null-tail elimination and one-added-player hardness reduction

Authors: `External mathematical response` (original ordinary-mathematics argument),
`CODEX_NEGATIVE_CERTIFICATE` (corrected packet assembly)

Independent reviews:
[CODEX_SNELL](../feedback/AKRS_REVERSE__BY_CODEX_SNELL.md),
[CODEX_SPINOZA](../feedback/CODEX_NEGATIVE_CERTIFICATE__AKRS_REVERSE_S3_NULL_TAIL_AND_HARDNESS__BY_CODEX_SPINOZA.md)

## Exact statement

Let (I) be a nonempty finite player set.  At every live stage, each player
independently chooses Continue or Quit.  A nonempty quitting coalition
(S\subseteq I) ends the game with payoff (r(S)\in\mathbb R^I); if nobody
ever quits, the payoff is (z\in\mathbb R^I).  Behavioral strategies are
arbitrary sequences of live-date Quit probabilities, and unilateral
deviations may replace one player's entire sequence.

For a row (q\in[0,1]^I), let

\[
 c(q)=\prod_{i\in I}(1-q^i).
\]

For a root sequence (x=(q_n)_{n\ge0}), let (a_{m,\infty}(x)) be the
limiting survival probability of the sequence restarted at date (m), and
let (\gamma_m(x)) be its terminal payoff, including
(a_{m,\infty}(x)z).  Let (Q_n^i,C_n^i,V_n^i) be player (i)'s Quit,
Continue, and prescribed mixed values at row (n), computed against the
actual continuation (\gamma_{n+1}(x)).  A row is
(\varepsilon)-perfect when

\[
 Q_n^i\le V_n^i+\varepsilon,\qquad
 C_n^i\le V_n^i+\varepsilon,
\]

and each pure action used with positive probability has value at least
(V_n^i-\varepsilon).

Say that (G=(I,r,z)) satisfies S.3 if there is
(\varepsilon_0>0) such that, for every
(0<\varepsilon<\varepsilon_0), there is a root sequence (x^\varepsilon)
with (a_{0,\infty}(x^\varepsilon)=0) and every row
(\varepsilon)-perfect against its own restarted-tail value.

For a behavioral profile (\sigma), define its unrestricted terminal
exploitability by

\[
 E_G(\sigma)=
 \max_{i\in I}\sup_{\tau_i}
 \left(U_i^G(\tau_i,\sigma^{-i})-U_i^G(\sigma)\right),
\]

where (\tau_i) ranges over all behavioral strategies of player (i).

Then the following statements hold.

1. **Null-tail lemma.**  If one initially absorbing
   (\varepsilon)-perfect root sequence (x) has
   (a_{m,\infty}(x)>0) for some (m), then

   \[
   r^i(\{i\})\le z^i+\varepsilon
   \quad\text{for every }i\in I.
   \]

2. **Inclusive null-tail alternative.**  If (G) satisfies S.3, then at
   least one of the following holds, and both may hold:

   - all Continue is an exact terminal Nash equilibrium; or
   - there is (\delta>0) such that every initially absorbing
     (\varepsilon)-perfect witness with (0<\varepsilon<\delta) terminates
     from every restarted tail.

3. **Exact one-player padding.**  For every (P>0), there is a quitting game
   (\widehat G) on (I\sqcup\{d\}) which has one stationary, exactly
   row-perfect, every-tail-terminating root sequence.  For every behavioral
   profile (\widehat\sigma) of (\widehat G), its old-player projection
   (\sigma) satisfies

   \[
   E_G(\sigma)\le
   \left(1+\frac WP\right)E_{\widehat G}(\widehat\sigma),
   \qquad
   E_{\widehat G}(\widehat\sigma)\ge
   \frac{P}{P+W}E_G(\sigma),
   \]

   where

   \[
   H_i=\max\bigl(\{z^i\}\cup\{r^i(S):S\ne\varnothing\}\bigr),
   \quad
   L_i=\min\bigl(\{z^i\}\cup\{r^i(S):S\ne\varnothing\}\bigr),
   \]

   (W_i=H_i-L_i), and (W=\max_i W_i).

4. **Cardinal shift.**  For every (n\ge1), if reverse S.3 holds for every
   ((n+1))-player quitting game, then terminal approximate equilibria exist
   for every (n)-player quitting game.  The zero-player case is trivial.
   Consequently

   \[
   \bigl[\text{reverse S.3 holds for every finite quitting game}\bigr]
   \quad\Longleftrightarrow\quad
   \bigl[\text{every finite quitting game has terminal approximate
   equilibria}\bigr].
   \]

   This equivalence is universal over all finite cardinalities; it is not a
   same-cardinality equivalence.

5. **Negative transport.**  If
   (E_G(\sigma)\ge\Gamma>0) for every behavioral profile (\sigma), then
   (\widehat G) satisfies exact stationary every-tail S.3 and

   \[
   E_{\widehat G}(\widehat\sigma)
   \ge \frac{P}{P+W}\Gamma
   \]

   for every behavioral profile (\widehat\sigma).

## Conjecture-facing change

This result makes two strict changes to the open reverse implication from the
S.3 branch of journal Theorem 3.4 to terminal approximate-equilibrium
existence.

First, failure of termination on restarted null tails is not an independent
obstruction: if it persists at errors tending to zero, all Continue is already
an exact equilibrium.  Thus one may restrict the genuinely unresolved branch
to every-tail witnesses.

Second, this restriction does not make the universal problem easier.  Every
finite quitting game embeds, after adding one player, into a game with a
stationary exact every-tail S.3 witness, while unrestricted terminal
exploitability retracts with the explicit factor (P/(P+W)).  Hence even the
statement

> every finite quitting game admitting one stationary exact every-tail S.3
> witness has terminal approximate equilibria

is universally equivalent to the general finite-quitting approximate-
equilibrium problem.

This does not prove reverse S.3 and does not construct a counterexample.  It
identifies the exact hardness of the remaining obligation.

## Definitions and assumptions

For (m\le N), set

\[
 a_{m,N}(x)=\prod_{t=m}^{N-1}c(q_t),
 \qquad
 a_{m,\infty}(x)=\lim_{N\to\infty}a_{m,N}(x).
\]

The limit exists because the finite products decrease in ([0,1]).  The
restarted payoff is

\[
 \gamma_m^i(x)=
 \sum_{n=m}^{\infty}a_{m,n}(x)
 \sum_{\varnothing\ne S\subseteq I}p_{q_n}(S)r^i(S)
 +a_{m,\infty}(x)z^i.
\]

Its finite-terminal coefficient is (1-a_{m,\infty}(x)).  The row
probability is the independent product law

\[
 p_q(S)=\prod_{i\in S}q^i\prod_{j\notin S}(1-q^j).
\]

For (T\subseteq I\setminus\{i\}), write (p_q^{-i}(T)) for the analogous
opponent product.  Then

\[
 Q_n^i=\sum_{T\subseteq I\setminus\{i\}}
 p_{q_n}^{-i}(T)r^i(T\cup\{i\}),
\]

\[
 C_n^i=\sum_{\varnothing\ne T\subseteq I\setminus\{i\}}
 p_{q_n}^{-i}(T)r^i(T)
 +p_{q_n}^{-i}(\varnothing)\gamma_{n+1}^i,
\]

and (V_n^i=q_n^iQ_n^i+(1-q_n^i)C_n^i=\gamma_n^i).

Perfect monitoring causes no hidden strategy-class restriction here.  While
the game is live, every earlier action must have been Continue, so there is
one live public history at each date.  A behavioral strategy is therefore an
arbitrary sequence of live-date mixed actions.  All deviation statements
below quantify over arbitrary replacements of one such sequence, including
Never and unbounded or randomized stopping laws.

The padding game is defined as follows.  Add one label (d).  Its Never
payoff is (\widehat z^d=0), and old Never payoffs remain
(\widehat z^i=z^i).  For a nonempty terminal coalition
(T\subseteq I\sqcup\{d\}), put (S=T\cap I).  If (S\ne\varnothing), set

\[
 \widehat r^i(T)=r^i(S)\quad(i\in I),
 \qquad \widehat r^d(T)=0.
\]

For the only fresh-only coalition, set

\[
 \widehat r^i(\{d\})=H_i\quad(i\in I),
 \qquad \widehat r^d(\{d\})=-P.
\]

## Source correspondence

The self-contained source question is
[`AKRS_THEOREM_3_4_REVERSE_S3_NULL_TAIL_GAP.md`](../questions/AKRS_THEOREM_3_4_REVERSE_S3_NULL_TAIL_GAP.md).
The paper-facing tracked statement is
[`AshkenaziGolanKrasikovRainerAndSolan2024.lean`](../../Literature/AshkenaziGolanKrasikovRainerAndSolan2024.lean).
Its `HasSmallAbsorbingSequentiallyPerfectProfiles` uses initial absorption,
not every-tail termination, and
`publishedApproximateEquilibriumExistence_iff_threeBranchAlternative` retains
the reverse direction with `sorry`.  The tracked source says the publisher's
24 May 2025 update changed only an affiliation; no separate mathematical
erratum is asserted here.

The project's zero-Never S.3 type is
`QuittingSequentiallyεPerfectAbsorbingExistence` in
[`ExistenceBranches.lean`](../../UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean).
It asks for witnesses at every positive error, whereas the journal/question
form asks only at sufficiently small errors.  The exact monotonic adapter is
already checked as
`hasSmallAbsorbingSequentiallyPerfectProfiles_iff_table` in the Literature
file: for a requested (\varepsilon>0), use a source error below both
(\varepsilon) and half the fixed threshold, then apply
`QuittingRowεPerfect.mono`.

The passive reward is `quittingPassivePaddingReward` in
[`PassivePlayerPadding.lean`](../../UniformEquilibrium/Quitting/Terminal/PassivePlayerPadding.lean).
The Lean model has zero Never payoff and adds a finite fresh block (J).  To
match the arbitrary-(z) construction exactly, first replace each terminal
coordinate by

\[
 r_0^i(S)=r^i(S)-z^i.
\]

The canonical upper and lower endpoints then equal (H_i-z^i) and
(L_i-z^i), and the canonical width remains (W_i).  Specialize the fresh
type to `PUnit`, so `Fintype.card J=1`.  Adding (z^i) back to every old
outcome recovers the displayed arbitrary-Never game and preserves all
unilateral gains.  Thus the checked general factor

\[
 \frac{P}{P+|J|W}
\]

in `HasTerminalExploitabilityGap.passivePlayerPadding_canonical` from
[`PassivePlayerPaddingCanonical.lean`](../../UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingCanonical.lean)
becomes exactly (P/(P+W)).

The pointwise unrestricted retraction is checked as
`retractionFactor_mul_quittingTerminalExploitability_project_le` in
[`PassivePlayerPaddingExploitabilityRetraction.lean`](../../UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingExploitabilityRetraction.lean).
The underlying arbitrary-deviation Nash statements
`isεAsymptoticNash_project_passivePadding_mul` and
`isεAsymptoticNash_project_passivePadding` are in
[`PassivePlayerPaddingRetraction.lean`](../../UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingRetraction.lean).
The exact dummy-sure-Quit S.3 source constructed below is new ordinary
mathematics; no existing Lean declaration is claimed to package that source.

The all-normal conditional consumer is checked by
`exists_terminalNash_of_all_normal_of_sequentiallyPerfectAbsorbing` and
`exists_uniformEquilibriumPayoff_of_all_normal_of_sequentiallyPerfectAbsorbing`
in
[`NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`](../../UniformEquilibrium/Quitting/Classification/Existence/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean).
The abnormal-player sign and floor facts are
`quittingSoloSelfPayoff_neg_of_abnormal`,
`quittingPunishmentValue_nonpos_of_abnormal`, and
`abnormal_singletonFloor_chain` in
[`AbnormalSingletonConsequences.lean`](../../UniformEquilibrium/Quitting/Classification/AbnormalSingletonConsequences.lean).

## Proof

### 1. Null-tail lemma

Fix an initially absorbing (\varepsilon)-perfect root sequence (x) and
suppose (a_{m,\infty}(x)>0) for some (m).  Since

\[
 a_{0,\infty}=a_{0,m}a_{m,\infty}=0,
\]

the finite product (a_{0,m}) is zero, so some (c(q_t)=0) before (m).
Positive survival from (m) implies (c(q_t)>0) for all (t\ge m).
There is therefore a last index

\[
 L=\max\{t:c(q_t)=0\}.
\]

Put (P_*=a_{L+1,\infty}(x)).  It is positive: the finite factors between
(L+1) and (m-1) are positive and (a_{m,\infty}>0).  For (n>L), tail
factorization gives

\[
 a_{n,\infty}(x)=
 \frac{P_*}{\prod_{t=L+1}^{n-1}c(q_t)}\longrightarrow1,
\]

because the denominator decreases to (P_*).  Since
(a_{n,\infty}\le c(q_n)\le1), it follows that (c(q_n)\to1).  For each
player (j),

\[
 q_n^j\le1-c(q_n),
\]

so every (q_n^j\to0).

Let

\[
 M_i=\max_{\varnothing\ne S\subseteq I}|r^i(S)-z^i|.
\]

The total finite-terminal mass of the tail restarted at (n) is
(1-a_{n,\infty}), hence

\[
 |\gamma_n^i-z^i|\le M_i(1-a_{n,\infty})\longrightarrow0.
\]

The Quit endpoint (Q_n^i) is a finite polynomial in the opponents' row
probabilities.  Those probabilities converge to all Continue, so

\[
 Q_n^i\longrightarrow r^i(\{i\}).
\]

Row perfection and (V_n^i=\gamma_n^i) give

\[
 Q_n^i\le\gamma_n^i+\varepsilon.
\]

Taking the limit proves
(r^i(\{i\})\le z^i+\varepsilon) for every (i).

### 2. Inclusive null-tail alternative

Assume S.3.  If non-every-tail witnesses occur at a sequence of positive
errors (\varepsilon_k\to0), the lemma gives

\[
 r^i(\{i\})\le z^i+\varepsilon_k
\]

for every (k), hence (r^i(\{i\})\le z^i).  Against opponents who always
Continue, any behavioral strategy of player (i) either eventually quits
alone or Never quits.  Its payoff is therefore a convex combination of
(r^i(\{i\})) and (z^i), and cannot exceed (z^i).  All Continue is an
exact terminal Nash equilibrium.

Otherwise such witnesses do not occur arbitrarily close to zero.  Hence some
(\delta>0) excludes every non-every-tail witness at
(0<\varepsilon<\delta).  S.3 still supplies an initially absorbing witness
at every sufficiently small such error, and every supplied witness must
terminate from every restarted tail.  This proves the stated inclusive
alternative.  The alternatives need not be disjoint.

### 3. Exact stationary S.3 source in the padded game

At every date prescribe

\[
 q_n^d=1,
 \qquad q_n^i=0\quad(i\in I).
\]

Every restarted tail terminates in its first row.  Its value is (H_i) for
each old player and (-P) for the dummy.  For an old player (i), prescribed
Continue gives the dummy-only coalition and value (C_n^i=H_i).  Quit gives
the coalition ({i,d}), whose old part is ({i}), and therefore

\[
 Q_n^i=r^i(\{i\})\le H_i=C_n^i=V_n^i.
\]

For the dummy, Quit gives (-P).  If the dummy instead Continues in the
current row, all old players Continue and the next prescribed row makes the
dummy quit surely, so the unused Continue endpoint is also (-P).  Thus

\[
 Q_n^d=C_n^d=V_n^d=-P.
\]

All global upper and used-action lower clauses of row perfection hold at
error zero.  The padded game therefore satisfies the stronger stationary
exact every-tail S.3 premise.

### 4. Unrestricted exploitability retraction

Fix an arbitrary padded behavioral profile (\widehat\sigma), and let
(\sigma) be its projection obtained by retaining every old player's
live-date Quit probabilities and discarding the dummy.  Let

\[
 \alpha=\Pr_{\widehat\sigma}
 (\text{the first terminal coalition is }\{d\}).
\]

The dummy's expected payoff under (\widehat\sigma) is exactly
(-P\alpha): every terminal coalition containing an old player pays the
dummy zero, as does Never.  If the dummy deviates to Continue forever, its
payoff is exactly zero.  Therefore

\[
 P\alpha\le E_{\widehat G}(\widehat\sigma).                 \tag{1}
\]

Couple the two plays using the same random actions for all old players, and
continue sampling their actions counterfactually after a dummy-only padded
termination.  Outside the dummy-only event, the first old quitting coalition
and the old player's payoff agree pathwise.  On the dummy-only event, the
padded payoff is (H_i), whereas the counterfactually continued projected
payoff is either an old terminal reward or (z^i), hence belongs to
([L_i,H_i]).  Consequently

\[
 U_i^G(\sigma)
 \le U_i^{\widehat G}(\widehat\sigma)
 \le U_i^G(\sigma)+\alpha W_i.                              \tag{2}
\]

Now take an arbitrary old-player behavioral deviation (\tau_i) and lift the
same live-date sequence to the padded game.  The dummy-only event under the
deviation may have a different probability; no equality of those
probabilities is needed.  The same pathwise upper-endpoint comparison gives
the one-sided inequality

\[
 U_i^G(\tau_i,\sigma^{-i})
 \le
 U_i^{\widehat G}(\widehat\tau_i,\widehat\sigma^{-i}).       \tag{3}
\]

Write (\widehat e=E_{\widehat G}(\widehat\sigma)).  From (2), (3), padded
exploitability, (1), and (W_i\le W),

\[
\begin{aligned}
U_i^G(\tau_i,\sigma^{-i})
&\le U_i^{\widehat G}(\widehat\tau_i,\widehat\sigma^{-i})\\
&\le U_i^{\widehat G}(\widehat\sigma)+\widehat e\\
&\le U_i^G(\sigma)+\alpha W_i+\widehat e\\
&\le U_i^G(\sigma)+\widehat e\left(1+\frac WP\right).
\end{aligned}
\]

Take the supremum over all (\tau_i), then the maximum over all old players.
This proves

\[
 E_G(\sigma)\le\left(1+\frac WP\right)
 E_{\widehat G}(\widehat\sigma).
\]

Since (P>0) and (W\ge0), rearrangement gives the factor form

\[
 E_{\widehat G}(\widehat\sigma)
 \ge\frac{P}{P+W}E_G(\sigma).
\]

Every deviation used here is an arbitrary behavioral replacement.  No
stationarity, bounded stopping time, finite controller, maximum-attaining
deviation, or supplied-profile completeness is assumed.

### 5. Cardinal shift, universal equivalence, and negative transport

Let (n\ge1), let (G) be any (n)-player game, and form
(\widehat G) with (n+1) players.  It satisfies exact stationary every-tail
S.3.  If reverse S.3 is known for all ((n+1))-player games, then, for any
(\eta>0), it supplies a padded profile with exploitability at most

\[
 \eta\frac{P}{P+W}.
\]

The projection inequality gives old exploitability at most (\eta).  Thus
reverse S.3 at cardinality (n+1) implies general approximate-equilibrium
existence at cardinality (n).  With no players, the unique empty profile is
trivially exact.

If reverse S.3 holds at every finite cardinality, the preceding shift covers
every finite quitting game.  Conversely, if every finite quitting game has
terminal approximate equilibria, then in particular every S.3 game does.
This proves the universal equivalence.

Finally, suppose (E_G(\sigma)\ge\Gamma>0) for every old behavioral profile.
Apply the pointwise factor inequality to every padded profile and its
projection.  Then

\[
 E_{\widehat G}(\widehat\sigma)
 \ge\frac{P}{P+W}E_G(\sigma)
 \ge\frac{P}{P+W}\Gamma.
\]

Together with the exact stationary every-tail S.3 source, this is the claimed
negative transport.

### 6. Normal and abnormal residue

Subtracting (z^i) from every outcome of player (i) preserves every row
comparison and unilateral gain.  It sets Never to zero.  If every normalized
own-singleton payoff is nonpositive, all Continue is exact.  If every player
is punishment-normal, the checked all-normal S.3 consumer produces terminal
approximate equilibria and a uniform-equilibrium payoff.  Thus any unresolved
S.3 instance must have both a positive own-singleton gap somewhere and an
abnormal player.

For the padded dummy, Never guarantees zero, and opponents who always
Continue cap its best-reply value at zero, whereas its own singleton payoff is
(-P<0).  Hence its punishment value is zero and it is abnormal.  This shows
concretely how the residual abnormal negative-singleton coordinate can carry
an arbitrary old game.

## Boundary tests

1. **The alternative is inclusive.**  In the one-player game
   (z=0=r(\{i\})), all Continue is exact.  The stationary row (q^i=1) is
   also exactly row-perfect and every-tail terminating.  Both arms of the
   null-tail alternative hold, disproving the stronger word "exactly".

2. **The supplied S.3 sequence need not be Nash.**  In the two-player game
   with (z=(0,0)), player 2's terminal payoff always zero, and player 1 paid
   (-1) whenever player 1 belongs to the quitting coalition and zero
   otherwise, prescribe player 1 to Quit surely and player 2 to Continue
   surely at every date.  Every tail terminates and every row is exactly
   perfect, but player 1 gains one by Never.  All Continue is nevertheless an
   exact equilibrium.  The theorem therefore uses S.3 only as a game property
   and never claims the supplied source profile is globally Nash.

3. **The upper endpoint must include Never.**  If (H_i) were maximized only
   over finite terminal coalitions and (z^i>H_i), then on dummy-only padded
   absorption the counterfactually projected play could end at Never above
   (H_i), invalidating the left inequality in (2).  Including (z^i) in
   both (H_i) and (L_i) is essential.

4. **Positive penalty is essential.**  At (P=0), the dummy's Never
   deviation gives no bound on (\alpha), and neither division by (P) nor a
   positive retraction factor is available.  The theorem assumes (P>0).

5. **The shift is real.**  The construction maps (n) old players to
   (n+1) players.  Reverse S.3 for `Fin 4` alone yields general approximate-
   equilibrium existence for `Fin 3`, not `Fin 4`.  Only quantification over
   every finite cardinality yields the displayed equivalence.

6. **Late and Never deviations are present.**  The coupling after a
   dummy-only stop explicitly samples arbitrarily late old behavior
   counterfactually, and the dummy's decisive deviation is Never.  Thus the
   proof is not a finite-deadline or bounded-controller calculation.

## Adapter and consumer

The new ordinary-math adapter takes an arbitrary finite nonempty quitting game
((I,r,z)) and (P>0), computes the finite extrema (H_i,L_i,W), and returns
the explicit padded table on (I\sqcup\{d\}) together with its stationary
exact every-tail S.3 source and pointwise exploitability retraction.

On the positive side, any consumer proving reverse S.3 for the padded
cardinality returns profiles of arbitrarily small padded exploitability; the
projection returns profiles of arbitrarily small old exploitability.  The
checked downstream semantic consumer
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors` in
[`TerminalUniformPayoffSelection.lean`](../../UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean)
then selects one fixed uniform-equilibrium payoff for the old zero-Never game.

On the negative side,
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap` in
[`ExploitabilityGap.lean`](../../UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean)
identifies failure of a uniform-equilibrium payoff with a positive
all-behavior terminal exploitability gap.  The checked padding corollary
`not_exists_uniformEquilibriumPayoff_passivePlayerPadding_canonical` in
[`PassivePlayerPaddingCorollaries.lean`](../../UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingCorollaries.lean)
is the zero-Never formal counterpart of the negative transport proved above.

These consumers do not supply the missing premise.  They explain exactly how
the new reduction attaches to the existing semantic endpoints.

## Lean handoff

A narrow formalization can reuse the current quitting-table and passive-
padding files without changing the general padding construction.

1. Formalize the null-tail lemma for `QuittingPayoffTable`, using
   `IsCompletelyAbsorbing` for initial absorption and an explicit positive
   restarted survival hypothesis.  The key outputs are convergence of tail
   survival to one, live hazards to zero, terminal values to `table.never`,
   and the own-singleton inequality.
2. Package the inclusive alternative only; do not encode the two arms as an
   exclusive sum.
3. Define the arbitrary-Never one-dummy table directly, or normalize through
   the existing zero-Never table adapter.  Specialize
   `quittingPassivePaddingReward` to `J=PUnit`.
4. Prove that the stationary dummy-sure-Quit roots are completely absorbing
   from every shift and satisfy `QuittingRowεPerfect` at error zero.  This is
   a finite simplification proof of the endpoint identities in the proof.
5. Reuse
   `retractionFactor_mul_quittingTerminalExploitability_project_le` rather
   than re-proving unrestricted behavioral retraction.  The only translation
   is coordinatewise subtraction of `z` and the identity
   `Fintype.card PUnit=1`.
6. Reuse `hasSmallAbsorbingSequentiallyPerfectProfiles_iff_table` for the
   small-error/all-error quantifier change.
7. State the cardinal result with an explicit `n+1` target type and treat the
   empty-player case separately.  Avoid a same-cardinality theorem.

Suggested theorem shapes are:

```text
solo_sub_never_le_of_completelyAbsorbing_not_everyTail
hasSmallAbsorbing_nullTailAlternative
oneDummyPadding_has_exactEveryTailRowPerfectRoots
oneDummyPadding_terminalExploitability_retracts
reverseS3_all_card_succ_implies_approximateExistence_all_card
reverseS3_universal_iff_approximateExistence_universal
```

The formalizer should not import this conference note or encode reverse S.3
as an assumption hidden inside a certificate structure.

## Scope and nonclaims

- This packet does **not** prove reverse S.3 for any new unresolved game.
- It does **not** prove the finite-quitting uniform-equilibrium conjecture.
- It does **not** construct a positive-gap counterexample.
- It does **not** say that an S.3 witness itself is an approximate equilibrium.
- It does **not** give a same-cardinality reduction: the hard direction adds
  one player.
- It does **not** remove the abnormal negative-singleton regime; the padding
  shows that regime can encode an arbitrary quitting game.
- The arbitrary-(z) padding and exact dummy-sure-Quit S.3 producer are
  ordinary mathematics pending Lean formalization.  Existing Lean
  declarations check the zero-Never padding reward, its unrestricted
  retraction and gap factor, the small-error adapter, the all-normal consumer,
  and the paper-facing open status.
- The tracked Literature source, not an alleged mathematical erratum, is the
  authority used for the current journal statement.
