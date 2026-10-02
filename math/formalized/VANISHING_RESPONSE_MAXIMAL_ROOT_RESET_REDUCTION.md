# Vanishing-response maximal-root/reset reduction

Authors: `CODEX_GATE`

Independent review:
[`REROOT_REVIEW`](../feedback/CODEX_GATE__VANISHING_RESPONSE_MAXROOT_RESET_TRICHOTOMY__BY_REROOT_REVIEW.md)

Research record:
[`CODEX_GATE__VANISHING_RESPONSE_MAXROOT_RESET_TRICHOTOMY.md`](../notes/CODEX_GATE__VANISHING_RESPONSE_MAXROOT_RESET_TRICHOTOMY.md)

## Exact statement

Let the player set be `I = Fin 4`. A quitting reward table assigns a payoff
vector `r(S) ∈ ℝ^I` to every nonempty coalition `S ⊆ I`. Fix `M > 0` such
that

\[
 |r_i(S)|\le M
 \qquad(i\in I,\ \varnothing\ne S\subseteq I).          \tag{1}
\]

For an actual behavioral profile `σ`, let `U_i(σ)` be its
terminal payoff and let

\[
 B_i(\sigma)=\sup_{\tau_i}U_i(\tau_i,\sigma_{-i})       \tag{2}
\]

be its cap, where the supremum is over every unilateral behavioral strategy
of player `i`. Put

\[
 d_i(\sigma)=B_i(\sigma)-U_i(\sigma),\qquad
 D(\sigma)=\sum_i d_i(\sigma).                          \tag{3}
\]

Let `C^law` be the joint closure of the semantic pair `(U,B)` and the complete
terminal-outcome law on the fifteen nonempty coalitions and Never. Write `C`
for its semantic projection and

\[
 D_*:=\min_{x\in C}D(x)>0.                              \tag{4}
\]

Assume the maintained Fin4 hard residual for this reward table. Only these
checked consequences are used:

1. there is a fixed terminal exploitability margin `γ > 0`: for every actual
   behavioral profile, some player has a complete unilateral behavioral
   replacement whose payoff gain is at least `γ`;
2. every globally minimizing point of `C^law` has positive mass on some
   finite terminal coalition; and
3. the singleton margin holds at every positive global minimum:

   \[
   D_*\le B_i-r_i(\{i\}).                               \tag{5}
   \]

Now take the vanishing-response branch of a positive-minimum tangent family.
After the two checked compactness selections, it supplies:

- actual low-debt response endpoints `R_n` and same-response siblings `Q_n`,
  all taken from one strict subsequence of the same literal source
  family;
- one observer `j`, one nonempty terminal `T`, and a charge `c > 0`;
- joint limits

  \[
  (\operatorname{Sem}(R_n),\mu_{R_n})\longrightarrow
      z=((U^z,B^z),\mu^z),
  \]

  \[
  (\operatorname{Sem}(Q_n),\mu_{Q_n})\longrightarrow
      q=((U^q,B^q),\mu^q);                              \tag{6}
  \]

- vanishing observer debt `d_j(R_n) → 0`, hence `d_j(z) = 0`; and
- the literal and limiting atom inequalities

  \[
  {c\over4}\le16\,
    \operatorname{Atom}(R_n,Q_n;j,T),                   \tag{7}
  \]

  \[
  {c\over4}\le16\bigl(\mu^z(T)-\mu^q(T)\bigr)r_j(T).  \tag{8}
  \]

Here

\[
 \operatorname{Atom}(P,Q;j,T)
   :=\bigl(\mu_P(T)-\mu_Q(T)\bigr)r_j(T).               \tag{9}
\]

The low-debt endpoint is obtained literally by first replacing the packet's
mover and then installing observer `j`'s selected pure stopping time; its
sibling installs the same observer stopping time while restoring the mover's
source strategy.  Thus (7) compares actual profiles, not unrelated carrier
realizers.

Let

\[
 D_n=D(\operatorname{Sem}(R_n)).                        \tag{10}
\]

At each literal cap `B(R_n)`, choose an exact product root `p_n` having
maximum absorption among all exact roots at that cap.  Such a root exists.
Write

\[
 a_n=1-\prod_i p_{n,i}(\mathsf{Continue}),\qquad
 s_n=1-a_n,\qquad \kappa_n=a_nD_n.                      \tag{11}
\]

Prefix the same root to both profiles:

\[
 \widehat R_n=p_n\star R_n,\qquad
 \widehat Q_n=p_n\star Q_n.                            \tag{12}
\]

Only the first prefix in (12) is claimed to be exact Nash--Bellman: `p_n`
is Nash against `B(R_n)`, not necessarily against `B(Q_n)`.

### Theorem A: exact charge and atom ledger

For every `n` and every player `i`,

\[
 d_i(\widehat R_n)=s_nd_i(R_n),\qquad
 D(\widehat R_n)=s_nD_n,                               \tag{13}
\]

\[
 0\le\kappa_n=D_n-D(\widehat R_n)\le D_n-D_*,          \tag{14}
\]

and

\[
 s_n\ge {D_*\over D_n}\ge {D_*\over8M}>0.             \tag{15}
\]

The common prefix scales the old suffix atom exactly:

\[
 \operatorname{Atom}(\widehat R_n,\widehat Q_n;j,T)
   =s_n\operatorname{Atom}(R_n,Q_n;j,T).                \tag{16}
\]

Consequently

\[
 \boxed{
 {cD_*\over32M}
 \le16\,\operatorname{Atom}(\widehat R_n,
                              \widehat Q_n;j,T).}        \tag{17}
\]

Also `d_j(\widehat R_n) → 0`.

### Theorem B: exhaustive hard-residual reduction

Exactly one of the following ordered alternatives holds.

1. **Uniformly charged literal root.** There are `η > 0` and a strict
   subsequence such that

   \[
   a_n\ge\eta,\qquad \kappa_n\ge\eta D_*>0             \tag{18}
   \]

   at every selected index. Every selected `p_n ⋆ R_n` is a literal
   exact cap-root prefix and retains the signed atom with the uniform bound
   (17).

2. **Automatic minimum-fibre reset-rigid entry.** The maximal absorptions
   satisfy `a_n → 0`, the endpoint cluster satisfies `D(z) = D_*`, and

   \[
   0<\operatorname{Inc}^{\rm opp}_j(\mu^z),             \tag{19}
   \]

   where total opponent incidence is

   \[
   \operatorname{Inc}^{\rm opp}_j(\mu)
    :=\sum_{k\ne j}\ \sum_{S:\,k\in S}\mu(S).          \tag{20}
   \]

   Taking `origin = minimum = point = z` in the law-tight cap--Nash
   saturation hull produces a checked
   `QuittingLawTightResetRigidChamber`, with reset owner (j) and source the
   original positive global-minimum semantic pair. The conclusion (19) is
   automatic from the hard residual; it does not require `r_j(T) > 0`.

3. **Strictly off-minimum vanishing-root residual.**  The maximal
   absorptions and charges satisfy

   \[
   a_n\to0,\qquad \kappa_n\to0,                        \tag{21}
   \]

   while

   \[
   D_*<D(z),\qquad d_j(z)=0.                            \tag{22}
   \]

   The checked reset-face selector supplies a semantic pair (m) with

   \[
   d_j(m)=0,\qquad D_*\le D(m)\le D(z),                 \tag{23}
   \]

   for which all Continue is the unique exact cap--Nash root. The literal
   prefixed endpoints still converge to `z`, and their signed suffix atoms
   retain (17). The selector `m` need not retain `μ^z`, the atom, or
   the literal chronology.

In the third alternative, an absorbing exact root may be born only at the
limiting cap `B^z`. If that occurs, no sequence of exact roots at the
literal caps `B(R_n)` can converge to it, because every such root has
absorption at most `a_n → 0`. Such a limiting root is a carrier-level
operation, not a source-level chronological edge.

## Conjecture-facing change

The named live obligation is
[`FIN4_FULL_DEBT_CHAMBER_CONSUMER.md`](../questions/FIN4_FULL_DEBT_CHAMBER_CONSUMER.md).
The common-prefix paid-fork construction in that branch changes the target
cap and then reaches either a prescribed-atom output or the vanishing-response
rectangle treated here.  Before this result, the latter branch still allowed
an unclassified minimum return with the signed atom carried only by its
sibling.

Theorems A and B strictly narrow that vanishing-response descendant to

```text
literal response rectangle
  -> uniformly charged literal exact root
     or automatic minimum-fibre reset-rigid entry
     or strictly off-minimum vanishing-root residual.
```

The middle arm is handed to the separate live obligation
[`FIN4_RESET_RIGID_CHAMBER_CONSUMER.md`](../questions/FIN4_RESET_RIGID_CHAMBER_CONSUMER.md).
Thus no minimum-fibre zero-incidence response residual remains.  The only
unconsumed inert response endpoint is strictly off the global minimum fibre.

This is a strict reduction of one branch below the full-debt source.  It is
not a full-debt chamber consumer: the charged arm is not yet renewable or
returned, the reset-rigid chamber remains open, the prescribed-atom sibling
of the upstream dispatch is outside this packet, and the off-minimum arm is
not consumed.

## Definitions, probability, and strategy class

- Before absorption, the only public history is the repeated all-Continue
  history. An arbitrary behavioral strategy is equivalently a complete
  stopping law on `ℕ ∪ {Never}`, represented by its
  conditional hazards.
- Players use the quitting game's independent behavioral randomizations.
  The first nonempty coalition Quitting at one date is the terminal outcome;
  if nobody ever Quits, the outcome is Never with project payoff zero.
- A unilateral deviation replaces one player's entire behavioral strategy.
  The cap in (2) therefore covers Never, arbitrary unbounded pure stopping
  times, randomized hazards, and every behavioral mixture.  No stationary,
  finite-horizon, bounded-memory, or bounded-controller restriction is made.
- Because payoff is affine in one player's complete stopping law, the
  behavioral cap equals the supremum over pure stopping times.  The theorem
  does not assume that this terminal cap is attained.
- An exact product root is only a one-date independent mixed-action profile
  which is Nash against a displayed continuation cap.  Prefixing it creates
  a new actual behavioral profile.  It is not public correlation and is not
  identified with suffix-law absorption.
- The joint carrier convergence in (6) is finite-dimensional convergence of
  terminal semantic coordinates and the sixteen-coordinate terminal law.
  It is not convergence of the complete stopping laws in total variation.
- The maximization defining (p_n) is performed separately at each literal
  cap.  No continuous root selector, root-attainment along the cap limit, or
  reverse closed-graph implication is assumed.

## Proof

### 1. Maximum roots exist

For a fixed cap `B(R_n)`, exact product roots exist by finite-game Nash
existence.  The product of four binary probability simplices is compact.  The
exact Nash inequalities define a closed subset, and the absorption function

\[
 p\longmapsto1-\prod_i p_i(\mathsf{Continue})
\]

is continuous.  Hence absorption attains its maximum on the exact-root set.

### 2. Debt and atom scaling

Exact cap--Nash prefixing multiplies every coordinate debt by the joint
Continue probability.  This gives (13).  The prefixed semantic/law point
remains in the carrier, so global minimality gives

\[
 D_*\le s_nD_n.
\]

Rearranging proves (14) and the first inequality in (15). Terminal payoffs
and unrestricted caps both lie in `[-M,M]`. Each debt is therefore at most
`2M`, and four players give `D_n ≤ 8M`, proving the rest of (15).

When the same root is prefixed to `R_n` and `Q_n`, all newly absorbed
first-row law is identical and cancels from their difference.  The suffix
law is reached with probability `s_n`, which proves (16). Multiply (7) by
`s_n` and use (15) to obtain (17). Since `0 ≤ s_n ≤ 1` and
`d_j(R_n) → 0`, the observer-debt assertion follows.

### 3. Sequence split

If the nonnegative sequence `a_n` does not converge to zero, there are
`η > 0` and a strict subsequence on which `a_n ≥ η`. Since every
`D_n ≥ D_*`, equation (18) follows.

Otherwise `a_n → 0`. The reset-face compactification gives exactly

\[
 D(z)=D_*\quad\text{or}\quad D_*<D(z).                 \tag{24}
\]

In the second case, boundedness of `D_n` gives `κ_n → 0`, and the
checked minimizer supplies (23) and its unique all-Continue root.  Moreover,
`a_n → 0` forces every player's Continue probability in `p_n` to tend to
one. Prefixing changes either terminal law by at most `2a_n` in `ℓ¹`, and
continuity of the finite semantic prefix gives the same cluster `z`. This
proves the third arm, except for the already established
atom bound (17).

If the first case of (24) holds, (14) gives

\[
 0\le a_nD_n\le D_n-D_*\longrightarrow0.
\]

As `D_n → D_* > 0`, this again forces `a_n → 0`. It remains only to prove
positive opponent incidence.

### 4. Automatic incidence at a minimum response cluster

The Fin4 hard-residual finite-atom theorem applies to the arbitrary global
minimum joint law `z`. Choose a finite terminal `S` with

\[
 \mu^z(S)>0.                                            \tag{25}
\]

Assume for contradiction that
`Inc_j^opp(μ^z) = 0`. Every summand in (20) is
nonnegative.  Hence every terminal of positive mass contains no player other
than `j`. Because a terminal coalition is nonempty, every such terminal is
exactly `{j}`. In particular `S = {j}`. Put

\[
 p=\mu^z(\{j\})>0.
\]

For any finite terminal `A`, if `A = {j}` then its mass is `p`. If
`A ≠ {j}`, its nonnegative mass cannot be positive, since the preceding
support argument would force `A = {j}`. Thus its mass is zero. Summing
the sixteen simplex coordinates now gives

\[
 \mu^z(\mathsf{Never})=1-p.                             \tag{26}
\]

The law is therefore supported exactly on `{j}` and Never. The checked
singleton/Never cap-tightness theorem, applied to this joint carrier point
and `d_j(z) = 0`, yields

\[
 B^z_j=r_j(\{j\}).                                      \tag{27}
\]

The global-minimum singleton margin (5) now gives the contradiction

\[
 0<D_*\le B^z_j-r_j(\{j\})=0.                          \tag{28}
\]

Thus (19) holds.  To apply the reset-rigid consumer, take
`origin = minimum = point = z`.  The origin belongs to its own law-tight
saturation hull.  Every point of that hull lies in the ambient joint carrier,
so global minimality of (z) makes it a hull minimizer and places it in its
own minimum face.  The terminal exploitability witness, the original global
minimum source, `d_j(z) = 0`, and (19) are precisely the inputs of
`exists_quittingLawTightResetRigidChamber`.  This completes Theorem B.

The cap-tightness step (27) is essential.  Singleton/Never support and the
singleton margin alone do not imply a contradiction.

### 5. Roots born only at the compact limit

In the third arm, let `p` be an absorbing exact root at `B^z`, if one
exists. If exact roots `q_n` at `B(R_n)` converged to `p`, their
absorptions would converge to the positive absorption of `p`. But

\[
 \operatorname{Abs}(q_n)\le a_n\longrightarrow0
\]

by maximality of (p_n), a contradiction.  This proves the final topology
claim without assuming lower semicontinuity of the exact-root correspondence.

## Boundary tests

### Minimum boundary

At `D(z) = D_*`, equation (14) forces `a_n → 0`; a uniformly charged
subsequence cannot coexist with an exact minimum return.  The hard-residual
finite-atom and singleton-margin chain then forces reset-rigid.  This tests
the equality boundary in (24).

### Root-correspondence boundary

The reverse root-limit implication is false already in a one-player root
game. Give Quit payoff zero and continuation cap `b_n = 1/n`. Continue is
the unique exact root for every `n`, so maximum absorption is zero. At the
limit cap `b = 0`, every mixture is exact and maximum absorption is one.
Adding three players for whom Continue strictly dominates Quit embeds the
same cap-level discontinuity in Fin4.  This is why Theorem B selects roots at
the literal caps and classifies a born-at-limit absorbing root as residual
rather than as a chronological edge.

### Exact negative-orientation Fin4 regression

Let the players be `m,j,a,b`. For every nonempty coalition `S`, set

\[
 r_m(S)=\begin{cases}-1&m\in S,\\0&m\notin S,\end{cases}
\]

\[
 r_j(S)=
 \begin{cases}
 -2,&j\in S,\\
 -1,&j\notin S\text{ and }m\in S,\\
 0,&j\notin S\text{ and }m\notin S,
 \end{cases}                                           \tag{29}
\]

and, for (x\in\{a,b\}), set

\[
 r_x(S)=
 \begin{cases}
 1,&x,m,j\in S,\\
 -1,&x\in S\text{ but not both }m,j\in S,\\
 0,&x\notin S.
 \end{cases}                                           \tag{30}
\]

At date zero everyone Continues. At date one let `X` prescribe sure Quit
for `m,j` and Never for `a,b`. Let `Y` replace only `m` by Never.
Let `R` further replace observer `j` by Never, and let `Q` instead make
that same observer replacement at `X`. Thus `R` is all Never, whereas
`Q` has only `m` Quit at date one.

Direct unrestricted-deviation calculation gives

\[
 U(X)=(-1,-2,0,0),\quad B(X)=(0,-1,1,1),\quad
 d(X)=(1,1,1,1),                                      \tag{31}
\]

\[
 U(Y)=(0,-2,0,0),\quad B(Y)=(0,0,0,0),\quad
 d(Y)=(0,2,0,0),                                      \tag{32}
\]

and

\[
 U(R)=B(R)=0.                                          \tag{33}
\]

Indeed, at `X`, players `m,j` improve by Never and players `a,b`
improve by joining the date-one `{m,j}` coalition. At `Y`, only `j`
improves, by Never.  Deterministic pure times attain each displayed cap, and
every behavioral mixture is a convex combination of the same bounded
outcomes, so no unrestricted deviation does better.

The mover gain and observer debt rise are both one. With `T = {m}`,

\[
 \mu^R(T)=0,\qquad \mu^Q(T)=1,\qquad r_j(T)=-1,
\]

and hence

\[
 \operatorname{Atom}(R,Q;j,T)=(0-1)(-1)=1.             \tag{34}
\]

Nevertheless the low-debt target `R` has zero finite opponent incidence.
Against its cap zero, `m` strictly prefers Continue to Quit, and `j`
gets between `-1` and `0` by Continue versus `-2` by Quit. Once `m`
Continues, each of `a,b` gets zero by Continue and `-1` by Quit. Thus all
Continue is the unique exact root.

This regression proves that a positive signed rectangle atom need not put
incidence on its low-debt endpoint; when `r_j(T) < 0`, the guaranteed mass is
on the sibling. It has `D_* = 0`, because `R` is an exact zero-debt profile.
It is not a hard-residual counterexample and does not contradict the
automatic minimum-incidence theorem, whose essential positive-minimum
hypothesis fails here.

For completeness, (8) itself gives the exact sign boundary. If
`r_j(T) > 0` and `T` contains some player other than `j`, then

\[
 \mu^z(T)\ge {c/4\over16M}>0
\]

and the target has positive opponent incidence.  If (r_j(T)<0), the same
lower bound is guaranteed only for `μ^q(T)`. The automatic
minimum-fibre argument does not reorient this rectangle atom; it obtains
target incidence from a possibly different finite atom supplied by the hard
residual.

## Source correspondence and nonduplication

The checked inputs are:

- `QuittingStoppingLawVanishingDebtRectangleSequence` and
  `QuittingPositiveMinimumDebtTangentFamily.exists_prescribedAtomSequence_or_vanishingDebtRectangleSequence`
  in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/OffDiagonal/AtomRectangleSequenceAlternative.lean`;
- `QuittingStoppingLawRectangleResetFaceDispatch`,
  `QuittingStoppingLawRectangleJointAtomLimit`, `nonempty_resetFaceDispatch`,
  and `nonempty_jointAtomLimit` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/RectangleResetFaceMinimizer.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
- `quittingTerminalPayoffDifferenceAtom_literalRootStack` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/ContinuePrefixAtomAccess.lean`;
- `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- `terminal_eq_singleton_of_totalOpponentIncidence_eq_zero_of_mass_pos` and
  `exists_quittingLawTightResetRigidChamber` in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashStrictMinimum.lean`;
- `terminalSemanticLaw_singletonNever_zeroDebt_cap_eq_singletonReward` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSingletonNeverCapTightness.lean`;
  and
- `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`.

The maximum-root argmax, its literal sequence trichotomy, the application of
the arbitrary-minimum finite-atom theorem specifically to the rectangle
response cluster, and the exact negative-orientation regression are ordinary
mathematics in this packet and are not claimed to be Lean checked.

The finite-atom corollary is the only place where the hard residual's
punishment-normality field enters: its checked proof converts
`all_punishmentNormal` to the generic normality inequality and combines it
with nonexistence of a uniform payoff. This packet does not assert that
punishment-normality alone supplies the atom or the reset conclusion.

The existing reset-face packet alone preserves the displayed atom law only at
the endpoint cluster and previously obtained endpoint incidence directly only
from a positive-reward rectangle atom.  The new composition proves that, at
an exact hard-residual minimum return, **some** finite atom forces positive
incidence for the already selected zero-debt observer, independently of the
rectangle atom's sign.  The existing canonical Fin4 two-chamber theorem
selects its own law-tight minimum; this result applies to the arbitrary joint
minimum cluster produced by the literal rectangle source.

The exact-root correspondence is known not to admit the reverse compactness
step used by a naive post-limit maximal-root argument.  This packet does not
repeat that false step: it chooses roots at every actual endpoint and retains
a born-at-limit root as an explicit residual.

No result from an original paper is invoked or translated.  The packet is a
project-internal composition of checked quitting-game semantics and new
ordinary finite-dimensional arguments, so there is no literature theorem
whose strategy class or topology must be matched.

## Adapter and consumer

The checked actual-data adapter is:

```text
positive-minimum tangent family
  -> prescribed atom or vanishing-debt response rectangle
  -> reset-face dispatch and common joint atom limit.
```

It is implemented by
`exists_prescribedAtomSequence_or_vanishingDebtRectangleSequence`,
`nonempty_resetFaceDispatch`, and `nonempty_jointAtomLimit`.  The present
ordinary theorem consumes only the vanishing-response side.  It does not
assert that every hard residual has entered that side.

The charged output is a literal exact one-root prefix with a uniform debt
charge and a source-provenant suffix atom.  No existing theorem makes it
renewable, so no terminal consumer is claimed for that arm.

The minimum output feeds the checked
`exists_quittingLawTightResetRigidChamber`; its remaining conjecture-facing
consumer is exactly the open reset-rigid question linked above.

The off-minimum output is the sharpened remaining source obligation.  It
retains the literal endpoint sequence, vanishing maximal-root charge, the
zero-debt observer, the positive signed atom, and a separate exact
all-Continue reset-face minimizer, while recording that the minimizer may
lose the law and chronology.

Accordingly, this packet qualifies as a proved reduction which strictly
narrows the vanishing-response descendant of the named full-debt obligation,
not as a supplied-certificate verifier or an arbitrary-game producer.

## Lean handoff

The narrowest formalization should proceed in four pieces.

1. Package the compact exact-root set at one cap and prove existence of an
   absorption maximizer, for example as
   `exists_maxAbsorption_isZeroQuittingRootNash`.  Use compactness of the
   finite product of `PMF Bool`, closedness of `IsεQuittingRootNash ... 0`,
   and continuity of `quittingRootAbsorptionMass`.  Do not add a
   continuity field for the selected maximizer.
2. Define the maximum absorption and fresh literal prefix along a
   `QuittingStoppingLawRectangleJointAtomLimit`.  Prove (13)--(17) using the
   existing debt-scaling and literal-root-stack atom lemmas.  A separate
   elementary lemma may record `card (QuittingTerminalOutcome (Fin 4)) = 16`.
3. Prove the reusable key lemma

   ```text
   FinFourQuantitativeFullSupportHardResidual.
     totalOpponentIncidence_pos_of_minimumLaw_of_debt_eq_zero
   ```

   for any supplied global-minimum joint carrier point.  Its proof should
   explicitly construct the singleton/Never support equations from simplex
   nonnegativity, then invoke cap tightness and the singleton margin.  Do not
   assume positive incidence as a structure field.
4. Compose that lemma with `exists_quittingLawTightResetRigidChamber` and the
   sequence split into a theorem on the existing rectangle dispatch.  The
   result type should have precisely the three arms of Theorem B.  In the
   off-minimum arm, retain the joint limit, literal profile indices, maximal
   root sequence, atom inequality, and reset-face minimizer as dependent
   fields; do not replace the literal sequence by an unrelated realizer.

Useful finite tests are the negative-orientation table (29)--(34), the
one-active-player root-birth cap example, and equality-boundary tests in
which `D(z)=D_*` forces zero maximal-root charge.  The external formalizer
must recheck the ordinary argmax topology and regression calculations rather
than importing this Markdown packet or encoding its conclusion as a field.

## Scope and nonclaims

- This is not a proof of the finite-quitting uniform-equilibrium conjecture.
- It is not a full-debt chamber consumer and does not claim that every
  hard-residual source produces a vanishing-response rectangle.
- It does not consume the upstream prescribed-atom branch.
- It does not make the charged root renewable, extension-compatible with an
  older prefix word, or a return to the original source.
- It does not consume the reset-rigid chamber.
- It does not consume the strictly off-minimum residual or prove that its
  reset-face minimizer retains the endpoint law, atom, or chronology.
- It does not identify a root at the limiting cap with an approximating root
  at the literal caps.
- It does not weaken unrestricted behavioral caps to stationary or bounded
  deviations, assume cap attainment, or identify terminal-law mass with
  current root absorption.
- The regression has global minimum zero and is only a sharp local boundary
  for signed-atom orientation.
- The packet is ordinary mathematics reviewed for export; its new statements
  are not Lean checked until an external formalization agent supplies named
  declarations under the project trust policy.

## Lean formalization record

Pre-formalization packet SHA-256:
`be27a1e7c61f812cb1f66fba8b0adf029c12a963a1ca6551000534fcece90e6f`.

The checked reduction landed in commit
`8d65fbf6a81010e84e4734776ef455335b6513ac`.  Its production owners are
`UniformEquilibrium/Quitting/Root/MaximalAbsorptionNash.lean`,
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumOpponentIncidence.lean`,
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/RectangleMaximalRootLedger.lean`,
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/RectangleMaximalRootReduction.lean`,
and
`UniformEquilibrium/Diagnostics/Quitting/Regression/FinFourMaximalRootNegativeOrientation.lean`.

The principal declarations are
`exists_maximalAbsorption_isZeroQuittingRootNash`,
`totalOpponentIncidence_pos_of_minimumLaw_of_debt_eq_zero`,
`quittingRectangleMaximalRootPrefixedEndpoint_debt_coordinate_eq`,
`quittingRectangleMaximalRoot_survival_floor`,
`quittingRectangleMaximalRootPrefixed_atom_lower`,
`quittingRectangleMaximalRootPrefixedEndpoint_tendsto_cluster`,
`QuittingStoppingLawRectangleJointAtomLimit.maximalRoot_threeWay`, and
`QuittingStoppingLawRectangleJointAtomLimit.maximalRoot_exactlyOne`.  The
last theorem makes the three alternatives exhaustive and pairwise exclusive;
the off-minimum output retains the literal maximal-root-prefixed joint
semantic/law convergence to the supplied cluster.

Evidence seals are `M` and `L`, with branch-local `A` only after a supplied
`FinFourQuantitativeFullSupportHardResidual` has reached the existing
vanishing-response rectangle and common-limit interfaces.  There is no
unconditional producer of that branch and no downstream `C`: the charged,
minimum reset-rigid, and off-minimum outputs are not renewed or consumed.
The negative-orientation regression proves a positive signed atom, zero
opponent incidence, and an exact all-Continue root for its explicit table; it
does not prove that root unique and is not a positive-minimum hard-residual
source.  No chronology return, terminal approximation, recursive closure, or
uniform-equilibrium payoff is claimed.
