# Pure-pair screening makes the two-port transport constant

**Author:** `CODEX_ADVERSARY`  
**Status:** **PROVED IN ORDINARY MATHEMATICS FROM THE CHECKED DECLARATIONS
NAMED BELOW; A COMPACT EXTENSION PASSPORT EXISTS, BUT ITS UPSTREAM PROJECTION
IS CONSTANT AND HAS ZERO TRANSPORT CONTENT**  
**Date:** 2026-08-30

## 1. Question and exact answer

The active two-port branch has:

- an upstream actual profile with a uniformly positive marked coalition atom;
- its literal post-mark continuation;
- a downstream endpoint with one killed debt coordinate;
- the downstream law-tight exact-cap-prefix saturation hull and its minimum
  level set.

Can coupling, disintegration, causal transport, joining theory, or an inverse
limit place the atom and the killed face into one extension-compatible state?

For the **actual current Fin4 forced-pair source**, the answer is sharper than
the earlier generic two-port warning.

The retained mark is a pure quitting coalition of cardinality two.  Conditional
on reaching that row, absorption is certain.  More strongly, after any one
player replaces their complete behavioral strategy, at least one member of
the pair still quits surely.  Hence the post-mark continuation is invisible
not only to the prescribed terminal law and payoff, but also to every
unrestricted one-player best-response cap.

Consequently:

1. there is a compact, extension-compatible two-port passport over the whole
   downstream hull;
2. every downstream point is paired with the **same** upstream joint
   semantic/law point;
3. the upstream point retains the positive pair atom;
4. downstream exact-prefix and same-law replacement edges lift literally
   behind the same prehistory sequence; but
5. no upstream disintegration, Markov kernel, optimal-transport coupling, or
   inverse-limit decoder can recover the downstream point.  The relevant
   conditioning event has probability zero and its conditional law is
   unidentified.

Thus the desired passport exists only in the information-zero form

\[
   \mathcal P=\mathcal H_{\rm down}\times\{z_{\rm up}\}.
\tag{1}
\]

This is a sharp source-attached no-go for using the retained forced-pair atom
to consume the killed downstream face.  It does not say that every conceivable
two-port source is screened.  A mixed marked row with positive joint and
player-deleted continuation could carry genuine transport; the present source
does not.

## 2. The checked source is a pure card-two screen

Fix

```text
packet : FinFourMinimumReturnPacket parent.
```

At rank $n$, write

\[
  m_n=(\operatorname{packet.stream.frame}n).\operatorname{stage},
\]

and let

\[
  \pi_n=(\operatorname{packet.normalizedDecoratedFamily}).
    \operatorname{profile}n
\tag{2}
\]

be the forced-pair target profile.  Its displayed terminal is the fixed
`packet.normalizedTerminal`, denoted $S$.

The exact declarations are:

- `FinFourSourcePreservingForcedPairPacket.pairProfile_eq_purePair`:
  the marked root is literally the pure coalition action of the routed
  terminal;
- `FinFourSourcePreservingForcedPairPacket.forcedTerminal_card` and
  `FinFourMinimumReturnPacket.normalizedTerminal_card`:
  $|S|=2$;
- `FinFourSourcePreservingForcedPairPacket.forcedPair_stageMass_eq_liveMass`:
  the coalition atom at the row equals the complete live mass reaching it;
  equivalently, the conditional root-coalition mass is one; and
- `FinFourSourcePreservingForcedPairPacket.resolution_le_forcedPairStageMass`:
  this unconditional atom has the fixed positive lower bound

  \[
    \lambda:=\operatorname{source.minimumSingletonClockResolution}>0.
  \tag{3}
  \]

The literal post-date continuation is retained by
`FinFourMinimumReturnPacket.forcedPairTail_eq_tail` and the post-date spine
equalities.  Nothing is wrong with that behavioral continuation as an object:
it is defined on the all-Continue history.  But that history has conditional
probability zero at the pure pair row.

## 3. Pure-screen theorem

The following statement is game-independent.

### Theorem 3.1 (complete pure-pair screening)

Let $I$ be finite, let $r$ be a quitting reward table, let $w$ be a
finite literal root word, and let $S\subseteq I$ have $|S|\ge2$.  For an
arbitrary complete behavioral tail $\sigma$, define

\[
 E_{w,S}(\sigma)
 =w\triangleright q^S\triangleright\sigma,
\tag{4}
\]

where $q^S$ is the pure root at which exactly the members of $S$ Quit.
Then for every two tails $\sigma,\tau$,

\[
 Z(E_{w,S}(\sigma))=Z(E_{w,S}(\tau)),
\tag{5}
\]

where $Z$ is the complete terminal-semantic pair consisting of prescribed
payoffs and unrestricted behavioral best-response envelopes.  Their complete
time-forgetting terminal-outcome laws are also equal:

\[
 \operatorname{Law}(E_{w,S}(\sigma))
 =\operatorname{Law}(E_{w,S}(\tau)).
\tag{6}
\]

The all-Continue continuation after the displayed row remains literally the
chosen tail.  Thus (5)--(6) do not identify $\sigma$ and $\tau$; they say that
the prefix screen forgets which one was installed.

### Proof

Equation (5) is exactly the content of
`quittingTerminalSemanticPair_literalRootStack_pureSet_screen` in
`UniformEquilibrium/Quitting/Paths/PureNonsingletonCommonPrefixScreening.lean`.
The theorem explicitly covers unrestricted best-response caps.  Its reason is
also elementary: if a deviator belongs to $S$, at least one other member of
$S$ still quits surely; if the deviator is outside $S$, both members still
quit surely.  No unilateral strategy can reach the tail.

For (6), the affine one-root law action is

\[
 \operatorname{LawPrefix}_{q}(\mu)(C)
 =\operatorname{RootMass}_{q}(C)+c(q)\mu(C),
\tag{7}
\]

with the analogous formula for Never.  At $q^S$, $c(q^S)=0$, the root
mass of $S$ is one, and every other root mass is zero.  Hence the law after
that row is $\delta_S$, independently of $\mu$.  Prefixing the common word
$w$ preserves equality.  This uses
`quittingTerminalOutcomeLawPrefix` and
`quittingTerminalOutcomeLawPrefix_outcomeMass` in
`TerminalSemanticResetIncidenceReturn.lean`.

The literal continuation identity is
`quittingAllContinueProfileSpine_crossTailClosure`; the exact marked-row atom
identity is `quittingStageCoalitionMass_crossTailClosure`.  `QED`

### Corollary 3.2 (constant extension operator)

For every fixed $w,S$ as above, the joint semantic/law extension map

\[
 \mathsf E_{w,S}:z_{\rm tail}\longmapsto z_{\rm upstream}
\tag{8}
\]

is constant on the entire joint carrier.  In particular it is continuous,
compactness-preserving, exact-prefix compatible behind the screen, and
same-law compatible, but it is not injective whenever the downstream carrier
has two points.

This is stronger than a failure of a quantitative estimate: the exact
transport coefficient is zero.

## 4. Production of the compact two-port passport

Let $t_n$ be any actual downstream tails selected on the active branch.  In
particular, they may be the best-response tails for which

\[
  d_p(t_n)\longrightarrow0
\tag{9}
\]

and whose joint semantic/law points converge to a killed endpoint
$z_0=(T,\mu_0)$.

Reattach them by the checked cross-tail construction:

\[
 \widehat t_n
 =\operatorname{quittingCrossTailClosure}(\pi_n,t_n,m_n).
\tag{10}
\]

Pass to a subsequence on which the upstream joint points converge:

\[
 J(\widehat t_n)\longrightarrow z_{\rm up}.
\tag{11}
\]

Compactness of the joint carrier supplies this subsequence.  By (3) and the
exact marked-stage identity,

\[
 z_{\rm up}.2(\operatorname{some}S)\ge\lambda>0.
\tag{12}
\]

Now let $K$ be **any** compact subset of the downstream joint carrier.  It
may be:

- the checked law-tight cap--Nash saturation hull;
- its checked minimum equality level set;
- the ordinary killed-player-face specialization; or
- any closed subspace needed by a later consumer.

Define

\[
 \mathcal P_K=K\times\{z_{\rm up}\}.
\tag{13}
\]

This is compact.  It is also source-faithfully realizable along the same
literal prehistory sequence in the following strong sense.

### Theorem 4.1 (universal same-prehistory realization)

For every $z\in K$, choose actual tail profiles $\sigma_n^z$ whose joint
points tend to $z$.  Then

\[
 J\bigl(\operatorname{quittingCrossTailClosure}
   (\pi_n,\sigma_n^z,m_n)\bigr)
 \longrightarrow z_{\rm up}.
\tag{14}
\]

The downstream continuation of every profile in (14) is literally
$\sigma_n^z$.  At $z=z_0$, the matched choice may be the original $t_n$.

### Proof

For each fixed $n$, Theorem 3.1 says that the upstream joint point is
independent of the installed tail.  Hence the left side of (14) is exactly
$J(\widehat t_n)$, not merely close to it.  Equation (11) proves the result.
`QED`

Thus the entire uncountable downstream compactum can be attached to one
upstream limit without an Arzelà--Ascoli argument, measurable selection, or a
new realization theorem.  The same finite prehistory at rank $n$ works for
every tail approximation used at that rank.

## 5. Compatibility with law-tight saturation and its minimum face

Let $\mathcal H$ be the downstream law-tight saturation hull above $z_0$,
or its killed-face refinement, and let $\mathcal M$ be its positive-debt
minimum level set.  Use the passport

\[
 \mathcal P_{\mathcal H}
 =\{(z,z_{\rm up}):z\in\mathcal H\}.
\tag{15}
\]

It has the following exact lifted operations.

1. **Exact downstream prefix.**  If $x$ is exact cap--Nash at $z$ and
   $P_xz\in\mathcal H$, then

   \[
     (z,z_{\rm up})\longmapsto(P_xz,z_{\rm up}).
   \tag{16}
   \]

   Literal realizers are obtained by installing
   $x\triangleright\sigma_n^z$ behind the same pure-pair prehistory.  The
   upstream joint point is still unchanged.

2. **Same-law debt-lowering replacement.**  If the law-tight hull inserts
   $(Y,\mu)$ below $(X,\mu)$, both are paired with the same upstream point.
   In fact the upstream *whole law* is the same even if the downstream laws
   differ, because the pure screen has zero Continue mass.

3. **Minimum face.**  Every $z\in\mathcal M$ is paired with the retained
   atom (12).  The checked theorem
   `quittingLawTightCapNashSaturationMinimumFace_rootNash_iff_allContinue`
   still says that all Continue is the unique exact root at the **downstream**
   cap.  It says nothing new about $z_{\rm up}$.

Therefore (15) is the strongest natural extension-compatible joint passport
produced by the actual source.  It genuinely preserves one literal chronology
and every downstream hull operation.  But its two coordinates are a direct
product, not a nontrivial joining.

## 6. Disintegration and causal-transport no-go

The product shape has an exact probabilistic explanation.

Let $C_n$ be the event that all players Continue at the marked pure-pair
row.  Then

\[
 \Pr(C_n\mid\text{the row is reached})=0.
\tag{17}
\]

The downstream tail law is a counterfactual conditional law on $C_n$.
Regular conditional probabilities are unconstrained on null events.  For
every downstream law $\mu$, one may pre-sample a counterfactual tail outcome
with law $\mu$ while keeping the same actual upstream process.  Hence the
identification region of the null-branch conditional is the entire
downstream law simplex.

This yields three precise no-go forms.

### Theorem 6.1 (no deterministic decoder)

Let `encode` factor through the upstream joint semantic/law point.  There is
no map `decode` such that

\[
 \operatorname{decode}(\operatorname{encode}(J(E_{w,S}(\sigma))))
 =J(\sigma)
\tag{18}
\]

for every tail $\sigma$, unless the downstream carrier is a singleton.

Indeed, choose $\sigma,\tau$ with distinct joint points.  The encoded inputs
are equal by Theorem 3.1, while the required outputs differ.

### Theorem 6.2 (no exact Markov-kernel decoder)

There is no Markov kernel $Q$ from upstream joint points to downstream
joint points satisfying

\[
 Q(J(E_{w,S}(\sigma)),\cdot)=\delta_{J(\sigma)}
\tag{19}
\]

for every supplied tail $\sigma$ with two possible downstream values.  The
same upstream argument would force one probability measure to equal two
different Dirac masses.

A product kernel that assigns some chosen downstream marginal certainly
exists.  It is an external convention; it is not a disintegration determined
by the upstream game law.

### Theorem 6.3 (no positive transport modulus)

For any metrics on the two compact carriers and any $\kappa>0$, an inequality

\[
 \kappa\,d_{\rm down}(z,z')
 \le d_{\rm up}(\mathsf E(z),\mathsf E(z'))
\tag{20}
\]

fails whenever $z\ne z'$, because the right side is zero.  Thus no
bi-Lipschitz embedding, inverse-continuity estimate, total-variation recovery,
or Wasserstein observability bound can cross this port.

The ordinary data-processing direction survives:

\[
 d_{\rm up}(\mathsf E(z),\mathsf E(z'))=0
 \le d_{\rm down}(z,z').
\]

It is useless for transporting a killed coordinate backward.

## 7. Optimal transport, martingales, and inverse limits

### 7.1 Optimal and causal transport

A causal coupling may store an actual upstream outcome $Y$ and a
counterfactual tail outcome $Z$.  The source fixes the law of $Y$, while
the causal constraint “$Y=Z$ on survival past the mark” is imposed on an
event of probability zero.  It is therefore vacuous.  Every coupling of the
fixed upstream marginal with an arbitrary downstream marginal is admissible
after choosing unused counterfactual randomization.

Any transport cost measurable only from the actual upstream path has the
same value for every downstream marginal.  A cost involving the artificial
coordinate $Z$ can select a coupling, but that selection is extra structure
and has no game-semantic force.  In particular an optimal plan cannot turn
the atom of $Y$ into a positive atom of $Z$.

### 7.2 Martingale transport

The pure pair row is a stopping time at which the actual game is absorbed.
Any payoff or cap martingale stopped there is unchanged when its values are
modified after that stopping time.  The post-mark value process lives only
on the null continuation branch.  Optional projection and optional stopping
therefore impose no constraint on it.

The card-two condition is essential for the cap statement.  With only one
sure quitter, that player can deviate to Continue and expose the tail.  With
two sure quitters, every unilateral replacement leaves another sure quitter,
which is exactly why the unrestricted cap is screened.

### 7.3 Inverse limits and joining theory

Every finite diagram which observes only the upstream stopped process has the
same restriction for every downstream extension.  The inverse-limit fibre
over $z_{\rm up}$ is therefore the whole downstream compactum $K$, not a
single point.  Compact inverse-limit existence proves only that some joined
extension exists; it cannot select or identify the killed-face extension.

In joining terminology, (13) is a joining over a one-point factor.  It has no
relative rigidity.  Relative independence is one possible joining, but all
other counterfactual joinings have the same observed factor.

This is compatible with, and sharper for this source than, the generic
`CounterfactualSuffixCompactnessNoGo`: that checked file shows that a current
response quotient can forget suffix depth.  Here the actual pure-pair source
already makes the complete terminal semantic/law quotient constant after one
specific marked row.

## 8. Exact seam consequence for the killed-debt construction

For the downstream best-response replacement, the killed coordinate and
Fin4 leakage are real:

\[
 d_p(T)=0,
 \qquad
 \sum_{i\ne p}(d_i(T)-d_i(S_{\rm down}))=d_p(S_{\rm down})>0
\tag{21}
\]

in the same-minimum arm.  But after reattaching both tails behind the pure
pair screen, Theorem 3.1 gives the exact stronger equality

\[
 Z(\widehat t_n)=Z(\widehat s_n)
\tag{22}
\]

for every $n$, not merely a small seam error.  Hence all upstream debt
coordinate changes are zero while the downstream coordinates can change by
order one.

This proves that an uncharged all-coordinate backward seam is not merely
unavailable: at this port it has the wrong information direction.  The
upstream atom is retained precisely because the screen prevents the
downstream replacement from affecting anything upstream.

## 9. Minimal repairs

There are only two honest ways to make this type of passport informative.

1. **Use a permeable marked row.**  A law-sensitive transport needs a positive
   joint Continue coefficient.  An all-behavior cap-sensitive transport for
   player $i$ needs positive opponent-deleted survival through the marked
   row.  For all-player transport one needs uniform lower bounds

   \[
     c(q^{\rm mark})\ge\gamma>0,
     \qquad
     c_{-i}(q^{\rm mark})\ge\gamma_i>0
     \quad\text{for every }i.
   \tag{23}
   \]

   The current pure pair has all these quantities equal to zero.  A mixed
   charged row would be a new producer, not a reinterpretation of the forced
   pair.

2. **Make the counterfactual tail a primitive port.**  The product passport
   (13) already does this.  A downstream consumer may use the killed face and
   an upstream consumer may use the atom, but a new two-port theorem must
   explicitly accept both and pay whatever seam connects its conclusions.
   No disintegration theorem can manufacture that seam from the stopped
   upstream law.

A singleton pure mark is only a partial repair: its owner can unilaterally
open the tail, but every outsider still sees that sure quitter as an opponent.
It does not transport all four unrestricted caps.

## 10. What changed and what remains open

The vague statement “the atom is upstream and the killed face is downstream”
can now be replaced by an exact source theorem:

```text
current forced-pair mark
  = pure coalition root of cardinality two
  => zero joint continuation
  => zero player-deleted continuation for every unilateral observer
  => upstream joint semantic/law extension is constant in the tail
  => compact two-port passport exists as H_down × {z_up}
  => no source-determined decoder or positive transport modulus.
```

This closes coupling, disintegration, martingale, and inverse-limit attempts
that use the retained **forced-pair** atom as a bridge to the killed face.
It does not consume the downstream neutral minimum face, prove a uniform
equilibrium, or exclude a different source with a permeable mixed mark.

The current mathematical blocker is therefore changed: it is not production
of a compact two-port object.  That object is automatic.  The missing datum is
a nonzero causal transmission coefficient across the marked row, or a new
consumer designed for two causally disconnected ports.

## Source declarations inspected

- `FinFourSourcePreservingForcedPairPacket.pairProfile_eq_purePair`,
  `forcedTerminal_card`, `forcedPair_stageMass_eq_liveMass`, and
  `resolution_le_forcedPairStageMass` in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingForcedPair.lean`;
- `FinFourMinimumReturnPacket.forcedPairTail_eq_tail`,
  `normalizedDecoratedFamily`, and `normalizedTerminal_card` in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionConsumers.lean`;
- `quittingTerminalSemanticPair_literalRootStack_pureSet_screen` in
  `UniformEquilibrium/Quitting/Paths/PureNonsingletonCommonPrefixScreening.lean`;
- `quittingCrossTailClosure`,
  `quittingAllContinueProfileSpine_crossTailClosure`,
  `quittingStageCoalitionMass_crossTailClosure`, and
  `quittingTerminalSemanticPair_spine_crossTailClosure` in
  `UniformEquilibrium/Quitting/Root/SelfTailClosure.lean` and
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSelfTailClosure.lean`;
- `quittingTerminalOutcomeLawPrefix` and
  `quittingTerminalOutcomeLawPrefix_outcomeMass` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`;
- `quittingTerminalSemanticPrefix_within` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPrefixMetric.lean`;
- the checked hull and minimum-face declarations in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashSaturationHull.lean`
  and `LawTightCapNashMinimumFace.lean`; and
- `no_currentResponseQuotient_suffixTransition_payoffObservable` and the
  all-depth compactness no-gos in
  `UniformEquilibrium/Diagnostics/Quitting/CounterfactualSuffixCompactnessNoGo.lean`.

No literature claim or AGKRS statement was used.  No Lean file or export was
modified.
