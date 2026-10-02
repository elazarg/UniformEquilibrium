# Law-tight cap--Nash saturation forces a neutral minimum set

Authors: conference synthesis from `CODEX_ADVERSARY`, corrected and assembled
by `CODEX_STRENGTHEN`

Independent review:
[`CODEX_ADVERSARY__FIN4_CAP_NASH_SATURATION_HULL__BY_CODEX_STRENGTHEN.md`](../feedback/CODEX_ADVERSARY__FIN4_CAP_NASH_SATURATION_HULL__BY_CODEX_STRENGTHEN.md)

This is a **staged export draft in `notes/`, not an export**.  Promotion awaits
the original author's final consistency check.  The mathematics below is
ordinary mathematics assembled from named checked carrier, prefix, reset, and
causalization declarations; the saturation theorem itself is not yet Lean
checked.

## Exact statement

Fix a finite nonempty player type (I) and a bounded quitting reward table
(r).  Let

\[
 \mathcal C=
 \operatorname{quittingTerminalSemanticLawCarrier}(r).
\]

A point (z=(X,\mu)\in\mathcal C) consists of a terminal semantic pair
(X=(u,c)) and a terminal-outcome probability vector

\[
 \mu:\{\operatorname{none}\}\cup
      \{\operatorname{some}S:S\subseteq I,\ S\ne\varnothing\}
      \longrightarrow[0,1].
\]

Here `none` is joint Never and `some S` records only the terminal quitting
coalition.  This is **not** a law of stopping dates, a vector of marginal
stopping laws, or a chronological source trace.

Write

\[
 d_i(X)=c_i-u_i,
 \qquad
 D(X)=\sum_{i\in I}d_i(X).
\]

Assume a positive global carrier floor

\[
 0<D_*\le D(X)\qquad((X,\mu)\in\mathcal C).       \tag{1}
\]

Fix an origin (z_0=(X_0,\mu_0)\in\mathcal C), a nonempty coalition
(S_0), and

\[
 b_0:=\mu_0(\operatorname{some}S_0)>0.             \tag{2}
\]

For a product root (x), put

\[
 q(x)=\operatorname{quittingStationaryContinueMass}(x),
 \qquad a(x)=1-q(x),                                \tag{3}
\]

and let (P_x(X,\mu)) be the checked joint semantic/outcome-law prefix:

\[
 P_x(X,\mu)=
 \bigl(
   \operatorname{quittingTerminalSemanticPrefix}(r,x,X),
   \operatorname{quittingTerminalOutcomeLawPrefix}(x,\mu)
 \bigr).                                            \tag{4}
\]

Only roots satisfying

\[
 \operatorname{Is\varepsilon QuittingRootNash}(r,c,0,x)                 \tag{5}
\]

are used.  Thus “exact root” below always means exact Nash against the
displayed **cap** (c=X.2), never against the prescribed payoff (u=X.1).

### Theorem A: law-tight cap--Nash saturation

There exist a nonempty compact set
(widehat{\mathcal H}=\widehat{\mathcal H}(z_0)\subseteq\mathcal C), a
number (D_H>0), and a nonempty compact minimum set

\[
 \mathcal M=
 \{(X,\mu)\in\widehat{\mathcal H}:D(X)=D_H\}        \tag{6}
\]

with all of the following properties.

We call (\mathcal M) the minimum face below only as shorthand for this
minimum level set.  No convexity of the hull or convex-geometric face property
is asserted.

1. **Origin and exact-prefix saturation.**  The origin belongs to the hull.
   If (z=(X,\mu)\in\widehat{\mathcal H}) and (x) is exact cap--Nash at
   (X), then (P_xz\in\widehat{\mathcal H}).

2. **Downward same-law closure.**  If ((X,\mu)) belongs to the hull,
   ((Y,\mu)\in\mathcal C), and (D(Y)\le D(X)), then
   ((Y,\mu)\in\widehat{\mathcal H}).

3. **Debt-weighted atom cone.**  Every ((X,\mu)) in the hull satisfies

   \[
    D(X_0)\mu(\operatorname{some}S_0)
       \ge D(X)b_0.                                  \tag{7}
   \]

   In particular every point of (mathcal M) satisfies

   \[
    \mu(\operatorname{some}S_0)
      \ge {D_H\over D(X_0)}b_0
      \ge {D_*\over D(X_0)}b_0>0.                    \tag{8}
   \]

4. **Hull and law-fibre minimization.**  The number (D_H) is the minimum
   of (D) on the hull.  Every ((X,\mu)\in\mathcal M) also minimizes debt
   on its entire terminal-outcome-law fibre:

   \[
    D(X)\le D(Y)
    \quad\text{whenever }(Y,\mu)\in\mathcal C.       \tag{9}
   \]

5. **Unique neutral cap root.**  At every ((X,\mu)\in\mathcal M),

   \[
    x\text{ is exact Nash against }X.2
      \quad\Longleftrightarrow\quad
    x=\text{all Continue}.                            \tag{10}
   \]

   The all-Continue joint prefix fixes ((X,\mu)) exactly.

6. **Global absorption bound.**  For every ((X,\mu)) in the hull and every
   exact cap--Nash root (x) there,

   \[
    a(x)\le {D(X)-D_H\over D(X)}.                    \tag{11}
   \]

   Consequently every finite exact-prefix chain
   (z_{n+1}=P_{x_n}z_n), (0\le n<N), in the hull obeys

   \[
    \sum_{n<N}a(x_n)
       \le {D(z_0.1)-D(z_N.1)\over D_H}
       \le {D(z_0.1)-D_H\over D_H}.                  \tag{12}
   \]

   Here (z_0) in (12) denotes the initial point of the displayed chain; it
   need not be the distinguished origin used to define the hull.

The theorem requires no continuity, lower hemicontinuity, or measurable
selection of the exact-root correspondence.

### Theorem B: Fin4 minimum regeneration or strict neutral saturation

Let (I=\operatorname{Fin}4), let `residual` be a
`FinFourQuantitativeFullSupportHardResidual r bound`, and let
(z_0=(X_0,\mu_0)\in\mathcal C) carry the positive atom (2).  Then Theorem A
applies with

\[
 D_*=\operatorname{quittingTerminalDebtSumInf}(r)>0. \tag{13}
\]

Exactly one of the following numerical alternatives holds.

1. **Same-point minimum regeneration:** (D_H=D_*).  Every selected
   (z_H\in\mathcal M) is globally minimum over the full semantic carrier.
   The checked same-point causalization theorem produces
   `QuittingMinimumLawCausalSuffixAtom r zH`.  Hence (z_H), not an
   independently selected minimum point, packages a
   `FinFourMinimumAtomProducer r bound` whose residual field is definitionally
   the supplied `residual`.

2. **Strict neutral saturation:** (D_*<D_H\le D(X_0)).  The returned
   law-tight saturation passport retains the quantitative atom (8), the
   whole compact minimum face, same-outcome-law fibre minimality, the exact
   all-Continue self-loop, unique exact cap-root property (10), and the
   global estimate (11).

Every strict neutral point (z=(X,\mu)\in\mathcal M) has the following
exhaustive Fin4 form.

1. **Full debt support:** (d_i(X)>0) for every player.
2. **Reset-rigid incidence:** some player (o) has (d_o(X)=0) and positive
   total opponent incidence in (mu).  There are a player (j\ne o) and a
   same-law point ((R,\mu)\in\mathcal M) returned by the checked fixed-law
   reset dispatch such that:

   - (d_o(R)=0) and (D(R)=D_H);
   - the dispatch retains a positive (o,j)-incidence coordinate, its
     opposite-face debt-transfer account, and a supported strict membership
     toggle; and
   - its dynamic absorbing exit is impossible, so its exact all-Continue
     fixed-face arm holds.

3. **Singleton/Never binding cycle:** there is a unique zero-debt owner (o)
   and a number (p>0) such that

   \[
    \mu=p\,\delta_{\operatorname{some}\{o\}}
       +(1-p)\,\delta_{\operatorname{none}}.          \tag{14}
   \]

   The owner is cap-binding,

   \[
    X.2_o=r_o(\{o\}),                                 \tag{15}
   \]

   and the finite set of cap-binding players contains a directed cycle of
   length at least two whose edge (i\to j) satisfies

   \[
    j\ne i,qquad X.2_j=r_j(\{j\}),qquad
    r_j(\{i,j\})-r_j(\{i\})>0.                        \tag{16}
   \]

The cycle need not contain the original zero-debt owner.

## Definitions and scope

### Terminal semantic/outcome-law carrier

The attainable points are

\[
 \left(
  \operatorname{quittingTerminalSemanticPair}(r,\sigma),
  \operatorname{quittingTerminalOutcomeMass}(r,\sigma)
 \right)
\]

for actual behavioral profiles (sigma).  The carrier (mathcal C) is
their closure.  Its semantic coordinate retains prescribed terminal payoff
and the coordinatewise supremum against every unilateral behavioral
replacement.  The unilateral cap therefore includes Never, arbitrarily late
randomized stopping, and every other behavioral hazard on the unique live
public history.

The carrier's law coordinate is finite-dimensional and time-forgetting.  A
carrier point need not itself be realized by one behavioral profile.  It is a
limit of actual semantic/outcome-law points.

### Law-tight cap--Nash invariants

A set (A) of joint carrier points is an admissible invariant above (z_0)
when:

1. (A) is closed in the ambient finite-dimensional topology;
2. (A\subseteq\mathcal C) and (z_0\in A);
3. (z\in A) and exact cap--Nash of (x) at (z) imply (P_xz\in A); and
4. ((X,\mu)\in A), ((Y,\mu)\in\mathcal C), and (D(Y)\le D(X)) imply
   ((Y,\mu)\in A).

Define

\[
 \widehat{\mathcal H}(z_0)
 =\bigcap\{A:A\text{ is an admissible invariant above }z_0\}. \tag{17}
\]

The downward direction in item 4 is essential.  Upward same-law closure would
not preserve the debt-weighted atom cone.

### Incidence

For distinct players (o,j), let

\[
 I_{o,j}(\mu)
 =\sum_{T:\ j\in T,\ j\ne o}\mu(\operatorname{some}T),
\]

and let

\[
 J_o(\mu)=\sum_{j\ne o}I_{o,j}(\mu).                 \tag{18}
\]

These are nonnegative on carrier laws.  They forget timing and count a
coalition once for each displayed opponent it contains.

## Proof of Theorem A

### 1. Nonempty compact saturation

The family in (17) is nonempty.  The whole carrier (mathcal C) is compact,
hence closed, contains (z_0), and is preserved by every prefix root through
`quittingTerminalSemanticLawPrefix_mem_carrier`.  Its law-tight clause is
tautological because it contains every carrier point.

An arbitrary intersection of closed sets is closed.  Every defining set
contains (z_0), so the intersection is nonempty, and it is a closed subset
of compact (mathcal C).  It is therefore compact.

Both invariances pass pointwise to the intersection.  In particular, suppose
(z\in\widehat{\mathcal H}) and an exact cap root (x) exists at (z).
For every defining invariant (A), one has (z\in A), hence (P_xz\in A).
Therefore (P_xz\in\widehat{\mathcal H}).  The proof never approximates
(x) by roots at nearby points.  A new exact root which appears only at a
limit point is automatically included.

### 2. Exact common scaling factor

Let (z=(X,\mu)in\mathcal C), let (x) be exact Nash against (X.2), and
write (P_xz=(Y,\nu)).  The checked cap--Nash prefix theorem gives for every
player

\[
 d_i(Y)=q(x)d_i(X),                                  \tag{19}
\]

and hence

\[
 D(Y)=q(x)D(X).                                      \tag{20}
\]

For the fixed finite atom, the checked affine law definition gives

\[
 \nu(\operatorname{some}S_0)
  =\operatorname{quittingRootCoalitionMass}(x,S_0)
     +q(x)\mu(\operatorname{some}S_0)
  \ge q(x)\mu(\operatorname{some}S_0).               \tag{21}
\]

The fresh root term is nonnegative because root coalition masses are
probabilities.

### 3. The atom cone is an admissible invariant

Let

\[
 K=\{(X,\mu)\in\mathcal C:
       D(X_0)\mu(\operatorname{some}S_0)\ge D(X)b_0\}.
\]

This set is closed by continuity and contains (z_0) with equality.  If
((X,\mu)\in K), equations (20)--(21) imply

\[
 \begin{aligned}
 D(X_0)\nu(\operatorname{some}S_0)
 &\ge q(x)D(X_0)\mu(\operatorname{some}S_0)\\
 &\ge q(x)D(X)b_0=D(Y)b_0,
 \end{aligned}
\]

so (K) is exact-prefix invariant.  If ((Y,\mu)in\mathcal C) and
(D(Y)\le D(X)), then the right side of the cone inequality only decreases,
so (K) is law-tight.  Thus (K) is one of the sets intersected in (17), and
(widehat{\mathcal H}\subseteq K).  Equations (7)--(8) follow.

### 4. Compact minimization and law-fibre minimization

Continuity of (D) on the nonempty compact hull gives a minimizer and a
minimum value (D_H\ge D_*>0).  The level set (mathcal M) in (6) is a
nonempty closed subset of the compact hull.

Fix ((X,\mu)\in\mathcal M) and any carrier point ((Y,\mu)).  If
(D(Y)>D(X)), (9) is immediate.  If (D(Y)\le D(X)), law-tightness puts
((Y,\mu)) in the hull and hull minimality gives (D(X)\le D(Y)).  This
proves (9), including equality whenever the tightening rule fires.

### 5. Unique all-Continue exact cap root

Fix ((X,\mu)\in\mathcal M) and let (x) be exact Nash against (X.2).
Prefix invariance and (20) give

\[
 D_H\le D(P_xX)=q(x)D_H.
\]

Since (D_H>0) and (q(x)\le1), one has (q(x)=1).  The checked theorem
`eq_quittingAllContinueRoot_of_continueMass_eq_one` gives
(x=\) all Continue.

The checked finite mixed-root theorem `exists_isZeroQuittingRootNash` supplies
at least one exact Nash root against (X.2).  The preceding paragraph forces
that root to be all Continue.  This proves both directions of (10).

The all-Continue law prefix is the identity.  On semantics, the prescribed
coordinate is unchanged, while exact all-Continue cap--Nash is exactly the
singleton upper-bound condition making the cap coordinate unchanged.  Thus
the joint prefix fixes ((X,\mu)).

### 6. Quantitative absorption bound

For an arbitrary hull point ((X,\mu)) and exact cap root (x), prefix
closure and (20) give

\[
 D_H\le (1-a(x))D(X).
\]

Because (D(X)\ge D_*>0), division and rearrangement give (11).  Along a
finite exact-prefix chain,

\[
 D(X_n)-D(X_{n+1})=D(X_n)a(x_n)\ge D_Ha(x_n).
\]

Summing telescopically proves (12).

## Proof of Theorem B

### 1. Hard-residual source and numerical split

`FinFourMinimumAtomProducer.exists_residual_eq_of_hardResidual` supplies a
minimum source whose residual is definitionally the input residual and whose
debt equals the positive infimum (13).  Its minimum theorem gives the lower
bound (1) on every semantic, hence every joint semantic/outcome-law, carrier
point.  Apply Theorem A to (z_0,S_0,b_0).

Since (z_0) belongs to the hull,

\[
 D_*\le D_H\le D(X_0).
\]

Split the first inequality into equality or strict inequality.

### 2. Equality gives same-point causalization

Assume (D_H=D_*) and choose (z_H=(X_H,\mu_H)\in\mathcal M).  Its semantic
projection belongs to `quittingTerminalSemanticCarrier r`.  For every
semantic carrier candidate (Y), the global minimum identity gives

\[
 D(X_H)=D_*\le D(Y).
\]

Thus the checked hypotheses of
`finFourHardResidual_minimumLaw_causalSuffixAtom` hold at the same point
(z_H).  Choose the returned causal suffix atom and package:

- the original `residual`;
- (z_H) and its joint and semantic carrier memberships;
- the displayed global minimum proof;
- positivity of the debt infimum and (D(X_H)=D_*); and
- the causal suffix atom.

These are exactly the fields of `FinFourMinimumAtomProducer`, and its residual
field is definitionally unchanged.  This same-point conclusion is the new
content; the hard residual already supplies some minimum source independently.

### 3. Strict neutral trichotomy

Assume (D_*<D_H) and fix (z=(X,\mu)\in\mathcal M).  Every coordinate debt
is nonnegative.

If every coordinate is positive, this is full debt support.  Otherwise let
(Z=\{i:d_i(X)=0\}\), which is nonempty.

Suppose first that some (o\in Z) has (J_o(\mu)>0).  Each summand in (18)
is nonnegative.  Positivity of the finite sum therefore gives

\[
 \exists j\ne o,\qquad I_{o,j}(\mu)>0.               \tag{22}
\]

This is the coordinate-incidence extraction needed by the checked reset
dispatch; positive total incidence cannot be passed directly as its `other`
argument.

Use the original hard-residual minimum semantic point as reset source and
(X) as target.  The checked fixed-law reset dispatch returns a semantic pair
(R), coupled to the identical law (mu), with

\[
 D_*\le D(R)\le D(X)=D_H.                            \tag{23}
\]

Because ((X,\mu)) lies in the hull, ((R,\mu)) lies in the carrier, and
(D(R)\le D(X)), law-tightness puts ((R,\mu)) in the hull.  Hull minimality
and (23) force (D(R)=D_H), so ((R,\mu)\in\mathcal M).  The dispatch's
absorbing dynamic alternative would give an exact cap prefix in the hull with
debt strictly below (D_H), impossible.  Hence its all-Continue fixed-face
alternative holds, while its reset, incidence, transfer, and supported-toggle
fields remain intact.  This is reset-rigid incidence.

It remains to suppose that (J_o(\mu)=0) for every (o\in Z).  Every
coordinate incidence is nonnegative, so every (I_{o,j}(\mu)) with
(o\in Z) and (j\ne o) is zero.  If a finite coalition (T) has positive
law mass, then (T) cannot contain a player distinct from (o); otherwise
that player's incidence coordinate would be positive.  Since (T) is
nonempty, (T=\{o\}).

The retained atom (8) gives at least one positive finite atom.  If two
distinct owners (o,o'\in Z) existed, the same positive finite atom would
have to equal both ({o}) and ({o'}), a contradiction.  Hence
(Z=\{o\}), and simplex normalization gives (14) for
(p=\mu(\operatorname{some}\{o\})>0).

### 4. Correct singleton/Never cap-tight lemma

We prove the generic lemma used in the last chamber.

> If ((X,\mu)\in\mathcal C),
> (mu=p\delta_{\operatorname{some}\{o\}}+
> (1-p)\delta_{\operatorname{none}}) with (p>0), and (d_o(X)=0), then
> (X.2_o=r_o(\{o\})).

The carrier is a closed subset of a finite-dimensional metrizable space and
is the closure of actual semantic/outcome-law points.  Therefore there is a
sequence of actual behavioral profiles (sigma_n) such that

\[
 \bigl(
   \operatorname{quittingTerminalSemanticPair}(r,\sigma_n),
   \operatorname{quittingTerminalOutcomeMass}(r,\sigma_n)
 \bigr)\longrightarrow(X,\mu).                      \tag{24}
\]

This is the required closure-sequence step; the limiting carrier point itself
need not be executable.

Let (N_{n,i}) be player (i)'s Never probability in (sigma_n), and put
(F_{n,i}=1-N_{n,i}).  Joint Never is the product of marginal Never
probabilities, so

\[
 \prod_iN_{n,i}\longrightarrow1-p.                  \tag{25}
\]

The terminal reward-moment identity on the carrier gives

\[
 X.1_o=p\,r_o(\{o\}).                                \tag{26}
\]

Since (d_o(X)=0),

\[
 X.2_o=p\,r_o(\{o\}).                                \tag{27}
\]

If (p=1), (15) follows immediately.  Suppose (0<p<1).  Choose
(\kappa>0) such that for all sufficiently large (n), the product in (25)
is at least (kappa).  Since every (N_{n,i}\le1), every individual
(N_{n,i}) is then at least (kappa).

Fix (j\ne o).  The limiting law gives

\[
 \Pr_{\sigma_n}(\text{terminal coalition }\{j\})\longrightarrow0. \tag{28}
\]

Independent behavioral randomization on the unique live history gives the
**one-sided cylinder inequality**

\[
 \Pr_{\sigma_n}(\text{terminal coalition }\{j\})
 \ge
 F_{n,j}\prod_{k\ne j}N_{n,k}.                       \tag{29}
\]

Indeed the event on the right says that (j) stops finitely and every other
player Never stops, which is a subset of the terminal-singleton event.  It is
not generally the whole singleton event: another player can have a later
counterfactual finite stopping time after (j) has already ended the game.
This corrects the false equality in the source note.

The product in (29) is eventually at least
(kappa^{|I|-1}>0).  Equations (28)--(29) therefore imply

\[
 F_{n,j}\longrightarrow0qquad(j\ne o).              \tag{30}
\]

Let (M\ge0) satisfy (|r_i(T)|\le M) for every terminal coalition and player.
If owner (o) deviates
to Quit at date zero, the payoff differs from (r_o(\{o\})) only if some
opponent also quits at date zero.  By the union bound this event has
probability at most (\sum_{j\ne o}F_{n,j}), so the absolute payoff error is
at most (2M\sum_{j\ne o}F_{n,j}); hence the immediate-Quit value converges
to (r_o(\{o\})).  If owner (o) deviates to Never, a nonzero terminal payoff
requires some opponent to stop finitely, again an event of probability at
most (\sum_{j\ne o}F_{n,j}); its payoff has absolute value at most
(M\sum_{j\ne o}F_{n,j}) and therefore converges to zero.  Each approximating
cap dominates both behavioral deviations, and the cap coordinate in (24)
converges.  Thus

\[
 X.2_o\ge\max\{0,r_o(\{o\})\}.                       \tag{31}
\]

Combining (27), (31), (p>0), and (p<1) gives both
(r_o(\{o\})\ge0) and (r_o(\{o\})\le0).  Hence the singleton reward and
cap are both zero.  This proves (15).

### 5. Binding collision cycle

At (z\in\mathcal M), all Continue is exact cap--Nash, so every singleton
reward is at most the corresponding cap.  Equation (15) makes (o) a binding
coordinate.  The checked theorem
`exists_quittingSingletonCollisionGain_pos_of_unique_allContinue` says that
every binding player (i) has a distinct binding successor (j) satisfying
the strict collision gain in (16).

Choose one such successor for each element of the finite nonempty binding
set.  Iteration of this self-map repeats a vertex.  Removing the preperiod and
choosing a first repetition produces a directed cycle.  No successor is a
self-loop, so the cycle has length at least two.  This completes the strict
trichotomy.

## Conjecture-facing change

The theorem removes one exact analytic obstruction: repeated off-minimum
positive cap-root descent no longer needs a chosen infinite chain, a uniform
absorption floor, or continuity of root selection.  Closing simultaneously
under exact prefixes, compact limits, newly appearing exact roots, and
downward same-terminal-law replacements produces one minimum face.  Every
positive root is consumed before minimization; the only strict output is the
typed neutral passport above.

For the Fin4 hard residual, equality with the global minimum regenerates a
causal source at the same hull point.  Strict inequality is reduced to the
three stated neutral chambers.

This does **not** answer
[`FIN4_ACTUAL_PAID_CAP_DESCENT_OR_INERT_STALL.md`](../questions/FIN4_ACTUAL_PAID_CAP_DESCENT_OR_INERT_STALL.md)
or
[`FIN4_MINIMUM_RETURN_CAPSTONE.md`](../questions/FIN4_MINIMUM_RETURN_CAPSTONE.md),
because those questions require preservation of an actual paid chronology and
complete post-row behavioral tail.  The hull retains only terminal semantics,
the terminal coalition/Never law, and the selected atom inequality.  A final
export decision must therefore treat this packet as a strict carrier-level
reduction, not as the requested source-preserving consumer.

## Exact remaining consumer

For the particular source-tagged origin and retained atom supplied by an
application, the packet leaves exactly the following alternative.

> Prove (D_H=D_*), or consume the strict passport described in Theorem B to
> produce an actual behavioral profile whose total unrestricted terminal debt
> is strictly below (D_*).

The latter output contradicts the defining global debt floor, so either route
eliminates the strict branch for that supplied seed.  This packet does not
claim the much stronger statement that every arbitrary positive-atom carrier
origin in a hard-residual game must have (D_H=D_*).

A quantitatively stronger sufficient consumer would show that every strict
passport and every (\varepsilon>0) produce an actual behavioral profile
(\sigma_\varepsilon) with

\[
 \sum_i\bigl(
   \operatorname{quittingContinuationBestResponseValue}
      (r,\sigma_\varepsilon,i)
   -\operatorname{quittingTerminalPayoff}
      (r,\sigma_\varepsilon,i)
 \bigr)<\varepsilon.                                \tag{32}
\]

The summands in (32) are the unrestricted behavioral-deviation debts.  Taking
(\varepsilon<D_*) would supply the required contradiction.  Neither this
quantitative consumer nor any chamber-specific strict-passport consumer is
currently checked.

Equivalently, one must do at least one of:

1. consume the full-positive-debt chamber using hard-residual table signs or
   source chronology;
2. turn the reset-rigid supported toggle into a history-compatible law change
   or total-debt decrease; or
3. transport the singleton/Never binding cycle into a source-compatible
   pair/collision block before the atom escapes the controlled chronological
   window.

No current checked declaration supplies any of these three transitions.

## Probability, information, and strategy-class audit

Before absorption a quitting game has one live public history at every date.
A unilateral behavioral replacement is therefore represented by an arbitrary
hazard sequence, including Never and arbitrarily late randomized stopping.
The semantic cap coordinate is the supremum over all such replacements.  The
exact cap--Nash prefix identities used here retain this unrestricted cap.

Players' behavioral randomizations are independent.  This is used only in the
cylinder product (29) and in the checked product-root laws.  The proof never
conditions a cap on a zero-probability event and never interchanges a supremum
with a limit.  In the singleton/Never lemma, two fixed deviations are evaluated
on every approximating actual profile; only afterward are their lower bounds
passed to the convergent cap coordinate.

The hull point and strict neutral passport are carrier objects, not necessarily
actual strategies.  No terminal or uniform equilibrium is claimed for them.

## Boundary tests

1. If (D_*=0), a minimum-face exact root may absorb while preserving zero
   debt, and (8) loses its positive atom floor.  Positive debt is essential.
2. If (b_0=0), the invariant cone retains no atom.
3. Approximate cap--Nash roots do not satisfy (19)--(20) exactly; an error
   ledger would be needed.
4. Nash against the prescribed coordinate does not imply exact scaling of
   unrestricted cap debt.  Conversely, the cap--Nash conclusion here does not
   activate prescribed-payoff plateau theorems.
5. Same terminal-outcome law does not mean equal stopping-time laws, equal
   marked dates, total-variation closeness, or common source ancestry.
6. The lower direction in law-tightness preserves the atom cone; an upward
   same-law closure need not.
7. A newly appearing positive exact root at a limit point is not a problem:
   intersection invariance applies that root at the limit point itself.
8. In (29), equality is false in general.  The lower bound is the exact
   direction needed to force outsider finite stopping probabilities to zero.
9. The binding cycle may live in a component reached after a preperiod and
   need not contain the original zero-debt owner.

## Source correspondence and novelty

Checked ingredients:

- `quittingTerminalSemanticLawCarrier_isCompact`,
  `terminalSemanticLawCarrier_fst_mem_carrier`,
  `terminalSemanticLawCarrier_mass_mem_stdSimplex`,
  `terminalSemanticLawCarrier_rewardMoment`, and
  `quittingTerminalSemanticLawPrefix_mem_carrier` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
- `eq_quittingAllContinueRoot_of_continueMass_eq_one` in
  `UniformEquilibrium/Quitting/Boundary/Analytic/SeamPriceResidual.lean`;
- `finFourHardResidual_minimumLaw_causalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- `FinFourMinimumAtomProducer` and
  `FinFourMinimumAtomProducer.exists_residual_eq_of_hardResidual` in
  `Research/Quitting/FinFourProducerAtlas/Source.lean`;
- `QuittingTerminalExploitabilityWitness.exists_fixedLaw_resetFace_dispatch`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`;
- `quittingTerminalTotalOpponentIncidenceMass` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceRatio.lean`;
- `exists_quittingSingletonCollisionGain_pos_of_unique_allContinue` in
  `Research/Quitting/BindingCollisionGainPositivity.lean`; and
- `quittingTerminalSemantic_allContinuePlateau_finiteRewardObstruction` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllContinuePlateau.lean`,
  inspected as a non-applicable theorem requiring Nash against the prescribed
  coordinate.

The checked source contains one-step exact-prefix descent and compact carrier
machinery, but no declaration forming the smallest closed law-tight invariant,
minimizing debt on it, or proving unique cap-root neutrality simultaneously
after all discontinuously appearing roots.  That saturation theorem is the
new content.  No literature theorem is invoked.

The same-point equality arm is stronger than merely invoking
`FinFourMinimumAtomProducer.exists_residual_eq_of_hardResidual`, which already
selects some minimum source: the new arm causalizes the particular retained
hull point.  The strict arm is a reduction, not a semantic consumer.

## Lean handoff

Suggested generic definitions and declarations:

```text
IsQuittingLawTightCapNashInvariant
quittingLawTightCapNashSaturationHull
quittingLawTightCapNashSaturationHull_isCompact
quittingLawTightCapNashSaturationHull_prefix_mem
quittingLawTightCapNashSaturationHull_sameLaw_of_debt_le
quittingLawTightCapNashSaturationHull_atomCone

structure QuittingLawTightCapNashSaturationPassport where
  hull
  origin_mem
  hull_compact
  prefix_mem
  sameLaw_of_debt_le
  atomCone
  minimumPoint
  minimum
  lawFibreMinimum
  exactRoot_iff_allContinue
  allContinue_prefix_eq
  absorption_le_debtDistance_div
```

The invariant family should quantify over ambient-closed subsets of the joint
carrier.  The atom cone should be proved to be one such invariant and then
inherited by intersection minimality.  Do not define the hull merely as the
closure of finite descendants: that form does not automatically handle a new
exact root appearing at a limit cap.

Suggested Fin4 declarations:

```text
finFourLawTightSaturation_minimumProducer_or_strictPassport
exists_positive_opponentIncidenceCoordinate_of_total_pos
terminalSemanticLaw_soloNever_zeroDebt_cap_eq_solo
finFourStrictSaturation_fullDebt_or_resetRigid_or_soloNeverCycle
```

For `terminalSemanticLaw_soloNever_zeroDebt_cap_eq_solo`, first extract the
approximating profile sequence from closure in the finite-dimensional metric
space.  Use a stopping-law cylinder inequality, not equality.  The immediate-
Quit and Never deviation bounds should be stated quantitatively using a
common reward bound and the finite union bound.

The Fin4 strict passport must store the original hard residual and the global
minimum source used by the reset dispatch.  It must not store the desired
terminal consumer as a field.

## Scope and nonclaims

- No theorem here proves a uniform-equilibrium payoff.
- No hull point is asserted to be an actual behavioral profile.
- No stopping-time tightness, strategic total-variation compactness, or
  ancestry-preserving decoder is produced.
- No paid row, prescribed-payoff Nash root, Bellman return, or admissible
  payoff gain is inferred from cap-root neutrality.
- The same-point equality arm does not identify its causal atom with the
  originally retained coalition (S_0).
- The strict trichotomy is not an exhaustive normal form for all Fin4
  quitting games; it classifies points produced by this strict saturation
  branch.
- The local regression tables from the source note are deliberately omitted.
  They are boundary evidence, not part of this standalone theorem.
