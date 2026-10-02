# Robust join cycles are persistent-base equilibrium producers

## Status

Independent proof audit: **PASS**.  The maximal producer statement below is
valid for every finite player type.  It is a direct adapter to the checked
persistent-base arbitrary-completion compiler.  Its directed-cycle and strict
counterexample-side corollaries are also valid.

This note is an audit, not an export packet and not a Lean-checked addition.

## 1. Exact question

Let `I` be a finite player set and let

\[
r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting-game reward table.  Extend notation only by writing rewards of
the displayed nonempty coalitions; no reward at the empty coalition is used.

For distinct players \(e,j\), define the robust join relation \(e\unrhd j\)
by

\[
  e\unrhd j
  \quad\Longleftrightarrow\quad
  \forall T\subseteq I\setminus\{e,j\},\qquad
  r_j(T\cup\{e,j\})\ge r_j(T\cup\{e\}).                 \tag{1}
\]

Let \(C\subseteq I\) satisfy \(|C|\ge2\), and assume that every \(j\in C\)
has a distinct predecessor \(e\in C\) with \(e\unrhd j\).

The claim audited is:

1. \(C\) satisfies `QuittingPersistentBaseComplementLeaveSafe r C`;
2. the game has a stationary profile which is exact terminal Nash against
   every unilateral behavioral deviation; and
3. the resulting terminal payoff is a uniform-equilibrium payoff.

The directed-cycle specialization takes \(C\) to be the vertex set of a
simple directed cycle of \(\unrhd\).

## 2. Source audit

I inspected

`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseArbitraryCompletionEscape.lean`.

The relevant checked declarations are:

* `QuittingPersistentBaseComplementLeaveSafe`;
* `quittingPersistentBaseRoot_endpointDifference_nonneg_of_complementLeaveSafe`;
* `exists_quittingPersistentBaseCertificate_of_complementLeaveSafe`;
* `QuittingPersistentBaseCertificate.isZeroAsymptoticNash`; and
* `exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe`.

The last theorem accepts a finite base of cardinality at least two and the
pointwise complement-leave-safe inequality, chooses a mixed Nash equilibrium
of the induced finite Boolean game on the complementary players, and returns
both exact terminal Nash against the full behavioral strategy class and a
uniform-equilibrium payoff.

The new mathematical content is only the finite table adapter from (1) to
`QuittingPersistentBaseComplementLeaveSafe`, plus its graph corollaries.  It
does not introduce a new terminal compiler.

## 3. Robust predecessors imply complement leave safety

Fix \(j\in C\), and choose a distinct \(e\in C\) with \(e\unrhd j\).  Let

\[
  Q\subseteq I\setminus C
\]

be an arbitrary complementary completion.  Define

\[
  T=(C\setminus\{e,j\})\cup Q.                         \tag{2}
\]

Because \(e,j\in C\), \(e\ne j\), and \(Q\cap C=\varnothing\), one has

\[
  T\subseteq I\setminus\{e,j\}.                       \tag{3}
\]

The two terminal coalitions in (1) are then exactly

\[
  T\cup\{e,j\}=C\cup Q,                               \tag{4}
\]

and

\[
  T\cup\{e\}=(C\setminus\{j\})\cup Q.                \tag{5}
\]

Since \(|C|\ge2\), the coalition in (5) is nonempty.  Therefore (1), applied
to the particular background (2), gives

\[
  r_j((C\setminus\{j\})\cup Q)
  \le r_j(C\cup Q).                                    \tag{6}
\]

This is precisely the `QuittingPersistentBaseComplementLeaveSafe r C`
inequality for player \(j\) and completion \(Q\).  Both were arbitrary, so
the predicate holds.

Applying
`exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe` now gives
the asserted stationary exact terminal Nash profile and uniform-equilibrium
payoff.

No compactness, chronology, punishment-floor, terminal-gap, or residual
hypothesis is used.

## 4. Behavioral-strategy audit

The constructed stationary row makes every member of \(C\) Quit surely at
date zero.  Since \(|C|\ge2\), after any one player changes their complete
behavioral strategy, at least one unchanged member of \(C\) still Quits at
date zero.  Hence absorption occurs at date zero even under the deviation.

For a base player \(j\), every behavioral deviation is payoff-equivalent to
one mixed date-zero choice between Quit and Continue.  Conditional on any
simultaneous quit set of the complementary players, (6) makes prescribed Quit
weakly optimal.

For a complementary player, the same sure-exit fact reduces every behavioral
deviation to its date-zero Quit probability.  The complementary players'
prescribed mixed actions form a Nash equilibrium of the induced finite
Boolean game, so no such deviation is profitable.

Thus the unrestricted behavioral conclusion is genuine.  It is not merely a
stationary-, pure-, finite-time-, or bounded-controller Nash statement.

## 5. Directed-cycle corollary

Let

\[
  e_0\unrhd e_1\unrhd\cdots\unrhd e_{m-1}\unrhd e_0,
  \qquad m\ge2,                                        \tag{7}
\]

be a simple directed cycle.  Set \(C=\{e_0,\dots,e_{m-1}\}\).  Every cycle
vertex has its preceding cycle vertex as a distinct robust predecessor.
Section 3 therefore applies.

Consequently, in any finite quitting game with no uniform-equilibrium payoff,
the robust join digraph is acyclic.  This is the strongest clean
counterexample-side graph screen: it is not restricted to four players or to
a selected collision map.

## 6. Strict collision-map reversal

Assume additionally that the game has no uniform-equilibrium payoff.  Let
\(f:I\to I\) be any map, and suppose a simple directed cycle of \(f\) is

\[
  e_0\mapsto e_1\mapsto\cdots\mapsto e_{m-1}\mapsto e_0. \tag{8}
\]

Suppose each selected empty-background join increment is strictly positive:

\[
  r_{e_{t+1}}(\{e_t,e_{t+1}\})
  -r_{e_{t+1}}(\{e_t\})\ge\gamma>0.                   \tag{9}
\]

If every edge of (8) satisfied the robust inequalities (1), Section 5 would
produce a uniform-equilibrium payoff, contradiction.  Hence some edge
\(e_t\mapsto e_{t+1}\) and some background

\[
  T\subseteq I\setminus\{e_t,e_{t+1}\}
\]

satisfy the strict reversal

\[
  r_{e_{t+1}}(T\cup\{e_t,e_{t+1}\})
  <r_{e_{t+1}}(T\cup\{e_t\}).                         \tag{10}
\]

The inequality is strict because it is the negation of the weak robust
inequality.  The background is nonempty because (9) rules out \(T=\varnothing\).

For `Fin 4`, a fixed-point-free map always has a simple cycle of length two,
three, or four.  On a cycle selected from a positive terminal-gap collision
map, (9) is supplied with the terminal gap.  Therefore some selected cycle
edge has either:

* a strict pair-to-triple reversal, when \(|T|=1\); or
* a strict triple-to-grand reversal, when \(|T|=2\).

This strictly strengthens the earlier weak `<= 0` cancellation screen.  The
strictness comes from negating the new weak robust relation, not from the old
sure-quitting propagation argument.

## 7. Boundary tests

### Weak equality

Equality in (1) is allowed and sufficient.  The relevant base player is
indifferent on that terminal background, which is compatible with exact
Nash.  Therefore replacing `>=` by `>` would unnecessarily weaken the
producer.  Conversely, the strict counterexample-side reversal in (10)
depends on defining the robust relation with `>=`.

### Two-cycle

For \(C=\{e,j\}\), the background used in Section 3 is simply the arbitrary
outsider completion \(Q\).  The two robust edges make both sure quitters
leave-safe for every outsider action.  One quitter remains after either
player deviates, so the unrestricted behavioral reduction is still exact.

### Empty free set

If \(C=I\), the induced complementary game has no effective player choices.
The all-base-Quits row is exact terminal Nash: after any unilateral deviation,
another base member quits immediately, and (6) makes Quit weakly optimal for
the deviator.

### Arbitrary outsider rewards

No sign or bound is imposed on any outsider payoff coordinate.  The induced
finite Boolean game always has a mixed Nash equilibrium, and sure exit by the
base makes that one-shot equilibrium control arbitrary later behavioral
plans.

### Non-simple closed walks

Only a simple directed subcycle is needed.  Every finite directed closed walk
contains one, and using the subcycle as the persistent base avoids repeated
labels and preserves the distinct-predecessor requirement.

### Necessity is not claimed

A game may have an exact terminal Nash or a uniform-equilibrium payoff without
any robust join cycle.  The theorem is a sufficient architecture and an
acyclicity condition for a counterexample, not a characterization of
existence.

## 8. Lean-facing shape

The narrow adapter can be organized as follows.

```lean
def QuittingRobustJoin
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (blocker receiver : ι) : Prop :=
  blocker != receiver /\
    forall background,
      background \subseteq Finset.univ \ {blocker, receiver} ->
      quittingSetReward reward (background \cup {blocker}) receiver <=
        quittingSetReward reward (background \cup {blocker, receiver}) receiver

theorem complementLeaveSafe_of_robustPredecessors
    (hcard : 2 <= base.card)
    (hpred : forall receiver \in base,
      exists blocker \in base, QuittingRobustJoin reward blocker receiver) :
    QuittingPersistentBaseComplementLeaveSafe reward base

theorem exists_exactTerminalNash_and_uniformPayoff_of_robustPredecessors
    ... :
    exists point ..., IsZeroAsymptoticNash ... /\ IsUniformEquilibriumPayoff ...
```

The proof of the first theorem is the set identity (2)--(5).  The second is a
single application of
`exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe`.

A graph-cycle wrapper should encode a finite list or `Fin m`-indexed simple
cycle and obtain `hpred` from predecessors.  The counterexample-side theorem
should accept either `not IsUniformEquilibriumPayoff` directly or a checked
terminal exploitability witness, and should state the strict nonempty
background reversal separately.

## 9. Verdict

**PASS, with maximal scope as stated above.**  The theorem has an actual-data
adapter (a finite table predicate or directed-cycle test), uses the existing
all-behavior semantic consumer, and gives a new arbitrary-player existence
class.  The only important calibration is that the equilibrium mechanism is
the already checked persistent-base arbitrary-completion compiler; the new
content is the robust-join graph adapter and the strict acyclicity/reversal
screen.
