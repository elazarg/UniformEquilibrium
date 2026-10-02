# Review of Proposition 4 in `CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE`

Reviewer: `CODEX_RAMSEY`

## Verdict

**PASS.**  The arbitrary-minimum strictness argument, compact uniformization,
and carrier-complement debt gap are valid.  The last conclusion must retain
the note's semantic-edge scope: the tail is a terminal-semantic carrier pair,
not merely a Bellman payoff vector to which a debt is assigned ad hoc.

## Every minimum pair is strictly singleton-separated

The selected plateau from Proposition 1 has positive globally minimal debt,
so the common minimum value `D_*` is positive.  Same-table punishment
normality is a property of `reward`, not of the selected plateau; hence

```text
P_i <= s_i
```

is available at every other minimum carrier pair `X`.

For arbitrary `X in M_*`, the checked minimum singleton-margin theorem gives

```text
D_* <= X.2_i-s_i.
```

Since carrier debts are nonnegative and sum to `D_*`, `d_i(X)<=D_*`; using
`X.2_i=X.1_i+d_i(X)` gives `s_i<=X.1_i`.  If equality holds, the exact
complementary-debt-plus-slack identity and nonnegativity of both summands give

```text
d_i(X)=D_*,
quittingTerminalSemanticSingletonSlack reward X i=0.
```

Equivalently, `i` is the unique debt gate; nonnegative debts summing to
`D_*` give `d_j(X)=0` for `j!=i`.  Thus `X,i` supplies the full
`QuittingSingletonTightMinimumFace` data, not only its owner equality.

The controlled-rate argument from Proposition 1 is uniform in the sense
needed here.  With `G=quittingSingletonCollisionGainMax reward i>=0`,

```text
q=D_*/(2(D_*+G))
```

is positive, at most one, and at most `D_*/(D_*+G)`.  The checked controlled
solo endpoint theorem and singleton-tight punishment theorem therefore give
`s_i<P_i`, contradicting same-table normality.  No property special to the
originally selected plateau is used.  Hence every `X in M_*` and every
player satisfy `s_i<X.1_i`.

## Compact minimum projection and root tube

The terminal-semantic carrier is compact and the debt sum is continuous, so
`M_*` is a nonempty compact closed subset.  The finitely many continuous
functions

```text
X |-> X.1_i-s_i
```

are strictly positive on it.  Their minimum over `M_* x Fin 4` is therefore
a single `delta_*>0`; the simultaneous four-player inequality is justified.

Every `X in M_*` is a positive minimum carrier point.  The checked
critical-face theorem says a non-all-Continue exact root against `X.1` must
be solo at a debt gate.  The just-proved strict singleton inequality excludes
every gate, so all-Continue is unique against each projected minimum payoff.

The passage to one open tube is also correct.  A tail within coordinate
distance `delta_*/2` of some projected minimum has every coordinate at least
`delta_*/2` above its own singleton.  Any non-all-Continue exact root selects
a positive-Quit player and the reviewed reverse endpoint estimate gives

```text
absorption(root) >= delta_*/(delta_*+4M)>0.
```

If such roots approached the compact projection, compactness of the minimum
fiber and root simplex would give a convergent pair `(X,q)`; closedness of
exact endpoint Nash and continuity of absorption would make `q` a positive-
absorption exact root against `X.1`, contradicting uniqueness.  Intersecting
with the open coordinate region `V_i>s_i` ensures all-Continue is itself
exact everywhere in the final tube `T_*`.

## Debt moat and edge orientation

The set

```text
C={X in carrier : X.1 notin T_*}
```

is closed in the compact carrier.  It is disjoint from `M_*`.  If nonempty,
continuity of debt gives an attained minimum on `C`; equality with `D_*`
would put that minimizer in `M_*`, a contradiction.  Thus

```text
min_C D-D_*>0.
```

Half this gap is a valid `epsilon_*`.  If `C` is empty, any positive
`epsilon_*` works because every carrier prescription is already in `T_*`.
Consequently `D(X)<D_*+epsilon_*` forces `X.1 in T_*`.

For an exact semantic prefix whose tail pair is this `X`, root uniqueness
makes the root all-Continue.  The checked all-Continue prefix identity (or
its direct prescribed/envelope calculation under exact Nash) makes the
current pair equal to `X`, and its charge is zero.  Contraposition therefore
gives

```text
positive charge => D(tail)>=D_*+epsilon_*.
```

This is correctly oriented at the carrier tail.  It does not assign semantic
debt to an arbitrary payoff-only Bellman tail, nor does it say that a head
near the minimum projection has a local tail.

## Scope

Proposition 4 is a genuine uniform strengthening of Propositions 1--3: it
freezes the entire minimum prescribed projection and prices every charged
exact **semantic** tail by a fixed excess-debt moat.  It still does not
produce a nonlocal charged edge, an exact return, a terminal approximate Nash
profile, or a uniform payoff.

## Corollary 4A addendum

**PASS, but it is a direct application of the already reviewed open-basin
path rigidity and should not be exported as a separate result.**

For a positive-minimum tangent family,
`frontier.source_tendsto` says that the terminal-semantic pairs of the literal
sources converge to `frontier.base`, and the base lies in `M_*`.  Proposition
4 therefore gives either of two uniform entries into `T_*`:

1. openness of `T_*` and prescribed-coordinate convergence put
   `Sem(frontier.source r).1` in `T_*` eventually; or
2. debt convergence gives `D(Sem(frontier.source r))<D_*+epsilon_*`
   eventually, and Proposition 4(3) gives the same conclusion.

Fix one such large rank.  A literal exact-root stack ending at that source has
the repository orientation

```text
current payoff = Succ(later suffix payoff,current root),
current root exact Nash against the later suffix payoff.
```

The terminal tail is in `T_*`.  The finite backward-rigidity theorem from
`OPEN_ALLCONTINUE_BASIN_NO_REENTRY` therefore applies to the whole list at
once: every root is all-Continue and every displayed payoff equals the
terminal source payoff.  Its cutoff is independent of the list length, so
the conclusion is genuinely uniform over arbitrary finite lengths growing
with rank.

The proof written in Corollary 4A is also valid.  Every dropped suffix is an
executable carrier pair; exact-prefix debt monotonicity and global minimality
give

```text
D_* <= D(suffix) <= D(terminal source)<D_*+epsilon_*.
```

Thus every suffix prescription lies in `T_*`, and uniqueness identifies its
preceding root as all-Continue.  Under exact Nash,
`quittingTerminalSemanticPrefix_allContinue_eq_of_isZeroNash` preserves both
coordinates of the semantic pair, not merely the prescribed payoff.  Every
root absorption mass is consequently zero.

The final atom suffix is not thereby made exact Nash: the result says only
that its exact access word is a pure delay.  Likewise an exact charged
semantic realization must have a carrier tail of debt at least
`D_*+epsilon_*`; no charged realization or atom-to-Bellman adapter is
produced.  These scope statements are correct.
