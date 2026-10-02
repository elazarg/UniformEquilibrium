# Review of Proposition 6BK and Theorems/Corollaries 6BK.1--4

Reviewer: `CODEX_EULER`

Verdict: **PASS after two applied bounded proof-writing repairs.**  The
strategic finite-net Nash theorem, behavioral realization of mixed stopping
laws, reward-dependent pseudometric estimate, total-variation criterion, and
late-finite-mass conclusion are mathematically correct.  The result is a
valid universal no-go for the precisely defined strategically precompact
watchdog architecture, not a reward-table producer.

## Exact repairs

1. In Corollary 6BK.2, some selector ranges `D_i` may be empty, whereas
   Theorem 6BK.1 assumes a nonempty family for every player.  Before applying
   the theorem, enlarge every empty `D_i` by one arbitrary behavioral law.
   Singleton additions are totally bounded and impose no selector condition,
   so the contradiction is unchanged.  Then the conclusion that at least one
   **nonempty original** selector range is not strategically totally bounded
   follows.
2. In Corollary 6BK.3, failure of uniform tightness gives

   ```text
   exists eps0>0, forall finite A, sup_(mu in D) mu(A^c) >= eps0.
   ```

   The supremum need not be attained.  Choose `kappa=eps0/2`; then for every
   `A_N={0,...,N,infinity}` there exists `mu in D` with
   `mu(A_N^c)>=kappa` (indeed `>kappa`).  This proves (6BK.7) without an
   attainment assumption.

## Finite-net Nash argument

For each strategically totally bounded nonempty `D_i`, choose a finite
`eps`-net `F_i subset D_i`.  Nash's theorem applies to the finite normal-form
game with pure strategies `F_i` and exact quitting-game expected payoffs.
Independently sampling one behavioral stopping law from each player's mixed
equilibrium, and then using its private randomization, produces independent
marginal mixtures of quit-time laws.  A mixture of probability laws on
`N union {infinity}` is again a law on that space and has the standard hazard
representation, including zero survival denominators and Never mass.  Thus
the mixed normal-form equilibrium is an ordinary behavioral quitting profile,
not a public-correlated profile.

Multilinearity of expected terminal payoff gives the exact finite-menu Nash
inequalities.  For arbitrary `tau in D_i`, the definition

```text
d_i(tau,f)=sup_(rho_-i) |U_i(tau,rho_-i)-U_i(f,rho_-i)|
```

applied at the constructed opponents transfers those inequalities with loss
`eps`.  The constructed `sigma_i` need not lie in `D_i`, which is allowed by
the all-profile conclusion.  Theorem 6BK.1 is therefore valid for every
`eps>0`.

After the empty-range repair, applying the theorem with `eps<g` proves the
profile-dependent selector obstruction with the stated quantifiers.  Merely
allowing the watchdog to depend arbitrarily on the profile does not help when
the union of its selected laws for each player is strategically precompact.

## Complete precompact reply classes

Theorem 6BK.4 is also **PASS**.  Its completeness hypothesis has the exact
needed pointwise quantifiers: for every player and every arbitrary behavioral
opponent profile, the supremum over `D_i` equals the supremum over all of that
player's behavioral strategies.  Apply Theorem 6BK.1 at any `eps>0`, take the
supremum of (6BK.2) over `D_i`, and substitute this equality.  One obtains

```text
sup_(all behavioral tau_i) U_i(tau_i,sigma_-i)
  <= U_i(sigma)+eps
```

simultaneously for every player.  Thus `sigma` is an unrestricted terminal
`eps`-Nash profile.  Repeating this for every positive `eps` gives exactly the
all-errors hypothesis of the checked declaration
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in
`Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`, and hence
a uniform-equilibrium payoff.  No closure or attainment of either supremum is
needed.

This strengthens the architecture no-go into a genuine special-class
all-behavior existence theorem: strategically precompact **and complete**
reply classes cannot support the requested counterexample.  It remains
conditional on the table admitting such classes and does not assert that the
full behavioral strategy space is precompact.

## Total variation and literal tail escape

Couple two own quit-time laws maximally and use the identical opponent clocks
in both copies.  When the own clocks agree, the first quitting coalition and
payoff agree, including ties and Never.  On the mismatch event, the payoff
difference is at most `2M`.  Hence, with total variation normalized as maximal
coupling mismatch probability,

```text
d_i(mu,nu)<=2*M*TV(mu,nu).
```

Thus TV total boundedness implies strategic total boundedness.

On the countable discrete space `Omega`, TV total boundedness is equivalent to
uniform tightness over finite sets.  The forward proof unions finite
high-mass sets for a finite net.  Conversely, move every law's mass outside a
common finite high-mass set to one fixed point of that set; the modification
is TV-close and the finite-dimensional probability simplex is totally
bounded.  Applying the repaired negation argument to
`A_N={0,...,N,infinity}` gives one fixed player and one `kappa>0` such that a
selected law puts at least `kappa` mass on finite times strictly beyond every
`N`.

The boundary examples are exact: finite/common-horizon/uniformly exponential
families are precompact; hazards tending to zero and the pure-time family are
not.  Adding the isolated Never law does not destroy uniform tightness of an
otherwise uniformly tight family because `infinity` can be included in the
finite tightness set.

## Scope and question correspondence

This is stronger than the finite-watchdog theorem and rules out a precise
universal architecture relevant to `questions/INCENTIVE_GADGET.md`: no family
with strategically totally bounded per-player selector range can certify a
fixed positive gain at every profile.  Any surviving selector must be
strategically nonprecompact; in TV terms, some selected laws carry a fixed
amount of mass arbitrarily far out at finite times.

The theorem does not construct the requested rational reward table, derive
either target pair mass, control the leftover mass, or rule out nonprecompact
best-response architectures.  It is therefore an architecture no-go, not a
solution of the full gadget question.

Both displayed repairs were applied exactly.  No mathematical objection
remains.
