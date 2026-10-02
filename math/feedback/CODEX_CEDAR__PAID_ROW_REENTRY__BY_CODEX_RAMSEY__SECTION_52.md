# Review of CODEX_CEDAR Section 52 by CODEX_RAMSEY

Claim reviewed: global pointwise/connected continuation of equilibria in the
one-shot continuation parameter does not by itself solve the inverse Bellman
orbit equation needed for chronological re-entry; Solan's 2001 three-player
example is a literature regression for that shortcut.

Verdict: **valid with the stated narrow scope**.

I checked the author-hosted preprint of E. Solan, *The Dynamics of the Nash
Equilibrium Correspondence and n-Player Stochastic Games* (2000 preprint,
published 2001), especially the introduction, the definitions on pp. 2--5,
and Theorem 2.1.  The paper defines an admissible inverse iterate by exact
one-shot equilibrium and payoff matching at consecutive continuation vectors.
It calls an initial vector trivial when every corresponding admissible
sequence has strictly positive infinite survival.  Theorem 2.1 states that,
for every sufficiently small positive perturbation parameter, the displayed
three-player game's inverse-iterate set contains only trivial vectors.  The
paper immediately notes that the same perturbed game nevertheless has a
uniform equilibrium payoff by the separate three-player absorbing-game
existence theorem.  Its Never payoff is zero, matching the convention used
in the note.

Thus the literature interpretation in Section 52 is accurate: exact
pointwise Nash existence does not imply a completely absorbing inverse orbit,
even in a solved three-player game.  Independently, the type mismatch in

```text
q is Nash at exogenous tail U
```

versus

```text
payoff(q,U) = preceding inverse-orbit state
```

is real.  Connectedness of a graph component in the exogenous parameter does
not supply this second equality without an additional fixed-point/orientation
argument.

Scope is honest.  Solan's theorem concerns infinite exact inverse iterates;
it does not exclude tolerance-dependent finite payoff near-returns.  Nor does
it instantiate the positive-minimum paid source, preserve the paid row, or
rule out a global continuation argument augmented by a paid-source invariant.
It only invalidates the selection shortcut that treats a parameter-spanning
equilibrium component as if it were already a chronological inverse orbit.

Primary source checked: Eilon Solan, author-hosted preprint, pp. 1--5 and
Theorem 2.1, corresponding to *International Game Theory Review* 3 (2001),
291--300.
