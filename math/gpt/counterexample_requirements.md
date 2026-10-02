A hypothetical four-player counterexample is now constrained by a surprisingly long list. Here is the strongest nonredundant
consolidation.

I’ll use:

- “checked” for kernel-checked Lean results;
- “Research-checked” for checked declarations in the tentative atlas architecture;
- “pending” for reviewed ordinary mathematics not yet fully formalized.

## 1. Global semantic requirements — checked

A counterexample must admit one constant (\gamma>0) such that every behavioral profile has some player with deviation gain at least
(\gamma). This covers unrestricted behavioral deviations, including Never and arbitrarily late stopping.

Equivalently:

- the infimum of terminal exploitability is positive;
- the compact terminal-semantic carrier has a minimum (D_*>0) of total debt;
- no terminal (\varepsilon)-Nash profile exists for (\varepsilon<\gamma);
- hence there is no exact terminal Nash profile, stationary or otherwise.

The minimum is literal: finite-clock product profiles are dense in the complete semantic carrier, and the finite-clock infimum equals the
full behavioral infimum. Thus a counterexample cannot hide solely in infinite-support strategies.

## 2. It can be taken rational and finitely certified — checked

If any real Fin4 counterexample exists, reward robustness produces a normalized rational counterexample.

Moreover, counterexamples are recursively enumerable:

- enumerate normalized rational Fin4 tables;
- enumerate scales and exact rational lower certificates;
- if a counterexample exists, the search eventually returns a finite certificate proving a positive unrestricted exploitability gap.

This is a semidecision, not a decision procedure: nontermination proves nothing.

So an actual counterexample has a finite rational avatar and an eventually discoverable exact certificate, even though we do not know the
required table or search scale.

## 3. Full hard-residual matrix geometry — checked

Every Fin4 counterexample lies in the quantitative full-support hard residual. In particular:

- all four players belong to the normal core;
- every player is punishment-normal;
- the normalized singleton matrix is standard-(Q);
- it has no homogeneous solution of the excluded kind;
- the full matrix is not projective-(\bar Q);
- some proper principal submatrix of cardinality exactly two or three is nonprojective-(Q);
- there is a full-support normalized singleton packet with explicit weight floor
  [
  \frac{1}{1+6R/\gamma},
  ]
  where (R) bounds the rewards.

Thus none of the already-consumed projective-(\bar Q), homogeneous, or smaller easy matrix chambers can contain a counterexample.

## 4. Every singleton has a full-gap collider — checked

For every player (j), there is some (o\ne j) such that

[
r_o({j,o})\ge r_o({j})+\gamma.
]

Equivalently, every pure singleton row has a distinct player who gains at least the full terminal gap by joining the collision.

These choices can be packaged as a fixed-point-free map on the four players. A counterexample therefore cannot have strategically isolated
singleton outcomes.

## 5. Every minimum law contains a positive finite atom — checked

Take any globally minimum joint semantic/law point. Its terminal law assigns positive mass to some nonempty finite quitting coalition.

Furthermore, this same point has a source-faithful causal realization by actual behavioral profiles:

- the semantic pairs converge to the selected minimum;
- their terminal laws converge to the selected law;
- the selected atom occurs at literal finite dates;
- arbitrarily deep exact cap–Nash prefixes can be retained.

But the atom need not become current root absorption. It may survive entirely in a remote suffix while all marginal stopping laws converge
weakly to literal Never. This “relative-timing bubble” is a genuine allowed feature of a counterexample.

## 6. The six entrance leaves have collapsed — Research-checked

The original source-preserving Fin4 atlas had six producer leaves. The following have been eliminated or merged:

- diffuse singleton atoms are compressed into fixed-mass one-date singleton endpoints;
- nonsingleton atoms cannot remain temporally diffuse;
- both same-stage monodromy leaves are impossible;
- quantitative tail escape contracts to the same concentrated endpoint class.

Every surviving minimum-atom source now produces a literal source-attached singleton endpoint and then a forced pure pair.

After subsequence stabilization, one has fixed players (j,o,p) and cofinally many actual rows with:

- the same pair ({j,o});
- a fixed positive reached-mass floor;
- zero marked defect for (o);
- positive marked defect for (p);
- an actual unilateral paid endpoint move by (p);
- exact subtraction of (p)’s debt;
- unchanged post-date behavioral tail;
- the original minimum-law provenance.

Thus a counterexample cannot avoid producing paid, fixed-resolution behavioral geometry.

## 7. Its source chronology has only two atlas-level terminal modes — Research-checked

The maintained completion atlas has contracted to:

1. uniform escape: the actual post-mark tail stays a fixed amount above (D_*);
2. minimum return: the post-mark tail debt converges to (D_*).

The former singleton, nonsingleton, diffuse, and monodromy alternatives are no longer independent terminal components.

This is an atlas normal form, not yet a proof that either terminal mode is consumable.

## 8. Every exact infinite spine has summable clocks — checked

For every canonical exact Nash–Bellman spine in a counterexample, every player’s marginal Quit-hazard series is summable:

[
\sum_t q_{t,i}<\infty
\qquad\text{for every }i.
]

Why:

- two nonsummable player clocks activate the checked chronological consumer;
- exactly one nonsummable clock activates the punishment-normal singleton compiler.

Both would yield a uniform payoff.

Consequently, no counterexample admits an exact spine with even one persistent Quit clock.

Its exact spines asymptotically become all-Continue phantoms: their late roots approach all Continue, while the semantic state may retain
positive debt.

## 9. Finite exact-block hazard capacity is uniformly bounded — newly checked

This is stronger than merely saying that each infinite spine is summable.

There exists a finite constant (H), depending on the table, such that every finite exact Nash–Bellman block in the canonical reward box
satisfies

[
\sum_{t< L}\sum_{i<4}q_{t,i}\le H.
]

This holds uniformly over:

- every block length (L);
- every legal exact block;
- every choice of annotations inside the canonical box.

If this capacity were unbounded, compact near-return extraction plus the one-persistent/two-persistent compilers would produce a uniform-
equilibrium payoff.

The theorem is existential: it does not presently give a useful numerical formula for (H).

This is a major restriction. A counterexample cannot accumulate arbitrary exact hazard before returning through a compact state space.

## 10. Exact positive-root prefixing is Zeno-like

Along an exact cap–Nash prefix orbit:

- every debt coordinate scales by the same continuation factor;
- marked paid gains and inherited suffix atoms scale by corresponding survival factors;
- if debt remains above (D_*>0), total prefix absorption is summable;
- the support and normalized proportions of debt can remain unchanged.

Therefore exact prefixing cannot supply a persistent charge source. It either returns toward the minimum or converges to an inert all-
Continue port with positive debt.

A counterexample must exploit precisely this Zeno possibility: infinitely much semantic restructuring with only finite total absorption.

## 11. Minimum-return debt can be killed exactly, but may leak sideways — pending formalization

The recent direct best-response handoff strengthens the minimum-return branch.

For some fixed payer (p):

- the source has (d_p) bounded positively away from zero;
- replacing (p)’s entire post-mark strategy by a near-best response gives actual positive payoff gain;
- the target satisfies (d_p\to0);
- the other players and upstream source atom remain attached.

At the limit:

- if the target remains on the minimum fibre and no inactive debt coordinate becomes positive, positive-debt support strictly decreases;
- otherwise the construction produces a (p)-zero, strictly off-minimum endpoint.

The unresolved mechanism is cross-coordinate cap leakage: eliminating (p)’s debt may create debt for another player. A counterexample must
perpetually use this leakage to avoid a renewable finite support descent.

## 12. The surviving off-minimum object is extremely inert — partly checked, partly pending

The present strict residual is approximately:

- one killed player (p) with (d_p=0);
- total debt strictly above (D_*);
- a retained positive law atom or upstream causal passport;
- exact cap-root saturation;
- ultimately an all-Continue neutral root, often uniquely;
- finite total exact absorption;
- no charged return to a fixed minimum point;
- no renewable support drop.

The upstream atom and the downstream inert cap port may be different chronological objects. That separation is crucial: the atom cannot
simply be treated as absorption available at the inert root.

The new saturation-hull work says that exact root saturation either returns to the minimum fibre or produces an even more rigid strict
inert passport. Its remaining strict chamber is not yet consumed.

## 13. Post-mark mass has an exhaustive residual split — ordinary mathematics

If the actual post-mark continuation contains nonsingleton terminal mass bounded below, collision anti-diffusion produces a literal later
row with fixed mass.

That row gives one of:

- a paid same-witness renewed row;
- a definite off-minimum tail escape;
- or, if no such nonsingleton mass exists, singleton/Never diffusion.

So the counterexample cannot indefinitely hide positive nonsingleton mass in individually negligible dates. Only singleton clocks and
Never mass can remain genuinely diffuse.

## 14. Many tempting identifications are formally ruled out

A viable counterexample may rely on all of these separations:

- terminal-law mass is not current root absorption;
- a paid horizontal endpoint move is not an exact chronological edge;
- fixed-law minimality says nothing about law-changing directions;
- semantic proximity does not control all players’ unrestricted caps;
- eliminating one player’s debt does not prevent support entry elsewhere;
- a pure same-stage cycle is not a temporal cycle;
- compact limits can lose relative timing and actual behavioral realization;
- a positive exact root at a cap does not by itself satisfy the payoff fixed-point equation required for a stationary equilibrium;
- all-Continue exactness does not automatically imply uniqueness.

These are no longer merely warnings; several have exact regression or no-go theorems.

## The current composite picture

A Fin4 counterexample would have to be an extraordinarily rigid inert machine:

1. It has a fixed positive all-behavior exploitability gap.
2. It lies in the full-support, punishment-normal, nonprojective hard matrix chamber.
3. Every minimum law has a positive causal finite atom.
4. That atom generates fixed-mass forced-pair rows and genuine paid behavioral deviations.
5. Every exact spine nevertheless has only summable player clocks.
6. All finite exact blocks have one common finite hazard-capacity bound.
7. Exact prefixing spends only finite total absorption.
8. Every paid debt elimination is offset by cap leakage, off-minimum escape, or support entry.
9. No iteration yields a fixed charged return, terminal approximants, or renewable support descent.
10. Its strict limit is an all-Continue inert port while its useful atom remains chronologically elsewhere.
11. Yet the entire configuration must be realizable by one rational reward table and would eventually admit a finite exact positive-gap
    certificate.

No table satisfying all of this is known. Existing regression examples realize selected pieces—unique all-Continue roots, debt circulation, Zeno absorption, cap leakage—but all have an equilibrium somewhere else.
