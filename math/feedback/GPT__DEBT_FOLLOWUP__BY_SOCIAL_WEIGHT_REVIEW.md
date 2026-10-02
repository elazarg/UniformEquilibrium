# Audit of `gpt/DEBT.md`, `## Followup`

Reviewer: `SOCIAL_WEIGHT_REVIEW`  
Date: 2026-08-31  
Verdict: **REVISE as a packet; the conditional mathematics is largely
correct.**  It does not repair the original fixed-ray quantifier error
internally and it does not consume the chamber.

## Exact claim

The followup assumes an outer same-source family `A_n,R_n` such that `A_n`
converges to a full-debt global minimum, `A_n` and `R_n` differ only in one
responding player's complete strategy, and that responder's debt on `R_n`
tends to zero.  It then refines the off-minimum/maximal-root branch into:

1. a uniform strict singleton-cap moat and unique all-Continue cap root;
2. a second asymptotically zero debt coordinate;
3. an actually reached root-time curvature fork with fixed labels; and
4. an induced sure-quitter Nash profile yielding either a negative-singleton
   Never wall or a positive-mass member-leaving wall.

It also shows that the source/response curvature survives every finite common
exact-prefix word by a fixed positive factor.

## Valid calculations

The following steps check out.

- Full debt plus the minimum singleton margin gives the strict prescribed
  singleton moat `U_i-s_i>0`.
- If a small-absorption exact cap root has an active label `k`, root
  indifference gives

  \[
  |b^R_{n,k}-s_k|
  \le {2M(1-\chi_{n,k})\over\chi_{n,k}}
  \le {2Ma_n\over1-a_n}\to0.
  \]

  The response label `j` cannot be this `k`, because its cap remains a fixed
  distance above its singleton reward.
- The source/response payoff gap in coordinate `k` is therefore bounded below
  by half the full-debt moat.  The fifteen-outcome averaging argument and its
  `alpha/30` signed-atom constant are correct.
- At an active root, replacing `k`'s current mixed action by pure Quit has
  exact gain `c_n d_k(R_n)`.  Against the source sibling, pure Continue has the
  opposite orientation with the claimed deleted-opponent factor.  At an
  all-Continue root, the corresponding gain is
  `d_k(R_n)-(b^R_{n,k}-s_k)`.  Hence the zero-second-debt/positive-fork split is
  valid after a subsequence.
- For a finite word of roots exact at the successive response caps,

  \[
  U_k(w::A_n)-B_k(w::R_n)
  =P(w)(u^A_{n,k}-b^R_{n,k}).
  \]

  Global minimality gives `P(w)>=D_*/D(R_n)>=D_*/(8M)`, so the
  `alpha D_*/(16M)` passport floor is correct.
- Fixing `k` to Quit and choosing a mixed Nash equilibrium for the other
  three players does make those three unrestricted debts exactly zero.  For
  `k`, pure-time extremality gives exactly

  \[
  d_k(W)=\left[
    p_0\max(0,-s_k)+
    \sum_{A\ne\varnothing}p_y(A)
      (r_k(A)-r_k(A\cup\{k\}))
  \right]_+.
  \]

  Global minimality therefore yields the stated `D_*/2` split, the
  `D_*/14` atomic product, and the `D_*/(28M)` probability floor.
- Appending the two sibling tails behind this sure-`k` root erases their
  prescribed payoff/law difference but retains a one-coordinate cap fork on
  the all-opponents-Continue event.  Inequality (54) is correct.  It should be
  described as conversion into a counterfactual cap fork, not preservation of
  the original terminal-law atom.

## The original quantifier failure is not repaired internally

The prior audit identified the false fixed-orbit inference

\[
D(R^{(m)})\to D_*
\quad\Longrightarrow\quad
d_j(R^{(m)})\to0.
\]

For one fixed ray the actual identity is

\[
d_j(R^{(m)})
= {D(R^{(m)})\over D(R^{(0)})}d_j(R^{(0)}),
\]

so the limit remains positive whenever the initial debt is positive.

The followup avoids this error by **assuming from the outset** an outer family
with `d_j(R_n)->0`.  That is the correct quantifier shape, and current paired
response/maximal-root machinery can supply such data.  But the followup does
not derive that outer family from the fixed ray used in the original answer.
It therefore fixes the mathematics only when read as a conditional consumer
of the already-correct outer packet, not as a repair of the original Section
3 proof.

This distinction should be explicit in any retained version, together with
the exact producer/interface supplying `A_n,R_n` and their common-source
provenance.

## Duplication and novelty

Much of the final sure-quitter normalization is already present in stronger
checked form:

- `persistentBase_inducedNash_free_semantics` in
  `TerminalSemanticFinFourSoloWallDispatch.lean` gives exact unrestricted
  semantics for free players behind a persistent sure-quitting base;
- `singletonBase_inducedNash_floorExcess_semantics` and the stationary
  handoff constructions in
  `LargeBaseStationarySemanticHandoff.lean` already analyze the remaining
  sure owner and paid outsider;
- the generic paid-response maximal-root packet already retains the coherent
  outer sequence, the exact-prefix survival floor, and a source/response cap
  displacement.

The useful incremental content is the particular binding-label extraction
from vanishing maximal absorption and its alignment with one fixed signed
payoff atom, followed by the explicit `D_*/14` induced-face wall.  This is a
sharpened conditional normal form, not a new source producer.

## No terminal consumer

The followup deliberately ends with the strict all-Continue moat or a static
negative-singleton/member-leaving wall.  The induced Nash profile is selected
anew from the reward table; it is not reached from the incoming source by an
extension-compatible chronology.  When `p_0>0`, the surviving object is a cap
fork between two profiles with the same prescribed payoff and law, not a paid
temporal edge.  When `p_0=0`, it is a finite sure-absorption wall.

Thus the result is a **conditional reduction**, not a chamber solution.  It
does not give a uniform payoff, charged near-return, renewable rank decrease,
or counterexample.

## Required revision

Retain the followup only after:

1. stating the outer paired family as an explicit supplied hypothesis and
   naming its existing producer;
2. removing any suggestion that it repairs the fixed-ray implication by
   itself;
3. changing “retained terminal-law difference” after the sure wall to
   “converted counterfactual cap fork”; and
4. presenting (55) as a conditional refinement whose strict moat and static
   wall still lack consumers.

