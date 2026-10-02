# Independent check of the VANISH bonus branch's pivot optimality

Reviewer: CODEX_HILBERT. **PASS for Section 7.2 and its Section 7.3
compatibility consequence only.** This is not a review of the entire coupled
fixed-point construction or the separate delayed example in Sections 1–6.

Source: Section 7 of
`notes/CODEX_RENY__PIVOT_LP_AND_FINITE_NONPIVOT_BEST_REPLY_COUPLING.md`.
Reviewed full-file SHA-256:
4f69e6e2575f70044ed92a0ea9a27722a81cb70c51bab09c2700e05aeccc3737.
Scope is exactly R=2,h=1, K≥1, N=3K and the fixed independent geometric
nonpivot laws displayed there. Write D=8^(−K). No arbitrary-table
conclusion is checked or inferred.

I independently checked the inequality d_0+g_(2,1)≥2D before applying
its consumer. The pivot's full cap is fixed at 2−D, so its debt is affine
in its law. The fixed player-2 response at date 1 and its prescribed payoff
are also affine in that same pivot law. Pure pivot times suffice:

- At date 0, both prescribed player 2 and its date-1 replacement earn −1,
  so g_(2,1)=0. The pivot debt 1−D is at least 2D since D≤1/8.
- At 1≤t<N, the pivot debt is 2^(−t)−D≥D. Player 2's date-1
  replacement earns one even at the tie t=1: it earns two on player 1's
  earlier date-0 quit, of probability 1/2, and zero otherwise. Adding a
  finite pivot cannot raise prescribed U_2 outcome by outcome: an earlier
  unchanged absorption retains its reward; a new absorption gives −1 unless
  player 2 also Quits, in which case its reward was already zero. Thus
  U_2≤1−D, giving g_(2,1)≥D.
- For finite t≥N, pivot debt is zero. Exactly the event that all three
  nonpivots chose Never changes U_2, from zero to −1, with mass D.
  Hence U_2=1−2D and g_(2,1)=2D.
- At pivot Never, the two gains are D and D.

Integration proves the same inequality for arbitrary mixed and unbounded
pivot laws, including Never. Since original full exploitability is at
least each of its two terms, it is at least D. Pivot Never attains D;
it is therefore an ACTUAL global unrestricted pivot-repair minimizer.

The previously checked compression theorem identifies this actual infimum
with the closed LP optimum, so no nonattained-boundary assumption is needed
for this good branch. Coupled with the exact outer best replies after the
planned player-2 Never bonus 4^(−K), this supplies an actual good fixed
point and bounds minimum original value over all bonus-coupled fixed points
by D. It does not make every coupled fixed point good or produce such a
branch outside the specified table.

The comparison law and auxiliary bonus are the independently developed
source in `notes/CODEX_HILBERT__VANISHING_PRIVATE_NEVER_BONUS_SELECTOR.md`.
The additional global pivot-optimality inequality reviewed here is RENY's
new compatibility step. No mathematical correction was found.
