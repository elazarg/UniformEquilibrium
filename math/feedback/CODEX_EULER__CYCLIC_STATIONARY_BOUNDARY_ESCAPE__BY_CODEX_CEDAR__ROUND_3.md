# Round 3 feedback on `CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE`

Reviewer: `CODEX_CEDAR`

## Scope

I independently audited only Section 9 / Theorem 5 and Section 10 / Theorem
6: the four-case pure classification for pair-local participation rewards,
all deterministic first-outcome deviations for the `{0,1,2}` table, the
period-two value and incentive algebra, and the extension from phasewise
endpoint Nash to unrestricted behavioral stopping laws.

## Verdict

**VALID ordinary mathematics in the stated scope.**  I found no missing pure
coalition, sign error, recurrence error, or all-behavior boundary case.
Theorems 5 and 6 rule out two concrete four-player gadget architectures; they
do not imply a universal incentive-gadget no-go.

## Theorem 5: classification

The cases cover all parameters.  If `B<=0`, case 1 applies.  Otherwise
`B>=0`; if `D>=C`, case 2 applies, and if `C>=D`, either `B>=A` (case 3) or
`A>=B` (case 4).  Equality causes only harmless overlap.

The deviation comparisons are exact:

- at all-Never, every finite pure time earns the solo payoff `B<=0`, versus
  zero from Never;
- at all-Quit, a sole deviator who Continues still sees its partner Quit and
  changes its payoff from `D` to `C`;
- at a transversal, a prescribed quitter compares `B` with `A`, while its
  excluded partner compares prescribed `C` with joining payoff `D`;
- at a singleton, the owner can only obtain a mixture of later solo payoff
  `B` and Never payoff zero, its partner compares `C` with `D`, and either
  opposite-pair outsider compares `A` with `B`.

In cases 2--4 absorption at date zero makes all later behavior irrelevant.
In case 1, and for the singleton owner in case 4, linearity in the player's
stopping-time law extends the displayed pure-time inequalities to arbitrary
behavioral deviations.

## Theorem 6: pure exits and periodic algebra

All-Never is strictly broken by the solo payoff `B_0=1`.  The five
pair-preserving coalition types exhaust the fifteen nonempty coalitions, and
the listed deviation in each type has the asserted literal payoff change:

```text
singleton:           C_0=0 -> D_0=1  (excluded partner joins),
one full pair:       A_2=0 -> B_2=1  (opposite outsider joins),
transversal:         B_1=0 -> A_1=2  (one quitter leaves),
three players:       D_1=0 -> C_1=1  (a full-pair member leaves),
grand coalition:     D_2=0 -> C_2=1  (one member leaves).
```

For a positive first date, joining at that date or moving one's clock just
after it changes the same terminal coalition; another original quitter
remains at the first date in every leaving case.  Thus the argument covers
arbitrary deterministic clock profiles, not only date-zero action profiles.

With active Continue probability `x` and `q=1-x`, direct conditioning gives

```text
v=q+x^2 w,
w=4qx+x^2 v.
```

At the active phase forced Quit pays `x B_0+q D_0=1`, while forced Continue
pays `xw`.  Setting `v=1` therefore gives

```text
x(4x-3x^2)=1,
(x-1)(3x^2-x-1)=0.
```

The interior solution is exactly `x=(1+sqrt(13))/6`, with
`3/4<x<4/5`, and

```text
w=4x-3x^2=1/x=3x-1>1.
```

At its inactive phase a forced Quit earns `x^2+q^2`; this is at most one and
strictly below `w`.  Hence every active player is indifferent and every
inactive player strictly Continues at both literal phase rows.

Finally, deleting any player's clock leaves its partner with Quit probability
`q>0` in the player's active phase and leaves both opposite-pair players with
positive Quit probability in the other phase.  Opponent-only survival over a
two-phase block is therefore at most `x^3<1`.  This is the required
player-deleted contraction: unrolling controls every finite pure Quit time and
pure Never, and stopping-time extremality then controls every behavioral
deviation.  The alternating profile is consequently an exact terminal Nash
profile despite the strict failure of every deterministic-clock profile.

## Scope

Theorem 5 completely excludes the payoff-anonymous pair-local class (9.1).
Theorem 6 shows that even strict destabilization of all deterministic first
coalitions and Never does not suffice once opposite-pair counts are visible.
Neither theorem excludes richer cross-pair/calibrator tables or all finite
support words, so neither is a universal gadget obstruction.
