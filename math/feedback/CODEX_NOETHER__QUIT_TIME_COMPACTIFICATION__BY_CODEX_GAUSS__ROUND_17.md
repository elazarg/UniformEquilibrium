# Round 17 Feedback on Quit-Time Compactification

Reviewer: `CODEX_GAUSS`

Reviewed note: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Sections 50--51, Propositions 47--48.  I independently checked the
stationary-prefix splice, the unrestricted deviation comparisons, the
selected-player punishment argument, the rare-owner calculation, and the
claimed reduction to the isolated all-Continue boundary.

Status:

- Proposition 47: `VALID_ORDINARY_MATHEMATICS`.
- Proposition 48: `VALID_ORDINARY_MATHEMATICS`.

These verdicts are not Lean or integration seals.  Proposition 47 should be
read with the standard precise meaning of “arbitrarily small”: for every
positive upper tolerance there is a smaller positive stationary Nash error
with a positive-absorption stationary witness (equivalently, there is such a
sequence with errors tending to zero).

## Proposition 47: min--max comparison

Let `p` be the stationary product row, `q=Q(p)>0`, and `h` the terminal payoff
of the infinite stationary profile.  Positive `q` makes absorption almost
sure and makes `h` the same payoff after every survived finite prefix.  If the
stationary profile is an unrestricted terminal `eta`-Nash profile, then for
every player `i`

```text
bestReplyValue(p_-i) <= h_i+eta.
```

The punishment value `chi_i` is the infimum of these best-reply values over
opponent profiles, so `chi_i<=bestReplyValue(p_-i)`.  Hence

```text
h_i >= chi_i-eta,                                    (F1)
```

with the stated orientation.  No best reply or optimal punishment need be
attained.  At the later splice one chooses an actual `delta`-punishment from
the defining infimum, with an arbitrarily smaller slack if necessary.

Choose `j` with largest marginal `m=p_j`.  Since `q>0`, `m>0`.  Repeat `p`
at dates `0,...,L-1`, and then use a punishment of `j`.  In the production
notation `quittingStationaryPrefixThenRoots`, whose horizon is inclusive, the
parameter is `L-1`; `L>=3` gives the required horizon inequality `1<L-1`.

If `B` bounds absolute terminal payoffs (and is enlarged to be positive if
needed), prescribed stationary and spliced payoffs differ only on complete
survival of all `L` prefix rows.  Therefore

```text
|P_i-h_i| <= 2B(1-q)^L <= 2B(1-m)^L.                (F2)
```

The second inequality uses `q>=m`.

## Nonselected deviations

Fix `i!=j` and replace `i`'s entire behavioral strategy.  Compare the same
deviation against the spliced and infinite-stationary opponent profiles.  The
opponents agree through the prefix.  To see a difference, the game must still
be live after `L` dates, which in particular requires the fixed opponent `j`
to Continue at every one of those dates.  This event has probability at most
`(1-m)^L`, independently of `i`'s behavior.  Thus changing the tail changes
the deviating payoff by at most `2B(1-m)^L`.  Combining this with the global
stationary `eta`-Nash inequality and `(F2)` gives

```text
regret_i <= eta+4B(1-m)^L.                           (F3)
```

This is a direct all-behavior comparison; it is not a stationary or
pure-time-only estimate.

## Selected deviation

For an arbitrary deviation by `j` in the splice, define an auxiliary
deviation against the infinite stationary opponents which agrees through the
first `L` dates and, after survival, resumes marginal `p_j`.  Its payoff is at
most `h_j+eta`.  Conditional on reaching the tail, the auxiliary continuation
has value exactly `h_j` by stationarity and `q>0`, whereas the actual
punishment holds every continuation behavior to at most

```text
chi_j+delta <= h_j+eta+delta
```

by `(F1)`.  Consequently the actual deviating payoff is at most
`h_j+2eta+delta`.  Together with `(F2)`, this gives

```text
regret_j <= 2eta+delta+2B(1-m)^L.                    (F4)
```

The argument remains valid for a strategy which conditions its post-prefix
behavior on its earlier randomization: on the unique surviving history all
earlier actions were Continue, and the shifted continuation is one of the
behavioral responses quantified by the punishment cap.

For independently specified positive `epsilon,delta`, choose the stationary
witness with `eta<epsilon/4`, then choose finite `L>=3` with
`4B(1-m)^L<epsilon/2`.  Both `(F3)` and `(F4)` are below `epsilon+delta`.
This matches the two independent quantifiers of
`QuittingStationarilyGeneratedApproximateEquilibria` in
`UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedBranch.lean`.

The contrapositive scope is also correct.  If the generated branch fails,
there is one positive accuracy at which no positive-absorption stationary
approximate equilibrium exists.  Zero absorption for a finite product row
means every marginal is zero, so the only surviving row is all Continue.  The
proposition does not itself prove that this row is an approximate equilibrium.

## Proposition 48: rare no-harm owner

Let `j` be normal, so `chi_j<=v_j`, and assume

```text
v_i <= r({j})_i  for every i!=j.                     (G1)
```

In the infinite row where only `j` quits with probability `a>0`, the
prescribed payoff of player `i` is `r({j})_i`.  A pure quit time of an outsider
`i!=j` either occurs after the game has already absorbed at `{j}`, or reaches
a live date and then pays

```text
(1-a)v_i+a*r({i,j})_i.
```

Relative to `r({j})_i`, `(G1)` and the absolute reward bound give gain at most
`2Ba`.  Never receives the baseline.  The checked pure-time extremality
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`
(`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`)
therefore gives the same cap against every behavioral deviation, proving
`(G3)`.

After `L` rare-owner rows, replacement by an actual punishment of `j` is seen
by an outsider only if the fixed owner survives, an event of probability

```text
s=(1-a)^L.
```

The deviation comparison and prescribed-payoff comparison each cost at most
`2Bs`, so outsider regret is at most

```text
2Ba+4Bs.                                              (G4)
```

For `j`, every response quitting before the splice earns exactly `v_j`; every
response reaching the splice is capped by
`chi_j+delta<=v_j+delta`.  The prescribed payoff is at least `v_j-2Bs`.
Thus

```text
regret_j <= delta+2Bs.                               (G5)
```

Choosing `a` first and then `L` proves the generated branch even when `v_j`
is negative.  This is the substantive improvement over the old infinite
rare-owner stationary argument.

Finally, if the generated branch fails and a normal `j` harmed no normal
outsider, then `(G1)` holds for normal outsiders.  For an abnormal outsider
`i`, `lemma3` (`Literature/Simon2007.lean`) gives

```text
r({j})_i >= chi_i > v_i,
```

because `j!=i`.  Hence `(G1)` holds for every outsider and Proposition 48 is
a contradiction.  The conclusion that every normal owner harms another
normal player is therefore valid.  It still does not supply a positive normal
solo owner; the finite harm-cycle/all-nonpositive-solo boundary remains.

## Source and remaining obligation

`StationarilyGeneratedBranch.lean` defines the exact corrected consumer and
proves its behavioral/root-sequence equivalence, but I found no named theorem
there already establishing either Proposition 47 or the punishment-strengthened
no-harm adapter of Proposition 48.  The 2007 literature transcription contains
the older stationary no-harm argument and `lemma3`; it does not remove the
negative-owner problem by a finite punishment splice.

Thus these propositions genuinely narrow the conjecture-facing necessity
seam, while remaining ordinary mathematics.  The unresolved universal case
is precise: at one fixed accuracy every positive-absorption stationary row
has positive regret, all Continue is the only zero-absorption candidate, and
the normal harm graph may cycle with all normal solo payoffs nonpositive.
