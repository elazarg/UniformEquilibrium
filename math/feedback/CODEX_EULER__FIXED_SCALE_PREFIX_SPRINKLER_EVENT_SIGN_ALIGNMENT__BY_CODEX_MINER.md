# Review of fixed-scale prefix sprinkler event/sign alignment

Reviewer: **CODEX_MINER**  
Verdict: **REVISE** — the incidence and temporal-separation mathematics
passes, but Proposition 2.2 is false for an arbitrary source as stated.  A
precise singleton-surcharge repair makes the later near-minimum application
valid.

## 1. Claim checked

I checked the full-support Fin4 prefix, its composition with the reviewed
fixed-weight recycling and half-reset packet, the claim that this removes
finite **label** circularity, and both examples separating label incidence
from a signed stage/Bellman event.

The exact root/law formulas in Proposition 2.1 are correct.  For
`0<kappa<=1/2`,

```text
mass_0(S)=kappa^|S| (1-kappa)^(4-|S|),
mass_0({w,j})=kappa^2(1-kappa)^2 >= kappa^2/4,
C_kappa=(1-kappa)^4 >= 1/16,
```

and every nonempty Fin4 coalition has stage-zero mass at least `kappa^4`.
The complete terminal law is the stage-zero root law plus `C_kappa` times
the shifted suffix law, including `Never` mass `C_kappa mu_sigma(Never)`.

The half-reset pointwise retention theorem really gives at the same edge

```text
mass_target(0,S) >= (1/2) mass_source(0,S),
```

so the displayed target bounds `kappa^2/8`, `kappa^4/2`, and the shifted old
atom bound `m/32` all follow.  (The note states the source shifted-atom bound
`m/16`; its target half-retention is then implicit.)

## 2. Mandatory cap repair

The sentence

```text
Prefix(allC,sigma) is literally sigma
```

is false for behavioral profiles and false for unrestricted caps in
general.  It is the one-date common delay of `sigma`.  A deviator gets a new
date-zero singleton option before the old opponents become active.  The
exact comparison is

```text
B_i(Prefix(allC,sigma)) = max(B_i(sigma), r_i({i})).       (2.R)
```

Consequently the opponent coupling proves

```text
|B_i(Spr_kappa(sigma))-
    max(B_i(sigma),r_i({i}))| <= 6 M kappa,                (2.S)
```

not (2.7) for every arbitrary `sigma`.  Equivalently, if

```text
s_i=(r_i({i})-B_i(sigma))_+,
```

then the universal version has the extra surcharge

```text
|B_i(Spr_kappa(sigma))-B_i(sigma)| <= 6M kappa+s_i,
|d_i(Spr_kappa(sigma))-d_i(sigma)| <= 14M kappa+s_i,
|D(Spr_kappa(sigma))-D(sigma)| <= 56M kappa+sum_i s_i.
```

Here is an exact Fin4 counterexample to the printed arbitrary-profile bound.
Let player `j` Quit surely at date zero and let the other three players,
including `i`, play Never.  For coordinate `i`, put

```text
r_i({i})=1
```

and put every other terminal reward of `i` equal to zero.  Take `M=1`.
Then `B_i(sigma)=0`: player `j` absorbs at date zero, and joining it also
pays zero.  Against the sprinkled source, however, player `i` can Quit at
the new date zero and obtains the singleton payoff whenever all three
opponents Continue, so

```text
B_i(Spr_kappa(sigma)) >= (1-kappa)^3.
```

For example at `kappa=1/20` this is greater than `6kappa`, contradicting
(2.7).

This does **not** invalidate Section 3.  Before sprinkling, the recycled
sources `rho_n` are already in the cap-freezing tube and all Continue is an
exact root against `B(rho_n)`.  Hence

```text
r_i({i}) <= B_i(rho_n)
```

for every player, all surcharges vanish, and (2.7)--(2.9) hold for the
sources actually used.  The note should state Proposition 2.2 under this
singleton-cap hypothesis (or print (2.R)--(2.S) first and specialize in
Section 3).  It should also replace “literally sigma” by “a common all-
Continue delay, with the same prescribed terminal law and payoff.”

## 3. Composition and label scope

Subject to that repair, the fixed-scale composition is correct.  Strict
unused tube slack absorbs the `56M kappa` perturbation.  The terminal gap at
the **sprinkled** literal source selects a debtor/reset mover there; no source
identification is made.  The reviewed global-retention reset then gives the
same `gamma/4`, aggregate `gamma/8`, and Fin4 recipient `gamma/24` bounds.

The sprinkler solves exactly the following circularity: one source is
prepared before the finite labels `w,j,T` are selected, yet it already has
positive stage-zero mass on `{w,j}` and on every possible nonempty decoder
coalition `T`; the same events survive on the half-reset target.  Moreover
every opponent of `w` has positive source-law incidence, so a selected
positive transfer recipient is in the matched-incidence arm rather than the
finite-separator arm.

It does **not** align:

1. the sign of the endpoint payoff-difference atom with its stage-zero copy;
2. the decoder terminal with the paid observer's first-disagreement row;
3. the sprinkled root with an exact Nash--Bellman root; or
4. the imported late-release sign through all independent mixed corners.

This scope is stated correctly in the note.

## 4. Separation examples

Example 4.1 is correct.  The two endpoint laws have identical pair mass
`kappa^2` at date zero and different pair mass at date one.  With reward one
only on that pair for recipient `j`, the total terminal payoff-difference
atom is positive while its date-zero signed contribution is exactly zero.
The phrase “otherwise Never only if desired” should be deleted when `j`'s
conditional date-one Quit probability is declared to be one, but this is
ministerial and does not affect the example.

The mixed-corner regression is also exact:

```text
E[g]=lambda^2-2lambda(1-lambda)=3lambda^2-2lambda<0
```

for `0<lambda<2/3`, even though the all-imported corner has sign `+1`.
The four corner values are realizable by product hazards and terminal reward
rows.  It is correctly scoped to the independent-graft architecture and is
not claimed to preserve `D_*>0` or the global hard residual.

## 5. Sources and recommendation

I checked the pointwise half-retention field of
`exists_halfStoppingLawReset_nearMinimum_transfer_and_globalRetention`, the
support-only statement of `exists_matched_transfer_incidence_or_separator`,
and the terminal-label output of
`hasQuittingEndpointDebtRecipientAtom_of_pos`.  None of those declarations
localizes the decoded sign to a prescribed date.

After the singleton-surcharge repair, I recommend **PASS at internal scope**.
The result is a useful all-label incidence producer and an exact temporal
no-go, but it has no current Bellman/rank/near-return consumer and should not
be exported.

## 6. Delta review after repair and signed-stage addition

**PASS at the stated internal scope.**  Proposition 2.2 now has exactly the
needed singleton-cap hypothesis and correctly treats the all-Continue prefix
as a common delay.  This resolves the only mathematical objection above.

New Proposition 4.1 is correct.  For fixed nonempty `T`, both nonnegative
stage-mass series are summable and have sums equal to the two terminal
`T`-masses.  Their difference, multiplied by the fixed coordinate
`r_j(T)`, is absolutely summable.  Therefore a positive total atom has at
least one positive same-profile-pair stage contribution, and its finite
partial sums eventually exceed half the displayed lower bound.  Applied to
the reviewed decoder constants this gives exactly

```text
prescribed window >= Gamma/1536,
rectangle window  >= Gamma/3072.
```

No lower bound on one selected date follows, as the note correctly says.
For the factorized rectangle chronology, the clean handoff is to invoke the
already checked
`exists_prescribedAtom_or_positiveCausalStage_and_actualTerminalMass_of_stoppingLawDebtSlope`
at `lambda=1` on the same positive recipient slope.  That theorem selects a
pure-time response without an additional constant loss.  Thus “choosing its
approximate cap response” should be replaced by this exact declaration (and
the duplicated phrase “and its exact chronology from” should be deleted),
but these are exposition repairs rather than mathematical objections.
