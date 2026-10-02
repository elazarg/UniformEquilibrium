# Focused feedback on Section 36 of `CODEX_CEDAR__PAID_ROW_REENTRY`

Reviewer: `CODEX_EULER`

## Verdict

**VALID ordinary mathematics, with one representation clarification.**  The
segment is affine/convex in the observer's complete stopping-law distribution;
its hazard-form behavioral realization need not be pointwise affine in hazard
coordinates.  No public randomization is required.

## Exact checks

An ex-ante mixture of the two pure Quit-time laws is one probability law on
`N union {Never}` and therefore has an ordinary behavioral hazard
representation.  Holding `sigma_{-o}` fixed, observer replacement removes its
prescribed law, so `B_o(t)` is constant.  If

```text
Delta=payoff_o(b;sigma_{-o})-payoff_o(a;sigma_{-o})>=g,
```

then

```text
U_o(t)=U_o(0)+t*Delta,
d_o(t)-d_o(s)=-(t-s)*Delta<=-(t-s)g
```

for `s<=t`, exactly as in (36.2).

For `j!=o`, every fixed deviation payoff is affine in the mixed observer law.
Changing `t` by `|t-s|` changes the payoff by at most `2M|t-s|`.  Taking the
supremum preserves that Lipschitz bound and makes `B_j` convex.  Prescribed
`U_j` is affine with the same bound, hence `d_j=B_j-U_j` is finite, continuous,
and convex.  The observer debt is affine, so total debt `D` is continuous and
convex and attains a segment minimum `tStar`.

Every segment profile is an actual behavioral profile, so
`D(tStar)>=DStar` and `pi>=0`.  The opponents faced by `o` never change.
Consequently both witness payoffs, their ordering, first-disagreement event,
live mass, and gain remain literal at `sigma_{tStar}`.  Thus `pi=0` really
gives a globally minimum actual profile carrying the paid row; `pi>0` is a
positive premium for retaining this exact opponent environment.

For `s>=tStar`, minimality and (36.2) give

```text
0<=D(s)-D(tStar)
  =d_o(s)-d_o(tStar)+sum_{j!=o}(d_j(s)-d_j(tStar)),
```

and hence (36.4).  Replacing `g` by the actual `Delta` is exact.

## Limitations

The stated limitations are necessary and correctly scoped.  Altering `o` can
change another player's cap and prescribed payoff, so zero reset-mover debt is
not retained merely because that mover's own stopping law is fixed.  If
`tStar=1`, there is no `s>tStar` in the segment and (36.4) has no positive
content.  Finally `pi` is semantic debt excess, not absorption charge, an
exact Nash--Bellman edge, or a floor-admissible return.

I recommend saying “compact affine segment in complete stopping-law space,
with executable behavioral realizations” rather than “convex family of
behavioral profiles”; this prevents confusion about pointwise mixtures of
hazard maps but does not change the proof.
