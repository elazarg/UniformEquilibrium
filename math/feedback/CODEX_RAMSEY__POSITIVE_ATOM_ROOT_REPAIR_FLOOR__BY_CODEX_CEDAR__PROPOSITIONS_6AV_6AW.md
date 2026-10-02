# Independent review of Propositions 6AV--6AW

Reviewer: `CODEX_CEDAR`

Reviewed note:
`notes/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md`.

## Verdict

**PASS in the stated vector-port and prefix-only scopes.**  The vector
exposure and atom constants, the coordinatewise conditioned successor, the
literal source/replacement graft, and the rational scale-loss regression all
check.  The propositions correctly leave open the decisive operational
condition: a fixed positive outer chart radius does not make every requested
scale legal when the two retained inner scales may collapse.

One hypothesis should remain explicit whenever Proposition 6AV is quoted:
the retained outer weights satisfy

```text
0 < w_first,w_second < 1.
```

Positivity is needed for `kappa>0`; strict upper bounds are needed for the
positive outer radius.  This is the “two retained strict weights” hypothesis
used in the proof, not a consequence of merely writing `w_j in [0,1]`.

## 1. Vector exposure

In coordinate `j`, the nested law collapses exactly to

```text
P_s(j)=(1-w_j s_j)A_j+w_j s_j R_j.
```

Applying the already reviewed endpoint-gain estimate with effective weight
`w_j s_j` gives, under `w_j s_j<=1/2`,

```text
EverQuitMass(P_s(j)) >= w_j s_j g_j/(2M).
```

For either retained label, `s_j>=h` therefore yields

```text
EverQuitMass(P_s(j)) >= 2 kappa h,
kappa=min(w_first g_first/(4M),w_second g_second/(4M)).
```

Truncating the two divergent/nonnegative raw-hazard sums at a common maximum
cutoff loses at most the factor two and gives at least `kappa h` for both
labels.  No equality of the inner scales is used.

## 2. Whole-face atom and error constants

Sequential complete-law coupling changes any fixed terminal-outcome mass by
at most

```text
L(s)=sum_j w_j s_j.
```

The corresponding full-replacement comparison costs no more: the replaced
mover coordinate is common on the two endpoint sides, and bounding by the
full `L(s)` is harmless.  Thus the two sides of the reward-weighted atom lose
at most `2KML(s)`.  Uniform coupling over every observer deviation gives the
rectangle endpoint debt increment `4ML(s)`.  Consequently

```text
2KML(s)<=q/8
```

is exactly sufficient for output charge `q/2` and error `e+4ML(s)`, with the
same terminal coalition and, in the rectangle arm, the same supplied pure
time.  This is the vector version of the independently reviewed 6S/6AS
calculation.

## 3. Exact vector successor and provenance

At a cutoff, write `S_j,Q_j` for the component survivals and

```text
D_j=(1-w_j s_j)S_j+w_j s_j Q_j.
```

The surviving replacement posterior is `w_j s_j Q_j/D_j`.  Refactoring with
the same outer weight gives precisely

```text
s_j^+=s_j Q_j/D_j.
```

Indeed the refactored source coefficient is

```text
1-w_j s_j^+=(1-w_j s_j)S_j/D_j.
```

Hence (6AV.9) is exact whenever `D_j>0` and `s_j^+<=1`; setting `s_j^+=0`
when `w_j=0` is also exact.  Choosing the component tails ex ante to be the
later frozen source and replacements makes the product residual literally
the later vector-scale profile.  A separately supplied positive-reach
replacement prefix, grafted to the later original replacement tail, gives
the counterfactual endpoint `update P_(s^+) mover R_m^+` literally.

The provenance qualification is essential and correct.  Positive reach from
6AU applies to the **regularized** source and replacement laws, and the atom
decoder must be rerun on that reconstructed family.  Proposition 6AV does
not recover the old unsmoothed endpoint roots or old atom by identity.

## 4. What the constant outer radius does not prove

Conditioning leaves the outer weights exactly `w_j`, so

```text
rho_outer=min(w_first,1-w_first,w_second,1-w_second)>0
```

is stable under the vector refactor.  But the exposure proof for a declared
scale `h` separately requires

```text
h<=min(s_first,s_second).
```

Thus `0<h<rho_outer` does not make the requested packet legal.  Replacing the
port radius by the minimum retained inner scale exposes the likelihood-ratio
loss in `s_j^+=s_jQ_j/D_j`; positive component reach gives no sublinear
control of that loss.  The atom estimate also needs the aggregate `L(s)`
small, not merely the minimum of the two retained coordinates.  These are
real remaining conditions, not presentation artifacts.

## 5. Proposition 6AW

For each retained label,

```text
w=1/2,  s=1/4,  S=1,  Q=1/2.
```

The executed first-row Quit hazard is

```text
ws(1-Q)=1/2*1/4*1/2=1/16.
```

After Continue,

```text
D=(1-ws)S+wsQ=7/8+1/16=15/16,
s^+=sQ/D=(1/8)/(15/16)=2/15.
```

After that row the two component tails coincide, so every nonempty prefix
which makes positive progress has the same successor scale.  With

```text
rho=min(s_first,s_second,w,1-w)=1/4
```

the successor radius is `2/15` and the loss is exactly

```text
1/4-2/15=7/60.
```

For every requested `0<h<1/4`, the same row supplies
`1/16>=h/4` for both labels.  A zero-length word cannot meet positive
progress, while every positive word crosses the same Bayes update.  Hence
any additive availability inequality forces `chi(h)>=7/60` at arbitrarily
small declared scales.

The quantifier has a narrow interface meaning.  Reusing the fixed row for
every smaller `h` is legal only for a packet type that lower-bounds progress
by `kappa h` and does not upper-bound actual root mesh by `h`.  It is not a
vanishing-mesh construction in the natural stronger sense: the literal row
hazard stays `1/16`.  Therefore 6AW is a sharp prefix-only/type-interface
regression, not a positive-minimum counterexample and not a refutation of
root movement, source reselection, or a genuinely mesh-sensitive packet
producer.

## Remaining boundary

Proposition 6AV removes the common-inner-scale algebraic mismatch found in my
prior review, but it does not answer Tier I.  The surviving producer must
control legal small scales and availability simultaneously—by source-matched
scale lowering/reselection, a sublinear lower bound on the retained successor
scales, or a different stable radius—and must still supply the rectangle
observer-deleted endpoint cap when that atom branch occurs.

## Addendum: Proposition 6AX

**PASS.**  With `w_j<=1/2` and `0<s_j<1`, the effective-weight premise
`w_j s_j<=1/2` is automatic.  The atom condition

```text
2KML(s)<=q/8
```

is exactly `L(s)<=c_atom=q/(16KM)`, so positivity of the five-way minimum
`rho(s)` supplies every strict local port condition claimed.

The scale increment is

```text
s_j^+-s_j
 =s_j[Q_j-D_j]/D_j
 =s_j(1-w_j s_j)(Q_j-S_j)/D_j,
```

so both sign and normalization in (6AX.2) are correct.  Let `Delta_j` denote
this signed increment.  The four adverse motions in `Xi` are exhaustive:

- `-Delta_first,-Delta_second` pay decreases of the retained clock scales;
- `sum_j w_j Delta_j` pays the decrease of atom slack
  `c_atom-L(s^+)`;
- `max_j Delta_j` pays the decrease of the upper-face margin
  `min_j(1-s_j^+)`.

Taking the maximum with zero also pays the unchanged outer-radius entry.
Comparing with each term of the minimum proves
`rho(s)-Xi<=rho(s^+)` exactly; no absolute values are missing.

In the 6AW regression both retained increments are `-7/60`, the weighted sum
and maximum increments are nonpositive, and hence `Xi=7/60`.  Thus the stated
remaining obligation is exact: one needs a uniform operationally sublinear
majorant for the selected packet's `Xi`, or a source/root movement which
changes this ledger.  Positive component reach alone cannot provide it.

The scope qualifications remain necessary: (6AX) assumes the refactored
scales stay in `[0,1]`, it does not freshly produce the later atom data or the
rectangle cap port, and `Xi(port,h)` acquires its `h` dependence only through
the yet-to-be-selected packet/cutoff.  It is an exact availability account,
not that selection theorem.
