# Review of the proposed four-player candidate in the second Q172 answer

## Decision

The proposed table is a useful **filter-grade capacity candidate**, not a
counterexample and not yet a `P × C` witness.  Its important design feature is
that it deliberately evades the singleton-lock obstruction: every singleton
owner has a designated spectator who strictly wants to join at every owner
mixing rate.

The reported bounded search is not reproducible from the answer alone: no
harness, serialized table, certificate list, or machine-readable output was
provided with it.  Its numerical census is therefore treated as a search
report rather than evidence.  The rational table and its exact affine blocking
criterion are worth reconstructing in this experiment.

## Exact rate-covering observation

Fix an owner `o` who quits with probability `p`, and an outsider `j`.  Against
the baseline in which eventual singleton `o` pays `r_j({o})`, the gain from
`j` quitting immediately is the affine function

```text
g_(j,o)(p)
  = p [r_j({o,j})-r_j({o})]
    + (1-p) [r_j({j})-r_j({o})].
```

It is strictly positive for every `p in [0,1]` exactly when both endpoint
gains are strictly positive:

```text
r_j({j})   > r_j({o}),
r_j({o,j}) > r_j({o}).
```

The first inequality is already encoded by a negative spectator entry in the
four-player singleton blocker.  The second is precisely the strict joining
inequality forced by the singleton-lock screen discovered in the `T × C`
investigation.  The blocker has one designated negative spectator per owner,
so completing those four pair-coalition coordinates with a positive joining
bonus is a natural way to eliminate all singleton-rate locks.

This eliminates one family of charge-positive stationary rows.  It says
nothing by itself about mixed multi-owner roots, longer exact cycles, or
unbounded nonrecurrent chains.

## Candidate table retained for reconstruction

The singleton columns are the existing four-player blocker table:

```text
             owner 0   owner 1   owner 2   owner 3
player 0        1         2/3        5/3        5/3
player 1       5/3         1          2          0
player 2       2/3        5/3         1          2
player 3        2         5/3        1/3         1
```

The four designated joining coalitions are

```text
r({0,1}) = (11/12, 1/2, 1/8, 1/8),
r({0,2}) = (1/2, 1/8, 11/12, 1/8),
r({2,3}) = (1/8, 1/8, 1/2, 7/12),
r({1,3}) = (1/8, 1/4, 1/8, 1/2).
```

The remaining pairs are

```text
r({1,2}) = (1/8, 1/2, 1/2, 1/8),
r({0,3}) = (1/2, 1/8, 1/8, 1/2).
```

Every triple pays zero to its members and `1/8` to its unique spectator; the
grand coalition pays zero.  This convention must be made explicit in any
executable reconstruction.

The designated strict joiners are

```text
owner 0 -> player 2,
owner 1 -> player 0,
owner 2 -> player 3,
owner 3 -> player 1.
```

Each receives exactly `1/4` more from the designated pair than from watching
the owner quit alone.

## Missing checks, in priority order

1. **Behavioral punishment floors.**  The normalized packet requires
   `chi_i <= target_i`.  Singleton data and stationary checks do not establish
   behavioral min--max values for the completed collision table.
2. **Positive-charge return search.**  One exact punishment-rational return
   path refutes universal capacity immediately.  This is cheaper and more
   decisive than attempting to certify all roots.
3. **All exact one-stage supports.**  The reported search leaves off-grid
   three- and four-mixer supports open.  These must be solved symbolically or
   enclosed rigorously before stationary survival means anything.
4. **Longer and nonperiodic charge.**  Absence of short cycles does not imply a
   bounded global budget.  A bounded potential on the complete floor root
   correspondence, or an equivalent proof, is required.
5. **Uniform terminal instability.**  Even a full proof of packet defect and
   bounded capacity would not by itself verify the universal profile
   quantifier in condition (A).

The most efficient falsification order is therefore: reconstruct the table,
obtain exact punishment upper certificates, search for a floor-reachable
positive-charge return, and only then complete the expensive support
elimination.  If a return is found, retain it as a regression and discard the
table as a capacity candidate.

## Relation to the pairwise program

The candidate is aimed exactly at the residual left by `P × C`: change
nonsingleton rewards so that joining deviations destroy the known packet
rotation and every singleton lock while preserving the singleton packet
geometry.  It is the right type of next experiment.

It does not alter the current pair classification.  Until punishment floors
and universal capacity are proved, `P × C` remains open and this table remains
a candidate input, not a consistency witness.
