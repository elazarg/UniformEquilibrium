# Review of the opponent-absorption-normalized incentive compiler

Reviewer: `CODEX_NOETHER`

Reviewed note: `notes/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION.md`,
Section 12, Proposition 7.

## Verdict

**Valid ordinary mathematics.**  The direct-defect sign, diagonal-gap
nonnegativity, generated-secant bound, opponent-absorption comparison, and
every-suffix telescope all check.  This is a useful scale-free conditional
compiler, not a producer of the normalized gaps or clocks.

## Reconstruction

At date `t`, use diagonal candidate successor pair

```text
(v_(t+1),v_(t+1))
```

and diagonal candidate current pair `(v_t,v_t)`.  Exact prescribed Bellman
recursion makes the prescribed defect zero.  The prefix cap is the supremal
one-row/tail response value against the fixed opponent root; it is at least
the payoff of following the prescribed mixed action and diagonal tail.
Therefore its excess over the prefix prescribed payoff is the nonnegative
diagonal gap `g_(t,i)`.

With direct defect in current-minus-template orientation,

```text
E_(t,i)=0-g_(t,i)=-g_(t,i).
```

This sign is exact: a positive diagonal root gap is adverse forcing and must
be paid, rather than canceled by the zero candidate debt.

The unrestricted cap prefix is a max of a successor-independent Quit branch
and a Continue branch with successor slope `O_(t,i)`.  Its secant between the
diagonal candidate successor and the actual next semantic cap therefore
satisfies

```text
0<=s_(t,i)<=O_(t,i)<=1,
```

including max-branch switches and nonattained tail suprema.  For an arbitrary
suffix start `m`, define `w_0=1` and `w_(n+1)=w_n s_(m+n,i)`.  Then

```text
w_n g_(m+n,i)
 <= eta w_n(1-O_(m+n,i))
 <= eta w_n(1-s_(m+n,i))
 =  eta(w_n-w_(n+1)).
```

The second inequality has the correct direction because `s<=O`.  Summing any
finite horizon gives

```text
-sum_(n<L) w_n E_(m+n,i)
 =sum_(n<L) w_n g_(m+n,i)
 <=eta(1-w_L)<=eta.
```

Thus the forcing quantifiers hold for every player, calendar start, and
finite length, stronger than the eventual-slack formulation.  Prescribed
discrepancy and initial candidate debt are zero; uniform boundedness of `v_t`
and the assumed literal clocks supply the remaining fields.

## Boundary checks and scope

- If `O_(t,i)=1`, condition `(12.3)` forces `g_(t,i)=0`.  This is necessary:
  without opponent absorption there is no local secant loss to pay a positive
  diagonal gap.
- If the generated secant is zero, the entire later forcing tail is screened;
  the telescope still holds with no division by a survival factor.
- Small own hazard alone does not improve the ratio because `O_i` omits the
  owner's hazard.  The note's scale warning is exact.
- Candidate diagonal pairs need not be actual semantic pairs.  The theorem
  uses only their bounded Bellman values and the generated secants against the
  actual root-sequence tail; no carrier membership is silently assumed.
- The conclusion remains conditional on a single bounded Bellman spine whose
  literal roots simultaneously have the two persistent labels and satisfy
  every normalized incentive inequality.  No atom/reset or residual-hard
  source is shown to produce such a spine.

