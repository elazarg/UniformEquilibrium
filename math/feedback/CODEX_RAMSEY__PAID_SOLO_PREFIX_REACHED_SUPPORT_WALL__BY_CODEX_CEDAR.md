# Independent review of `PAID_SOLO_PREFIX_REACHED_SUPPORT_WALL`

Reviewer: `CODEX_CEDAR`

## Verdict

**REVISE, then PASS after one literal orientation repair.**  The semantic
prefix formulas, cap-defect debt preservation, carrier provenance, bounded
first-failure estimate, one-edge near-return conclusion, and root-displacement
constant are mathematically valid.  The only objection is that `(3.2)` writes
the punishment-floor charged-relation arrow backwards.

The exact repair is:

```text
U^m -> U^(m+1),             0<=m<N,
```

when `->` denotes the charged relation used by the maintained near-return
question.  Equivalently, `U^(m+1)` is the current/prefixed payoff and `U^m`
is its Bellman continuation tail.  The actual behavioral chronology reads
the row at `U^(m+1)` and then continues with `U^m`, so it is legitimate to
describe that *behavioral prefix order* in reverse, but it must not be called
the charged-relation path orientation.  Corollary 3.2 should make the same
replacement.  Endpoint distance and charge are unchanged, so no theorem or
constant changes.

## Lemma 2.1 and the support-wall formula

For a solo-`k` root of rate `p`, prefixing gives

```text
U^(n+1)_k=p s_k+(1-p)U^n_k=s_k,
U^(n+1)_j=pR_j+(1-p)U^n_j.
```

Thus `(2.1)` is exact.  The outsider forced-Quit endpoint is

```text
Q_j=(1-p)s_j+p r({k,j})_j,
```

whereas forced Continue at `U^n` is

```text
pR_j+(1-p)U^n_j
 =R_j+(1-p)^(n+1)(U_j-R_j).
```

Their difference is exactly `(3.6)` with the displayed exponent `n+1` and
sign.  Exactness at `n=0` gives nonpositive outsider gaps.  The named gap
converges to `g_i>0`, so a least positive failure time exists.  Since
`|U_i-R_i|<=2M`, `p>=alpha`, and `0<alpha<1`, condition `(3.5)` implies
strict failure at `n=H`; hence `N<=H`.  There is no off-by-one error.

## Lemma 2.2: cap-coordinate debt preservation

I checked the argument against
`quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`.

For an outsider `j`, the inductive hypothesis gives `B^m_j=U^m_j`.
Although the cap and prescribed vectors may differ in owner coordinate `k`,
player `j`'s forced-Continue endpoint uses only continuation coordinate `j`,
and its forced-Quit endpoint is continuation-invariant.  Therefore the cap-
coordinate defect is the literal coordinate defect.  Exact root Nash makes
it zero.  Joint survival times the old zero debt is also zero, proving the
new outsider debt is zero.

For the owner, `U^m_k=s_k` and `B^m_k=s_k+d_k`.  At the cap, forced Continue
is `s_k+d_k`, forced Quit is `s_k`, and the prescribed solo mixture has
expected coordinate `s_k+(1-p)d_k`.  Its cap-coordinate defect is therefore
`p d_k`.  Adding joint survival `(1-p)d_k` returns exactly `d_k`.  Thus the
unique positive debt and total debt are preserved at every exact reuse.

`quittingTerminalSemanticPrefix_mem_carrier` applies to every prefix even
before exactness is used.  Exactness supplies floor-forward invariance, so
all states through the first failure tail have the claimed carrier and floor
provenance.  If the initial carrier point is merely in the compact closure,
the later points remain closure points; the note correctly does not upgrade
them to attained profiles.

## Corollary 3.2 and the charged relation

If exactness never fails, the corrected relation edge is

```text
tail=U^n, current=U^(n+1)=Succ(U^n,q).
```

It has charge `p`, both endpoints are boxed and floor-safe, and

```text
||U^(n+1)-U^n||_infinity<=2Mp(1-p)^n ->0.
```

Consequently these one-edge relation paths do answer the maintained
near-return question in that branch.  The orientation repair is therefore
not cosmetic in notation, but it leaves the conclusion fully valid.

## Wall root displacement

At `U^N`, if a replacement exact root `z` does not make witness `j` Quit
surely, Continue has positive support and its Quit-minus-Continue gap is
nonpositive.  The incoming solo root has strictly positive gap.  The
forced-action difference is an expectation over opponents of a function
bounded in absolute value by `2M`.  Coupling the two product opponent laws
and using the union bound gives

```text
Delta_j(U^N,q)
 <=4M sum_(ell!=j)|z_ell-q_ell|.
```

Thus `(4.1)` has the correct factor and orientation.  If `z_j=1`, absorption
is exactly one.  As the note stresses, this is only a source-specific positive
distance: the all-Continue root can realize it by deleting the old owner's
hazard, so it is not yet semantic debt descent or a paid return.

## Scope

After the arrow repair, the theorem is a valid literal carrier-enriched
bounded-depth reduction.  It does not select an exact root at the wall,
lower debt there, prove support activation, or close the paid near-return
producer.  I agree with keeping it internal.
