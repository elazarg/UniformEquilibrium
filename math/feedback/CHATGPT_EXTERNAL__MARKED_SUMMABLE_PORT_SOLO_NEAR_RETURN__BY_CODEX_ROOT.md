# Review of marked summable-port solo near-return

Reviewer: `CODEX_ROOT`

Contribution: external `ChatGPT` argument supplied by the user

## Verdict

**REVISE.**  The singleton-tight solo iteration is valid for a prescribed-
payoff exact floor orbit on the minimum fiber.  It does not compose with the
new cap-lifted port, whose roots are exact Nash against behavioral caps.

The proposed Fin4 large-base closure and the claim that the marked cap port
already forces cumulative near-return are therefore unsupported.  The valid
minimum-fiber prescribed-orbit lemma is retained internally.

## Exact type mismatch

The equality-stratum theorem
`quittingTerminalSemanticDebt_prefix_eq_of_minimum` assumes

```text
IsεQuittingRootNash reward pair.1 0 root,
```

where `pair.1=U` is the prescribed coordinate.  Its positive-debt face theorem
then gives unit **opponent** Continue mass and zero exercise premium, allowing
one debtor's solo Quit mass to remain.

The cap lift instead supplies

```text
IsεQuittingRootNash reward pair.2 0 root,
```

and the exact identity

```text
Debt(Prefix(root,pair),i)=JointContinue(root)*Debt(pair,i).
```

If total positive debt is constant along this cap-Nash prefix, joint Continue
must equal `1`; the root is all Continue.  A positive labelled root cannot lie
in this equality case.  One cannot replace this joint-scaling theorem by the
prescribed equality-stratum theorem.

## Solo iteration mismatch

The controlled solo root is proved exact Nash against `pair.1`.  The file
`TerminalSemanticSingletonTightMinimumFaceIteration.lean` separately proves
that its owner has cap-Nash defect exactly

```text
rate*DebtSum(pair)>0.
```

Thus the proposed positive solo edge cannot be appended to the exact cap
orbit.  Moreover, the cap port guarantees the punishment floor for `b∞`, not
for `u∞`; the cumulative admissible path requires its displayed prescribed
annotations to be floor-safe.

## What survives

Suppose independently that:

1. the orbit is exact Nash against its prescribed values;
2. those prescribed values dominate punishment;
3. the semantic orbit and limit lie on the positive global minimum fiber; and
4. a signed label has positive cumulative root mass.

Then the contribution's unique-debtor argument is correct.  A charged stage
has one solo owner, the port is singleton-tight, the controlled positive solo
root iterates on that face, and late fixed-length segments give cumulative
charge at least `1` with vanishing payoff seam.

This is a useful conditional composition of existing declarations, but it
does not have the actual-data adapter claimed in the answer.

## Descent arm

The off-minimum case also needs sharper wording.  Choosing the already-known
global minimizer below an off-minimum port is neither a directed exact path nor
a well-founded reduction.  A finite incoming debt drop is genuine, but a
strict decrease in a real-valued quantity does not by itself permit finite
iteration.  The descent arm requires a named consumer, a uniform decrement,
or a finite rank before it can count as closure.

## Export decision

Keep internal.  The claimed cap-port consumer fails, and the surviving
prescribed-orbit theorem remains conditional on the floor/source interface
that the cap lift was introduced to avoid.

