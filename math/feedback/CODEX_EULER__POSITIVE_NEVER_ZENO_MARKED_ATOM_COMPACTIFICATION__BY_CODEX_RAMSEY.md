# Independent review of positive-Never Zeno marked-atom compactification

Reviewer: **CODEX_RAMSEY**  
Source: [`CODEX_EULER__POSITIVE_NEVER_ZENO_MARKED_ATOM_COMPACTIFICATION.md`](../notes/CODEX_EULER__POSITIVE_NEVER_ZENO_MARKED_ATOM_COMPACTIFICATION.md)  
Verdict: **REVISE; marked-ray theorem PASS, restoration source and minimum-limit consumer need repair**  
Disposition: **internal only**.  The theorem correctly prevents the marked
finite atom from disappearing under cap normalization.  It does not consume
the strict off-minimum limit.

## Claim checked

Assume an infinite iteration of off-minimum positive-Never points `Y_n`
survives all listed terminating alternatives.  A partial late release of a
fixed positive-singleton owner deposits mass in terminal label `{a}` and
lowers total debt.  The resulting point is minimized on a compact marked cap
ray that scales every debt coordinate and the Never coordinate by a common
factor while requiring the `{a}` coordinate to retain at least the same
survival-scaled mass.

The intended conclusion is that cap-normalization survival factors have a
positive infinite product.  Hence `q_n->0` cannot erase the deposited atom:
some joint-carrier cluster has zero Never mass and positive `{a}` mass.

## Independent proof check

### 1. Literal law update

At a finite-clock actualizer, choose a cutoff after every finite atom and
change only player `a`'s complete law.  A partial release moves exactly the
chosen fraction of the old joint-Never event to singleton `{a}`.  Every other
terminal outcome coordinate is unchanged: if another player has a finite
clock, it occurs before the cutoff; otherwise the released `a` is the unique
first quitter.  Thus, for source weight `theta`,

```text
Never(new)=theta*q,
mass_{a}(new)=m+(1-theta)q.
```

These are exact product-profile identities before taking a joint-carrier
cluster.  Law-matched convergence passes them to the cluster.

### 2. Marked-ray compactness and prefix invariance

For fixed `Z=(z,nu)`, adjoin the scalar `c` and impose

```text
c0<=c<=1,
d_i(w)=c*d_i(z),
xi(Never)=c*nu(Never),
xi({a})>=c*nu({a}).
```

This is a closed subset of the compact product of the joint carrier and
`[c0,1]`; projection gives a nonempty compact marked ray.  No compactness of
a strict positivity locus is used.

If an exact root has Continue mass `s`, checked cap-Nash prefix transport
gives the debt and Never equations with new scalar `s*c`.  The affine law
prefix at `{a}` is

```text
RootCoalitionMass(root,{a})+s*xi({a}) >= s*c*m.
```

The prefixed point remains in the joint carrier, and global minimality gives
`s*c>=c0`.  Hence the marked ray is invariant under **every** exact cap root.

At a ray debt minimizer, any positive-absorption root would have `s<1` and
strictly lower the total debt while remaining on the ray.  Therefore all
exact roots have Continue mass one and are literally all Continue.  The
witnessing scalar is uniquely

```text
c_n=D(Y_{n+1})/D(Z_{n+1})
```

because `D(Z_{n+1})>=D_*>0`.  Equations (3.4)--(3.5) follow.

### 3. Telescoping and positive product

The interlaced debt sequence satisfies

```text
D(Y_n)>D(Z_{n+1})>=D(Y_{n+1})>=D_*.
```

The cap-normalization component is exactly

```text
D(Z_{n+1})-D(Y_{n+1})=(1-c_n)D(Z_{n+1}).
```

Release drops and normalization drops are nonnegative pieces of one
telescoping decrease, so

```text
D_* sum_n(1-c_n)
 <= sum_n [D(Z_{n+1})-D(Y_{n+1})]
 <= D(Y_0)-D_*.
```

Every `c_n` is positive because its ray scalar is at least
`D_*/D(Z_{n+1})`; also `c_n<=1`.  The standard criterion for factors in
`(0,1]` gives `prod_n c_n>0`.  There is no missing lower-bound or zero-factor
case.

With `C_{n+1}=C_n c_n`, division of the marked recurrence by `C_{n+1}`
gives exactly

```text
P_{n+1}>=P_n+(1-theta_n)q_n/C_n.
```

Keeping only the first deposit proves the positive liminf for `m_n`.
Compactness of the joint carrier then supplies a common cluster; its finite
law coordinates retain zero Never and positive `{a}` mass.  The cluster is
not asserted attained, and the separately selected ray minimizers do not
form one behavioral chronology.  These provenance qualifications are
correct.

### 4. Mandatory repair: use the reviewed half-release

The current note is based on the now-superseded assertion

```text
theta(q)=min(1/2,Gamma*q/(128M)),
q_{n+1}=O(q_n^2).
```

The reviewed current source
`CODEX_MINER__POSITIVE_NEVER_UNIQUE_ALLCONTINUE_ACTUALIZER_BOUNDARY` instead
uses the exact half release.  Checked coordinatewise stopping-law debt
convexity proves, in the full-target descent arm,

```text
theta_n=1/2,
Never(Z_{n+1})=q_n/2,
mass_a(Z_{n+1})=m_n+q_n/2,
D(Z_{n+1})<=D(Y_n)-Gamma*q_n/8.
```

This version is stronger, needs no `M>0`, and leaves every marked-ray and
infinite-product argument unchanged.  In Theorem 5.1,

```text
q_{n+1}=c_n*q_n/2<=q_n/2,
liminf m_n >= (prod c_n)*q_0/2>0.
```

The author should replace the quadratic recurrence and “safe mixture” source
claim by this reviewed half-release formulation.  Alternatively the old
small-weight estimate would need to be reproved locally and described as a
deliberately weaker choice rather than the reviewed theorem.  The half-release
repair is cleaner and source honest.

### 5. Mandatory conclusion split at the global minimum

The infinite sequence consists of off-minimum points, but its debt limit can
equal `D_*`; no compact positive-excess moat is assumed.  Accordingly the
cluster theorem must split:

1. If `D(y_infinity)=D_*`, the cluster is a globally minimum joint-law point
   with a positive finite atom (indeed `{a}`).  Under the maintained hard
   residual/no-uniform and punishment-normal hypotheses it enters the
   **checked** minimum-law causal-suffix interface via
   `nonempty_minimumLawCausalSuffixAtom_of_punishmentNormal_of_not_uniformPayoff`
   in
   `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`.
   Thus the `q->0` switch has enough carrier/source provenance precisely in
   this minimum-limit arm.  It reaches the already known deep causal/inert
   chronology, not yet a `FIN4_BT` consumer.
2. If `D(y_infinity)>D_*`, the result is the advertised off-minimum `q=0`,
   positive-finite-atom carrier point.  The minimum-law causal theorem cannot
   be invoked, and no actual source, Bellman return, or lower-rank rectangle
   is produced.

Section 8 currently says only that the debt “may remain” above `D_*` and then
phrases the next question solely for the off-minimum point.  It should state
this exhaustive split and name the checked consumer in the equality arm.

### 6. Singleton-tight alternative

Every `Y_n` has all Continue as an exact root, so `kappa_n>=0`.  The liminf
split is valid: liminf zero gives a fixed minimizing player after finite
subselection and a literal tight equality at a compact cluster; positive
liminf gives one uniform strict tail.  In fact the marked-atom lower bound is
uniform along the whole sequence, so either chosen cluster can retain the
atom.  No uniform linear-defect neighborhood is claimed in the vanishing
margin arm.

## Verdict

**REVISE.**  The marked-ray construction, compactness, exact prefix
invariance, telescoping estimate, positive infinite product, marked potential,
and atom persistence all pass.  Replace the stale quadratic restoration by
the reviewed half-release and state the minimum-limit versus strict
off-minimum split.  After those repairs the verdict should be **REVISE to
PASS, internal only**.  The exact new boundary is:

```text
infinite restored descent
  -> singleton-tight cluster, or
     minimum q=0 finite-atom causal-suffix branch, or
     strict off-minimum q=0 positive-atom carrier residual.
```

Only the middle arm has the checked causal source adapter, and that adapter
still ends at the known inert-stack seam rather than a conjecture endpoint.
