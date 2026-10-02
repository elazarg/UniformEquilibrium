# Feedback on `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION` — Round 40

## Claim checked

I independently checked Section 60, Proposition 80: unbounded sublinear
maximal finite-prefix charge on a compact closed predecessor-serial relation
need not produce one infinite path of divergent total charge.

**Verdict: VALID ordinary mathematics after one definitional clarification.**
The intended `A_N` should be stated explicitly as

```text
A_N = sup {sum_(t=0)^(N-1) a(omega_t) : omega in Omega}.
```

With that standard meaning, all estimates and path quantifiers check.

## Verification

Every state `y_(n,k)` lies in the square with both coordinates at most `1/n`.
Thus any sequence whose branch index tends to infinity converges to `o`; a
bounded branch index has a constant subsequence in a finite set.  This proves
compactness.  For the edge graph, a convergent sequence is either eventually
inside one finite branch or has both endpoints tend to `(o,o)`, which is an
edge.  Hence the relation is closed.

The self-loops give predecessors to `o` and every `y_(n,0)`; each later state
has the preceding branch state as predecessor.  From any state the unique
positive branch suffix reaches `o`, so every state has a viable infinite
future.  The charge is continuous: nonzero branch charges are `1/n`, tending
uniformly to `a(o)=0` as states approach `o`.

An infinite path can wait on at most one `y_(n,0)` zero-loop and then traverse
only branch `n`; after reaching `o` it cannot enter another branch.  It
therefore pays at most the finite total `n^2/n=n`.  This verifies the
individual-path quantifier, including paths starting in the middle of a
branch.

For an `N`-row prefix, branch `n` offers at most

```text
min(N,n^2)/n.
```

Starting at `y_(n,1)` attains this quantity, so the horizon indexing has no
lost initial zero row.  If `n<=sqrt(N)`, the expression is `n<=sqrt(N)`; if
`n>=sqrt(N)`, it is at most `N/n<=sqrt(N)`.  Thus `A_N<=sqrt(N)`.  With
`n=floor(sqrt(N))`, one has `n^2<=N` and the complete branch contributes `n`,
giving the stated lower bound, including `N=1`.

## Exact scope

The example is not embedded in the quitting punishment-floor relation.  It
does exactly refute the generic compactness inference from unbounded finite
prefixes to a single divergent path; a quitting-game proof must add nesting,
source matching, or game-specific geometry.
