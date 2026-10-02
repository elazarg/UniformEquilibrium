# Review of unique-sure child to shifted-cap ray

Reviewer: CODEX_GROMOV

Reviewed exact SHA-256:
`8e6e657578a31093b3e133757b6763fd60599c8c05ff12d497dc3f87ab0c8916`

## Verdict

**REVISE, with one finite case omission.** The unique-sure theorem itself is
correct: global exact-block capacity makes the zero-survival indices finite;
the last unique-sure root leaves one distinct finite-clock anchor, selects the
unique debtor, attains its cap by a finite pure time or Never, and transports
that same cap with a positive debt floor through every later positive-survival
root. The indices and product estimates check.

The displayed exhaustive conclusion (18), however, omits the case in which
there is no zero-survival root at all. In that case there is no “last
zero-survival index” `L`. For the late-reset application this case is already
handled by Hahn's positive-survival restart, but the standalone arbitrary-
source theorem as written needs either:

1. an input assumption that some zero-survival root occurs; or
2. a third branch saying all selected roots have positive survival, with the
   initial finite-clock source supplying a fixed debtor and attained
   finite/Never cap which shifts from depth zero.

The second repair is immediate: the fixed anchor `b` has zero debt at
`sigma^0`; the terminal gap chooses `k != b` with debt at least `Gamma`; the
anchor makes `k`'s cap attain its maximum among finitely many times and Never;
then Section 3 transports it through all roots. No new compactness is needed.

## Checks which pass

### Zero-survival indices are finite

For every `N`, the literal chronology is
`q^(N-1),...,q^0,sigma^0`. It is one exact Nash--Bellman block in the
canonical box. The checked no-uniform-payoff capacity theorem bounds its sum
of marginal hazards uniformly in `N`. Every zero-joint-survival product root
has at least one marginal Quit probability equal to one, so only finitely
many such indices can occur.

### Last unique-sure child

If `k` is the unique sure quitter, every other coordinate has zero debt after
the prefix because its opponents-Continue factor is zero and exact root Nash
has no local defect. The terminal gap is therefore carried by `k`, so
`d_k >= Gamma`; since the persistent finite-clock anchor `b` has zero debt,
`k != b`.

The positive `k`-debt activates the Continue-cap branch. Because `b` remains
a distinct sure quitter by a finite date even after replacing `k`, the tail
cap is attained among the finitely many relevant pure times and Never. The
child cap is exactly Continue followed by that tail cap, hence its clock is
shifted by one (or remains Never).

### Later transport and the product floor

At every later positive-survival root, `k` has positive Continue support.
Exact root Nash makes its prescribed Continue endpoint maximal; replacing the
tail payoff by the strictly larger cap makes the cap Continue branch uniquely
maximal. Thus

`d_k(sigma^(n+1)) = s_(n,k) d_k(sigma^n)`

and the same attained cap shifts literally. Since
`s_(n,k) >= c_n`, the post-last-zero marginal hazard series is summable and
no later factor is zero, the infinite product is strictly positive. This
gives the claimed uniform fixed-debtor floor. The indexing in (12), (16), and
the reversed finite block (13) is consistent.

## Scope

The repaired theorem remains a literal source theorem, not a forward infinite
chronology or consumer. A common fixed finite-clock anchor ensures cap
attainment, but the clocks still escape to the far end under reverse
prefixing. Repeated owner renewal still crosses horizontal cap-child seams.

## Delta review of repaired revision

Repaired exact SHA-256:
`dd1da90ccc9fafb7fbc994799d708148470e641d843849aaec0aab65f785133d`

**PASS.** The new three-branch statement is exhaustive. If no zero-survival
root occurs, it selects the fixed debtor and attained finite/Never cap already
at `sigma^0`, then applies the same positive-survival transport. If zero roots
occur, the two-sure terminal branch and last-unique-sure branch are exactly as
reviewed. The explicit boxed annotations also make the reverse chronological
block used by the capacity theorem unambiguous. No conclusion or constant was
strengthened beyond the repaired proof.

## Exact-final export review

Candidate:
`/tmp/FIN4_UNIQUE_SURE_ACTUAL_CHILD_LITERAL_SHIFTED_CAP_RAY.md`

Exact SHA-256:
`08a5cce730f2fbc179cac6eb494582aafc5d9cf5ab89752f49262dd1fa23e834`

**PASS.** The standalone packet retains the corrected exhaustive three-way
statement, including the no-zero-survival initialization at `sigma^0`, and
faithfully preserves the source theorem's cap attainment, shifted-cap debt
product, distinct finite anchor, literal reverse-block provenance, and
projective nonconsumer boundary. It introduces no stronger claim or omitted
hypothesis.
