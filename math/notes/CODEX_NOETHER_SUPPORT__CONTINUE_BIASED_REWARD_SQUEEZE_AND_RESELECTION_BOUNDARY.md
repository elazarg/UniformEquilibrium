# Continue-biased reward squeeze: the exact reselection boundary

Author: CODEX_NOETHER_SUPPORT.

Status: completed bounded operation test. The fixed-root comparison is
exact; it does not give an increasing unrestricted infimum or exclude
the opposed-reversal source. The required global envelope condition is
already in the extremal-table/coupled-calendar work. No new compiler,
raw-table class, solved-table trap, or export is proposed.

## 1. Concrete different-table operation

At a signed unit-cube table r, retain the four own singletons. For each
owner i and nonempty S⊆I\{i}, change its disjoint membership pair by

    r_i^t(S)=(1−t)r_i(S)+t,
    r_i^t(S∪{i})=(1−t)r_i(S∪{i})−t,      0≤t≤1.          (1)

These pairs partition the other 56 coordinates, so (1) is one common
feasible reward perturbation, not a source-conditioned reward table.
Every Continue-minus-Quit difference on such a pair becomes

    g^t=(1−t)g+2t.                                      (2)

After this change, ALL four independent stopping laws are allowed to
reselect when computing η(r^t). The test was whether original worst-table
maximality forbids a positive three-sure opposed-reversal minimum through
this operation. It is not another sure-owner clock release.

## 2. Exact fixed-root full-cap comparison

Let K be three sure date-zero owners, o the optional owner, and p its
Quit probability, with 0<p<1; all later prescribed clocks are Never.
Every unilateral response still has a sure opponent at date zero.
Hence Quit at zero and Continue are the entire cap menu; every later
finite response and Never have the Continue payoff. No singleton or
post-support response is dropped.

If the root is an attained positive global minimum m, all four full
debts equal m. Each sure owner's Continue-minus-Quit expectation is m,
so after (1), at the SAME laws, its complete debt is

    d_i^t=(1−t)m+2t,       i∈K.                           (3)

This strictly increases for t>0 because m<1/2. The root's full E
therefore increases. This is a fixed-profile fact, not yet a fact about
η(r^t).

For the optional owner put G=Continue−Quit at the original root.
If Continue is best, m=pG and, for small t, its debt derivative is

    (d_o^t)'_(t=0)=2p−m.                                (4)

If Quit is best, m=(1−p)(−G), and the derivative is instead

    (d_o^t)'_(t=0)=−2(1−p)−m<0.                         (5)

The active optional response in (5) is genuinely part of the complete
max-debt envelope. It cannot be discarded because (3) rises.

For an opposed-reversal root in the Continue-best case, the core with
negative Continue-minus-Quit gap when o is absent has a positive gap
when o is present. Its expected gap m forces 2p>m. Thus (4) is strictly
positive in that particular case. Even positivity of all these rows at
one supplied root does not control jointly reselected laws.

## 3. Which global datum would be needed

The original table r* maximizes η on the full reward cube. The final
membership-stretched table r maximizes η only over its four own
singletons. Perturbation (1) changes the frozen 56 coordinates, so
final-table fiber maximality does not apply to it. Applying (1) at r*
is legal for original maximality, but the supplied final-table root
need not be a minimizing profile at r*: the source gives η(r*)≥m,
not E_(r*)(q)=η(r*).

There is a second, independent obstruction even if one assumes that
equality. An increase at one old minimizing profile is not an increase
of the infimum after law reselection. Nor would a fixed-profile increase
at every old minimizer alone justify freezing the nonsmooth active
response set as the laws move on the perturbation scale.

The needed common set is ALL limiting complete response rows that are
near-active at ALL globally near-minimizing actual profiles of r*.
HILBERT's approximation-safe separation theorem explicitly uses this
set, rather than a chosen root or a finite sample. A uniformly positive
directional account on that entire set gives a genuine increase of η.
The present source neither places that set inside the three-sure face
nor controls the rows outside it. In the Quit-best case (5) even the
selected root already has a negative active response derivative.

The stronger coupled-calendar theorem retains actual source laws and
their SAME tester weights while deriving a full reward normal only for
the COMPLETE tuple mixture. Formula (1) may be paired with that normal,
but selecting a convenient three-sure entry does not retain normality.
The resulting averaged directional inequality is precisely an existing
necessary envelope condition, not a new upper or lower comparison for
this operation. No common exposed face containing all minimizing law
limits has been proved here.

## 4. Narrow corpus check and stopping point

The relevant proof, quantifiers, and boundary were read in:

- [HILBERT's extremal-table test](CODEX_HILBERT__EXTREMAL_REWARD_TABLE_VARIATIONAL_TEST.md),
  the approximation-safe cube-normal separation and complete limiting
  response family;
- [the coupled-calendar source](CODEX_NOETHER_SUPPORT__WORST_REWARD_TABLE_COUPLED_CALENDAR_CERTIFICATE.md),
  the smoothed outer envelope, joint law reselection, and same-tuple
  reward normal;
- [SKEPTIC's global portfolio dual](CODEX_SKEPTIC__GLOBAL_PORTFOLIO_DUAL_AND_SINGLETON_RAY.md),
  the alternative nonlocal mechanism using ALL response selectors on
  a complete timing portfolio.

The portfolio mechanism does not bypass this boundary: its convex
certificate ranges over whole finite portfolios, not only globally
near-minimizing sources or the supplied opposed root. The existing
singleton-ray source likewise does not identify its profile with the
worst-table source. No legal identification was found in this check.

Therefore this Continue-biased operation is stopped at (3)–(5) and
the exact missing all-source comparison. The next mathematical question
is not another formula for this direction: it is whether a different
operation controls the complete limiting family, or whether an actual
additional source theorem confines that family to an identified face.
No further scalar normal-form packaging is proposed.
