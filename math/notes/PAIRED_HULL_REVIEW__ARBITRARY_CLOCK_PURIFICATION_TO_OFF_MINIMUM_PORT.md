# Arbitrary-clock purification reaches the off-minimum paid-port waist

Identity: PAIRED_HULL_REVIEW  
Status: ordinary-mathematics proof draft; not Lean checked; independent review requested

## 1. Result

Let \(I\) be finite and let \(D_*>0\) be the global minimum of total complete
terminal-semantic debt. Suppose one retained sequence of actual behavioral
profiles satisfies

\[
 \operatorname{Sem}(\sigma_n)\longrightarrow z_*,
 \qquad D(z_*)=D_*.
\tag{1.1}
\]

After literal one-player replacements on strict refinements of this same
sequence, one obtains either

1. an actual descendant family staying a fixed distance above \(D_*\),
   with an outgoing complete behavioral paid first-disagreement row; or
2. one actual canonical pure-time/Never profile attaining \(D_*\) exactly.

The reviewed pure finite-clock deadline-rank theorem sends alternative 2 to
alternative 1. Thus every retained positive-minimum realizing sequence
produces a source-attached off-minimum paid port.

This contracts arbitrary mixed-clock minimum sources to the already open
off-minimum waist. It does not consume that waist.

## 2. One arbitrary own clock can always be purified

Fix an actual profile \(\sigma\) and a player \(h\). Let
\(\pi_h\) be the stopping-time law induced by \(h\)'s behavioral strategy on
\(\overline{\mathbb N}=\mathbb N\cup\{\infty\}\). Against the fixed opponents
put

\[
 V_h(q)=U_h(\operatorname{QuitAt}(q),\sigma_{-h}),
\]

with \(q=\infty\) denoting Never. Behavioral payoff is the exact average

\[
 U_h(\sigma)=
 \sum_{q\in\overline{\mathbb N}}\pi_h(q)V_h(q).
\tag{2.1}
\]

There is a positive-support point \(q_h\) with

\[
 V_h(q_h)\ge U_h(\sigma).
\tag{2.2}
\]

Otherwise every positive summand in the expectation of
\(U_h(\sigma)-V_h(q)\) would be strictly positive while their sum is zero.
The literal replacement

\[
 \sigma\longmapsto
 \sigma[h\leftarrow\operatorname{QuitAt}(q_h)]
\tag{2.3}
\]

therefore does not lower the mover's prescribed payoff and makes its complete
strategy pure-time/Never. Its unrestricted cap is unchanged because its
opponents are unchanged. No cap assertion is made for the other players.

This works for arbitrary countable support and does not assume cap
attainment.

## 3. Finite purification with an off-minimum split

Process the players in a fixed order. Suppose the current descendant family
\(\sigma_n^k\) is a strict refinement satisfying

\[
 D(\operatorname{Sem}(\sigma_n^k))\longrightarrow D_*,
\tag{3.1}
\]

and its first \(k\) players already use pure clocks. Apply (2.3) to player
\(k+1\). Total debt is bounded, so refine until

\[
 D(\operatorname{Sem}(\sigma_n^{k+1}))
 \longrightarrow L_{k+1}\ge D_*.
\tag{3.2}
\]

If \(L_{k+1}>D_*\), the targets are uniformly off minimum after a finite
discard. More explicitly, put

\[
 \varepsilon=\frac{L_{k+1}-D_*}{2}>0.
\]

Eventually the target debt is at least \(D_*+\varepsilon\). Choose a
maximum-debt player at every target and stabilize its label. In Fin4 that
coordinate then has debt at least \((D_*+\varepsilon)/4\), giving an
explicit fixed positive debt floor. The actual-reach
first-disagreement theorem supplies an outgoing actual paid row on those
same targets. The source profiles, purification targets, and paid rows stay
on one refinement of the incoming sequence.

If \(L_{k+1}=D_*\), continue. Later steps never edit an already purified
player. After at most \(|I|\) equality steps one gets literal descendants
\(\xi_n\) in which every player uses a pure time or Never and

\[
 D(\operatorname{Sem}(\xi_n))\longrightarrow D_*.
\tag{3.3}
\]

For Fin4 there are at most four such replacements per source profile.

## 4. Finite relative-order lemma

For a pure-clock profile \(t=(t_i)_{i\in I}\), define its calendar type by:

1. the ordered partition of finite-deadline players into deadline-tie blocks;
2. the set of Never players; and
3. the total first-date flag: `none` if every player uses Never, and otherwise
   `zero` or `positive` according as the first finite deadline is zero or
   strictly positive.

There are finitely many types for fixed finite \(I\).

### Lemma 4.1

Two pure-clock profiles of the same calendar type have exactly the same
prescribed terminal payoff, unrestricted behavioral cap vector, terminal
law, and debt vector.

### Proof

The prescribed outcome is the first finite tie block, or Never.

Fix player \(i\). If no opponent has a finite deadline, finite stopping gives
the singleton payoff \(s_i\), while Never gives zero, so

\[
 B_i=\max\{s_i,0\}.
\tag{4.1}
\]

Otherwise let \(m\) be the earliest opponent deadline and \(A\) its tie
coalition. A pure response has only the values

\[
 \begin{array}{c|c}
 q<m&s_i,\\
 q=m&r_i(A\cup\{i\}),\\
 q>m\text{ or }q=\infty&r_i(A).
 \end{array}
\tag{4.2}
\]

The first value is available exactly when \(m>0\). The calendar type
determines this fact and \(A\). Every behavioral response averages pure-time
values, so the unrestricted cap is their maximum. This proves the lemma.

The three-way `none`/`zero`/`positive` first-date flag is essential and is
total, including the all-Never profile. Absolute deadline gaps and later
escape to infinity are not.

## 5. Exact attainment in the equality branch

Apply finite pigeonhole to (3.3) and retain one calendar type. Lemma 4.1 says
that all pairs \(\operatorname{Sem}(\xi_n)\) on this subsequence are literally
equal to one pair \(z^{\mathrm{pure}}\). Hence

\[
 D(z^{\mathrm{pure}})=D_*.
\tag{5.1}
\]

Every retained \(\xi_n\) is therefore an actual pure-time/Never global
minimum. No limit of QuitAt-\(t_n\) strategies is taken, so the usual
time-escape discontinuity is absent. Choose one retained index; it keeps its
finite literal ancestry from the corresponding source profile.

The independently reviewed theorem
PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT now applies to this
actual profile. Anchored erasure and deadline-support descent construct an
actual off-minimum pure-clock profile, an outgoing complete behavioral
response of positive gain, and its literal first-disagreement row.

Combining the strict and equality branches gives

\[
\boxed{
\text{retained positive-minimum realizing sequence}
\Longrightarrow
\text{source-attached actual off-minimum paid port}.}
\tag{5.2}
\]

## 6. Source correspondence

For a FinFourMinimumAtomProducer, start with its retained literal realizing
profiles or a later source-faithful refinement. Every purification is
performed on those exact profiles. In the strict branch the target and paid
row remain indexed by the same refinement. In the equality branch the
selected actual pure minimum retains its finite replacement ancestry from
one source profile.

If a new minimum-law source wrapper is wanted at the pure endpoint, its joint
point is attained by that endpoint. Hard-residual finite-atom selection and
source-faithful causalization therefore need not change the semantic target.

The theorem bypasses full-debt and reset-rigid descriptions as terminal
components by acting on the incoming minimum realization itself. It does not
show that a later off-minimum construction cannot return to such a chamber.

## 7. Boundaries and nonclaims

1. The proof stabilizes exact calendar types; it does not assume cap
   continuity under QuitAt-\(t_n\to\infty\).
2. A purification edge may have zero gain. A separate max-debt response is
   used in the strict branch.
3. The finite replacement list is ancestry, not Nash--Bellman chronology.
4. The result gives no consumer for the off-minimum paid port.
5. The number of non-pure clocks is a finite rank only within this one
   source-to-port contraction. It is not a renewable global atlas rank.

## 8. Lean-facing obligations and sources

The new reusable statements are:

    exists_support_pureTime_payoff_ge_prescribed
    pureClock_semantics_eq_of_calendarType_eq
    minimumRealizingSequence_purify_or_offMinimumPaidPort
    minimumRealizingSequence_exists_offMinimumPaidPort

The first must use the actual stopping law and its expectation, not an
unsupported cap selector. The second must retain the first-deadline flag.

The stopping-law expectation and support APIs are in
UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean and
fable/lean/FableStoppingSelection.lean. The actual-reach output is in
fable/lean/FableDebtActualReach.lean. The finite-clock capstone is
formalized/PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT.md.

A narrow search found finite-support purification but no arbitrary-support
realization theorem using finite pure-clock calendar types.
