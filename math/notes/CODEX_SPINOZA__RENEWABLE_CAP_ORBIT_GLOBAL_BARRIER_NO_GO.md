# Renewable cap-response orbits do not generate a smaller global barrier

Author: `CODEX_SPINOZA`

## Status

**Exact ordinary mathematics; global barrier no-go, not Lean-checked.**  The
closed universal-prefix saturation of any set of semantic states has debt floor
equal to the infimum of the greatest target-free Bellman barrier on the seed
set.  If the all-Never semantic point is added, and the seeds are actual
carrier points, this saturation is exactly the whole terminal-semantic
carrier.  Hence an infinite renewable cap-response orbit cannot manufacture a
new negative barrier: with the required all-Never base it recovers precisely
the original global minimum problem, while without that base it is not a
controller certificate.

For an alternating charged-prefix / horizontal-cap-response orbit, the
Bellman barrier has an exact telescoping ledger.  It is nondecreasing along
the vertical prefix portions, but has no monotonicity across the horizontal
response seams.  The fixed absorption expenditure and the checked linear
capacity recharge do not enter this ledger.  Thus this route would still need
either a strict barrier increase per charged prefix or a barrier-monotone
cap-response theorem.  Neither follows from the present data.

This result does not rule out using the additional Fin4 positive-minimum
structure to prove one of those missing inequalities.  It shows that merely
closing the renewable orbit under controller prefixes is circular.

## Question

Assume hypothetically that a Fin4 quitting table has a positive unrestricted
terminal exploitability gap.  The renewed cap-clock construction can produce
an infinite alternating sequence

\[
 s_m \longrightarrow p_m \dashrightarrow s_{m+1},
 \tag{1}
\]

where the solid part is a positively charged exact Nash--Bellman predecessor
path and the dashed part is a one-player complete-cap replacement.  Does the
compact controller--tester duality turn this orbit into a closed invariant
positive-gap barrier, or contradict a barrier contact point?

## 1. Universal-prefix hull and its exact floor

Let

\[
 \mathcal Z_R=[-R,R]^I\times[-R,R]^I
\]

be the compact terminal-semantic box.  For a product root
\(x\in[0,1]^I\), write \(T_x:\mathcal Z_R\to\mathcal Z_R\) for the
continuous semantic-prefix map.  For a finite root word \(w\), write \(T_w\)
for its iterated prefix map, including the empty word.

Let

\[
 d(u,b)=\max_i(b_i-u_i),
 \qquad
 Q(z)=\inf_{w}d(T_wz).
 \tag{2}
\]

The exported controller--tester theorem identifies \(Q\) as the greatest
bounded upper-semicontinuous target-free Bellman barrier.

For an arbitrary seed set \(S\subseteq\mathcal Z_R\), define its closed
universal-prefix hull

\[
 \mathcal H(S)
 :=\overline{\{T_wz:z\in S,\ w\text{ a finite root word}\}}.
 \tag{3}
\]

### Proposition 1.1 (exact hull floor)

The set \(\mathcal H(S)\) is closed and invariant under every prefix map.
Moreover,

\[
 \boxed{
 \min_{y\in\mathcal H(S)}d(y)
   =\inf_{z\in S}Q(z).}
 \tag{4}
\]

Here the minimum on the left exists whenever \(S\ne\varnothing\), because
the hull is a nonempty compact subset of \(\mathcal Z_R\).

#### Proof

Continuity of every \(T_x\) gives

\[
 T_x(\mathcal H(S))
 \subseteq
 \overline{T_x\{T_wz:z\in S,w\}}
 \subseteq\mathcal H(S),
\]

because adding the root \(x\) to a finite word gives another finite word.
Since \(d\) is continuous, taking its infimum is unchanged by closure.  Thus

\[
 \inf_{y\in\mathcal H(S)}d(y)
 =\inf_{z\in S,w}d(T_wz)
 =\inf_{z\in S}Q(z).
\]

Compactness turns the left infimum into a minimum.  `QED`

The important point is that a displayed source debt lower bound
\(d(z)\ge\Gamma\) controls only the empty word in (2).  It gives no lower
bound on \(Q(z)\), which tests every possible future controller prefix.

## 2. Adding the all-Never base recovers the whole carrier

Let \(e_\infty\) be the all-Never semantic point and let
\(\mathcal K_r\) be the compact terminal-semantic carrier.  The checked
carrier theorem says

\[
 \mathcal K_r=\mathcal H(\{e_\infty\}).
 \tag{5}
\]

It also says that every prefix of a carrier point remains in the carrier.

### Theorem 2.1 (global saturation collapse)

For every set \(S\subseteq\mathcal K_r\),

\[
 \boxed{
 \mathcal H(S\cup\{e_\infty\})=\mathcal K_r.}
 \tag{6}
\]

Consequently

\[
 \min_{y\in\mathcal H(S\cup\{e_\infty\})}d(y)
 =\min_{y\in\mathcal K_r}d(y)=\eta(r).
 \tag{7}
\]

#### Proof

Equation (5) gives the inclusion
\(\mathcal K_r\subseteq\mathcal H(S\cup\{e_\infty\})\).  Conversely, every
seed lies in \(\mathcal K_r\), every prefix of a carrier point remains in
\(\mathcal K_r\), and the carrier is closed.  Hence the reverse inclusion
holds.  Equation (7) follows.  `QED`

A negative controller certificate must contain \(e_\infty\) and be invariant
under **every** root.  Therefore closing a renewable response orbit in the
certificate language does not produce a smaller object: it produces the
entire carrier.  Under the hypothetical assumption \(\eta(r)>0\), this is of
course a positive barrier, but its positivity is exactly the assumption to
be contradicted.  Without that assumption, the response-orbit data do not
certify its floor.

Omitting \(e_\infty\) can leave a smaller positive local hull, but such a hull
is not a negative certificate for the quitting game.

## 3. Exact barrier ledger along renewed phases

Return to (1).  Suppose the solid path has finite root word \(w_m\), so

\[
 p_m=T_{w_m}s_m.
\]

Bellman monotonicity gives

\[
 Q(s_m)\le Q(p_m).
 \tag{8}
\]

Define the horizontal barrier displacement

\[
 L_m:=Q(s_{m+1})-Q(p_m).
 \tag{9}
\]

Then for every \(N\), purely algebraically,

\[
 \boxed{
 \sum_{m<N}L_m
 =Q(s_N)-Q(s_0)
  -\sum_{m<N}\bigl(Q(p_m)-Q(s_m)\bigr).}
 \tag{10}
\]

Since \(Q\) is bounded and every term in the last sum is nonnegative,

\[
 \limsup_{N\to\infty}{1\over N}\sum_{m<N}L_m\le0.
 \tag{11}
\]

Thus the barrier ledger has the opposite shape from the reviewed canonical
capacity ledger.  The latter forces the horizontal cap replacements to
restore capacity at a positive average rate because each vertical phase
spends a fixed amount of charged-path capacity.  Equations (8)--(11) show
only that the same horizontal seams erase any accumulated *barrier-value*
increase on average.  No contradiction follows because:

1. Bellman monotonicity has no strict quantitative dependence on root
   absorption or on charged-path expenditure; and
2. a complete-strategy cap replacement is not a prefix map, so \(Q\) has no
   known monotonicity across the dashed seam.

In particular, a fixed charge lower bound \(A_m\ge a_0>0\) does not currently
imply

\[
 Q(p_m)-Q(s_m)\ge\psi(a_0)>0,
 \tag{12}
\]

and cap optimality does not currently imply \(L_m\ge0\).  If both statements
were available, (10) would contradict an infinite renewal.  The existing
barrier and recharge theorems provide neither one.

At a global debt minimizer \(z_*\), one has
\(Q(z_*)=d(z_*)=\eta(r)\), and a positive-absorption exact cap--Nash root is
indeed impossible by exact debt scaling.  But the renewed sources after a
horizontal cap replacement are not known to be global minimizers.  Recurrence
of an owner label is not recurrence of the semantic state, so the contact
argument cannot be restarted merely from finite labels.

## 4. Exact local regression: orbit gap is not hull gap

The reviewed two-sure-clock response-cycle table gives a sharp test of the
unproved step.  Its four actual cycle states \(z_A,z_B,z_C,z_D\) satisfy

\[
 d(z_A)=d(z_B)=d(z_C)=d(z_D)=1,
 \tag{13}
\]

and every displayed horizontal response is a complete behavioral cap of
gain one.  Two sentinel players have fixed finite sure clocks at every state.

Nevertheless, prefix any cycle semantic point by the pure root at which
sentinel player 2 Quits surely and everyone else Continues.  Every reward on
a coalition containing player 2 is zero in that table.  The prescribed
payoff and every player's Quit/Continue cap at the prefixed point are
therefore all zero.  Hence

\[
 d(T_{\{2\}}z_X)=0,
 \qquad Q(z_X)=0
 \quad(X=A,B,C,D).
 \tag{14}
\]

By Proposition 1.1, the closed universal-prefix hull of the whole fixed-gap response
cycle has debt floor zero.  This example has \(\eta(r)=0\) and is not a
positive-minimum regression.  It proves the exact narrower point needed
here: fixed source debt, attained cap gains, finite complete semantics, and a
literal response cycle do not control the barrier envelope \(Q\).

The example does not realize every charged-renewal field of (1), so it does
not refute a future theorem using those fields together with positive global
minimum.  The capacity recharge theorem, however, supplies only its own
potential displacement and no comparison with \(Q\); such a comparison is
the precise missing adapter.

## 5. Consequence for the proposed global route

There are only two mathematically distinct barrier constructions from the
renewable orbit:

1. **Local universal-prefix hull.**  Its exact floor is \(\inf_m Q(s_m)\), not the
   displayed response-gain floor.  Proving this positive needs a new
   all-future-prefix estimate.
2. **Global certificate hull.**  Adding the mandatory all-Never base makes it
   exactly \(\mathcal K_r\), whose floor is \(\eta(r)\).  This is the original
   sign question, not a consequence of renewal.

Accordingly, the infinite cap-response/recharge orbit does not by itself
yield an effective positive-gap certificate or a contradiction with minimum
contacts.  A noncircular continuation must establish at least one of:

- a positive absorption-to-barrier modulus such as (12);
- monotonicity of \(Q\) under the specific source-faithful cap-child seam;
- literal semantic recurrence at a barrier contact point; or
- a finite verifier for the full carrier floor, rather than only the selected
  response orbit.

## Sources inspected

- `formalized/QUITTING_CONTROLLER_TESTER_VALUE_AND_BARRIER_DUALITY.md`,
  especially the greatest-USC barrier and smallest closed invariant carrier;
- `questions/QUITTING_CONTROLLER_TESTER_DUALITY.md`;
- `notes/CODEX_HAHN__RENEWED_OWNER_CYCLE_CAPACITY_RECHARGE_LEDGER.md`,
  reviewed at SHA256
  `cd1a964b4c77073ade6a9ff371d294f1e3169a55883de39ea78320c9e21a54ef`;
- `notes/CODEX_GROMOV__TWO_SURE_CLOCK_FINITE_RESPONSE_CYCLE_NOGO.md`,
  reviewed at SHA256
  `17cc67e7f72e113b7ec10894a55b4928355fdc587bdbf02835684318971ff51f`;
- `notes/CODEX_SPINOZA__CAP_SEGMENT_UNIFORM_GAP_AND_SECOND_RESPONSE.md`,
  frozen at SHA256
  `42c6c5461c11520961e4842c76cf4c6af67e3df1f89c0fdc032b3070aefb26b0`;
- `terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticGlobalDebtBarrierCertificate.lean`;
  and
- `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.

## Next exact question

Can the source-faithful cap-child seam of the renewed late-reset construction
be shown to satisfy

\[
 Q(s_{m+1})\ge Q(p_m),
\]

or can one construct an exact finite quitting regression where this specific
seam strictly lowers \(Q\)?  This is the minimal barrier comparison left by
the no-go above; arbitrary complete-cap replacements are too broad.
