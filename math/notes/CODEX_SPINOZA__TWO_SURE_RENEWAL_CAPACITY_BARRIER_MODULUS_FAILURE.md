# Two-sure renewal forces a macroscopic seam or capacity discontinuity

Author: `CODEX_SPINOZA`

## Status

**Exact conditional ordinary mathematics; hard-residual reduction, not
Lean-checked and not a consumer.**  Combine the renewed-owner capacity ledger
with the two-sure universal-descendant theorem.  If an infinite renewed
finite-clock orbit exists under bounded exact Nash--Bellman capacity, then
there is a subsequence of horizontal cap children on which the exact capacity
recharge stays uniformly positive while the target-free barrier increment
tends to zero.

Consequently no continuous modulus can price capacity recharge by the
barrier increment.  More geometrically, after a subsequence either the full
terminal-semantic horizontal seam remains macroscopic, or the canonical
exact-block capacity-to-go is discontinuous at one limiting payoff.  This is
a quitting-specific consequence of the maintained hard-residual renewal
data, not a generic charged-relation example.  Neither output is presently a
terminal consumer.

## Question

Can Lipschitz regularity and monotonicity of the target-free barrier control
the horizontal capacity recharge in the two-sure renewed cap-clock branch?

The answer is negative at the level of scalar moduli: any infinite renewal
itself forces fixed recharge at vanishing barrier increment.  What remains is
to consume the resulting macroscopic seam or the source-specific capacity
discontinuity.

## 1. Alternating hard-residual data

Let

\[
 s_m\longrightarrow p_m\dashrightarrow s_{m+1}
\tag{1}
\]

be the alternating sequence supplied by an indefinitely renewed finite-clock
construction.  Assume:

1. the solid phase is a finite exact Nash--Bellman predecessor path with
   absorption charge \(A_m\ge a_0>0\);
2. the dashed phase is one actual deterministic finite-clock cap child;
3. from the displayed index onward, both \(p_m\) and \(s_{m+1}\) retain two
   distinct prescribed finite sure-clock players;
4. \(\Phi\) is the bounded capacity-to-go value of the full canonical boxed
   exact Nash--Bellman relation; and
5. \(Q\) is the bounded target-free universal-prefix barrier evaluated on
   the actual terminal semantic pairs.

Put

\[
 K_m=\Phi(s_{m+1})-\Phi(p_m),
 \qquad
 L_m=Q(s_{m+1})-Q(p_m).
\tag{2}
\]

Here \(\Phi\) uses the fixed boxed decorations of the renewal ledger.  Its
value in fact depends only on the payoff coordinate of its source: the
simplex coordinate of the tail state is explicitly irrelevant in
`IsQuittingNashBellmanEdge`, so two boxed sources with the same payoff have
identical outgoing finite exact paths and identical capacity value.

The bounded-capacity ledger gives a constant \(C_\Phi\) such that

\[
 \sum_{m<N}K_m\ge Na_0-C_\Phi
\tag{3}
\]

for every \(N\).  The two-sure theorem makes the cap child an actual
universal-prefix descendant of \(p_m\), while the solid phase already has
that orientation.  Therefore

\[
 Q(s_m)\le Q(p_m)\le Q(s_{m+1}),
 \qquad
 L_m\ge0,
 \qquad
 \sum_mL_m<\infty.
\tag{4}
\]

All statements use unrestricted behavioral caps.  The two sure clocks are
exactly what makes the cap child's finite word tail-independent even after a
unilateral replacement.

## 2. Fixed recharge at vanishing barrier increment

### Theorem 2.1

There are infinitely many indices \(m\) for which

\[
 \boxed{K_m\ge a_0/2.}
\tag{5}
\]

Along those indices one can select a subsequence \(m_n\) satisfying

\[
 \boxed{K_{m_n}\ge a_0/2,
 \qquad L_{m_n}\longrightarrow0.}
\tag{6}
\]

#### Proof

If (5) held only finitely often, then eventually \(K_m<a_0/2\).  Since
\(\Phi\) is bounded, the finitely many exceptional terms contribute only a
constant, and hence

\[
 \limsup_{N\to\infty}\frac1N\sum_{m<N}K_m\le a_0/2,
\]

contradicting (3), whose lower Cesaro limit is at least \(a_0\).  Thus there
are infinitely many such indices.  Equation (4) gives \(L_m\to0\) along the
whole sequence, hence also along this subsequence.  QED

### Corollary 2.2: failure of every vanishing scalar modulus

There is no function \(\omega:[0,\infty)\to[0,\infty)\) with
\(\omega(t)\to0\) as \(t\downarrow0\) for which all sufficiently late seams
satisfy

\[
 K_m\le\omega(L_m).
\tag{7}
\]

In particular, neither global Lipschitz continuity of \(Q\) nor its
two-sure monotonicity can yield the comparison

\[
 K_m\le\lambda L_m+o(1)
\tag{8}
\]

needed by the \(\Phi-\lambda Q\) Lyapunov scalarization.

This conclusion does not refute a source theorem proving (8): such a theorem
would instead rule out the hypothesized infinite renewal.  It identifies
exactly what any such theorem must contradict.

## 3. Semantic-seam/capacity-discontinuity dichotomy

Write \(X_m=\operatorname{Sem}(P_m)\) and
\(Y_m=\operatorname{Sem}(S_{m+1})\), and let \(\rho\) be the coordinatewise
sup metric on the full prescribed-payoff/cap pair.

### Theorem 3.1

After a further subsequence of (6), one of the following alternatives holds.

1. **Macroscopic two-sure seam.** There is \(r_0>0\) such that

   \[
    \rho(X_{m_n},Y_{m_n})\ge r_0
   \tag{9}
   \]

   for every \(n\), while still \(K_{m_n}\ge a_0/2\) and
   \(L_{m_n}\to0\).

2. **Capacity discontinuity at a common payoff.** One has

   \[
    \rho(X_{m_n},Y_{m_n})\longrightarrow0.
   \tag{10}
   \]

   The prescribed payoff coordinates of both sequences converge to one
   vector \(u_*\), but their capacity values have limits \(P,S\) satisfying

   \[
    S-P\ge a_0/2.
   \tag{11}
   \]

   Hence the payoff-indexed canonical capacity value \(\phi\) is
   discontinuous at \(u_*\).  More quantitatively, at least one of the two
   sequences stays at distance at least \(a_0/4\) from \(\phi(u_*)\) in the
   limit.

#### Proof

The nonnegative scalar sequence \(\rho(X_{m_n},Y_{m_n})\) has a subsequence
converging to some \(r\ge0\).  If \(r>0\), discard finitely many terms and use
\(r_0=r/2\), proving alternative 1.

If \(r=0\), compactness of the semantic carrier gives a further subsequence
on which both semantic pairs converge to the same point, hence their payoff
coordinates converge to one \(u_*\).  Boundedness of \(\Phi\) lets us pass to
a further subsequence such that

\[
 \Phi(p_{m_n})\longrightarrow P,
 \qquad
 \Phi(s_{m_n+1})\longrightarrow S.
\]

Equation (5) gives (11).  Since \(\Phi\) depends only on the payoff coordinate,
write the common value as \(\phi\).  If \(\phi\) were continuous at \(u_*\),
both limits would equal \(\phi(u_*)\), contradicting (11).  Finally the
triangle inequality gives

\[
 \max\{|S-\phi(u_*)|,|P-\phi(u_*)|\}
 \ge |S-P|/2\ge a_0/4.
\]

This proves alternative 2.  QED

## 4. Relation to the target-free Lipschitz theorem

The target-free barrier satisfies

\[
 |Q(X)-Q(Y)|\le2\rho(X,Y).
\tag{12}
\]

Thus alternative 2 is consistent with \(L_{m_n}\to0\); (12) merely confirms
it when the semantic seam vanishes.  Alternative 1 shows the converse fails
at the exact place it is needed: a vanishing scalar barrier increment need
not make the terminal semantic seam small.

The private cap-segment estimate

\[
 |Q(X^t)-Q(X^s)|\le4M|t-s|
\]

also points in this same direction.  It is an upper estimate on scalar
variation, not an inverse estimate on semantic displacement and not a
continuity theorem for \(\Phi\).

## Sources inspected

- `notes/CODEX_HAHN__RENEWED_OWNER_CYCLE_CAPACITY_RECHARGE_LEDGER.md`,
  reviewed at SHA-256
  `cd1a964b4c77073ade6a9ff371d294f1e3169a55883de39ea78320c9e21a54ef`;
- `notes/CODEX_HAHN__TWO_SURE_CLOCK_CHILD_IS_UNIVERSAL_PREFIX_DESCENDANT.md`,
  reviewed at SHA-256
  `8296721fcfad9e373c012b01481ae414ef0f7c0cda86f7a1868a46ec563f82ad`;
- `notes/CODEX_SPINOZA__TARGET_FREE_BARRIER_LIPSCHITZ_AND_CAP_SEGMENT_VARIATION.md`;
- `notes/CODEX_SPINOZA__LINKED_SIBLING_BARRIER_CAPACITY_LYAPUNOV_CRITERION.md`;
- `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`,
  especially `IsQuittingNashBellmanEdge` and the irrelevance of the tail
  simplex coordinate;
- `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorChargedRelation.lean`;
  and
- `MathUE/ChargedPathBudget.lean`, especially `ChargedRelation.value` and
  `ChargedRelation.value_tgt_add_charge_le_value_src`.

## Boundary and nonclaims

- The theorem assumes the infinite renewed two-sure finite-clock branch.  It
  does not produce that branch from every Fin4 table.
- The hard-residual input is used through bounded exact-block capacity and
  the fixed phase-charge floor.  The argument is not an abstract
  two-state-cycle regression.
- A Never cap child is outside the two-sure universal-descendant theorem and
  is not covered.
- Alternative 2 proves discontinuity of the canonical capacity value along
  the actual source-derived payoff sequences.  It does not promote the
  horizontal cap child to an exact Nash--Bellman edge.
- Neither a macroscopic semantic seam nor a capacity discontinuity is already
  a terminal approximate Nash profile, a source-compatible return, or a
  contradiction to bounded capacity.

## Next exact question

Can the macroscopic two-sure seam in alternative 1 be fed to the checked
two-cut/paid-port machinery with its universal-descendant ancestry retained?
If not, can the source-derived discontinuity in alternative 2 be sharpened
to a limit-born exact charged path whose escaping first charge gives a
persistent-clock object rather than another horizontal sibling?
