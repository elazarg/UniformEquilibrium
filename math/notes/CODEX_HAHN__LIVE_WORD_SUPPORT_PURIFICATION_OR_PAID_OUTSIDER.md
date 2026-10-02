# A uniformly live word admits support purification or pays an outsider

Author: CODEX_HAHN

## Status

**Exact ordinary mathematics; not Lean-checked and not a terminal
consumer.**  A finite actual word whose final joint reach has a fixed positive
floor can be upgraded from ordinary approximate root Nash to support-wise
approximate root Nash after a vanishing-total-variation deletion of bad Quit
mass.  The only alternatives are literal fixed-gain complete responses by a
fixed outsider, either at one row or by deleting all bad Quit choices of that
outsider.

Applied to the unique-sure live cap-band target, the purified word has exact
Bellman equations, a common compact payoff box, and vanishing support error.
It still has bounded rather than arbitrarily large charge, and no punishment
floor or renewable endpoint.  Hence this removes one local obstruction to the
checked finite-forward packet but does not invoke its consumer.

## 1. Self-contained input

Let \(I=\operatorname{Fin}4\), let \(R>0\), and assume every reward
coordinate lies in \([-R,R]\).  For each \(n\), let

\[
 Y_n=(y_{n,0},\ldots,y_{n,m_n-1})\triangleright Z_n
\tag{1}
\]

be an actual behavioral profile, with \(m_n>0\).  Write \(U_{n,t}\) for the
prescribed payoff of the actual suffix at row \(t\), so

\[
 U_{n,t}=F(y_{n,t},U_{n,t+1}).
\tag{2}
\]

Let \(A_{n,t}\) be joint survival through the rows strictly before \(t\), and
assume

\[
 A_{n,m_n}\ge\eta>0.
\tag{3}
\]

Consequently

\[
 A_{n,t}\ge\eta,
 \qquad
 c_{n,t,i}:=\Pr_{y_{n,t}}(i\text{ Continues})\ge\eta
\tag{4}
\]

for every displayed row and player.

Fix a host \(k\) whose complete debt satisfies

\[
 d_k(Y_n)\le e_n,
 \qquad e_n\longrightarrow0.
\tag{5}
\]

At a displayed row define the losses of the two pure actions against the
literal payoff successor:

\[
 \ell^Q_{n,t,i}=\max\{Q_{n,t,i},C_{n,t,i}\}-Q_{n,t,i},
 \qquad
 \ell^C_{n,t,i}=\max\{Q_{n,t,i},C_{n,t,i}\}-C_{n,t,i}.
\tag{6}
\]

If \(q_{n,t,i}=1-c_{n,t,i}\) is the Quit probability, the ordinary
coordinate Nash defect is exactly

\[
 h_{n,t,i}=q_{n,t,i}\ell^Q_{n,t,i}
             +c_{n,t,i}\ell^C_{n,t,i}.
\tag{7}
\]

## 2. Exhaustive theorem

After passing to a subsequence, at least one of the following holds.

### A. A fixed paid outsider row

There are \(i\ne k\), \(\xi>0\), and \(t_n<m_n\) such that changing only
player \(i\)'s action at \(t_n\) to a better pure action, while copying the
whole prefix and continuation, has full-profile gain at least

\[
 \eta\xi.
\tag{8}
\]

### B. A fixed aggregate paid outsider response

There are \(i\ne k\), \(\delta,\rho>0\), and sets of rows \(S_n\) such
that at every row in \(S_n\), player \(i\)'s Quit action is worse than
Continue by more than \(\delta\).  The complete response which replaces
player \(i\)'s Quit probability by zero at all rows in \(S_n\), and otherwise
copies its strategy, gains at least

\[
 \delta\rho.
\tag{9}
\]

Its first disagreement is in the displayed word, and it leaves the literal
tail unchanged.

### C. Vanishing-TV support purification

There are thresholds \(\delta_n\downarrow0\) and actual profiles

\[
 \widetilde Y_n=(\widetilde y_{n,0},\ldots,
 \widetilde y_{n,m_n-1})\triangleright Z_n
\tag{10}
\]

obtained only by changing selected bad Quit marginals to pure Continue, such
that

\[
 S_n:=\sum_{t<m_n}\sum_{i\in I}
  \operatorname{TV}(\widetilde y_{n,t,i},y_{n,t,i})
 \longrightarrow0,
\tag{11}
\]

and every action in the support of every new root is within

\[
 \varepsilon_n:=\delta_n+4RS_n\longrightarrow0
\tag{12}
\]

of the better pure endpoint against the new literal successor payoff.  The
new Bellman identities are exact, its final joint reach is at least \(\eta\),
and all its suffix payoffs remain in the fixed box \([-R,R]^I\).

## 3. The one-row branch

Put

\[
 H_n=\max_{t<m_n,\ i\in I}h_{n,t,i}.
\tag{13}
\]

If \(H_n\) has a positive lower bound, a maximizing row and finite pigeonhole
give one fixed player and the copied-prefix one-date response (8).  Its gain
is \(A_{n,t_n}H_n\ge\eta H_n\).

This player is eventually not \(k\): the same response belongs to the host's
complete deviation class, while (5) bounds every host deviation gain.  This
proves A.  Hence it remains to treat a refinement on which

\[
 H_n\longrightarrow0.
\tag{14}
\]

## 4. Aggregate deletion and its exact gain

For a threshold \(\delta>0\), let

\[
 M_{n,i}(\delta)=
 \sum_{\substack{t<m_n\\ \ell^Q_{n,t,i}>\delta}}
 A_{n,t}q_{n,t,i},
 \qquad
 M_n(\delta)=\sum_iM_{n,i}(\delta).
\tag{15}
\]

Fix \(i\) and replace its Quit probability by zero at all rows counted in
\(M_{n,i}(\delta)\).  Let \(A'_{n,t}\) be reach under the modified strategy.
Because only Quit mass was deleted,

\[
 A'_{n,t}\ge A_{n,t}.
\tag{16}
\]

Backward subtraction of the two scalar payoff recursions gives the exact
policy-improvement identity

\[
 U_i(Y'_n)-U_i(Y_n)
 =\sum_{\substack{t<m_n\\ \ell^Q_{n,t,i}>\delta}}
 A'_{n,t}q_{n,t,i}\ell^Q_{n,t,i}.
\tag{17}
\]

The tail term is zero because the two strategies agree after \(m_n\).  Thus

\[
 U_i(Y'_n)-U_i(Y_n)\ge\delta M_{n,i}(\delta).
\tag{18}
\]

If some fixed \(\delta\) has \(M_n(\delta)\) bounded below, finite pigeonhole
fixes \(i\) with \(M_{n,i}(\delta)\ge\rho>0\), proving B.  Equation (18) and
(5) again show that this fixed payer cannot be the host \(k\).

## 5. Diagonal purification

It remains to assume that, after diagonal refinement,

\[
 M_n(\delta)\longrightarrow0
 \quad\text{for every fixed }\delta>0.
\tag{19}
\]

Choose \(\delta_n\downarrow0\) sufficiently slowly that

\[
 M_n(\delta_n)\longrightarrow0,
 \qquad
 {H_n\over\eta}\le\delta_n.
\tag{20}
\]

At every row and player for which
\(\ell^Q_{n,t,i}>\delta_n\), replace the Quit marginal by zero.  This defines
the actual profile (10).  By (4),

\[
 S_n
 =\sum_{\substack{t,i\\\ell^Q_{n,t,i}>\delta_n}}q_{n,t,i}
 \le {M_n(\delta_n)\over\eta}
 \longrightarrow0.
\tag{21}
\]

Couple every original and modified Bernoulli draw, row by row and player by
player.  For the full profile, for every suffix, and after forcing either
pure current action of any one player, the probability that the two coupled
executions ever differ is at most \(S_n\).  Since rewards lie in
\([-R,R]\), every corresponding payoff or pure endpoint changes by at most
\(2RS_n\).

It remains to check support losses before perturbation.  Continue always has
positive original probability by (4).  If Continue is worse, (7) and (14)
give

\[
 \ell^C_{n,t,i}\le {H_n\over c_{n,t,i}}
 \le {H_n\over\eta}\le\delta_n.
\tag{22}
\]

Any Quit action retained with positive probability has
\(\ell^Q_{n,t,i}\le\delta_n\) by construction.  No new supported action is
introduced.  The maximum endpoint can rise by at most \(2RS_n\), and the
payoff of the retained action can fall by at most \(2RS_n\); hence its new
loss is at most (12).  This proves support-wise approximate Nash at every
new row.

The new suffix payoffs are the actual payoffs of the modified finite word, so
their Bellman identities are exact.  Removing Quit mass only increases final
survival, proving the remaining claims in C.

## 6. Exact relation to the forward consumer

Reverse the purified word in C.  It supplies the following fields of
`QuittingFiniteForwardPacket` from
`UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`:

1. the exact forward policy equation;
2. `IsQuittingRootSupportApproxNash` with error \(\varepsilon_n\); and
3. one common compact carrier, namely \([-R,R]^I\).

It does **not** supply the punishment-floor field.  If \(a_{n,t}\) denotes
the one-row absorption mass of the purified root and
\(\widetilde A_{n,m_n}\) its final joint survival, its survival floor gives

\[
 \sum_{t<m_n}a_{n,t}
 \le\sum_{t<m_n}-\log(1-a_{n,t})
 =-\log\widetilde A_{n,m_n}\le-\log\eta.
\tag{23}
\]

Thus its additive charge is uniformly bounded, whereas the checked producer
needs arbitrarily large charge as the requested target grows.  Nor is its
tail identified with a next renewable source.  Hence no existing terminal
consumer accepts C without additional global input.

Branches A and B are actual source-attached complete responses with fixed
gain and a first disagreement before the tail.  Their targets need not
revalidate any old root or return to the source fibre.

## Sources inspected

- `notes/CODEX_SPINOZA__EXACT_WORD_FORCES_LATE_CAP_BAND_RECEIVER_AND_LIVE_TARGET.md`;
- `notes/CODEX_HAHN__LIVE_TARGET_PAYOFF_ROOT_OR_PAID_OUTSIDER_FORK.md`;
- `UniformEquilibrium/Quitting/Root/NashDefect.lean`;
- `UniformEquilibrium/Quitting/Root/LiteralPrefixDeviationTransport.lean`;
- `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`;
  and
- `UniformEquilibrium/Quitting/Paths/SupportWitnessClockCollapse.lean`.

## Boundary tests and nonclaims

- The fixed final-reach floor is essential twice: it bounds every Continue
  probability below and converts reached bad-Quit mass into total variation.
- The aggregate branch uses a complete multirow response, not the sum of
  gains of incompatible one-row deviations.  Identity (17) is the required
  common-strategy telescope.
- The purification may change every player's prescribed payoff and cap.  The
  coupling argument controls only the new support inequalities and Bellman
  values; it does not preserve the original minimum fibre or paid passport.
- The charge bound goes in the wrong direction for the forward consumer:
  positive tail reach prevents divergent absorption inside one word.
- No punishment admissibility, source return, renewable rank, terminal
  approximate Nash profile, or uniform-equilibrium payoff is claimed.
