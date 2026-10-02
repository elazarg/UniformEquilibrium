# Same-source singleton pressure forces delayed loss or tie alteration

Author: CODEX_NOETHER_SUPPORT.

Status: complete ordinary-mathematics event calculation, not independently
reviewed or Lean-checked. Its worst-table application is conditional on the
unreviewed
[silent source bridge](CODEX_FRECHET_CYCLE__SILENT_SOURCE_COUPLING_TO_WORST_REWARD_PRESSURE.md).
This is the first concrete sign test of the retained scalar pressure. It
does not prove that pressure is positive. Instead it identifies the two
literal event types that must carry nonvanishing mass at the SAME source.
No new equilibrium producer or export is proposed.

## 1. Exact source and selected-response data

Fix any bounded quitting table |r_i(S)|≤M, M>0, with zero Never payoff.
Let p be any actual independent stopping-law profile. For each i let T_i
be its prescribed clock and O_i=min_(j≠i) T_j the first opponent clock.
Order Never above all finite dates. Every complete unilateral behavioral
deviation is admitted; pure time r is evaluated against the ORIGINAL
opponents. Finite tables and finite support are not needed for the event
identity itself.

Let λ be a probability law on labelled pure responses (i,r), possibly with
an additional zero tester. The zero tester contributes zero to every
quantity below. In the intended application λ is the SAME near-active
law used for the enlarged profile-direction inequalities and the retained
scalar pressure. Write E=E(p) and suppose its inactivity is at most a:

    Σ_(i,r) λ_(i,r) g_(i,r)(p) ≥ E−a.                  (1)

Define the singleton pressure

    S=Σ_(i,r) λ_(i,r)
         [Pr(r finite and r<O_i)−Pr(T_i finite and T_i<O_i)].

This uses strict opponent survival; a same-date joint quit is NOT an own
singleton. Assume a supplied upper bound S≤sErr. The worst-table source
provides a→0, sErr→0, E→Ω>0, not four separate singleton signs.

Sampling labels under λ is only proof notation. The counterfactuals remain
one-player interventions on the same independent source p; no λ mixture
is played as a common public random strategy.

## 2. Three disjoint changes of the terminal coalition

Fix a labelled response (i,r) and couple old and new play with the same
opponent clocks and the source clock T_i. Put

    X=1[T_i is finite and T_i<O_i],
    Y=1[r is finite and r<O_i].

Define the three event probabilities

    A_i(r)=Pr(Y=1 and X=0),
    L_i(r)=Pr(X=1 and Y=0),
    C_i(r)=Pr(O_i is finite and min(T_i,r)=O_i<max(T_i,r)).
                                                               (2)

A is an increase of the owner's singleton event, necessarily caused by
advancing its clock. L is a loss of that event, necessarily caused by
delaying its clock. C changes whether the owner joins the original first
opponent coalition, while neither outcome is an owner singleton.

The events in (2) are disjoint, and the old and new terminal COALITIONS
(including Never) differ if and only if their union occurs. Indeed:

- If X=Y=1, both outcomes are {i}, regardless of the two absorption dates.
- If X≠Y, one outcome is {i} and the other is not.
- If X=Y=0 and O_i is Never, both own clocks must be Never, so the
  outcomes agree.
- If X=Y=0 and O_i is finite, both own clocks are at least O_i. The
  opponent first-quitter set is unchanged. The only possible difference
  is that exactly one own clock equals O_i; this is exactly C.

Thus there is no missing later coalition, collision, or Never event.
Different absorption dates yielding the SAME terminal coalition do not
contribute, since the terminal game has no timing payoff.

The exact singleton change and reward bound are consequently

    Pr(Y=1)−Pr(X=1)=A_i(r)−L_i(r),
    |g_(i,r)(p)|≤2M[A_i(r)+L_i(r)+C_i(r)].             (3)

The second inequality only uses the reward difference bound on outcomes
whose coalitions differ. It holds without near-optimality of the response.

For clarity, the events retain these literal endpoint formulas. If r is
finite,

    A_i(r)=Pr(r<O_i≤T_i),
    L_i(r)=Pr(T_i<O_i≤r),
    C_i(r)=Pr(O_i=r<T_i)+Pr(T_i=O_i<r).                (4)

In the first formula equality O_i=T_i=Never is included: the response
creates a singleton from joint Never. If r=Never, then

    A_i(Never)=0,
    L_i(Never)=Pr(T_i finite and T_i<O_i),
    C_i(Never)=Pr(T_i=O_i<Never).                      (5)

In particular (5) keeps withdrawal from an old joint first-quitter
coalition distinct from loss of an old singleton.

## 3. The retained scalar produces a quantitative residual

Average (2) under the SAME λ and write A,L,C for the three results.
Equation (3) gives the exact identity S=A−L and the bound

    E−a ≤ Σλg ≤2M(A+L+C)=4ML+2MC+2MS.

Hence

    4ML+2MC ≥ E−a−2M sErr.                            (6)

Applied to the coupled silent source, still conditional on that bridge,

    liminf (4ML+2MC) ≥ Ω>0.                            (7)

Thus delayed singleton losses and tie alterations cannot BOTH vanish.
For example, if L→0, then liminf C≥Ω/(2M); if C→0, then
liminf L≥Ω/(4M). Those statements use the SAME actual source and response
weights as the scalar sign. No unrelated favorable source is selected.

Positive weight for all four owners is available from the proposed silent
bridge, but is not needed for (6). The calculation neither assumes nor
produces per-owner signs. It also does not replace the full regret maximum
by its λ average: the latter is used only as the lower bound (1).

## 4. Early falsification of the tie-free argument

A same-date joining premium can be fully paid while singleton pressure is
zero. For a concrete canonical Fin4 test, put s=(1,0,0,0), let
r_0({0})=r_0({0,1})=1, and let every other reward entry be zero.
At the actual source where 1 quits surely at zero and everyone else Never,
player 0's response Quit0 is an exact cap response of gain one. Its old
and new singleton probabilities are both zero: the response joins {1}.
For this labelled response, A=L=0 and C=1. A delay from an old simultaneous
quit gives the reverse tie mechanism.

This fixture tests ONLY the pointwise event partition and the need to keep
C. It is not a positive global-minimum source: the game is solved by pure
coalition {0}, and the displayed source lacks the all-owner multiplier
conditions. Therefore it refutes removing C from the payoff identity, not
the possibility that genuine global source conditions might rule out the
remaining collision branch.

## 5. Source comparison and exact next question

FRECHET's
[clamp calculation](CODEX_FRECHET_CYCLE__CLAMP_CROSS_AMPLIFICATION_AND_SOURCE_INTERVAL_REACH.md)
already splits full-law replacements into advancing and delaying clamps
and retains the interval Pr(T_i<O_i≤r). FRECHET independently supplied
the A−L interpretation of singleton pressure during this sign test.
The additional calculation here is the COMPLETE disjoint coalition-change
partition, including tie alteration C and Never, and its use with the
retained scalar to obtain (6). No new clamp, first-disagreement, or
full-response extremality theorem is claimed.

The exact source for S≤sErr is the reviewed
[coupled reward certificate](CODEX_NOETHER_SUPPORT__WORST_REWARD_TABLE_COUPLED_CALENDAR_CERTIFICATE.md),
followed, for a silent all-owner source, by the separate unreviewed bridge
linked above. Its weights are genuinely recomputed and transported there;
they are not identified with the original unshifted softmax weights.

The tested implication “all-owner columns force S>0” remains unproved.
The concrete surviving alternatives are now (7): consume delayed OWN
singleton losses with their original-opponent interval events, or consume
the positive tie-alteration mass without discarding the other full testers.
Neither raw payoff signs on those events nor an actual full-regret descent
follows from (6) alone. This is a source-level residual, not a negative
answer to the quitting conjecture or a consumed producer branch.
