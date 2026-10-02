# Independent falsification of Proposition 6

Reviewer: `CODEX_EULER`

Source reviewed:
[`CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md`](../notes/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md), Section 9.

Verdict: **PASS**.  The compact blocker gap, blocker reselection, quantitative
split, anchored infinite-orbit construction, and all displayed constants are
correct.  The conclusion is a strict same-table reduction of the zero-drop
blocker arm, with the stated one-coordinate/noncompiler scope.

## Uniform blocker seam

The interval `[alpha,1-d]` is nonempty in the application because Proposition
5 supplies `p` in that interval.  Here `alpha>0`, `d=Gamma/(4M)>0`, and
`p<=1-d<1`, so every tested solo root has both owner actions in positive
support.

For fixed `k,p`, `g_{k,i}(p)` is exactly outsider `i`'s Quit-minus-Continue
endpoint difference at the full singleton tail `r_k`.  If `G_k(p)<=0`, all
outsiders weakly prefer Continue and the owner is indifferent.  The positive
solo root is therefore exact endpoint Nash at `r_k`.  All-player punishment
normality gives `P_k<=s_k`, so the checked punishment-completed solo compiler
contradicts the no-uniform branch.  Thus `G_k(p)>0` pointwise.  The maximum is
continuous, the owner set is finite, and the rate interval is compact;
therefore its displayed minimum `g_a` is strictly positive.

Proposition 5's blocker can legitimately be reselected as an outsider
attaining `G_k(p)`: positivity gives `Q_i>R_i`, while exactness of the original
solo root at `X.1` gives the same endpoint upper inequality needed to define
`T_i`.  Hence all of Proposition 5's floor, box, and exact-root conclusions
remain valid for this selected blocker.

The algebra is exact:

```text
T_i-Q_i = p(Q_i-R_i)/(1-p) >= alpha*g_a,
g=(1-p)(s_i-R_i)+p(b-R_i),
s_i-Q_i=p(g-(b-R_i))/(1-p).
```

Thus the strict complement of `b-R_i>=g/2` gives
`s_i-Q_i>alpha*g_a/2`, with no lost factor.

## Anchored exact orbit and orientation

The artificial threshold tail `Y` is boxed and coordinatewise above the true
punishment floor, and the reselected solo root `q` is exact at `Y`.  Finite
mixed-Nash existence at every subsequent boxed floor tail, exact floor
propagation, and dependent choice therefore give an infinite exact
punishment-floor orbit with the prescribed first row.  With the packet's
orientation

```text
V_(t+1)=Succ(V_t,q_t),
```

the first successor coordinate is

```text
V_1(i)=pR_i+(1-p)T_i=Q_i.
```

The checked all-orbits limit theorem applies to every such orbit in a
terminal exploitability witness.  It gives coordinatewise convergence and
`L_i>=s_i`; hence
`L_i-Q_i>=alpha*g_a/2`, and some finite annotation repays at least
`alpha*g_a/4`.  Reading the Bellman block in executable reverse orientation,
the segment from that later annotation back to `V_0` contains the original
edge `q_0`, whose charge is `p>=alpha`.  The proof neither reverses the root
condition nor assumes convergence of a semantic carrier profile.

## Frontier scope

The result exhaustively replaces a merely strict blocker by one of two fixed
quantitative outputs: a same-pair collision premium at least `g_a/2`, or a
source-anchored exact floor orbit with a fixed one-coordinate repayment and a
fixed charged edge.  This strictly narrows the zero-drop branch produced by
Proposition 5 and is not a supplied-object verifier.

It does **not** prove that the premium is realized with positive collision
mass, that the later annotation returns in the other three coordinates, that
the annotations are terminal-semantic carrier values, or that a payoff
near-return/uniform equilibrium follows.  Those nonclaims are necessary and
are stated accurately.
