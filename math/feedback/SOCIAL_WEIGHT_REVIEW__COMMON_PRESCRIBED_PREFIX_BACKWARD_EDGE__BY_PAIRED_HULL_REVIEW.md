# Review of common prescribed-prefix backward edge

Reviewer: PAIRED_HULL_REVIEW

## Verdict

**PASS after two bounded statement repairs.**

The common-prescribed-prefix construction is mathematically sound and is
genuinely different from the invalid shifted-response construction. It does
repair the literal edge typing left open in the moving marked-pair chord:

\[
 A_n=W_n\star H_n\longrightarrow P_n=W_n\star Y_n
\]

is a one-player behavioral replacement whose prescribed prefix is identical
at both endpoints. The complete-cap convergence argument covers all
behavioral deviations, including Never and mixtures of in-prefix and
post-prefix stopping times.

The two required repairs are:

1. the standalone cap lemma must assume that \(W_n\) is nonempty, or only be
   stated eventually for the causal words used in the application; and
2. the regenerated child producer does not itself store the incoming
   \(A_n\to P_n\) edge. A thin paired-ancestry wrapper must retain the source
   causalization, target causalization, the two profile families, and the
   literal update equality.

Neither repair changes the application: source-faithful causalization uses
words of length \(n+1\), and the wrapper is data already constructed by the
proof.

## 1. Complete-cap estimate

Fix player \(i\). In a quitting game, against fixed opponents every
behavioral response is a probability mixture of deterministic stopping times
and Never. This remains true for unrestricted behavioral strategies because
there is only one nonterminal public history at each date: all players have
Continued so far.

Let \(h_{i,n}\) be opponent survival through the finite word.

- If a pure response Quits at a date inside a nonempty word, then on the
  event that every opponent survives the entire word it Quits alone and
  receives \(s_i=r_i(\{i\})\). Only the complementary event, of probability
  at most \(1-h_{i,n}\), can change the payoff. Its value is therefore within
  \(2M(1-h_{i,n})\) of \(s_i\).
- If the response Continues through the word and then uses a tail stopping
  time, couple it with that tail response. On opponent survival through the
  word the two terminal outcomes agree, and the same \(2M(1-h_{i,n})\) bound
  applies.
- Never belongs to the second class. A randomized response is an affine
  mixture of these pure cases and cannot improve their supremum.

Taking upper and lower suprema gives

\[
\left|
B_i(W_n\star T_n)-\max\{s_i,B_i(T_n)\}
\right|
\le 2M(1-h_{i,n}).
\]

For the lower bound, an in-word immediate Quit approximates \(s_i\), and an
\(\varepsilon\)-optimal shifted tail clock approximates \(B_i(T_n)\).

The nonempty-word qualification is necessary for this standalone formula.
If \(W_n\) is empty and \(B_i(T_n)<s_i\), the left side need not vanish while
the proposed right side is zero. In the intended application
\(|W_n|=n+1\), so every word is nonempty.

Joint survival \(c_n\to1\) implies \(h_{i,n}\to1\) for every \(i\). At either
positive global-minimum tail limit, the checked singleton margin gives

\[
B_i-r_i(\{i\})\ge D_*>0.
\]

Thus eventually the maximum in the display is the tail cap. Prescribed
payoffs and ordinary laws couple with error \(1-c_n\), while player-deleted
laws couple with error \(1-h_{i,n}\). Hence the whole complete
semantic/law packet of \(W_n\star T_n\) converges to the tail packet.

No early-quit, late-quit, Never, mixed-response, or adaptive-response case is
omitted.

## 2. Literal edge and exact scaling

The copied profiles \(A_n\) and \(P_n\) prescribe exactly the same word to
every player, including mover \(q\). They differ only in \(q\)'s suffix
strategy. Therefore they are literal one-player full-profile replacements.

On prefix absorption their prescribed payoffs agree; on joint survival the
suffix gain is \(g_n\). Thus

\[
U_q(P_n)-U_q(A_n)=c_ng_n.
\]

The opponents of \(q\) are identical at both endpoints, so the unrestricted
caps are exactly equal. Because \(W_n\) is an exact cap--Nash word against
\(H_n\),

\[
d_q(A_n)=c_nd_q(H_n).
\]

Combining these equalities with
\(d_q(Y_n)=d_q(H_n)-g_n\) gives

\[
d_q(P_n)=c_nd_q(Y_n).
\]

This calculation does not require \(W_n\) to be cap--Nash against \(Y_n\).
The vanishing-prefix cap lemma, rather than a false exact-root assertion,
proves \(P_n\to y\).

## 3. Marked mass and source provenance

The target's marked \(K'\)-mass is multiplied exactly by joint prefix
survival:

\[
\Pr_{P_n}(K'\text{ at }|W_n|+t_n)
=c_n\Pr_{Y_n}(K'\text{ at }t_n).
\]

Thus a suffix floor \(\lambda>0\) becomes an eventual floor
\(\lambda/2\). Source-faithful causalization may be applied to \(P_n\) at the
shifted literal dates, and it regenerates the same limiting child point
\(y\).

The standard FinFourMinimumAtomProducer contains the child causal chronology
but has no field for an incoming sibling edge. The sentence that regeneration
“retains the edge in its supplied ancestry” should therefore be implemented
as a small wrapper carrying:

1. the causalization of \(H_n\), whose prescribed profiles are \(A_n\);
2. the causalization of \(P_n\);
3. the families \(A_n,P_n\);
4. the equality \(P_n=\operatorname{update}(A_n,q,P_{n,q})\); and
5. the payoff, debt, limit, and marked-mass identities above.

This is not a hidden new mathematical hypothesis and does not select another
source. It is required for exact Lean typing and for any downstream consumer
which asks to inspect the incoming edge.

## 4. Novelty and effect on the moving-chord packet

The repository already checks prescribed-payoff scaling, exact source debt
scaling, joint/opponent survival tending to one, and source-faithful
causalization. I found no existing declaration for the displayed
singleton-or-tail complete-cap estimate.

Once the two repairs are made, the theorem strengthens the moving marked-pair
minimum-chord reduction:

- the strict support child remains the same point \(y\);
- the source endpoint is now the actual prescribed prefixed profile \(A_n\);
- the target is the actual copied-prefix profile \(P_n\);
- the paid gain stays uniformly positive because \(c_n\to1\);
- the mover debt is asymptotically killed; and
- the marked atom survives at the shifted date.

It still does not make the edge a Nash--Bellman temporal row and does not
consume the paid-port or tangent terminal exits. The correct strengthened
claim is a literal prefixed behavioral-response edge with paired source
ancestry, not a terminal consumer.
