# Which raw rewards determine a limiting first-exit law?

Consider independent private quitting clocks, one live state, finite original rewards \(r_i(S)\) and zero live and perpetual-Continue payoffs. Let \(s_i=r_i(\{i\})\), \(\Gamma_{ij}=r_i(\{j\})-s_i\). A law records all first-quitting coalitions and Never. Terminal regret is the maximum gain from a complete unilateral replacement, including Never. Let \(\mathcal A\) be any downward-closed collection of subsets of the four players containing every singleton.

Keep the following entries fixed.

1. \(r_i(S)\) for every player \(i\) and every nonempty \(S\in\mathcal A\).
2. \(r_i(S\cup\{i\})\) whenever \(\varnothing\ne S\subseteq B\in\mathcal A\), \(|B|\ge2\), and \(i\notin B\).

The other entries may change arbitrarily and independently between the source table and the destination table. On the source table suppose each player's supremum payoff against **every** opponent profile is at least \(s_i\). A sufficient raw test is that the native passive and joining rewards sum to a nonnegative number at every nonempty pure rival coalition; a constant private half hazard then guarantees \(s_i\). For each \(i\) suppose in addition that either \(s_i\ge0\) or there is a distinct \(j\) with \(\Gamma_{ij}\le0\). Destination-table security is unnecessary.

**Theorem.** Suppose a sequence of source profiles has regret tending to zero and total first-exit probability outside \(\mathcal A\) tending to zero. On every destination table there is a sequence with regret tending to zero whose first-exit laws and prescribed original payoffs differ from those of the source sequence by amounts tending to zero. The destination calendars use only allowed support masks at every date, including after a refusal, and their largest hazard on singleton-only dates tends to zero. Thus every limiting law and its associated uniform-equilibrium payoff transfer. Among source-eligible completions the sets of attainable limiting laws supported in \(\mathcal A\) and their associated payoffs are identical. No positivity of a particular own level, no-sure hypothesis or lower bound on simultaneous activity is assumed.

Consequently a counterexample must fail this test for every allowed family. If even one source table agreeing on the displayed entries meets the source hypotheses and has a limiting equilibrium law supported on the family, the destination admits its payoff. When all own levels are nonnegative, one can make a source with the stated half-hazard security exactly when each nonempty rival set whose passive and joining entries are both fixed satisfies their sum bound. For recipient $i$ and rival set $T$, the required inequality is $r_i(T)+r_i(T\cup\{i\})\ge2s_i$. Each raw entry of that recipient belongs to just one such pair, so each missing entry can be completed to satisfy its inequality. This constructs the security property. Existence of an allowed limiting equilibrium law is a separate condition.

For a partition take \(\mathcal A\) to be all subsets of its parts. The numbers of free original entries are 21 for sizes \(3+1\), 24 for \(2+2\), 34 for \(2+1+1\), and 44 for four singletons. These counts follow by first counting all \(4\sum_B(2^{|B|}-1)\) prescribed entries and then \(\sum_{|B|\ge2}(4-|B|)(2^{|B|}-1)\) outside joining entries. Joint play within a nonsingleton part may have positive first-exit mass.

## Proof

Couple the original hazards \(q_i(t)\) by independent Bernoulli trials, including trials after a prescribed stop. Removing one player's trials prices all previously completed dates for its deterministic replacement deadlines or Never. A behavioral replacement is a private mixture of such deadlines. Let \(M\ge1\) bound absolute original rewards on the two fixed tables. Write \(\tau_n\) for the source's probability of a forbidden first exit. Choose \(\delta=\alpha=(\tau_n+1/n)^{1/9}\) at large \(n\). Then \(\tau_n<\alpha^4\delta^4\) and \(\delta(1+|\log\alpha|)\to0\). Retain through the first date by whose end any of the four individual survival probabilities falls to at most \(\alpha\); retain the whole infinite calendar if there is no such date. On every retained date joint pre-date survival satisfies \(S_t\ge\alpha^4\). Also
\[
 \sum_{\text{retained }t}\sum_iq_i(t)\le 4(1+|\log\alpha|),
\]
by \(-\log(1-q)\ge q\) before the terminal crossing, with at most four hazards on that crossing.

On each retained date put \(B=\{i:q_i(t)>\delta\}\). This set belongs to \(\mathcal A\): if not, simultaneous success by all of \(B\) on that date would have first-exit probability at least \(S_t\delta^{|B|}\ge\alpha^4\delta^4\) on a forbidden coalition. Use all clocks of \(B\) together at the first subdate; play each remaining positive clock on its own subsequent subdate, in any fixed order. If \(B\) has just one member, subdivide its hazard into finitely many pulses of size at most \(\delta\) with the same aggregate probability. If that single large hazard is exactly one, replace it by \(1-\delta\) before subdivision. There can be only one such change, on the cutoff date. Couple the aggregate trials to the old ones and sample the pulse index conditional on success. All singleton-only hazards are now at most \(\delta\).

Completed-date outcomes agree unless a small clock and another clock succeed on the same original date, or the one possible sure trial was altered. By a union bound the probability of these events over the entire prefix is at most
\[
 D=\delta+4\delta\sum_{\text{retained }t}\sum_iq_i(t)=o(1).
\]
Indeed each small hazard in an intersecting pair is at most \(\delta\). The same upper bound holds with any one clock suppressed. Outside these events all completed-date prescribed and passive rewards agree: the common exiting coalition is contained in \(B\) or is a singleton, and its rewards are fixed. The cost of this coupling for any completed prefix is at most \(2MD\). Its law discrepancy in total variation is at most \(D\).

Consider a new stopping deadline within a retained block. Compare payoffs conditional on original pre-date survival with the deviator waiting to that block in both calendars. At a joint first subdate its immediate offer differs from the original forced offer by at most \(8M\delta\): only a small rival trial can cause a difference, and the forced outcomes against \(B\) use the two lists of fixed entries. If a stop is at a small subdate after completing the large group, compare with **waiting on the original date and optimizing from the next one**. Any earlier large-rival exit has the same passive payoff, apart from an \(O(M\delta)\) chance of a small-rival interference on this date. Conditional on no large-rival exit, the new stop gives at most \(s_i+O(M\delta)\) while the old future cap is at least \(s_i\). The same argument applies if \(B\) is empty or if its complete singleton was subdivided.

For a stop inside a subdivided large singleton \(j\), an outsider \(i\)'s conditional return is at most \(s_i+q_j(\Gamma_{ij})_++O(M\delta)\): the probability of an earlier \(j\) exit is at most \(q_j\), and a simultaneous paid \(ij\) outcome can occur only on the single pulse where \(i\) quits. The old conditional cap is at least \(s_i\), and waiting on the old date then optimizing gives at least \(s_i+q_j\Gamma_{ij}-O(M\delta)\) since other rivals are small. Together these alternatives dominate the new stop up to \(O(M\delta)\). A stop by \(j\) itself gives \(s_j\) on its own pulse and its old cap is at least that. Each comparison uses one old feasible replacement, waiting to the pertinent original date and then using its selected action and continuation, with arbitrarily small error for an unachieved supremum. Pricing earlier dates under suppression by the completed-prefix coupling bounds the increase of any new prefix-deadline payoff over the old initial cap by \(O(M(D+\delta))\). No such cost is accumulated for multiple deadlines.

If there is no finite cutoff, prescribed and Never payoffs couple over all completed dates, including perpetual continuation. At a finite cutoff let \(k\) be one of its crossing owners. Append AllContinue if \(s_k\ge0\); otherwise append only a constant \(\delta\)-hazard rival \(j\) with \(\Gamma_{kj}\le0\). In the latter case earlier passive exits pay at most \(s_k\), a simultaneous premium can occur only on the deadline with probability at most \(\delta\), and Never pays \(r_k(\{j\})\le s_k\). Thus the tail cap for \(k\) on the destination table is at most \(s_k+O(M\delta)\), while the old source cap after the cutoff is at least \(s_k\). This also bounds the increase for \(k\)'s late deadlines or Never by the same coupling estimate. Under prescribed play or a replacement by any other player the tail is reached with probability at most \(\alpha+D\), since \(k\)'s own survival remains so bounded. The tail therefore changes original prescribed payoffs and all those later replacement payoffs by \(O(M(\alpha+D))\), and the prescribed first-exit law by \(O(\alpha+D)\). The total estimates prove the theorem. Convergence of approximate terminal Nash profiles to a target gives the fixed uniform payoff by the terminal-to-uniform selection theorem.

## A pointed transfer beyond allowed supports alone

For the partition \(\{0,1\},\{2\},\{3\}\), start with own levels one and every native entry zero except \(Z_0(2)=2,\ Z_1(3)=3,\ Z_0(01)=Z_1(01)=1\). Nonnegative native rewards give the required security. On successive dates let only 2 quit with chance \(1/2\), only 3 quit with chance \(1/2\), and both 0 and 1 quit surely. This is an exact equilibrium. At the last date 0 and 1 earn positive native payoffs from joining, and 2 and 3 are indifferent. The two solo owners tie at native zero and each quiet player weakly prefers its nonnegative continuation to immediate Quit at zero. This yields the law assigning \(1/2,1/4,1/4\) to \(2,3,01\), respectively, and target \((9/4,2,1,1)\). The same law and target are approached on every one of the unrestricted 34-entry completions.

A macroscopic isolated pulse cannot simply be kept. Raise only \(Z_0(02)\) to \(M>0\). In any strategy sequence approaching that target with vanishing regret, at every date a player-0 stop pays at least one plus \(M\) times the unconditional first-exit probability of singleton 2 at that date: on the latter event the same rival trials yield coalition 02 when 0 stops, and every other outcome for this deadline pays at least one. Thus the largest such single-date mass has limsup at most \(5/(4M)\). Capturing half of the prescribed singleton-2 mass requires order at least \(M\) dates as \(M\) grows. Conversely subdivide the first solo block into \(\lceil 2M\rceil+1\) equal hazards with aggregate \(1/2\). Its pulse size is at most \(1/(2M)\), so 0's immediate native offer is at most \(1/2\), while its assigned Wait throughout the block is at least \(1/2\). The other comparisons are unchanged. These finite exact profiles attain the same law and target and the matching linear date bound. The nonzero \(01\) mass prevents any globally solo approximation to this law.

The forbidden-coalition moment and removal theorem assumes a positive own level, no sure opening at punishment, and a positive blocker margin. It gives one-table allowed supports, retaining the possibility of large isolated pulses. The example has a sure opening and its inherited allowed calendar fails for large \(M\). The earlier vanishing-collision serialization treats the case where *all* joint first-exit probabilities vanish. Here the specified law has \(01\) mass \(1/4\). The checked payoff consumer is quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto in UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean. The present comparison and transfer are ordinary mathematics.

Source security matters even with all own levels positive. Give every coalition and player original reward one except $r_0(2)=r_0(02)=0$. A sure solo exit by 2 with everyone else waiting and an AllContinue tail after refusal is exact and pays $(0,1,1,1)$. On the partition $01|2|3$, change just $r_0(02)$ to two. The entries in the two displayed lists agree, but 0 now guarantees one by quitting immediately. The same target cannot be approached.

## Common first-exit laws across arbitrary reward completions

Fix any subset of the sixty original reward entries and allow each remaining entry to range independently over all finite reals. Call a nonempty coalition incomplete if at least one of its four entries is free. A law records all fifteen first-exit coalitions and literal Never. Say that a game attains a law if some sequence of independent behavioral profiles has terminal exploitability tending to zero and prescribed law tending to that law in total variation.

**Theorem.** If every completion attains a specified law, that law gives every incomplete coalition probability zero. Moreover there is **one sequence of profiles** attaining the law on all completions. Its regret tends to zero uniformly on every bounded set of completions. Its prescribed payoff converges, with the same uniformity, to the single vector obtained from the fixed coalition rewards and zero at Never. In particular this is an original uniform-equilibrium payoff on every completion. The converse about attainment of the law is immediate. The theorem permits different profiles on each completion in its hypothesis.

To see the support assertion, fix one missing entry of recipient \(i\) at coalition \(S\). Give just that entry reward \(-K\), leaving every other reward bounded in absolute value by \(B\ge1\), independently of \(K\). Player \(i\) can avoid this entry by Never when \(i\in S\), and by quitting immediately when \(i\notin S\). Thus its best replacement earns at least \(-B\), while its prescribed reward is at most \(B-(K+B)m_S\) when \(m_S\) is the prescribed probability of \(S\). Any profile of regret at most \(e\) satisfies \(m_S\le(2B+e)/(K+B)\). First pass to the law on this completion and then let \(K\to\infty\).

Next complete **every** missing entry by \(K_n=n\). On this table choose a profile of regret at most \(1/n\) whose prescribed law differs from the common law by at most \(n^{-2}\) in total variation. Its probability of all incomplete outcomes together is at most \(n^{-2}\). On any fixed bounded set of destinations with missing entries in \([-C,C]\), the same profile and any replacement induce exactly the same laws as they do on the selected table. When \(n\ge C\), every replacement's payoff on a destination is at most its payoff on the selected table, while the prescribed payoff can decrease by at most \((n+C)n^{-2}\). The claimed regret and payoff convergence follow. The original terminal-to-uniform conclusion applies for each destination by the checked theorem `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

**Two solved completions can have disjoint sets of attainable laws.** Take all own singleton rewards equal to one, with centered singleton matrix

    0 −1 −1  5
   −5  0  2 −1
   −2  4  0 −5
    3 −4  2  0.

On the first completion each native passive payoff is the sum of that recipient's singleton comparisons against the quitters, and its native payoff for joining is the negative of that sum over the other quitters. The proportional-additive existence theorem gives a uniform-equilibrium payoff. The exact example in the singleton-path classification gives an \(\eta>0\) such that every attainable law on this completion has total joint-exit mass at least \(\eta\). Indeed each column has a negative entry, the only directed arc is \(2\to3\), and every recipient secures its own level by a constant half hazard. [Proportional-additive existence](../revisit/ALL_PROPORTIONAL_ADDITIVE_FOUR_PLAYER_UNIFORM_EQUILIBRIUM.md) · [Exact matrix, finite path test and collision bound](../exports/GENERIC_FOUR_PLAYER_SINGLETON_PATH_CLASSIFICATION.md)

## A whole affine line with incompatible equilibrium laws

Keep the displayed singleton matrix Γ and all own levels equal to one. For every real v, let each outsider receive one plus the sum of its Γ entries against the quitters. A sole quitter receives one. A participant in a nonsingleton S receives

    1 − ∑_{j∈S} Γ_ij + 2v.

Every table on this line has an original uniform-equilibrium payoff. Nevertheless the attainable first-exit laws at v=0 are a positive distance from all those at sufficiently negative v.

For v≤−1 let player 2 quit surely while everyone else waits. After a refusal everyone continues. Each outsider's advantage from joining at the opening is 2(v−Γ_i2)≤0 because the three entries are −1,2,2. Player 2 can receive at most one by refusing. For −1≤v≤0 use the matching 02|13 with multiplier one in the raw two-pair criterion. For every i, its mate j satisfies Γ_ij≤−1. Its comparison c_i=2(v−Γ_ij) is nonnegative and at least Γ_ij. Against a nonempty subset of the opposite pair the native joining reward is at most the negative of the passive reward, as required. Here native means subtracting one from each nonempty outcome for each recipient. [Two-pair criterion, equation (1)](../revisit/ALL_PROPORTIONAL_ADDITIVE_FOUR_PLAYER_UNIFORM_EQUILIBRIUM.md)

For 1/5≤v≤1, use a single date with hazards (1,1,(1+v)/2,(2−v)/5). Every owner faces a sure rival, and its native Quit advantage is twice v−(Γq)_i. For 0 and 1 these half-advantages are (5v−1)/2 and (22−v)/5. Both other owners are indifferent. For 1≤v≤3 use the sure coalition 123. The row sums against it are (3,1,−1,−2). For v≥3 let everyone quit surely. The full row sums are (3,−4,−3,1). These profiles are exact against every unilateral behavioral alternative.

For 0≤v≤1/5 alternate the pairs 02 and 13. Write j for i's mate, O for the opposite pair, z=q_j, a=−Γ_ij, J=a+2v, c=2a+2v, P=∑_{k∈O}Γ_ik q_k and H=∏_{k∈O}(1−q_k). The native values at the player's scheduled and opposite dates are U=Jz and W=cz/(1−z), respectively. At the scheduled date these give exact indifference, since Wait earns Γ_ij z+(1−z)W. At the opposite date Wait earns P+HU. Thus its required value equation is

    F_i(q,v)=(1−z)P−az−(a+2v)z[1−(1−z)H]=0.

The certificate below gives a simultaneous solution with each q_i>0.016 and every sum of two hazards below 0.11. At an opposite date, Quit earns −P+2v(1−H). From the value equation the advantage of waiting is

    2cz/(1−z)−HJz−2v(1−H) ≥ 3az−2v∑_{k∈O}q_k > 0.004.

Each owner's rivals absorb with geometric tails under any unilateral deviation on this repeated two-date calendar, so the value equations price every stopping deadline and Never. The two-date calendar gives an exact terminal Nash profile and its fixed original uniform-equilibrium payoff.

**Rational certificate.** In each of eight parameter intervals the map q↦q−BF(q,v) maps a closed radius-1/1000 box into itself with sup-norm Lipschitz constant below 0.217. Its self-map bound divided by the radius is below 0.818. In particular B is invertible, since I−B∂F has norm below one. Every interval is closed and no choice of a common root at a shared endpoint is required. The following Python uses exact rational arithmetic. In the Jacobian error bound at fixed v, the mate derivative contains −P−a−(a+2v)(1−H+2zH), whose last factor changes by at most 4r. An opposite derivative contains z(1−z)(1−q_l), changing by at most 1.07r since z<0.07. The central residual and Jacobian are affine in v, so endpoint bounds suffice.

```python
from fractions import Fraction as F
from math import prod
G=((0,-1,-1,5),(-5,0,2,-1),(-2,4,0,-5),(3,-4,2,0))
mate=(2,3,0,1)
B=((-665,-123,-595,-344),(-1144,22,-1078,-844),
   (-2053,248,-1985,-1180),(-596,73,-779,-507))
B=[[F(b,1000) for b in row] for row in B]
ends=((20149,40192,63515,23259),(19748,39475,62320,22861),
      (19363,38784,61169,22477),(18992,38116,60060,22106),
      (18635,37471,58991,21746),(18291,36847,57959,21398),
      (17960,36244,56963,21062),(17640,35660,56001,20735),
      (17332,35095,55070,20418))
I=range(4)
r=F(1,1000)
def fields(q,v):
    A=[[F(0) for k in I] for i in I]
    f=[]
    for i in I:
        j=mate[i]; O=[k for k in I if k not in (i,j)]
        a=-G[i][j]; z=q[j]
        P=sum(G[i][k]*q[k] for k in O); H=prod(1-q[k] for k in O)
        f.append((1-z)*P-a*z-(a+2*v)*z*(1-(1-z)*H))
        A[i][j]=-P-a-(a+2*v)*(1-H+2*z*H)
        for k in O:
            A[i][k]=(1-z)*G[i][k]-(a+2*v)*z*(1-z)*prod(1-q[l] for l in O if l!=k)
    return f,A
for n in range(8):
    q=[F(x+y,2000000) for x,y in zip(ends[n],ends[n+1])]
    vs=[F(n,40),F(n+1,40)]
    residual=max(abs(sum(B[i][k]*f for k,f in enumerate(fields(q,v)[0]))) for i in I for v in vs)
    # Every partial derivative is multiaffine in all inputs except the term
    # z(1-z), increasing for z<1/2. A bound from the center's Jacobian:
    # its separate dependence on v is affine. In a radius-r box,
    # |delta P| <= r*sum |G_ik|, |delta(1-H+2zH)|<=4r;
    # |delta[z(1-z)(1-q_l)]| <= (1+max q)r <= 1.07r.
    E=[]
    for i in I:
        j=mate[i]; a=-G[i][j]; O=[k for k in I if k not in (i,j)]
        es=[F(0) for k in I]
        es[j]=r*(sum(abs(G[i][k]) for k in O)+4*(a+2*vs[1]))
        for k in O:
            es[k]=r*(abs(G[i][k])+F(107,100)*(a+2*vs[1]))
        E.append(es)
    R=max(sum(abs((i==k)-sum(B[i][l]*A[l][k] for l in I))
              +sum(abs(B[i][l])*E[l][k] for l in I) for k in I)
          for i in I for v in vs for A in [fields(q,v)[1]])
    assert min(q)-r>F(16,1000) and max(q)+r<F(66,1000)
    assert sum(sorted(q)[-2:])+2*r<F(11,100)
    assert R<F(217,1000) and R+residual/r<F(818,1000)
```

At v=0 the singleton-path result above supplies η>0 such that every attainable law gives joint exits mass at least η. Set K=−2v>2. On this same line a nonjoining recipient gets at most 6, and a nonsingleton participant gets at most 8−K. Never guarantees each player at least −6. If its probability of participating in a nonsingleton exit is m_i, a profile with exploitability e therefore satisfies (K−2)m_i≤12+e. Each joint exit counts at least twice in ∑m_i. Passing to a limiting law gives total joint mass at most 24/(K−2). For K>2+48/η the two sets of attainable laws have total variation distance at least η/2. This separation holds even when each table chooses its own behavioral profiles.
