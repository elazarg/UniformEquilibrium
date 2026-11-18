# Vanishing collisions and solo calendars in four-player quitting games

Consider independent behavioral strategies in a four-player quitting game. Live play and perpetual continuation pay zero. All fifteen nonempty coalitions have finite reward vectors. Write $s_i=r_i(\{i\})$, $\Gamma_{ij}=r_i(\{j\})-s_i$ and $J_{ij}=r_i(\{i,j\})-s_i$ for distinct players. Let $U_i$ be the prescribed terminal payoff, $B_i$ the supremum under complete unilateral behavioral replacement, $e=\max_i(B_i-U_i)$, and $C$ the unconditional probability of at least two simultaneous first quitters. A solo calendar has at most one positive hazard on **every** date, including dates reached only after a deviation.

**Theorem.** Suppose every player $i$ satisfies $s_i\ge0$ or has a distinct opponent $j$ with $\Gamma_{ij}\le0$. Then, for every target $u\in\mathbb R^4$, the following are equivalent.

1. Some profiles satisfy $U\to u$, $e\to0$ and $C\to0$.
2. Some solo calendars satisfy $U\to u$ and $e\to0$.

In fact, take any profile and let $M\ge1$ bound absolute original rewards. For every $0<a<1/4$ with $6C\le a^6$ there is a solo calendar with payoffs and caps satisfying

    max_i |U'_i−U_i| ≤ 8 M a,       B'_i ≤ B_i+12 M a for every i.

The inequality for caps is one-sided. These estimates apply even when the profile has positive probability of perpetual continuation.

## Comparing a prefix and its solo calendar

Let $q_i(t)$ be the behavioral hazard on date $t$, $h_i(t)=\prod_{v<t}(1-q_i(v))$ individual survival, and $S(t)=\prod_i h_i(t)$ actual joint survival. Use independent Bernoulli trials at all dates. While play is live its sole public history is past continuation. Every independent replacement stopping law is a mixture of pure deadlines and Never. We may therefore price each pure deadline and literal Never separately.

Take the prefix through the first date $T$ for which some $h_i(T+1)\le a$. If there is no such date use the whole infinite calendar. Every date included has $S(t)\ge a^4$. Each event that a specified pair quits on a reached date is contained in the event of a simultaneous first quit there. Thus, on the prefix,

    K = sum_t sum_{j<k} q_j(t)q_k(t) ≤ 6C/a^4 ≤ a².

On dates with largest hazard greater than $a$, keep only a player with largest hazard, at the original single date. The probability over all such old dates that any discarded Bernoulli trial succeeds is at most $K/a$, since each discarded hazard times the largest occurs in the pair sum. On the remaining dates use four consecutive subdates with one original hazard each in a fixed order. The probability that any such date has two successful trials is at most $K$. Set $D=K/a+K\le2a$. The same coupling and bounds apply with any player's trials omitted.

Outside these two events the original and new outcomes of every completed prefix agree for prescribed play, and for a player continuing through that prefix. A deadline at a retained single date faces the same offers outside the exceptional event. For a deadline inside a four-subdate block compare with the old deadline at its original date. The additional probability that a rival acts anywhere in that block is at most $3a$. Therefore the new payoff of each prefix deadline is at most its old counterpart plus $2M(D+3a)$. In the whole-infinite-calendar case the same union bound couples the prescribed payoffs and every Never payoff, including perpetual continuation. This proves the estimates in that case.

## Finding the last date and paying for refusal

In the finite case fix an owner $i$ crossing the threshold on date $T$. Call a date good if all its rival hazards are at most $a$. Over the other dates the sum of $q_i(t)$ is at most $K/a\le a$. There is a good date, since individual survival fell from one to at most $a$ and each decrease is at most $q_i(t)$. Let $n\le T$ be the last good date. Its remaining personal survival satisfies

    h_i(n+1) ≤ h_i(T+1) + sum_{n<t≤T} q_i(t) ≤ 2a.

Keep the edited prefix only through $n$. In the original calendar the probability of reaching its end is at most $2a$ under prescribed play, and under any other player's replacement that waits to its end. That player's opponents still include $i$. The coupling therefore bounds the prescribed payoff change by $2M(D+2a)$, independently of the new continuation. For a deviator other than $i$, compare every deadline beyond the prefix, including Never, with old Never. Its increase is also at most $2M(D+2a)$.

If $s_i\ge0$, let everyone continue forever after the prefix. Owner $i$'s conditional best payoff is $s_i$. If $s_i<0$, choose a distinct blocker $j$ with $r_i(\{j\})\le s_i$; let only $j$ quit with constant hazard $a$ thereafter. For any deadline of $i$, prior passive absorption pays at most $s_i$, and the deadline conditional on survival gives $s_i+aJ_{ij}\le s_i+2Ma$. Never gives $r_i(\{j\})\le s_i$. This is a solo tail in the original game.

Compare any late response by $i$ with its old deadline $n$. Outside the coupling error through earlier blocks and an event of probability at most $3a$ for any opponent acting on date $n$, earlier opponent absorption gives exactly the same reward. On survival the old response receives $s_i$ and the conditional benefit of the new tail is at most $2Ma$, using independence of its future trials. Thus the excess of the new response over the old cap is at most $2M(D+4a)$. These bounds imply the stated $8Ma,12Ma$ estimates. A vanishing-collision sequence admits choices $a\downarrow0$. The converse follows by taking the solo calendars themselves.

## What the reduction decides about reward data

At a solo date with prescribed quitter $j$, prescribed play sees only singleton rewards. A deviation by $i\ne j$ can additionally see the joint payoff **to $i$** at the pair $\{i,j\}$. A deviation by $j$ can only produce a singleton or continued play. Therefore the payoffs and full caps of every fixed solo calendar depend only on the four own levels and the twelve entries of each of $\Gamma,J$. The other 32 rewards are free. For fixed $s,\Gamma,J$ satisfying the theorem, the entire set of targets in condition 1 is identical across all completions, with arbitrary higher and passive-pair entries. The comparison uses original rewards including literal zero at Never throughout, so it also covers defective prescribed and deviating laws. In particular it applies for every fixed nonnegative vector of own levels.

If that common target set is empty, compactness of the bounded payoff cube gives a strictly positive lower bound on $e+C$ for every individual completion. The amount may depend on the completion. If it is nonempty, the same solo sequence at a chosen target works across every completion. The checked theorem `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` passes each convergent terminal Nash sequence to an original uniform payoff. Convergence gives a fixed target before accuracy, and each accuracy allows its own profile and threshold for all sufficiently large finite-average horizons.

Every hypothetical four-player counterexample has full normal core by `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff` in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`. The declaration `exists_core_blocker_of_mem_normalCore` in `UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean` then supplies the stated distinct blocker in every row. The remaining low-collision problem on this entire domain is the classification of approximate solo calendars from the 28 entries, including their macroscopic solo atoms. A table with no such calendar still needs a simultaneous-quitting equilibrium producer or a proof of positive unrestricted regret.

## A signed boundary example

Label the players $P,K,L,H$. Row $P$ pays $-1$ at $\{P\},\{K,L\},\{P,K,L\}$ and zero elsewhere. Each of $K,L$ receives one whenever it participates or the exiting coalition is $\{P\}$, and zero otherwise. Row $H$ is zero. Let $P$ quit surely at the first date, with $K,L$ both quitting surely at the next date following refusal. This gives exact terminal Nash and $C=0$. On any globally solo calendar let $p$ be the unconditional probability that $P$ exits first. Player $P$ guarantees zero by Never, so its regret is at least $p$. Players $K,L$ each guarantee one by immediate Quit. Their combined regret is at least $1-p$, since their combined prescribed payoff is at most $2p+(1-p)$. Thus $e\ge1/3$ on all solo calendars. The failing row is precisely the negative-own row $P$ with every opponent singleton strictly above its own.

## Prior results and formalization handoff

`isAsymptoticNash_quittingSerializedRoots` in `UniformEquilibrium/Quitting/Root/SequentialSerializationEquilibrium.lean` transfers Nash profiles with unit own singleton rewards and a uniform bound on all hazards. Sections 3–6 of `NATIVE_COLLISION_FLOOR_AND_GLOBAL_MASS_DICHOTOMY.md` use large-date deletion and fine-date serialization on small total finite clock mass in an own-zero native game. The new cutoff controls the player who can reach late dates upon unilateral refusal even after prescribed survival vanishes. `GENERIC_FOUR_PLAYER_SINGLETON_PATH_CLASSIFICATION.md` gives the continuous-path converse under additional row protection. `DIAMOND_SOLO_AND_JOINT_UNIFORM_EQUILIBRIUM.md` classifies low-collision equilibria by a six-run test on its asymmetric diamond. The present reduction makes no row-protection, pattern, or period assumption and does not supply a finite test for arbitrary solo calendars. The reduction and signed example are ordinary mathematical proofs.
