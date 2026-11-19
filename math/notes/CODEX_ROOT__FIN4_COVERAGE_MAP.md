# Fin4 coverage and completion map

Maintainer: `CODEX_ROOT`

## Status and finish line

Fin4 is open. The exact question is whether every reward table has terminal profiles with arbitrarily small maximum gain from a unilateral deviation. Compactness selects one payoff target before the accuracy. A refutation needs one table and one positive gain floor that works against every profile, including every nonperiodic behavioral calendar. [Terminal payoff selection](../../UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean) · [Exploitability gap](../../UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean)

| Scope | What is established | What would finish this route |
| --- | --- | --- |
| All original games, by source | On a given table the checked atlas has two possible outcomes. If any signed counterexample exists, an open ball of counterexamples has a selectable source entering through `TailEscapeSubsequence` and ending in `FinFourUniformEscapePacket`. An original joint exit is positively reached, and every later literal restart exceeds the entrance threshold. | A proof of UE for this single escape configuration would settle arbitrary Fin4. Converting its actual, higher-debt continuation into UE or a contradiction is open. [Single-obligation theorem](../exports/ONE_ESCAPE_OBLIGATION_FOR_ARBITRARY_FOUR_PLAYER_GAMES.md) · [Exact source map](#existing-exhaustive-source-map-two-open-consumers) |
| All games, by native rewards | Existence of any counterexample is equivalent to a positive infimum of total regret **on absorbing profiles** for one of the 56-dimensional tables with zero own singleton rewards. After a generic perturbation the least-Never construction partitions such tables into three disjoint cases. | Prove this infimum zero on all three cases, or exhibit one positive infimum. The minimizers used for this partition have a different objective from the source stream above. [Native reduction](#universal-native-domain) · [Three cases](#native-source-geometry-three-disjoint-table-branches) |
| On the residual reward domain, by continuation payoffs | On the hypotheses stated below, UE is equivalent to a cycle at every accuracy in a finite payoff graph. On the normal positive-own branch without a sure opening, UE is also equivalent to convex feasibility at every polynomial degree. Specifying the target or allowable joint exits gives finer tests under their respective hypotheses. | Force recurrence allowing the period to grow, or establish all-degree feasibility for every residual game. A separating polynomial of any one degree at one such table suffices for a refutation. [Payoff graph](#a-finite-payoff-graph-on-the-residual-games) · [Payoff moments](#a-convex-test-on-the-original-payoff-polytope) · [Exit laws](#which-exit-laws-remain-possible) |
| On the same conjecture, by behavioral constructions | Stationary and sure-opening producers, continuous singleton paths, finite calendars with simultaneous exits, and variable-length constructions cover overlapping classes. The constant, triangle and quadrilateral tests decide the continuous singleton path question on every singleton matrix. Higher rewards govern the payoff for joining another quitter. | Construct or exclude the remaining behavior on actual rewards. The four disjoint work-queue arms take the complement of five named raw criteria only. A complete executable registry of the union of all known sufficient criteria is still missing. [Singleton paths](#a-complete-test-for-continuous-singleton-paths-on-every-matrix) · [Raw work queue](#reward-class-work-queue) |

The integrated chronological approach also has a rank reduction to positive total slope, zero-debt support entry, or a paid off-minimum row. Its consumers require chronological blocks or an admissible return with the stated source data. On the negative side, a Research theorem gives a rational semidecision procedure that eventually returns a certificate if any real Fin4 counterexample exists. Any bounded run without a certificate leaves the question open. The conference formalization records for the [source-preserving atlas](../formalized/FIN4_SOURCE_PRESERVING_COMPLETION_ATLAS.md) and [negative search](../formalized/EXACT_FIN4_SCALE_RESOLUTION_AND_COUNTEREXAMPLE_SEMIDECISION.md) state which parts have reached Lean. The Lean claims in this note were checked against declaration text. No fresh Lean build is claimed. [Current proof dependencies](../../docs/FRONTIER.md#current-proved-dependency-dag) · [Rank reduction](../../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FlatCirculationSupportRankElimination.lean) · [Counterexample search](../../Research/Quitting/FinFourCounterexampleSemidecision.lean)

**A bounded joining reward on every singleton matrix.** Fix any real hollow singleton comparison matrix, allowing ties. It selects a recipient $o$ and a rival $j$. Holding the other entries fixed, either tail of the single centered reward $Z_o(\{o,j\})$ gives an original uniform equilibrium. On every strict matrix surviving the singleton exclusions, the proof produces an exact stationary profile with at least three positive hazards of order $1/|Z_o(\{o,j\})|$. It also covers a second independently signed scale carried by the two triples containing $o,j$ with positive comparable coefficients. The ten other higher rewards in the selected recipient’s row can grow without limit in the directions that reinforce the selected reward. The other three rows have bounds growing with coalition size. The remaining obligation includes intermediate values of the selected reward and simultaneous growth outside these bounds. [One joining payoff on every singleton matrix](../exports/ONE_JOINING_PAYOFF_ON_EVERY_FOUR_PLAYER_SINGLETON_MATRIX.md)

For a chosen three-player child with individually finite approximate equilibria, the largest gain a quiet fourth player can achieve in the limit is exactly the supremum of zero and the gains at two kinds of one-date opening. One uses a three-player Nash opening with an attainable continuation exit law. The other has a sure quitter and tests the cost of refusing to quit. A sufficient test on the seven-coalition simplex can certify a lift even when the fixed withdrawal inequalities fail on all fourteen proper children. The separating example also has a mixed stationary equilibrium. On another surviving singleton matrix a child debt of $t^2$ can leave the outsider a gain of $t$, even though the lift works at vanishing regret. [Quiet-player product test and exact regret](../exports/WITHDRAWAL_AND_PRODUCT_OPENINGS_FOR_A_QUIET_PLAYER.md)

**Every table with at most five nonzero centered nonsingleton rewards has a uniform-equilibrium payoff.** At six, at most 96 of 7,059,052 possible position sets survive. At seven, at most 31,628 of 38,320,568 survive. These are upper bounds on possible supports over arbitrary singleton matrices. A signed test after truncation also bounds regret on dense tables. [Support counts and bounds](../exports/FIVE_NONSINGLETON_REWARDS_AND_THE_SIX_ENTRY_FRONTIER.md)

On the six-entry frontier there are eight strict, eleven one-tie and four two-tie singleton sign classes. All 23 have the same further restriction throughout their full singleton magnitude ranges. Complementarity at a specified target either produces a three-player singleton cycle giving equilibrium for every completion, or identifies one outsider with a strictly positive inverse column. That outsider's positive higher reward must exceed a strictly positive threshold determined by the singleton matrix, however large the other five rewards are. With those five fixed the same price must also stay below a finite upper threshold. Hence all sufficiently small six-entry perturbations of the zero higher table are solved at *every fixed singleton matrix*, including ties. The two proofs use an exact three-date equilibrium and a return built from increasingly long private calendars, depending on which outsider receives the positive triple reward. When that reward goes to the selected outsider, a second calendar keeps working above its threshold: the mates mix with one outsider on the first date and with the other on the third. The price bounds hold in all 23 chambers, with both choices of withdrawing mate. At witness 6 an integer table with prices 16, 16, 48 and three unit grand rewards has such an exact equilibrium and a positive regret gap over all stationary profiles. Both properties also hold on an open set of full tables. [Proofs for both assignments](../exports/FIVE_NONSINGLETON_REWARDS_AND_THE_SIX_ENTRY_FRONTIER.md)

Some of the middle interval is covered as well. Near integer witness 18 the marked mate's withdrawal advantage may be as large as one with all five other prices independently unbounded, for either choice of withdrawing mate and either implementation of both withdrawals. At high grand prices the proof allows simultaneous variation of all 38 additional higher entries. Near witnesses 6 and 18 a sufficiently large positive passive withdrawal reward can instead be handled by allowing all four players to mix when the three-player calendar gives the fourth player a profitable deviation. The same construction works for a specified withdrawal owner near each of witnesses 8, 19 and 21. At witness 6 the other withdrawal can be arbitrarily large independently of the first when it is a negative grand reward, and also in its passive implementation when the positive triple reward is at most one. A two-dimensional return also covers large negative participating withdrawals for either mate near witness 6 and one mate near witness 18. [Large withdrawal rewards and four-player dates](../exports/SIX_ENTRY_EQUILIBRIA_WITH_LARGE_WITHDRAWAL_REWARDS.md)

Six centered nonsingleton entries can force both nonstationarity and simultaneous quitting by all four players on one date in the same game. On witness 6 with the other outsider receiving the positive triple reward, a family of tables has a uniform-equilibrium payoff, a strictly positive regret floor on stationary profiles and a strictly positive one-date grand-exit probability in every sufficiently accurate profile. These two positive quantities may depend on the table. [Proof and exact parameter quantifiers](../exports/SHARP_SPARSITY_FOR_COMPULSORY_GRAND_EXITS.md#compulsory-grand-exits-together-with-a-positive-stationary-regret-gap)

### A reward-independent formulation for arbitrary Fin 4

Subtract each player's own singleton reward from that player's rewards on every nonempty exit. Call the resulting table native. **Arbitrary Fin 4 is equivalent to the following convex-hull assertion in 56 coordinates.** Give each owner two ordered lists of $N$ stopping labels. At each cut the two cumulative counts for that owner differ by at most one. At least one player must have only finite labels on both lists. In the universal equivalence, one may also prescribe the same finite owner for all orders by the [singleton translation](../exports/ZERO_SINGLETON_COLUMN_EQUIVALENCE.md). A test observes the order of the first lists and replaces one player's clock by an observed rank or Never. Using independent uniform draws from the second lists, compute how that replacement changes the probabilities of each first-exit coalition, omitting the player's own singleton. For every $N$ and every choice of nonnegative weights on the tests, the convex hull of the weighted change vectors over all admissible orders must contain zero. A strictly separating table would have positive regret on all absorbing private calendars. Raising one player's exit payoffs by any positive amount would give an original counterexample.

For the positive tail there is a stronger one-row statement. Every singleton matrix which could admit a counterexample has a player with a unique strictly positive foreign singleton and two strictly negative ones, including at a tied matrix. Once that row is chosen, a sufficiently large positive reward for joining its unique positive donor needs only one-sided bounds on that recipient’s ten remaining higher rewards. All 45 raw entries of the other three recipients can then change arbitrarily. This explicit estimate follows from the earlier seven-coalition test for one recipient. [One positive joining reward and three free rows](../exports/ONE_JOINING_PAYOFF_ON_EVERY_FOUR_PLAYER_SINGLETON_MATRIX.md#one-positive-joining-entry-and-three-unrestricted-recipient-rows)

Two tests on a pair of recipients also give original uniform equilibrium with the other two entire payoff rows unrestricted (30 raw entries). For each pair of outsider hazards the proposed sure owner must weakly prefer quitting when its mate waits, and its mate must weakly prefer waiting when that owner quits surely. On seven of the 21 strict singleton sign classes, a separate stationary construction applies when selected pair and triple rewards in one row are large at their respective scales. All eleven higher rewards of the other leaf may have arbitrary independent values. The proof also handles a large grand reward and a same-sign triple in the controlling row. A one-sided stationary version covers eight additional mixed-sign core classes, bringing that result to 15 of 21. Neither construction settles all completions of these classes. [Two free rows and the seven singleton classes](../exports/TWO_FREE_ROWS_FROM_A_RECIPROCAL_PAIR.md)

For any nonempty set of strictly positive inverse columns, the corresponding grand rewards can traverse the entire nonnegative orthant except its origin. A full-support stationary equilibrium persists under explicit simultaneous higher-reward errors. As the grand rewards approach zero, twelve participating triples and their paired passive entries can diverge in either sign within the stated bounds, while all four hazards approach one. [Positive grand rewards at every scale](../exports/POSITIVE_GRAND_REWARDS_AT_EVERY_SCALE.md)

The least number of nonzero higher entries needed to require three or four simultaneous quitters in arbitrarily accurate play is zero or four, respectively. On a six-entry family at high grand price $R$, the best possible order of the total probability of a grand first exit is $1/R$. On one date the corresponding sharp order is $R^{-4/3}$. The equilibrium construction and the necessity bounds hold on the same family. [Sharp sparsity and grand exits](../exports/SHARP_SPARSITY_FOR_COMPULSORY_GRAND_EXITS.md)

Ranks one through three pass for every signed table in the unrestricted test, and for every native table with any finite owner prescribed. At rank three one can take all four owners finite whenever there is a weak blocker. This uses the 20-plus-one sign classification and a physical continuation after two unobserved dates. Universal rank four remains open. Every positive matching passes rank four for all twelve singleton magnitudes and arbitrary higher rewards. Each player values its mate’s singleton positively and both crossed singletons negatively. Every symmetric matched matrix passes ranks four, five and six for every completion and arbitrary positive row scalings. [Matched order tests](../exports/MATCHED_SINGLETON_ORDER_TESTS_AT_RANKS_FOUR_TO_SIX.md) A failure at that level also forces one of two named participants to have positive cumulative hazard sum below $\log(4/3)$ on every backward sequence of Nash stages for the specified continuation. [Third-rank theorem](../exports/EVERY_FOUR_PLAYER_QUITTING_GAME_PASSES_THE_THIRD_ORDER_TEST.md) For the order set allowing the finite owner to vary, several classes pass at every level. Rules testing only the first or last finite rank on each owner's list pass. When all recipients use the same distribution over ordinal ranks, tests may copy any other owner at any rank, even on strongly connected graphs of copies. A single polynomial-size network computes the full hull for fixed donor-and-rank weights. A separator must sometimes test a strictly interior rank, and at each proper subgame it must test entry by an absent player on observations reached by accurate absorbing equilibria of that subgame. For arbitrary rules a twelve-equation system tests whether sixteen explicit orders suffice. The all-level assertion for fully observation-dependent, interior-rank tests remains open.

Every four-player table with **at most one strictly positive foreign singleton comparison in each payoff row** passes the fourth all-four-finite order test. For strict comparisons the positive-donor graphs on the remaining branch are two matched pairs, the two reciprocal-pair configurations, or a three-cycle with a fourth player pointing into it. Replacing ties by small negative comparisons and taking limits gives the general statement. Of the 21 strict and 95 tied classes surviving the earlier singleton tests, the four closures account for 4 strict, 13 one-tie, 22 two-tie and all 10 three-tie classes. A fourth-rank failure therefore remains possible in at most **17 strict, 33 one-tie and 17 two-tie classes**. Higher ranks and general UE remain open on these sign classes. [Two reciprocal-pair configurations](../exports/RECIPROCAL_CORE_AT_RANK_FOUR.md) · [The three-cycle and its dependent](../exports/THREE_CYCLE_WITH_A_DEPENDENT_AT_RANK_FOUR.md)

All 21 strict and 95 tied integer calibrations pass rank four for every completion. More generally write $P_i,M_i$ for the sums of the positive singleton comparisons and the magnitudes of the negative ones in row $i$. Three rows may have any ratios $20/21\le P_i/M_i\le21/20$ and the fourth needs only $P_h/M_h\ge20/21$. The result includes zero rows by its undivided inequalities. On the same calibrations, setting the higher rewards to zero and the own singletons to one forces any sufficiently high-rank certificate to place a positive fraction of two owners' labels together on one date in every extension of each observed training order. [Row totals and compulsory multiplicities](../exports/COMPARABLE_SINGLETON_ROW_TOTALS_AT_RANK_FOUR.md)

For a specified signed game there is also a 60-coordinate test, retaining its own singleton rewards and a distinct late deadline. Each passing level gives genuinely private clocks of total terminal regret at most $192M/N$ on payoffs bounded by $M\ge 1$. A fixed training order admits a polynomial-size validation flow. If a native counterexample exists, varying just one positive row shift on the same bounded kernel gives original counterexamples that pass any prescribed number of these signed tests. In the native absorbing test there is an unconditional timing bound in the other direction. One fixed solvable table with entries in $\{-1,0,1\}$ needs order $N$ distinct finite ranks in every positive training cell at level $N$. The general upper bound of $4N$ dates therefore has the optimal order of growth. [Order tests, proofs and examples](CODEX_ROOT__INTERLACED_ORDER_TESTS_FOR_ARBITRARY_FOUR_PLAYER_GAMES.md)

There is now an equivalent test using only finite labels on both lists of all four players. Form the same convex hull over the entirely finite orders. For each of the 21 singleton sign classes below, the hull must contain a vector whose 44 changes at nonsingleton coalitions vanish and whose twelve singleton changes have signs opposite the corresponding rewards or are zero. Each class may use a different vector. This must hold at every level and for every observation-dependent collection of test weights. Alternatively one may ask only whether this same hull meets the nonnegative ray in a single specified singleton coordinate. A strict separation gives a finite certificate and an explicit lower bound on the true gap. [Finite-label order theorem](CODEX_ROOT__INTERLACED_ORDER_TESTS_FOR_ARBITRARY_FOUR_PLAYER_GAMES.md#finite-labels-and-singleton-sign-cones)

The zero-column translation preserves the exact optimization problem at each finite rank when the owner is prescribed. A weak blocker for that owner lets all four sets of clocks be completed at the same level. In 17 of the 21 sign classes this also preserves the optimum when the finite owner in the original order may vary. The entirely finite tests pass through rank three in all 21 classes. A fixed-point argument cancels all tests to finite ranks against four chosen fallback laws, but one explicitly solvable rank-copy example in every sign class requires order priors outside that construction. [Completion](CODEX_ROOT__INTERLACED_ORDER_TESTS_FOR_ARBITRARY_FOUR_PLAYER_GAMES.md#exact-clock-completion-at-a-fixed-rank-level) · [Fixed-point calculation and example](CODEX_ROOT__INTERLACED_ORDER_TESTS_FOR_ARBITRARY_FOUR_PLAYER_GAMES.md#cancelling-every-finite-rank-response-with-prescribed-fallback-laws)

For each finite rank $N$, every surviving strict or boundary singleton sign class contains a positive-kernel matrix with a full singleton neighborhood of radius $c/N$ passing that rank. All 44 higher payoffs may vary freely. Some matrices in each strict neighborhood also pass all the singleton counterexample screens. The radius depends on the rank, so these certificates give no fixed neighborhood of equilibria. [Positive-kernel order tests](../exports/FINITE_ORDER_TESTS_NEAR_A_POSITIVE_SINGLETON_KERNEL.md)

There is a smaller exact target for the remaining all-rank question. Erase a single recipient’s row at a positive inverse column. The three retained singleton rows then have a common strictly positive kernel vector $z$. At each rank impose all three retained players’ conditional incentive inequalities. For every collection of test weights for the erased player, the 14-dimensional set of attainable changes in that player’s exit probabilities must meet one ray. Its eleven nonsingleton coordinates vanish, and its three foreign singleton coordinates are proportional to $-z_j$ with nonnegative proportionality factor. This assertion at all ranks is equivalent to arbitrary Fin4. The ray is met at zero for every test using any of the erased player’s own labels, a first or last label of any player, Never, or a date at or after the first rival’s final label in the constructed orders. A separating test must sometimes use a rival’s interior label strictly before all three rivals’ final labels. For a global separating test the directed graph of such interior requests must cross every nontrivial cut in both directions. Each donor must also be tested by a recipient who gets a negative payoff on that donor’s singleton. Four of the surviving strict sign classes require at least five directed recipient–donor pairs at any failing rank. [One-recipient reduction and endpoint theorem](../exports/FINITE_ORDER_TESTS_NEAR_A_POSITIVE_SINGLETON_KERNEL.md#which-positive-kernel-centers-are-left)

### Choosing the signs and the players in the escape problem

The same native counterexample would have to supply the escape for **each of the fourteen nonempty proper choices** of recipients who gain at every exit. In the original games the absolute gains and losses can be arbitrarily large. Each game has its own marked coalition and a positive regret increase at every later reached restart. With one designated losing recipient, all limiting native regret falls on that player. With one designated winning recipient and generic loss weights, only the winner's clock absorbs surely. At least one losing player actually participates in a first exit. At least two losing players have positive native regret, each equal to its weight times the same strictly positive minimizing coefficient. This excludes a native limit supported entirely on solo quits of the designated winner, and also excludes a single native debtor for this choice of signs. [Signed escape theorem and proof](../exports/PRESCRIBED_SIGNS_AND_NATIVE_LIMITS_OF_FOUR_PLAYER_ESCAPE.md)

At a generic native table the four continuation payoffs either are all strictly positive or all vanish. In the zero case, for generic loss weights, at least four linearly independent original reward vectors must occur with positive first-exit probability. At least three players therefore quit with positive probability. The zero case also requires the native AllNever-only branch. The positive case can occur only if the actual absorbing source has all four augmented payoffs strictly above zero. [Continuation alternatives and four-column proof](CODEX_SOURCE_GATE__GIFTED_CAP_POSITIVE_OR_ZERO.md)

For every choice of sole debtor, one can minimize on a smaller set where all three other clocks stop at a finite date almost surely. At least one choice of the debtor achieves this at the original global coefficient. On that source every player therefore faces rivals who absorb even if the player waits forever. Certainty that a winning player eventually stops on their private clock does not imply that this player stops before the game ends. The proof uses the full normal core, the negative singleton pair and the positive inverse column to choose the globally admissible partition. [Three absorbing winners](CODEX_SOURCE_GATE__GIFTED_CAP_POSITIVE_OR_ZERO.md#which-winning-clocks-can-be-required-to-absorb)

At a strictly positive continuation the first date carrying nonvanishing stopping mass has an actual product row $q$. Put $S=\prod_i(1-q_i)$, let $R(q)$ be the expected reward from exits on this date, and let $H$ be the convex hull of the fifteen nonempty native reward vectors. For the same row there must exist $v\in H$ and $\rho>0$ such that $b=R(q)+Sv+\rho c$. The loss weights $c$ vanish on winners. Each losing hazard is strictly below one. Every immediate Quit offer is at most $b_i$, with equality at each positive hazard. At a zero continuation the test instead requires $-\rho c\in H$, with the four-column restriction above after generic selection. These are finite real-algebraic necessary tests in each sign direction. They use the continuation after this one row, whereas the actual minimizing source must support an entire calendar. [First significant date and its common continuation](../exports/UNIFORM_EQUILIBRIUM_FROM_A_BOUND_ON_POSITIVE_QUIT_OFFERS.md) · [All sign partitions](../exports/PRESCRIBED_SIGNS_AND_NATIVE_LIMITS_OF_FOUR_PLAYER_ESCAPE.md)

With one winning pivot, a strictly positive minimum also fixes three losing players' payoffs when each individually chooses Never. A single collection of independent conditional clocks on at most 29 ordered dates and Never must realize those three values, all four prescribed tail payoffs and the original marginal Never masses. The joint feasibility test is finite and polynomial. At fixed marginals its convex hull has 75 candidate order vectors. A rational positive opening satisfies every linear bound from those vectors, yet every independent tail misses at least one required deletion payoff by more than $1/1600$. This distinguishes private timing from a mixture of calendars sharing a random signal. The 29 dates preserve the seven payoff coordinates; the full deviation caps and survival optimality at the actual continuation still have to hold. [Finite common-tail theorem and cyclic-order obstruction](CODEX_ROOT__INDEPENDENT_TAILS_AT_THE_FIRST_POSITIVE_OPENING.md)

The coefficient describes every sufficiently accurate minimizing sequence on the intermediate price scales, and every native minimizer can be recovered by actual independent strategies. Each such minimizer specifies four continuation payoffs. In the game obtained by subtracting those payoffs from the corresponding exit rewards, every sequence of approximate equilibria must have exit probability tending to zero. The rigidity applies to arbitrary private calendars. It gives a further way to attack the minimum by constructing a nonvanishing exit at its particular continuation. The original marked probabilities can shrink along the sequence of tables. [Continuation and participation proof](../exports/PRESCRIBED_SIGNS_AND_NATIVE_LIMITS_OF_FOUR_PLAYER_ESCAPE.md#all-finite-moves-the-never-bonus-and-compulsory-participation)

On the positive-gap branch at a **strictly positive** continuation, the translated game admits a nonblank limiting equilibrium law exactly when its one-date game has a nonblank Nash row. Positive total survival keeps the last significant date reached, and the positive continuation makes later small quitting masses too costly. Thus a longer block tested at this same payoff supplies no additional exclusion. The shared opening and successor constraint above does supply extra information. [Last-date proof and scope](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md#a-strictly-positive-continuation-reduces-the-block-test-to-one-date)

There is an exact global restriction on each continuation actually reached at a signed minimum. If the probability of reaching a cut tends to $s>0$ and its four effective payoffs tend to $v$, the least limiting survival probability of **any** approximately Nash finite timing block with terminal payoff $v$ is exactly $s$. The historical prefix attains this minimum. With one winning player the end can be reduced to one final date after a bounded amount of cumulative quitting hazard. With three surely finite winning clocks and one debtor, the end either has a sure winning quit or reaches a three-player equilibrium suffix in which the debtor always waits. In the latter case that suffix maximizes the debtor's passive payoff among absorbing three-player equilibrium laws with the same three winning payoffs. Replacing it by an improvement would reduce the original price. A finite test determines exactly which of the seven single-coalition laws can fill a suffix with all three clocks surely finite. [Cut identity, outsider maximum and vertex tests](CODEX_ROOT__SURVIVAL_AT_CUTS_OF_A_SIGNED_MINIMUM.md)

Two-zero continuations now have an exact minimum-survival calculation. At such a continuation the last short portion uses only the two zero-payoff owners. Two linear order identities and the first-date inequalities give the entire attainable menu of payoffs and survival probabilities, including zero or tied reward entries. On generic tables, approaching the two-zero face from either side also has a uniform reduction. One unrestricted product row and at most five portions involving two owners take a positive step or reach survival minimum one. The portions may use arbitrarily many dates. On compact sets away from nonnegative continuations with at least three zeros, a bounded number of these steps suffices. This reduces a surviving block's timing choices and still allows approach to a three-zero or four-zero continuation. [Exact face and both-sided theorem](CODEX_ROOT__OPTIMAL_TIMING_BLOCKS_AT_SMALL_CONTINUATIONS.md) · [Earlier geometric-contact proof](../exports/UNIFORM_THREE_OWNER_TAIL_DISPERSION.md)

There is a global reduction for the entire minimum-survival function on bounded continuations above the players' security values. At any nonzero payoff, either a single four-player date suffices for the next step, or one player strictly waits in a short final block. For that block only three players' private clocks remain, and its law and their complete response caps can be determined to arbitrary accuracy from the seven three-player reward columns. This works at three-zero payoffs, with arbitrary signs and without a genericity assumption. The value on the whole domain is determined by such paths and one scalar, the least limiting native joint Never probability at continuation zero. If a signed source reaches a cut requiring a limiting path into zero, every native least-Never payoff can serve as the effective payoff of a global optimum for that same choice of signs and weights. A finite convex-hull test rules out this alternative in some directions. The path values still depend on the game, and reaching survival minimum one ends the block calculation. It does not establish equilibrium on the original table. [Global path formula, scalar boundary and signed-source consequence](CODEX_ROOT__OPTIMAL_TIMING_BLOCKS_AT_SMALL_CONTINUATIONS.md#the-only-boundary-value-needed-by-the-three-player-bellman-reduction)

The remaining origin alternative also has a finite rejection test. At the required price (the optimal price divided by the native least-Never probability), impose the zero effective cap on the same four marginal Never probabilities, four payoffs, four literal Never offers and four unrestricted best-response caps. The existing finite-clock compression gives a computable error at each resolution. A strict separation, including separation on a certified price interval, excludes this alternative and gives a uniform bound on the number of reduction steps for cuts whose reach is bounded below. [Zero-source price test](CODEX_ROOT__OPTIMAL_TIMING_BLOCKS_AT_SMALL_CONTINUATIONS.md#a-finite-exclusion-test-at-the-origin-price)

A finite-degree moment test now describes all first-exit laws and their attainable upper bounds on unrestricted deviation payoffs, at every signed table and at positive as well as zero regret. In particular one can impose a lower bound on exit probability and minimize total regret. Applied to a continuation above, every fixed positive lower bound on exit probability gives a strictly positive minimum, and a sufficiently high finite degree certifies a positive lower bound. Which degree suffices depends on the table and the exit bound. No computation has found such a certificate against every profile of an original candidate counterexample. [Law and cap proof](CODEX_ROOT__TRUE_CAPS_AND_FIRST_EXIT_LAWS.md)

At both published pair-data examples for the quadratic cost, its true unconstrained coefficient is zero for all positive price weights, while the cost with a nonnegative singleton payoff at the beginning stays strictly positive. Every higher-reward completion admits exact native equilibria at each sufficiently small prescribed absorption probability. At the asymmetric example a single 25-date sequence of supports yields a two-dimensional surface of exact native equilibrium payoffs. On an open subfamily the only one-date Nash row at continuation zero is blank and every finite equilibrium block with positive survival is blank. The infinite calendars still exist and all four players have positive probability of Never. These are constraints on the native zero-absorption boundary; they leave the absorbing-regret question for generic higher completions open. [Exact equilibria and proof](CODEX_ROOT__EXACT_CLOCKS_AT_ALLNEVER.md) · [Exact arithmetic](../experiments/CODEX_ROOT__TWO_EXPANDING_NATIVE_CLOCKS.py)

### What the remaining argument must allow

There is a nonempty open set of the full 60-dimensional reward space on which every game admits a uniform-equilibrium payoff and every sufficiently low-regret profile must give **all fifteen coalitions** positive first-exit mass on **one common date**. The date is specific to the profile. Each unconditional probability has a positive lower bound fixed by the table. There is no sure opening, no exact terminal equilibrium of any period or with an aperiodic calendar, and every finite period bound has a positive regret floor. The full proof constructs the profile by alternating joint decisions with a pair of players returning two continuation coordinates to zero. It also proves that this pair’s two quiet opponents prefer waiting throughout. This excludes the entire union of constructions that omit even one coalition from first exits. Existence for arbitrary games whose laws use all fifteen coalitions remains open. [Open family, unrestricted deviations and common-date theorem](../exports/EVERY_FIRST_QUITTER_COALITION_CAN_BE_COMPULSORY.md)

Another nonempty open set in all 60 reward coordinates has **exactly eight** possible first-quitter coalitions in every limiting law of vanishing-regret profiles. Each nonempty subset of 013 occurs with positive mass on one common date, and 2 must also quit alone. All seven joint coalitions containing 2 have combined probability at most a constant times regret. Each game has a uniform-equilibrium payoff and excludes every exact behavioral equilibrium. On the calibrated large-premium tables, the total mass of 013 is of order $1/L$, the most any one date can carry is of order $L^{-3/2}$, and the minimum number of dates needed for half that mass is of order $\sqrt L$. A wider existence region tests 39 coordinates and leaves the other 21 independently unrestricted. It also covers a whole signed line of singleton rewards. The exact-support conclusion uses the protected open subset. [Eight compulsory coalitions, raw tests and sharp date bounds](../exports/EIGHT_COMPULSORY_FIRST_QUITTER_COALITIONS.md)

A separate solved family allows nine reward entries to move without a common magnitude bound. Fix the singleton matrix and the additive native baseline in the proof. Five participant rewards range independently over the entire real line: player 0 on 013, 023 and 0123, and player 1 on 123 and 0123. At the same time player 0's two passive rewards on 23 and 123 can increase independently, and player 1's two passive rewards on 23 and 023 can decrease independently. All four original own singleton levels are free. This covers **every reward of players 0 and 1 on the four coalitions containing both 2 and 3**, with the indicated one-sided restrictions when the recipient stays, and one further reward on 013. The other native entries remain fixed. The earlier construction gave nonnegative returns on the two-premium plane and on a nonnegative four-parameter region. At the new packet’s explicit table there is no stationary equilibrium or sure opening, and at a reachable positive input every nonblank stage equilibrium gives player 1 a native output below $-34$. The new construction repairs even two negative coordinates and reenters the positive region. This closes the entire specified family and leaves the general two-zero continuation problem open. [Nine raw rewards and signed continuations](../exports/SIGNED_CONTINUATIONS_ON_THE_TWO_PLAYER_COALITION_BLOCK.md) · [Earlier positive return and scalar construction](../exports/TWO_SIGNED_TRIPLE_REWARDS_AND_INDEPENDENT_GRAND_REWARDS.md)

The same signed nine-entry family also allows eight independent nonnegative paired adjustments for the two other recipients. For player 2 and each of the four rival sets containing player 3, increase its passive reward and decrease its reward for joining by the same amount. Independently do the analogous four adjustments for player 3 when 2 is among its rivals. All eight sizes are unbounded. The changed rows require a new bound at the full-support stage of the return. This retains the signed two-zero construction on a larger set of tables. [Extension and proof](CODEX_ROOT__COUPLED_PAIR_RETURN_AND_ITS_LIMIT.md#independent-paired-changes-for-both-pinned-recipients)

On the original two-premium slice with own levels one and $K\ge L\ge L_0$, every sufficiently accurate private calendar pays one of 013, 123 or 0123 with probability bounded below for that table. There is no stationary equilibrium or sure opening. If both $L$ and $K/L$ are sufficiently large, no exact behavioral equilibrium exists and every fixed period bound has a positive regret floor. The original one-seed return still selects a target of the form $s+7x e_2$ on the ordered positive region. The larger existence construction can use several successive seeds. These statements concern different prescriptions and give distinct information even at the same raw table. [Compulsory triple exits and the one-seed target](../exports/UNIFORM_EQUILIBRIUM_REQUIRING_TRIPLE_FIRST_EXITS.md)

The four individual singleton exits remain compulsory in this large-premium family. The one-owner blocking margin is 4 since all pair rewards are unchanged. The deletion test excludes every pair of participants. On the four possible three-person sets 012, 013, 023 and 123 use rows 1, 0, 2 and 3, respectively. The required passive comparisons have signs $+,-,-,-$, and the extra reward to 0 on 013 only strengthens its negative-passive comparison with joining. All four singleton payoff vectors lie in the same affine hyperplane as before, and the unchanged pair rewards on 02 and 03 remain strictly on its opposite sides. Hence all limiting equilibrium payoffs have positive distance from the boundary of the reward hull at each such table. The support of a limiting first-exit law is closed under taking nonempty subsets on the no-sure branch. Consequently at least eight of the fifteen coalition types occur on this family, counting four singletons, one triple and its three pairs. Eight is a lower bound. [Deletion and hull tests](../exports/ALL_FOUR_FIRST_QUITTERS_AND_UNBOUNDED_JOINT_DATES.md) · [Support census](#which-exit-laws-remain-possible)

The global gap test supplies a different way to measure the remaining domain. For every signed table with rewards of magnitude at most one, an unrestricted exploitability floor $g>0$ forces failure of a moment test by degree $O(g^{-2}\log(2/g))$. Passing that specified degree at a table excludes the entire gap scale there. No calculation has shown that all residual tables pass. A candidate for a disproof still needs a physical certificate valid against arbitrary private stopping rules. [Degree, rounding and quantifiers](../exports/FINITE_MOMENT_DEGREE_AT_EVERY_EXPLOITABILITY_SCALE.md)

For the positive-own, no-sure residual with positive sole-owner margin, the grand-coalition test locates the boundary between proper and full first-exit supports. If a vanishing-regret sequence loses any one nonempty coalition in its limiting law, downward closure forces its grand mass to vanish. The forbidden-coalition theorem then supplies a sequence in which at most three players act at each date. In the other direction, a positive lower bound on grand mass at small regret gives a positively reached date where all four hazards are bounded below. No sure opening bounds those same hazards away from one. Consequently all fifteen exact outcomes have positive lower bounds on that date. Testing each permanently absent player separately misses calendars that change the absent player across dates. A uniform-equilibrium example is now known on each side of this distinction. [Exit-law characterization](../exports/FORBIDDEN_COALITIONS_AND_FIXED_TARGET_MOMENTS.md) · [Common-date argument](../exports/EVERY_FIRST_QUITTER_COALITION_CAN_BE_COMPULSORY.md)

The common-date bound also renews on arbitrary time-dependent calendars. Suppose regret at most $e_0$ guarantees a date with each of the fifteen unconditional first-exit probabilities at least $c>0$. From any restart with this guarantee, the chosen date is reached with probability at least $c$ and each of the four Continue probabilities on it is at least $c$ because a coalition omitting that player has probability at least $c$. Survival through the date is at least $\beta=c^5$. At a restart of reach $S$ the regret is at most $e/S$ by following the calendar and then switching. For $0<e\le e_0$, iteration therefore gives at least $1+\lfloor\log(e_0/e)/\log(1/\beta)\rfloor$ distinct dates on which all four players have both actions available with probability at least $c$. For each selected date, its bound in the original calendar is multiplied by the probability of reaching the corresponding restart. This bound counts physical dates, leaving open how many distinct phases in a period they occupy. [Physical first-exit bounds](../exports/EVERY_FIRST_QUITTER_COALITION_CAN_BE_COMPULSORY.md)

A November 2026 result for multiplayer stopping games uses conditional atomlessness of the publicly observed filtration to coordinate stopping. Simon, Solan and Tomkowicz identify ordinary quitting games in Section 3.5 as the case with a trivial filtration and homogeneous rewards. The only observation on a live path here is that everyone has continued. Their theorem without the filtration assumption covers three players. The four-player private-clock obligation in this map remains open. [Simon, Solan and Tomkowicz, Theorems 2.11–2.12 and Section 3.5](https://arxiv.org/html/2611.07184v1)

## The starting index is settled on the generic frontier

Every possible counterexample has a recipient Y with exactly one positive singleton comparison, paid when X quits alone. The remaining two comparisons are nonpositive, with zero allowed. At least one of the other players assigns X a strictly negative comparison. On the generic frontier one can **always choose** such X and Y so that eliminating Y's singleton indifference equation gives a three-dimensional complementarity map of degree exactly minus one. The five-variable map obtained by giving two dates to each remaining player has the same degree. This uses only the twelve off-diagonal singleton comparisons. A particular choice can give zero, so the selection matters. Since an actual counterexample would have a positive exploitability gap stable under small reward changes, the generic reduction suffices for existence. [Global selection theorem](../exports/UNIVERSAL_REDUCED_SINGLETON_DEGREE.md) · [Strict inverse column](../exports/FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md) · [Negative Hamiltonian chord](../exports/NEGATIVE_CHORD_HAMILTONIAN_UNIFORM_EQUILIBRIUM.md)

There are now two distinct uses of degree at the starting point. The reduced-index theorem selects a core from twelve singleton comparisons. A separate three-date existence proof retains the six scheduled decisions, including both core players’ best-response equations. It can therefore leave Y quiet on its scheduled date, price the associated deviation, and use the full matrix degree directly. This removes the old four-weight test from **equilibrium construction** as well as from index selection. The positive-hazard assumptions that remain concern actual rewards for quitting with other players. The new proof restricts them to explicit feasible sets of twin hazards on the two joint dates. [Six-decision existence theorem and raw tests](../exports/THREE_DATE_EQUILIBRIUM_WITHOUT_SINGLETON_WEIGHTS.md)

Selecting a negative starting index does not settle the nonlinear boundary. The earlier weight test can fail before any higher rewards are even considered. Consider
```
Γ = [0,5,9,−4; −10,0,10,8; 8,−3,0,2; −5,8,−8,0].
```
Its pair and triple determinants in lexicographic order are (50,−72,−20,30,−64,16) and (670,120,166,352); the full determinant is 9828. These determinants and the negative in each column imply R₀. At target t=(101,203,307,411), solve Γ_SS x=t_S for each pair or triple S. The minimum over the coordinates of x and the outside slacks Γ_out,S x−t_out is respectively (−530,−49871/72,−10151/10,−20881/15,−3283/8,−9419/8) and (−825193/670,−641/4,−412033/83,−119969/88). Full support gives the unique solution (479876,824066,19230,825193)/9828, with index +1. Column 2 of Γ⁻¹ is (608,440,60,685)/4914. The singleton path arcs form the chain 3→2→1→0.

Only Y=3 has a unique positive supplier, X=1. For U=0,V=2, normalizing Γ_YX gives d=(5/8,1), e=(5,−3), h=(9,8). The weight normalization 5w_U−3w_V=−1 requires w_V≥1/3, while the opposite-slot constraint requires 8w_V≤ℓ_U<5/8. This obstruction is independent of the higher rewards. The six-decision theorem gives an explicit completion of this matrix (after relabeling and normalizing the Y row) with an exact three-date equilibrium even though all of the old weights are impossible. Its exact checks exclude every stationary equilibrium and every sure opening. The four old inequalities were a genuine restriction on the earlier producer. [Three-date weight test](../exports/UNRESTRICTED_CORE_SINGLETON_ROW_THREE_DATE_EQUILIBRIUM.md) · [Singleton path arcs](../exports/GENERIC_FOUR_PLAYER_SINGLETON_PATH_CLASSIFICATION.md)

### Two joining rewards with no sign or magnitude restriction

A different table isolates the finite-hazard difficulty. Hold the benchmark's singleton matrix fixed and vary $t=J_{YU}$ and $q=J_{YV}$ independently. The entire real $(q,t)$ plane now admits a uniform-equilibrium payoff. For $-1/2\le q\le5$ an exact two-date calendar suffices for **every** $t$. At an intermediate chart parameter Y can join at both dates. As the first-date U hazard tends to zero, the product governing Y’s indifference stays finite even as $t$ tends to infinity. On the two outer ranges explicit sure openings cover every $t$. Eight other payoff entries are unused by these strategies and all relevant unilateral comparisons. Small simultaneous perturbations of the tested entries are allowed on the stated side of the tied U comparison. [Whole-plane theorem and reproducing verifier](../exports/TWO_ARBITRARY_JOINING_REWARDS_ON_SEPARATE_DATES.md)

The point $q=0,t=100$ illustrates the gain. Every sure-opening and stationary support fails at the specified table. The old three-date weighting and the two-recipient and payoff-domain tests also fail. Its exact two-date equilibrium uses support contained in $\{X,Y,U\}$ on the first date and $\{Y,V\}$ on the second. This closes the particular unbounded parameter family that the previous schedule missed. The two payoffs vary independently here while the other tested reward relationships remain part of the theorem. [Exact calibration](../exports/TWO_ARBITRARY_JOINING_REWARDS_ON_SEPARATE_DATES.md#a-calibration-without-a-stationary-equilibrium-or-sure-opening)

The identity of the necessary first quitters has its own sharp transition within this solved plane. Fix $q=0$ and own levels one. For $t\le\tau$, where $\tau=(-353281-12\sqrt{378267726})/22801\approx-25.7300$, an exact equilibrium keeps U out of the first exit. For each $t>\tau$, every sufficiently accurate profile gives U a positive lower bound on first-exit participation. At $t=100$ all four singleton first-exit probabilities are bounded below, and an exact two-date equilibrium suffices. The threshold varies real-analytically when the other 59 independent reward coordinates change locally, with the same two alternatives along the entire real $t$ axis. The two-date existence assertion already covered this plane. [Sharp threshold and deviation proof](CODEX_ROOT__SHARP_FIRST_QUITTER_PARTICIPATION_THRESHOLD.md)

### Why the generic degree cannot force an exact calendar

There is a single table that tests three proposed shortcuts together. In the nonmatching pair family take $g=6/5$, row factors $v=(3,1,1,2)$ and original own levels $s_i=1$. Its native passive rewards add the singleton entries on the exiting coalition; when the recipient joins, multiply that sum by $-v_i$. The singleton matrix is

```
Γ = [0,−2,−5,4; −6,0,−4,6; 1,3,0,−5; 1,−6/5,4,0].
```

This matrix passes the generic degree test. Its determinant is $74/5$, its triple principal determinants in lexicographic order are $(98,84/5,41,48)$, and column 2 of its inverse is $(162,275,42,190)/37$. All pair determinants are nonzero, each column has a negative outsider, and the full matrix is invertible, so it is $R_0$. At offset $(101,203,307,411)$ solving the active principal systems and imposing the outside inequalities retains only full support, of positive index. The eligible ordered cores $(X,Y)=(3,0),(3,1)$ have reduced twin determinants $-41/2,-68/3$. There is no directed Hamiltonian cycle. Only the triangle $1,2,3$ remains for the continuous singleton test. Its active zero equations force $d_1=5d_3$, $d_2=3d_3/2$ and contraction $1/3$. The starting numerator for quiet player 0 is $(-10-15/2+4)d_3<0$. Thus the constant and cycling singleton alternatives both fail. [Universal degree selection](../exports/UNIVERSAL_REDUCED_SINGLETON_DEGREE.md) · [Finite singleton path test](../exports/ALL_FOUR_PLAYER_SINGLETON_PATHS_HAVE_A_FINITE_TEST.md)

At these rewards there is no exact terminal Nash profile of any kind. For each finite period bound $N$ there is a positive regret floor for calendars of period at most $N$. Nevertheless the table **has a uniform-equilibrium payoff**. Longer calendars approximate it through the return involving players 0 and 1. The additive center and a nonempty nearby open family with strict participant security have these properties under the hypotheses of the family theorem. In particular this example does not imply a common positive floor over all $N$. It precludes an argument from the generic degree and failure of singleton paths to the existence of an exact three-date equilibrium. Any proof using the degree for arbitrary tables needs an additional exit, such as a limiting construction. [Nonmatching pair return and fixed-period obstruction](../exports/NONMATCHING_PAIR_LIMIT_RETURN_UNIFORM_EQUILIBRIUM.md)

### What genuinely needs all four players

A single open family now separates four suggested endpoints simultaneously. Every sufficiently low-regret calendar gives each of the four players a positive lower bound on the probability of quitting alone at the first exit. A simultaneous first exit also has probability bounded below. Every uniform-equilibrium payoff is a positive distance inside the four-dimensional hull of exit rewards. No exact behavioral terminal equilibrium exists. Nevertheless an explicit uniform-equilibrium payoff is attained in the limit. Its law gives mass to exactly five coalitions, the four singletons and the pair $\{1,3\}$. Thus a strategy can need all four identities across time while using at most two on any date. The additive center already had an existence producer. On the strict open family perturbations break proportionality in every row, and a proof of existence is supplied directly for these raw rewards. [Full theorem and rational certificates](../exports/ALL_FOUR_FIRST_QUITTERS_AND_UNBOUNDED_JOINT_DATES.md)

There is a corresponding general reduction on the positively protected branch. Assume positive own levels, no sure opening, a compulsory simultaneous first exit at low regret, and for each player a positive weight $u_i$ such that $Q_i(D)+u_iP_i(D)>0$ for every nonempty rival coalition $D$. If a sequence of near-equilibria has at most $K$ dates per period on which two or more players can quit, its entire limiting first-exit law is realized by an exact periodic equilibrium of at most $K$ dates. The intervening solo stretches may be arbitrarily long. On the open example, attaining terminal regret at most $\varepsilon$ requires order $\log(1/\varepsilon)$ such joint dates per period, even with a free choice of target. The explicit construction attains that order. At its specified target the minimum uniform finite-horizon threshold is of order $\log(1/\varepsilon)/\varepsilon$, allowing arbitrary behavioral profiles, including nonperiodic ones. [Bounded joint dates and sharp timing](../exports/ALL_FOUR_FIRST_QUITTERS_AND_UNBOUNDED_JOINT_DATES.md#what-boundedly-many-simultaneous-dates-imply)

The older open no-exact example already required unbounded total period. Its singleton graph has a different sign pattern. Here the lower bound counts the dates on which simultaneous moves are possible and survives unrestricted subdivision into solo dates. For global recurrence, the unrestricted finite-payoff graphs below still give an exhaustive criterion. The new reduction decides their bounded-joint-date endpoint under its hypotheses. A universal proof still has to supply recurrence when the necessary number of joint dates grows. The two exhaustive source capstones retain their separate obligations. [Older no-exact class](../exports/NONMATCHING_PAIR_LIMIT_RETURN_UNIFORM_EQUILIBRIUM.md) · [Source obligations](#existing-exhaustive-source-map-two-open-consumers)

The strict open example also forces a delay on **aperiodic calendars with the target left free**. For some $c,d>0$, every sufficiently low-regret profile has a date with unconditional probability at least $c$ of simultaneous first exit. Before it there is an interval containing at least $c\log(1/e)$ dates with two positive hazards, during which no two hazards reach $d$ on the same date. Consequently the order $\log(1/\varepsilon)/\varepsilon$ for the minimum uniform horizon on this open family holds even if the payoff target can vary.

To see this, mark dates with two hazards at least $d=k/12$, where $k$ is the collision floor. On a low-regret restart the first mark is reached with conditional probability at least $k/2$, since earlier tie probabilities sum to at most $6d$. Stop the original calendar when total hazard exceeds the oscillation of the bounded scalar cap $\lambda b$ by two, using the drift row $\lambda$ of the full theorem. This prefix exists and has survival bounded below independently of $e$ by the proper-hazard and Never bounds. Every next mark from it thus has absolute reach bounded below, and the sum of unweighted row losses to that mark is $O(e)$. Call a prefix date covered when at most $K$ joint dates intervene until its next mark, counting a mark at the current date as zero. Propagating its successor cap backwards over joints and arbitrary solo stretches as in the bounded-joint-date proof gives every covered cap a lower bound $B_K=c_0r^K$ for fixed $r>0$, $r<1$, provided $e/B_K^2$ is small. The same trimming argument then gives $\lambda P(q)\le-a+O(\ell/B_K)$ on covered dates of hazard sum $a$ and local loss $\ell$. On the remaining dates use $|\lambda P(q)|\le M a$. Summing the waiting recursions across the prefix would exceed the oscillation of $\lambda b$ unless the uncovered dates have total hazard bounded below. Taking $K=\lfloor c_1\log(1/e)\rfloor$ for small $c_1>0$ ensures $e/B_K^2\to0$. The first mark at or after any uncovered date gives the claimed interval and unconditional tied-exit mass. Its incoming survival and the finite-horizon payoff identity in the full proof give the target-free horizon bound. This argument uses strict protection on the open family. [Row drift, cap propagation and horizon identity](../exports/ALL_FOUR_FIRST_QUITTERS_AND_UNBOUNDED_JOINT_DATES.md#what-boundedly-many-simultaneous-dates-imply)

## Which exit laws remain possible

A comparison across reward tables now identifies entries one can vary while preserving a **specified** limiting law and its payoff. Fix a downward-closed collection of allowed coalitions containing the singletons. Keep each allowed coalition's payoffs and the outsider's immediate joining rewards at every allowed date with two or more active players. From a source meeting the stated security and signed-tail hypotheses, any limiting equilibrium law supported on this collection transfers to every such completion. Disjoint groups of sizes $3+1$, $2+2$, $2+1+1$ and $1+1+1+1$ leave 21, 24, 34 and 44 raw entries free, respectively. On a calibrated $2+1+1$ example, raising one free joining premium to $K$ requires order $K$ separate solo dates to carry half the specified solo mass. The theorem compares target and law under complete unilateral replacement. A general producer of the required source law is open. [Proof, completion criterion and sharp example](CODEX_ROOT__WHICH_REWARDS_DETERMINE_A_FIRST_EXIT_LAW.md)

A law attainable separately on every completion of any fixed reward entries is attainable by one common strategy sequence, with regret tending to zero uniformly over bounded sets of completions. Giving one free entry an arbitrarily negative value forces its coalition to have zero limiting mass, since its recipient can avoid that coalition. Giving all free entries a common large positive value then bounds every replacement payoff from above when those entries are lowered. Two solved games with the same twelve singleton comparisons and four own levels can have equilibrium-law sets separated by positive total variation distance. Thus letting strategies depend on all rewards still cannot guarantee one law chosen from the singleton data. [Proof and explicit completions](CODEX_ROOT__WHICH_REWARDS_DETERMINE_A_FIRST_EXIT_LAW.md#common-first-exit-laws-across-arbitrary-reward-completions)

For the explicit singleton matrix in the common-law theorem this separation already occurs on one affine line **every member of which has UE**. Start with additive passive rewards and their negatives for joining. Add the same signed bonus to every nonsingleton participant's reward. Sure openings and the earlier raw two-pair criterion cover part of the line. On the intervening positive bonus interval an exact two-date equilibrium alternates 02 and 13, with all four hazards positive. Eight rational interval calculations certify the whole interval. The zero-bonus table forces a positive total probability of joint exits, whereas that probability tends to zero uniformly over attainable laws as the bonus tends to minus infinity. [Signed line and exact checker](CODEX_ROOT__WHICH_REWARDS_DETERMINE_A_FIRST_EXIT_LAW.md#a-whole-affine-line-with-incompatible-equilibrium-laws)

On the positive-own, no-sure-opening branch with a positive sole-owner margin, one can now test a specified target payoff or the entire distribution of first quitters. At every degree, the raw table defines a convex hull and the proposed target specifies the point that must belong to it. The sixteen law coordinates include perpetual continuation. For an arbitrary list of forbidden coalitions, the same tests may use only calendars whose active players never contain one of those coalitions. Every limiting law attainable with vanishing regret and vanishing forbidden exit probability remains attainable under that stronger date-by-date restriction. In particular the support of any limiting exit law on the nonempty coalitions is downward closed. The solo case previously had a target-preserving approximation. Intermediate support families and the per-target moment equations are the additions. Existence of some target passing all degrees for every residual table is still open. [Fixed-target and forbidden-coalition theorem](../exports/FORBIDDEN_COALITIONS_AND_FIXED_TARGET_MOMENTS.md)

The top support in this classification is now realized with every one of its fifteen members compulsory on an open set without an exact equilibrium. Since the support bound holds at a single positively reached date, no scheduling of smaller joint decisions can replace that date. Compactness puts every limiting first-exit law in the interior of the fifteen-outcome probability simplex at each such table. The earlier four-identity example and the newer open family both admit uniform-equilibrium payoffs. They have different minimal requirements on first-exit supports. [Full-support construction](../exports/EVERY_FIRST_QUITTER_COALITION_CAN_BE_COMPULSORY.md)

The unconstrained first-degree test cannot refute the conjecture on the necessary nonzero-degree singleton branch. An elementary stationary averaging calculation already balances it on the singleton simplex. On a separate table with no stationary equilibrium, degree one allows a purely diffuse law, degree two forces a simultaneous move, and the existing two-pair theorem supplies an actual two-date equilibrium. This identifies the first truncation that detects the needed collision there. [Degree calibration and source comparison](CODEX_ROOT__INTRINSIC_MOMENT_DEGREE_CALIBRATION.md)

No schedule bound of three simultaneously active players can cover arbitrary four-player games. On a rational table, every vanishing-regret sequence converges at each date to the calendar with four hazards of one half. Every nonempty first-exit coalition then has probability 1/16 on date one and 1/15 over the whole play. On an open neighborhood the unique behavioral calendar and its payoff vary with the table, and two polynomial degrees suffice to identify the only feasible target and law. Earlier four-mover necessity was limited to period two. The new example itself has a stationary equilibrium and does not eliminate a class of games that lack one. [Behavioral rigidity and the quadratic test](../exports/UNIQUE_FULLY_MIXED_BEHAVIORAL_QUITTING_EQUILIBRIUM.md)

### The remaining possible supports of a limiting exit law

Assume a positive own singleton level, no sure opening at the punishment vector, and the positive sole-owner margin $\Delta$ of the [restricted-law theorem](../exports/FORBIDDEN_COALITIONS_AND_FIXED_TARGET_MOMENTS.md). Assume the twelve off-diagonal singleton comparisons are nonzero. For each fixed pair $i,j$ there is now a complete test. A sequence with vanishing regret can put asymptotically all first exits on $i,j$ exactly when $q_j=\Gamma_{ij}/J_{ij}$ and $q_i=\Gamma_{ji}/J_{ji}$ define proper positive probabilities and both outsiders prefer to wait at the resulting stationary payoff. An undefined ratio fails the test. Every such sequence then converges in its **first-exit law and payoff** to those of that row. This applies even when outsiders sometimes act along the sequence. Degree two already decides the restricted moment problem. A table with one flat comparison admits an exact alternating equilibrium where the stationary test fails on that pair. [Fixed-pair classification and sharp example](../exports/TWO_POSSIBLE_FIRST_QUITTERS_FORCE_STATIONARITY.md)

Once stationary equilibria have been excluded, every sufficiently accurate calendar must give at least three distinct players individually a positive lower bound on the probability of quitting **alone** at the first exit. The lower bound can depend on the reward table. Different players may get this probability on different dates. This distinction matters in the existing rational five-date example with two of those players scheduled together on one date and the third player scheduled alone. A full support census on the same table excludes stationary equilibria and sure openings. [Three identities with only single and pair dates](../exports/CORE_FREE_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md#6-an-exact-five-date-instance-and-full-dimensional-stability)

Here is the exhaustive count for any one limiting law in this residual. Discard the empty mask, since perpetual continuation has zero limiting mass. Let $k$ count all identities with positive singleton mass, and let $d$ be the largest coalition with positive mass. The table counts possible downward-closed support families combinatorially. The entries in parentheses identify families up to player relabeling. For $k=3$ the three names are fixed before counting.

| Identities $k$ | $d=1$ | $d=2$ | $d=3$ | $d=4$ |
| --- | ---: | ---: | ---: | ---: |
| 3 | 1 (1) | 7 (3) | 1 (1) | 0 |
| 4 | 1 (1) | 63 (10) | 49 (8) | 1 (1) |

To reproduce the count, include all $k$ singleton masks, choose any graph on them for the allowed pairs, then choose any subset of the graph's triangles for the allowed triples. A four-player mask can be included only after all four triangles have been included. Identify graphs with their selected triangles under the $k!$ permutations to get the parenthesized counts. Several families can be attained on the same table. The counts identify all possible forms to test and make no assertion of attainability for a particular reward table. The full four-identity family still allows arbitrary play. A law with no collisions is a separate case even when all four identities occur.

There is a further restriction on **boundary payoffs**. Impose generic affine position of the fifteen reward vectors, so every five are affinely independent. Every proper face of the four-dimensional exit-payoff hull then contains at most four of them. A supporting hyperplane through an attainable target contains every reward with positive limiting exit probability, because the target is the mean of that law. If such a target has a positive collision, downward closure and the three-singleton lower bound force its entire law support to be $\{\{i\},\{j\},\{k\},\{i,j\}\}$ for three distinct players. All four masses are positive, so the target is in the relative interior of the corresponding tetrahedral facet. This gives a finite boundary test using only the convex hull. If no such facet exists and all collision-free laws are excluded, every attainable target is interior. Existence of an appropriate target on arbitrary tables remains open. This restriction is sharp even when a positive probability of a collision is necessary. On a rational protected table with no stationary equilibrium and no sure opening, one exact equilibrium alternates a pair and a solo player. Its first-exit masses on $\{0\},\{1\},\{0,1\},\{3\}$ are $14/79,14/79,2/79,49/79$. Its payoff belongs to the relative interior of the indicated facet. All 3,003 five-point determinants are nonzero. The collision requirement and the facet equilibrium persist on an open set. Thus this single surviving facet type cannot be removed by appealing to genericity, a compulsory collision or failure of stationarity. [Rational facet and support checks](CODEX_ROOT__THREE_IDENTITY_BOUNDARY_FACET.md)

For the two-identity problem, there is also a complete existence test on an exceptional face of the singleton matrix. If *both* reciprocal singleton comparisons vanish and at least one of the corresponding joining premiums is nonzero, either the segment joining the two singleton rewards meets the coordinatewise own-payoff bounds, or an exact alternating calendar of two solo dates works. Failure of both finite tests excludes that pair. The first branch uses dilute stationary hazards. An explicit example needs the second branch. In the case of just one flat direction the stationary conclusion can also fail, as the fixed-pair export shows. [Tied-singleton proof and sharp example](CODEX_ROOT__TWO_TIED_SINGLETON_COMPARISONS.md)

A fixed-payoff search has a different boundary from a search for existence of *some* payoff. There is a rational table whose entire set of uniform-equilibrium payoffs is a Cantor set. It has stationary equilibria as well as equilibria indexed by infinite words on three action rows. On this single table, an explicit sequence of unattainable rational targets requires polynomial degrees at least $2n+2$ to reject the $n$th target in the fixed-target hierarchy. The Cantor-set property persists on a full-dimensional open family. This rules out a finite-degree test for **all targets on a fixed table**. It leaves open a finite cutoff for the existence question, and the example itself already answers existence positively. [Construction, unrestricted behavior proof and degree lower bound](CODEX_ROOT__CANTOR_SET_OF_UNIFORM_PAYOFFS.md)

## A finite payoff graph on the residual games

After the existing all-Continue, sure-opening and sole-owner dispositions,
the remaining games have the following exact test. At each accuracy
partition the four-dimensional continuation-payoff cube into small boxes.
An edge represents an actual finite block whose prescribed payoff starts
in the first box given the second box as continuation, up to the specified
error. The same block bounds every unilateral gain from every phase and has
a fixed positive chance of absorption by opponents after deleting any player.
The game has a uniform-equilibrium payoff exactly when the graph has a
directed cycle at every reciprocal-integer mesh. A counterexample must have
acyclic graphs at all sufficiently fine meshes.

For fixed raw rewards and mesh h, there are O(h⁻⁴) vertices. Each edge is an
independent semialgebraic problem on O(h⁻¹) dates. Equivalently, an existing
equilibrium can be approximated by periodic calendars of length O(ε⁻⁵)
that are ε-Nash after every phase. The constants and the surviving-table
hypotheses are given in the proof. Simon's earlier theorem already searches
cyclic orbits, and quantile compression already supplies finite initial-regret
tests. The additional structure gives a concrete way to attack general
existence: force cycles in these payoff graphs or certify a fine acyclic
graph for a particular residual table. The universal cycle-existence
statement is open. [Renewable blocks, period bound and payoff graph](../exports/RENEWABLE_PERIODIC_BLOCKS_AND_FINITE_PAYOFF_GRAPH.md)

## A convex test on the original payoff polytope

On the normal, positive-singleton, no-sure-opening branch, equilibrium
existence is equivalent to the following raw-table condition. At every
polynomial degree D, the convex hull of a specified list of normalized
one-step moment changes must contain zero. At positive quit rates take
exact independent one-stage Nash moves. At rate zero take directional
derivatives along singleton exits for players pinned at their own quitting
value. A single probability measure balances all the moments if and only if
every finite-degree test passes. In degree D at most binomial(D+4,4)
points are needed. All continuations can be confined to the convex hull of
the fifteen exit payoffs above all four punishment values. All action rows
there stay uniformly away from a sure quitter.

The checked rational-polynomial nonexistence theorem is the source of the
duality. Previous work already excludes low-degree potentials in the
enclosing box and balances cubic moments on a specific table. The new
test eliminates the relative tolerance and uses the intrinsic payoff
polytope with explicit zero-rate rows. One infeasible intrinsic degree on
one residual table would refute Fin4. Universal feasibility on that polytope
remains open. [Compact moment criterion](../exports/COMPACT_PAYOFF_FLUX_MOMENTS.md)

### A finite moment degree at each prescribed accuracy on all tables

Normalize the absolute value of each exit reward to at most one by a common positive scaling. Let $e_*$ be the infimum of terminal exploitability over all original behavioral profiles. For every $0<g\le1$, **every table with $e_*\ge g$ fails the enclosing-box moment test by an explicit degree $D(g)=O(g^{-2}\log(2/g))$**. Thus passing this single degree guarantees a profile with regret below $g$, with the payoff free. This works for signed own singleton rewards. Under a positive gap each player's punishment is at most its own singleton level. A finite solo prefix followed by its punishment then shows that the raw sole-owner margin $\Delta$ must be at least $g$. With a larger known lower bound $\Delta\ge\delta$, the degree improves to $O((g\delta)^{-1}\log(2/(g\delta)))$. [Proof, explicit constants and raw-game adapter](../exports/FINITE_MOMENT_DEGREE_AT_EVERY_EXPLOITABILITY_SCALE.md)

The separating polynomial can have dyadic coefficients, total encoding length $O(g^{-10}\log^5(2/g))$ bits, and a specified positive relative tolerance of order $g^2$. Given these data, a violation of the robust inequality is a real feasibility test in twelve variables. Earlier formalized results already gave a terminating search at a specified scale and a semidecision for a positive gap. The new result bounds the degree, tolerance and encoding length of the polynomial witness itself. It yields no verified pass at a new numerical scale. For example, at $g=1/10$ the conservative explicit bound is degree 605,773,732,400. A counterexample could still have an arbitrarily small positive gap as far as these estimates show. Exact existence requires a mechanism that forces passes at unbounded degrees, or a counterexample requires one verified separating certificate and the relevant sure-opening exclusions. [Earlier scale theorem](../formalized/EXACT_FIN4_SCALE_RESOLUTION_AND_COUNTEREXAMPLE_SEMIDECISION.md) · [Original polynomial characterization](../../UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean)

There is also a sharp distinction between bounding the degree and imposing a lower bound on the quit rate. On the rational four-identity example, every cutoff $\eta>0$ permits a polynomial decreasing on **all** individually rational Nash moves with total hazard at least $\eta$. The degree required is at least $\log_4(c/\eta)$ for a game-dependent $c>0$. This same game has UE. Its two infinite geometric sequences of exact rows balance the normalized polynomial increments at every degree, using only positive-rate rows, but their mean reciprocal rate is infinite. If that mean were finite, weighting by the reciprocal rate would give an invariant law per physical date and an exact terminal equilibrium. This explains why numerical searches imposing any fixed minimum quit probability can sustain a false lead even when all simultaneous moves are tested. [Physical-date equivalence and lower bound](CODEX_ROOT__PHYSICAL_DATE_MOMENTS_AND_RATE_CUTOFFS.md)

### A coupled return with two continuing payoffs equal to zero

On the protected reward domain with no sure opening, choose a pair whose members view each other's solo quits negatively and whose rewards for joining each other are positive. For any positive lower cutoff on the two observer payoffs, a six-variable fixed-point argument produces a nonblank one-date Nash row together with the continuation obtained by letting the pair bring its own two payoffs back to zero. The other two players' payoffs are clipped at the chosen floor. The input is the raw table. A sufficient condition for an equilibrium is that the observers prefer to wait on the whole pair return and the remaining cutoff error tends to zero faster than the probability of absorption.

Both remaining checks matter. On the open family requiring all fifteen outcomes, sufficiently accurate periodic play forces a positive lower bound on player 0's total hazard *outside its largest date in a period*, even when all other players may act on every date and period lengths grow. A single unrestricted date followed only by one of the eligible pairs therefore fails there. A computed branch can also pass all observer comparisons while its cutoff error remains proportional to its absorption probability. The construction is a source of candidate continuations across the protected domain. Its two outstanding comparisons are a concrete boundary for this approach. [Coupled return and unrestricted-period obstruction](CODEX_ROOT__COUPLED_PAIR_RETURN_AND_ITS_LIMIT.md) · [Earlier pair-reset comparisons](../exports/TWO_ZERO_CONTINUATION_REDUCTIONS.md)

A raw support test extends one step of the signed construction to other tables. At input $(U,V,0,0)$ with $U>0$, $V\ge0$, let $d_i(T)$ be native Wait minus Quit on the pure rival coalition $T$ at zero continuation, so $d_i(\varnothing)=0$. Assume
\[
 d_3(1),d_3(2)<0,\quad d_3(12)\le0,\qquad
 d_2(0),d_2(3)<0,\quad d_2(03)\le0,\qquad
 d_1(0)>0,\quad d_1(2),d_1(02)\ge0.
\]
Then there is a nonblank stage Nash row, and each such row has a sure quitter, support 013, or full support. To obtain a nonblank row, give players 2 and 3 a positive vanishing bonus for Quit and take a limit of finite-game equilibria. Near blank, player 0 strictly prefers Wait. Against a quiet 0, the three displayed $d_3$ signs then force the perturbed player 3 to quit surely. At a proper unperturbed row with 0 absent, player 3's Wait comparison forces both 1 and 2 absent, and player 2's comparison then forces 3 absent. With 1 absent the same argument first uses player 2's comparison and then player 3's. Both 0 and 1 must therefore participate in any proper nonblank row. If 3 were absent, the positive probability of the sole rival 0, the displayed $d_1$ signs and $V\ge0$ would make 1 strictly prefer Wait. This proves the support test. The nine-reward theorem also supplies a refusal punishment for each possible sure owner and a complete continuation for each proper output. On an arbitrary table the support test alone supplies neither. [Full construction at the specified rewards](../exports/SIGNED_CONTINUATIONS_ON_THE_TWO_PLAYER_COALITION_BLOCK.md)

## Universal native domain

The original domain consists of 60 real rewards: four recipients at each of
15 nonempty quitting coalitions. Live play and Never pay zero. Strategies
are independent complete stopping laws on natural dates plus Never; deviations
replace one owner's entire law. UE means one payoff target fixed before
accuracy, with the full uniform finite-horizon contract.

It suffices, and is necessary for the conjecture, to prove

    A_Z=inf{D_Z(P): P actual, nu(P)=0}=0

for every native table Z with Z_i({i})=0. Here U is prescribed payoff, B the
unrestricted behavioral response cap, D=sum_i(B_i-U_i), and nu the ORIGINAL
joint Never probability. The other **56 coordinates are unrestricted**.
Native AllNever itself is always Nash; A_Z>0 concerns absorbing profiles.

For any nonnegative recipient-row raise s with sigma=sum s_i>0, set
r_i(S)=Z_i(S)+s_i on every nonempty S, keeping Never zero. On the SAME profile,

    B_i^r=B_i^Z+s_i, U_i^r=U_i^Z+s_i(1-nu),
    D_r=D_Z+sigma nu.

Finite deadlines determine the cap because own singleton rewards are
nonnegative; each finite deadline absorbs surely. The reviewed repair bound
A_Z<=D_Z+14M nu^(1/4), M>=1 bounding |Z|, therefore gives

    UE(Z+s) iff A_Z=0.

Indeed A_Z=0 supplies absorbing approximations. If A_Z>0, every profile has
D_r>=min(A_Z/2,sigma(A_Z/(28M))^4)>0. The checked single-pivot normalization
produces from any signed counterexample a NEW literal counterexample with
own singleton vector e_p. Subtracting those recipient rows gives A_Z>0;
conversely Z+e_p converts any native positive gap into a counterexample.
Normalization does not transport a previously chosen source or chronology.

There is a stronger pointwise identity for **every** native table. If $F_Z(c)$ is the unrestricted infimum of total regret at signed rewards $Z-c$ (zero on perpetual play), then
$$
A_Z=A_{Z,p}=F_Z(G_{\cdot p})=\max_c F_Z(c) \quad\text{for each }p.
$$
Here $A_{Z,p}$ requires that particular player's clock to be finite. Thus it suffices to solve games where all four players get zero when a designated player quits alone. Every counterexample, centered on its **own** kernel, gives four such games with the same positive gap. The full translated payoff and cap sets also coincide with those of the prescribed finite face. One weakly nonpositive off-diagonal entry anywhere in $G$ suffices to require all four clocks finite without changing the infimum. If there is no such entry, the entrywise-positive example in the proof has absorbing infimum zero and all-four-finite infimum one. An exact continuation criterion gives further defaults and permits independent unbounded changes of the negative coordinates for the scalar comparison. The criterion can fail at the midpoint of two valid singleton defaults even for an invertible matched matrix of degree one. [Proof, signed translations and sharp examples](../exports/ZERO_SINGLETON_COLUMN_EQUIVALENCE.md)

The column identity also improves the quantitative native repair at every profile. If $D$ is its total regret and $m$ its joint probability of Never, then $A_Z\le D+C\sqrt m$, where $C$ is the maximum absolute column sum of the singleton matrix. This uses only singleton payoffs. On the 21 remaining singleton sign classes the strongest exponents supplied by individual singleton columns are $1/2$ on four, $2/3$ on seven, $3/4$ on one, and $1$ on nine. In those last nine classes sufficiently large nonnegative row raises already attain $A_Z$ exactly. Thus an arbitrarily small joint Never probability at a low-regret profile is incompatible with a fixed native absorbing gap, with stronger bounds than the older fourth-root repair. [Proof and scope of the exponent](../exports/ZERO_SINGLETON_COLUMN_EQUIVALENCE.md#a-bound-from-the-joint-probability-of-never)

The FULL anchored singleton matrix of every native A_Z>0 table is already
R0 of degree1: apply
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`)
to a restored-pivot table. Recipient-row invariance is
`quittingSingletonMatrix_sub_payoff`
(`UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`).
The accepted [strict-column/all-END reduction](../exports/FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md)
also already proves det Gamma>0 and SOME strictly positive inverse column
for the SAME native table, without perturbation. These are universal matrix
constraints, not restrictions confined to the AllNever source alternative.
The full JOINING pencil condition below still has its stated source scope.

Exact ingredients are
`exists_finFour_no_uniformPayoff_iff_exists_singlePivot`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`),
`quittingContinuationBestResponseValue_eq_finitePureReplyValue_of_solo_nonneg`
(`UniformEquilibrium/Quitting/Punishment/FinitePureReplyValue.lean`), and
`quittingFinitePureReplyValue_playerwiseAffine` and
`quittingTerminalPayoff_playerwiseAffine`
(`UniformEquilibrium/Quitting/Terminal/TerminalAffineReward.lean`).
The repair and perturbation arguments are in
[global least-Never reduction](../exports/GLOBAL_LEAST_NEVER_SOURCE_REDUCTION.md).

A_Z is 8-Lipschitz in the entrywise native reward norm. A positive gap thus
persists on an open set. For the existence problem we may avoid any specified
finite collection of proper polynomial zero sets, then select sources afresh.
Equivalently, proving A_Z=0 on a dense generic native domain covers its
boundary by continuity. This removes exceptional TABLE loci, not zero
coordinates or singular source configurations at a fixed table.

## Joint conditions on every counterexample

At a common vector of independent hazards let P_i be the native payoff
on waiting at the current date, Q_i the Quit payoff, H_i opponent
survival, and B_i=P_i-(1-H_i)Q_i. For each nonempty subset M there
must be an opening at which at least one member has P_i>0 and every
member has Q_i<P_i. The joint test can settle a game after each
individual row has failed. A different test uses a recipient with
B_a>=0 on a survival surface H_a=d. The reduced three-player degree
with a silent must then equal one; a nonpositive residual of another
recipient throughout the reduced region gives an equilibrium.

For any four strictly positive weights w, there must also be a continuous
path from zero hazards to a sure exit with q_i B_i=lambda w_i>0
for every player after the start. In particular, at every fixed joint
survival d in (0,1) the ratios must be attainable. Here nonzero weights
on *any* subset suffice for the fixed-survival statement: approximate
zero weights by positive ones and take a compact limit. Its lambda
cannot vanish, since then the nonzero limiting profile is complementary
and already gives a uniform payoff. With a single nonzero weight this
forces the other three recipients to satisfy their stationary comparisons
at the same opening. These conditions describe a stationary calculation.
The earlier additive hard example also has the positive-weight paths,
since it has local degree one and no nonzero stationary complementary
root. Its equilibrium uses alternating dates.
[Joint tests, both calibrations and path proof](../exports/JOINT_RECIPIENT_AND_REVERSE_DEGREE_UNIFORM_EQUILIBRIUM.md)
and [additive calibration](../exports/ALL_PROPORTIONAL_ADDITIVE_FOUR_PLAYER_UNIFORM_EQUILIBRIUM.md)

The positive-residual path has a quantitative restriction at every ordinary interior point when all rewards have absolute value at most one and the original exploitability infimum is at least $g>0$. Normalize $\max_i w_i=1$, and let $A$ be the joint exit probability and $A_i=1-H_i$ its analog after deleting player $i$. On $q_iB_i=\lambda w_i$, the stationary profile's full regret is $\max_i\lambda w_i/(A_i A)$ by the exact Quit and Never comparisons. Choose $j$ with largest hazard. The sole-$j$ challenger from $\Delta\ge g$ has $B_i\le-gq_j$ on the sole row. Restoring the other hazards of total $\alpha$ changes $B_i$ by at most $10\alpha$: changes of $P_i$ and $Q_i$ are each at most $4\alpha$, and changing $A_i$ costs at most $2\alpha$. Since every $B_i>0$ on the path, $\alpha\ge gq_j/10$. Thus $\min A_i=A_j\ge\alpha/3\ge gA/120$. This forces $\lambda\ge g^2A^2/120$ and $q_i\ge w_i g^2 A/480$ using $B_i\le4A_i\le4A$. Each prescribed joint-survival level must admit these quantitatively interior witness rows on any table with that gap. [Global path](../exports/JOINT_RECIPIENT_AND_REVERSE_DEGREE_UNIFORM_EQUILIBRIUM.md) · [Signed sole-owner margin](../exports/FINITE_MOMENT_DEGREE_AT_EVERY_EXPLOITABILITY_SCALE.md)

A raw reward test applies this path to large coalition payoffs. Given the singleton matrix $\Gamma$, consider $x\ge0$ with $\max x_i=1$ and $\Gamma x\ge0$. Select pairs so that the support of every such $x$ contains a selected pair. A sufficiently large positive reward for one outsider joining each selected pair forces a small stationary equilibrium on the nonzero-degree branch under the stated one-sided bounds on the other rewards. On each generic candidate singleton matrix, two pairs around a single supplier can always be chosen. There are matrices passing the degree and inverse-column tests where one pair cannot serve this purpose. The note gives the thresholds, a two-scale example with four active hazards, and the more general version for other coalition sizes. The old positive-residual path exclusion already covers these existence verdicts. [Raw criterion and sharp directional example](CODEX_ROOT__SPARSE_LARGE_COALITION_REWARDS.md)

For the entire hazard cube of a repeated calendar, the residual degree
at period m equals the m-th power of its one-date degree when the
original punishment bounds hold and genuine sure-quitter openings
are excluded. A nonzero degree then supplies sure dates with any
prescribed cyclic order of players benefiting from waiting. These
tests already follow from the stationary hypotheses at a hard table.
A periodic argument that distinguishes such a table must use more
information than this total degree.
[Period degree calculation](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md#32-why-the-degree-on-a-full-periodic-hazard-cube-adds-no-stationary-test)

### Two applications of the positive-residual path

There is an explicit four-entry sufficient test. For each singleton
quitter j, choose a different recipient i (recipients may repeat).
Suppose the four selected native pair rewards Z_i({i,j}) are at least
21M/2, where M>0 bounds the selected recipients' passive rewards above
and their participant rewards below by -M. At the point on the path
where max q=1/3, take j attaining this maximum and its recipient i.
The probability pi that j alone quits among i's opponents is at least
4/27; D_i=1-H_i is at most 19/27. Thus Q_i>=(21M/2+M)pi-M D_i>=M
and P_i<=M D_i. This contradicts B_i>0. The resulting equilibrium
class allows arbitrary signed own levels and has no upper bound on
other participant rewards or lower bound on passive rewards.

A more general sufficient test fixes the singleton matrix and marks
entries by a recipient i and a nonempty rival set T. Marking means
raising Z_i(T+i) to at least K or lowering Z_i(T) to at most -K; in
the second case require |T|>=2 to preserve the singleton data. Impose
uniform lower bounds on all participant rewards and upper bounds on all
passive rewards. Require that every v>=0 with sum v_i=1 and Gamma v>=0
have T contained in its support for at least one mark. This is a finite
linear feasibility test on the supports omitting every T. Then some
finite K suffices uniformly for all such rewards, independently of the
relative sizes of the marked entries.

Indeed at small r=sum q_i the one-sided bounds give
B_i(q)<=(Gamma q)_i+C r^2 with C uniform. The singleton contributions
to P have quadratic error, the passive mass on larger coalitions is
O(r^2), and Q_i>=-C(1-H_i). By compactness there is eta>0 such that
every normalized v with Gamma v>=-eta in each row has some marked T
with v_j>=eta for all j in T. Otherwise a converging sequence violates
the support hypothesis. Choose fixed 0<r<1 with Cr<eta. At the path
point on that shell all B_i>0, so the normalized q/r meets this test.
The exact rival coalition T has probability at least
(r eta)^|T| (1-r)^(3-|T|), and 1-H_i>=r eta. The negative passive
mark would send P_i to minus infinity with Q_i bounded below. A positive
participant mark would send Q_i to plus infinity with P_i bounded above.
Either contradicts B_i>0 when K is sufficiently large. In particular,
for every rival pair {j,k} it suffices to mark a triple joining reward
of one owner i outside that pair. At a counterexample each singleton
column has a negative entry by R0, so every v in the support test uses
at least two players. These applications use the path theorem above.

## Existing exhaustive source map: two open consumers

**One obligation suffices for the conjecture.** If any table lacks UE, an open ball of such tables admits a specifically selected source. On each table in this ball an actual coalition of at least two players has both positive first-exit probability and positive total participant premium above the minimum-debt threshold. This same coalition can be supplied to the checked source constructor. On the unedited reference, its marked exit and survival past it both have fixed positive probability. If its law mass is $p$ and the global minimum total debt is $m$, **every literal restart after the mark has debt exceeding $m+mp^2/16$** at every sufficiently large selected rank. The source enters the earlier atlas through `TailEscapeSubsequence` and the later one through `FinFourUniformEscapePacket`. The conclusion remains available on a rational reward table outside any prescribed finite list of proper algebraic exceptional sets.

The proof raises all nonempty terminal rewards in a native game by a common price. At a selected price the minimum total debt has a quadratic lower support as a function of price. At an actual joint exit, independence bounds absorption from below by the square root of the original marked mass. Conditioning on survival then raises the probability of perpetual continuation enough to force the required excess. The quantitative margin permits all 60 rewards to vary in a neighborhood. On any fixed original counterexample with a positive Never atom in at least one minimizing law, maximizing that atom over the joint minima already gives the later escape packet. The specified earlier entrance uses the stronger quantitative argument. Fin4 consequently follows from a universal consumer for the selected escape configuration. Other choices on an original table can still give minimum-return streams. The checked two-outcome theorem below continues to describe them. [One escape obligation](../exports/ONE_ESCAPE_OBLIGATION_FOR_ARBITRARY_FOUR_PLAYER_GAMES.md)

There is also one open set of **56-dimensional native tables** on which the same reduction works for *every* allocation of one unit among the four own singleton rewards, including a pure pivot. To see this, scale the center and its ball by a common positive constant and intersect with the slice where all four own levels are $1/4$. For a native table $Z$ in this slice and an allocation $s\ge0$ of total one, add $s_i$ to all of player $i$'s nonempty terminal rewards. On any actual profile with Never probability $v$, its prescribed payoff increases by $s_i(1-v)$, and its full cap increases by $s_i$. Every finite stopping deadline gains $s_i$ and the finite supremum dominates the literal Never reply before and after the change. Thus total debt is always $D_Z+v$. Cap-Nash comparisons on any fixed child shift both actions by the same amount. The same original calendars, coalition, marked dates and tail-excess bounds work through the earlier entrance for every allocation. The hard residual and the later payer witnesses can be selected on each resulting table. In particular, the outstanding proof can use rational native rewards and own levels $(1,0,0,0)$. [Debt-shift identity, equation (14)](../exports/SUPPORTWISE_LOW_OR_CHARGE_UNIFORM_EQUILIBRIUM.md) · [Escape proof](../exports/ONE_ESCAPE_OBLIGATION_FOR_ARBITRARY_FOUR_PLAYER_GAMES.md)

**What a return from the escaping tail must pay.** On the price-selected table write $D_t=D_Z+4t v$, write $m=\inf D_t$, and let $\alpha$ be the least $v$ on the compact native zero-debt set. At the selected price every minimizing sequence has the same limiting $v_*>0$. For an original reference with survival $S$ to any physical cut and literal child $C$, its accumulated stage defects sum to $L=D_t(\mathrm{ref})-S D_t(C)$. They have the same sum in native units, since $v(\mathrm{ref})=S v(C)$. A new finite prefix of any length over that very child, with survival $H$, gives joint Never $H v(C)$. If the rebuilt profiles also approach $m$, the common Never limit and $v(C)\ge v_*/2$ imply $H-S\to0$. Hence the rebuilt prefix must reproduce $L$ up to an error tending to zero. A fixed positive accumulated defect rules out returns by all words of cap-Nash rows, even as their length grows.

There are two possibilities at this same price. If $m<4t\alpha$, compactness gives a native debt tolerance $d>0$ such that every profile with $D_Z\le d$ has raised debt at least $(m+4t\alpha)/2$. Each positive-Never reference eventually has arbitrarily small native debt on all later spines, since its remaining finite hazard tends to zero and the native own rewards are zero. Every cap-Nash prefix over such a spine multiplies its native debt by its survival. The same lower bound on raised debt therefore holds for **every length** of cap-Nash word over every sufficiently late cut, and for words of sufficiently small accumulated defect. The physical cutoff can depend on the reference. The argument permits earlier return attempts at the atlas mark itself. The native AllNever-only case necessarily has $m<4t\alpha$, since AllNever fails the near-minimum cap bound on the raised table.

If $m=4t\alpha$, the native zero-debt minimizer of Never attains the raised value on the compact carrier. The common Never limit is then $v_*=\alpha$ and the references have native debt tending to zero. The prefix recursion bounds the native debt of **every** actual later spine by $D_Z(\mathrm{ref})/S$ with $S\ge v_*/2$. Thus every augmented native limit of these spines belongs to the native zero-debt set. At the first reached substantial row the parent again approaches the raised minimum. Its native caps exceed the explicit minimum-debt bound of Section 1 in the escape proof, and the vanishing native debts force every active owner to be indifferent in the limit. This produces a positively reached joint Nash row at the actual outgoing native continuation limit. Neither case constructs an equilibrium in the raised game. [Escape and cap estimate](../exports/ONE_ESCAPE_OBLIGATION_FOR_ARBITRARY_FOUR_PLAYER_GAMES.md) · [Earlier native debt transport](../exports/NATIVE_COLLISION_FLOOR_AND_GLOBAL_MASS_DICHOTOMY.md)

A fixed-child shortcut fails even if one exhausts every finite exact cap-Nash word. In an explicit solved game backward iteration from AllNever has only three continuation-cap vectors. It reaches a proper four-player row at which every coalition can be first, and its smallest raised debt over all word lengths is $(1-\kappa)^4/4>0$, with $\kappa=(3-\sqrt5)/2$. An absorbing stationary equilibrium gives unrestricted debt zero on that very table. The missing premise in applying such local evidence to the conjecture is optimality over complete original calendars. [Exact word orbit and stationary witness](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md#three-cap-states-exhaust-every-exact-backward-word-from-allnever)

The exact source-preserving Research reduction is

```text
arbitrary no-UE reward
  -> full-support hard residual and one positive-minimum law source
  -> source-preserving cofinal singleton stream
  -> stabilized forced-pair stream
       -> uniformEscape -> uniformEscape -> ...
       -> minimumReturn -> minimumReturn -> ...
```

The two old monodromy entrance tags are impossible. The remaining entrance
tags reach the common stream. The source, actual profiles, dates, laws,
literal tails and fixed mass/gain floors remain part of the packets.

| Open capstone | Exact stream property | What still needs a universal consumer |
| --- | --- | --- |
| `uniformEscape` | Literal post-date continuation debts stay at least D_*+delta for one delta>0 along the retained stream | Same-tail half-floor return selection, or absorption undercharge with AllContinue/singleton blocker, must yield UE or a valid global contradiction |
| `minimumReturn` | Those literal continuation debts converge to D_* | Normalized whole equality produces a three-role endpoint whose target may ascend or regenerate; strict whole excess gives a point whose only exact cap-Nash root is AllContinue. Neither output yet supplies global descent or UE |

The precise completion contract is already stated by
`FinFourUniformEscapeCapstone`, `FinFourMinimumReturnCapstone`, and
`finFourCompletion_of_capstones`
(`Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionAtlas.lean`).
Each capstone quantifies over EVERY reward realizing its mode. The conditional
theorem proves UE for every bounded Fin4 reward from both premises. Every
finite reward table has a bound. **Neither premise is proved.**

The stronger structural dispatch is
`uniformPayoff_or_sourcePreservingConsumedOutcome`
(`Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionConsumers.lean`).
“Consumed” here means structural information, not a completed UE proof.
A return only to D_*+delta/2 is not arbitrary-accuracy return. Convergence of
reference profiles or literal tails does not make edited whole profiles
near-minimal. Regeneration preserves specified law/source data but supplies
no renewable paid orientation.

The two modes are not asserted to give a disjoint reward-table partition:
the theorem does not identify mode choices across permitted selections.
The graph has three singleton strongly connected components, two terminal,
by its declared four-edge table. This
classifies that reduction graph, not every underlying continuation dynamic.
See the [SCC ledger](CODEX_ROOT__FIN4_SCC_PROGRESS_LEDGER.md) for its internal
cycles and [declaration inventory](CODEX_ROOT__FIN4_PRODUCER_ATLAS_DIRECTED_KNOWLEDGE.md)
for the exact producer chain.

## Native source geometry: three disjoint table branches

This is an alternative research reduction on the native positive-gap domain,
not an identification with the preceding atlas minimum. Let C be the compact
closure of ACTUAL tuples (U,B,e,N), where e is the Never response and N retains
each owner's original Never mass. Put E=C intersect{D=0}, and define

    alpha=min_E nu,
    m=min_{X in E, min_i U_i<=0} nu,
    M_m={X in E: min_i U_i<=0, nu=m},
    delta_m=min_{X in M_m} min_i U_i.

All minima are attained; AllNever supplies feasibility, and repair gives
alpha>0. Assume joining-genericity: all twelve off-diagonal entries and all
four principal triple determinants of L=J-Gamma are nonzero, where
Gamma_ij=Z_i({j}), J_ij=Z_i({i,j}), with diagonals zero.

| Disjoint branch | Forced source geometry | Status / sufficient contradiction |
| --- | --- | --- |
| `N0`: alpha=1 | E consists only of AllNever; m=1, U=0 | Open. A neighborhood good-root theorem near the nonpositive payoff boundary suffices; a good root at 0 alone does not |
| `N-`: alpha<1, delta_m<0 | Every alpha-source is strictly positive; alpha<m<1. Select an m-source with a negative coordinate; EVERY root there is proper with strictly positive successor coordinates | Open. A good root at that selected source, or a valid comparison lowering m, suffices |
| `Nb`: alpha<1, delta_m=0 | Every alpha-source is strictly positive; alpha<m<=1. Every m-source has nonnegative payoff with a zero coordinate; its only good root is AllContinue, and strict-negative all-bad annotations accumulate there | Open. Local good-root control at all nearby strict-negative annotations, or a finite-word comparison lowering m, suffices |

Two further open sets of singleton and pair rewards exclude `N0` for every completion of the 32 higher native entries. At one center, every one of the 24 tested entries can vary by $10^{-4}$. At the asymmetric center, one feasible stopping date costs strictly less than the lower bound for any source with a permitted limiting payoff. Both centers pass the earlier degree-one test along the entire joining pencil and avoid the 27 named finite-clock constructions compared in the proof. On these sets a hypothetical positive absorbing gap would have to come from a nonblank native zero-debt source. [Quadratic proof and exact calibration](../exports/QUADRATIC_COST_AND_ALLNEVER_SOURCE_EXCLUSION.md)

The coefficient of minimum regret at total finite clock mass $b$ depends only on those 24 entries, with an error bounded by a constant times $b^3$. It rules out intermediate scales between order $t$ and order $\sqrt t$ for sufficiently accurate minimizers after a small positive row shift $t$. The coefficient and its version with constrained terminal payoffs can each be approximated by a finite rational grid with error $O(1/N)$. Their equality is necessary on the AllNever-only branch. A different result excludes arbitrarily long sequences of uniformly strict simultaneous steps there, by realizing any such sequence as a genuine nonblank native equilibrium. [Grid and error proof](CODEX_ROOT__NATIVE_QUADRATIC_GRID.md) · [Aperiodic realization](CODEX_ROOT__APERIODIC_PATHS_AT_ALLNEVER.md)

A local return excludes `N0` on a nonempty open test of 21 native reward coordinates, for every independent choice of the remaining 35. At arbitrarily small positive $T$, the native zero-debt carrier contains payoff $T e_2$ and first-exit probability bounded above and below by fixed positive multiples of $T$. In a separate open set the only exact native profile is AllNever, although these nonzero limiting payoffs exist. At a proper boundary minimum in `Nb`, a Nash prefix must recruit an owner with positive payoff if the zero set has size two. With three zeros, a failure of recruitment requires a single explicitly computable three-owner root, including an outsider tie test, to account for the full index. The other boundary and return cases remain open. [Local construction and boundary recruitment proofs](CODEX_ROOT__TWO_NATIVE_SOURCE_REFINEMENTS.md)

This is genuinely disjoint even if one table has both negative and boundary
m-minimizers: the secondary minimum delta_m sends it to `N-`. Exhaustiveness
follows from the global least-Never dichotomy and delta_m<=0. The strict
inequality alpha<m follows from compact attainment: equality would give an
alpha-minimizer with a nonpositive coordinate. The alpha- and m-sources are
generally DIFFERENT points. Nearby bad annotations need not be actual payoffs.

The [negative-dual/actual-repair reduction](../exports/NONNEGATIVE_MINIMUM_SOURCE_PENCIL_REDUCTION.md)
now narrows the proper nonnegative m-sources for ARBITRARY native tables.
Their zero set T has size2 or3 and admits y>0 with y^T Gamma_T<0.
Under the existing joining genericity, every matrix Gamma_T-tJ_T,
0<=t<=1, has its own strict negative left certificate and degree0.
This principal-pencil fact is distinct from the full Gamma degree1 above.
The old solo-cover/negative-clock criterion remains a sufficient broader
source consumer on its stated raw family; the new theorem excludes the
entire semipositive proper-zero singleton-block case without that cover.

More importantly, the new degree-produced repair turns nearby positive E
points into eligible E points with STRICTLY lower ORIGINAL Never. If
eta=min_(i in T)U_i>0, the produced gain is at least eta nu/(12M).
At a proper selected source this gives a quantitative local lower bound
nu>=m/(1-eta/(12M)) for nearby positive E points. No payoff-fibre minimum
is substituted for the original m.

For the ENTIRE m<1 generic branch, put

    P_m={X in E:nu(X)<=m,U(X)>>0},
    beta=(A_Z/(14M))^4>0.

P_m is compact and, when nonempty, has ONE positive buffer
kappa_m=min_(P_m)min U>0 through level m itself. All-zero E at nu<=m is
excluded by finite two-copy renewal; proper zero limits are excluded by the
actual repair. This removes the former kappa_s->0 seam as s approaches m.
A given positive source with nu0<=m has an actual augmented-carrier Nash
head reaching either eligibility at nu=m or nu>m in at most

    1+floor(log(m/nu0)/[-log(1-kappa_m/(64M))])

retained macroscopic cuts. Replacing nu0 by beta makes the bound uniform
on P_m. The same positive sublevel is closed under auxiliary Nash prefixes
and has finite nonzero-prefix height before root inertia. These results
do not identify that carrier head with the stronger literal source data of
the two atlas capstones, produce a finite-calendar representation of E,
or consume a finite-amplitude jump above m.

Every strict-negative m-source has m<1, since nu=1 forces U=0. In `Nb`,
m<1 now has the same compact positive sublevel; m=1 retains the AllNever
endpoint degeneration. The new uniform bound does not resolve either
branch's finite-amplitude joint-return consumer. `N0` remains open too.

There is a raw security filter on these cases. If for each i some a_i>0
satisfies Z_i(T+i)+a_i Z_i(T)>=0 at every nonempty opponent coalition T,
hazard1/(1+a_i) guarantees0 against every complete opponent law. Every
actual cap and every zero-debt closure payoff is then nonnegative: `N-`
is absent on that class. With all these inequalities strict and Gamma R0,
every ACTUAL ALL-END profile with a zero cap is AllNever. Other zero-cap
ALL-END endpoints must be unattained. Two zero caps force every owner's
finite stopping probabilities before any fixed date to vanish along
realizing sequences; original Never may still be below1. The
[proof and exact boundary test](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md) include
a joining-generic strict-security table with positive inverse pivot columns:
actual exact Nash tuples converge to an unattained two-zero source with
original Never1/40. The table is already absorbing-Nash-covered. Thus the
compact-limit seam is real, while its consumption under a positive absorbing
gap remains open. These are source filters, not a new UE game class.

Here a good root q is an auxiliary Nash root with some q_i=1 or with a
successor payoff coordinate <=0. The precise source comparison and the open
neighborhood consumer are in
[payoff-domain orientation](../exports/PAYOFF_DOMAIN_ORIENTATION_UNIFORM_EQUILIBRIUM.md).
Under the further genericity in Section9 of the
[global source theorem](../exports/GLOBAL_LEAST_NEVER_SOURCE_REDUCTION.md),
`N0` requires EVERY matrix Gamma-tJ, 0<=t<=1, to be R0, standard Q and of
degree1. A crossing excludes `N0` only; passing the pencil settles no branch.

The marked actual/mixed endpoint program now has a UNIVERSAL matrix
adapter: the strict positive inverse column is already produced by the
[strict-column/all-END reduction](../exports/FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md).
That reduction also supplies one fixed positive recipient-weight box K
and t0>0 such that EVERY original SUM-debt minimum at theta_i[Z_i+t],
for theta in K and0<t<t0, has all four NATIVE END caps active and all
original Never marginals bounded away from0. Its universal all-END consumer
remains open. This is a different minimizing objective from native m.

The [compact first-joint-contact reduction](../exports/COMPACT_MINIMUM_FIRST_JOINT_CONTACT_REDUCTION.md)
now gives a common finite head for BOTH actual and nonrealized minima.
Choose a compact all-END full-SUM minimum with least ORIGINAL nu among
those minima. At this SAME source X it produces

    X=prefix(q,Y), Y in C, B(Y)=e(Y), N_i(Y)>0,
    q in[0,1)^4 with at least two positive coordinates,
    Q_i^Z(q)=B_i^Z(X)=e_i^Z(X) for some owner i.

The current finite query is paid in the ORIGINAL raised game, and the row
is the first prescribed joint stage. The source X need not have an actual
calendar. A uniformly charged deletion of tiny leading rows in actual
realizers preserves the entire SAME(U,B,e,N), then a finite affine prefix
ray forces contact by secondary original-Never minimality. The old strict
cap margins and early-collision mechanism are credited and reproduced as
needed; the new consumer is the exact compact contact ray.

The row is NOT asserted Nash, and Y is neither assumed minimizing nor
actually realized. Native Never is a maximizing response; raised literal
Never remains strictly below the raised cap. This removes actual attainment
as a prerequisite for the finite first-contact normal form, not for its
suffix or the actual-calendar Hessian arguments below. The universal
remaining target is to consume this finite paid contact with its genuine
compact suffix and the same original full-SUM objective.

The [actual minimum contact/support reduction](../exports/ACTUAL_MINIMUM_CONTACT_AND_SUPPORT_REDUCTION.md)
now supplies a complete necessary condition for ACTUAL minima of this
original full-SUM problem. Write rho=t sum theta_i. Choose ONE theta in
the old box before t and before any source. For every sufficiently small
t, an actual all-END minimum cannot have all four finite stopping supports
unbounded while its finite cap-contact dates are bounded. The proof uses
eight late hazards, an exact END-level manifold and its tangent Hessian;
it forces the identity

    (theta_i+rho s_i)Gamma_ij=(theta_j+rho s_j)Gamma_ji,
    s_i=sum_j(Gamma inverse)_ji.

One fixed price chosen in the open box makes this impossible for all small
t. This uses only Gamma invertibility, already universally available at
the SAME native table. No new raw-table genericity, joining-rank or
simultaneous-support hypothesis is needed for this exclusion.

If an original minimum is actual, a finite modification also selects a
minimum with a finite cap contact. The strict floor needed is
mu<min(theta_i)A_Z, supplied by choosing t small. Repeated finite contact-time
descent aligns the earliest contact with the first prescribed stage, which
has at least two positive own atoms. It may be reindexed to date0. Every
owner's ORIGINAL raised debt is positive. Existing four-player quadratic
cap margins and the old solo-first collision ledger are reused; the new
content is this same-table contact alignment and the support/price
obstruction. The modifications preserve each owner's bounded/unbounded
support status and the bounded/unbounded status of its contact dates.

The [compact END-contact dichotomy](../exports/COMPACT_END_SEPARATED_CONTACT_EXCLUSION.md)
removes actual attainment from the source-case partition. Avoid the singleton
zero hyperplanes, select the native table afresh, then fix its produced
cheap recipient weights before t and before any minimum. For EVERY marked
representation of an all-END global minimum, exactly one geometry remains:

| Marked source case | Necessary surviving geometry | Open consumer |
| --- | --- | --- |
| Accumulating interior contacts | Distinct native cap-query locations approach the final finite END c from below | Consume their whole-source interaction; contacts need not be prescribed actions |
| Isolated finite END | A last positive common-mixture atom has its retained interval ending at c; no owner has cofinal finite mass | Consume this last-atom source with its genuine earlier history |

The complete exclusion covers two, three or four cofinal physical owners,
including nonatomic and nonrealized clocks. One cofinal owner already forces
interior contact accumulation. Zero cofinality is exactly the isolated-END
last-atom case. Fixed bounded latent densities compile every comparison into
the SAME actual-tuple carrier, retaining all original N and old cap queries.
Two cofinal owners admit an exact timing direction; three or four are excluded
by the finite LP/two-form/Morse argument. An actual calendar is not an input.
The accepted [late-tail debt bound](../exports/GENERAL_LATE_TAIL_DEBT_AND_END_CAP_MINIMUM_REDUCTION.md),
Theorem A, already excludes a sole cofinal owner under A>0; this older
constraint is reused rather than counted as a new exclusion.

The older [native collision floor](../exports/NATIVE_COLLISION_FLOOR_AND_GLOBAL_MASS_DICHOTOMY.md)
also applies to EVERY old conditional suffix of a native E source with
positive original Never. If its total conditional finite mass beta is
nonzero and less than1/2, its pair-collision mass obeys
C>=c_A beta^2, c_A=(A/(400M))^18/16. Each such suffix therefore contains
one date with two distinct owner atoms each at least c_A beta/3.
These bursts occur cofinally as finite tail mass tends to zero, though
their owner pair may change. Purely nonatomic, singleton-only and
vanishing-relative-collision tails were already excluded by this result.
Dense shared bursts remain open. At original full-SUM raised minima its
separate dichotomy is total finite mass O(t) or a pair-macroscopic burst;
the E-only every-suffix floor is not asserted at positive native debt.

These are disjoint modes of a CHOSEN marked representation, not raw reward
classes or an actual-attainment theorem. A last positive atom does not imply
that the preceding marked history is finite or realized on natural dates. For the additional raw condition that Gamma has no
reciprocal zero pair, EVERY actual all-END local minimum with positive
original Never has a finite cap contact:
otherwise at least two owners persist and their entire singleton block
must be zero. The nongeneric contact selector above does not need that
condition. Nonrealized minima and all stated contact consumers remain open.

The [complete actual bounded-contact exclusion](../exports/ACTUAL_BOUNDED_CONTACT_EXCLUSION.md)
now rules out the ENTIRE bounded-contact case at one fixed produced price
vector. Avoid only the singleton zero hyperplanes, select the table afresh,
then choose the prices BEFORE t and before every minimum. Every ACTUAL
all-END global minimum at all sufficiently small raises has UNBOUNDED
finite cap-contact dates, regardless of its persistent-owner count.

The proof produces one common cone-KKT multiplier using late positive and
one-sided zero controls. The strict inverse column keeps every effective
price close to the chosen price and forbids reciprocal balances. With two
persistent owners an exact timing derivative forces such a balance. With
three or four, the multiplier set is a point or segment; finite LP duality
and a two-quadratic-form alternative produce a normal PSD multiplier,
contradicted by five negative directions against codimension at most4.
No2x2/3x3 minor, constant-rank or simultaneous-support hypothesis remains.
This subsumes the intermediate incidence-size and two-persistent stages;
they are not separate outstanding cases or exports.

Unbounded contacts may be unused replies, including repeated equivalent
late queries, and do not imply infinitely many prescribed atoms or UE.
The universal remaining target is still the finite paid contact with its
genuine compact suffix; actual contact sets and suffix realization are
not replaced by a convenient calendar or equilibrium.

The compact deletion identity in Section21 of the
[method note](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md) additionally excludes
one complete two-active-owner configuration. Fix the native table and theta
with 0<alpha=min_E nu<1. At all sufficiently small rho, no all-END compact
global minimum can have exactly two physically active laws, the other two
literally Never, and every outside native cap contact a payoff-kernel alias of Never. This includes bounded
physical supports, last atoms and nonrealized clocks. Four legal Never-mixing
directions produce one common contact dual; exact deletion gives F=rho N,
nu=N^2, contradicting the fixed-table alpha envelope. A surviving such two-active source therefore needs a genuinely different
outside response kernel on a positive-probability event. Equal expected
response values alone do not make kernel aliases. Those genuine outside
contacts and alpha=1 remain open; physical inactivity alone is insufficient.

The [oriented-pair dispersion theorem](../exports/ORIENTED_PAIR_UNIFORM_THREE_OWNER_DISPERSION.md)
gives a quantitative restriction under a finite raw pair test. Suppose every
off-diagonal Gamma entry is nonzero, and each unordered pair has a direction
with Gamma_ij(Gamma_ij-J_ij)>0. At A>0 there is an explicit fixed-table c>0
such that EVERY actual profile and its original augmented closure satisfy

    D+beta epsilon>=c beta^2,
    beta=sum_i(1-N_i), epsilon=f_(3)+f_(4).

Thus every nontrivial native E point has at least three finite masses each
at least c beta/2. At original raised full-SUM minima, either beta=O(t)
or the third mass is at least c beta/4. The literal fixed13 family below
satisfies every pair test at A>0, without any perturbation of its31 free
rewards. This quantitative literal statement does not follow from the older
dispersion packet's row-distinctness hypotheses. It excludes concentration
near a one-/two-owner mass face, including dispersed three-cofinal tails
whose third mass becomes negligible. It does not close a raw UE game class
or assert a common three-owner atom.

Section24 of the method note unifies this argument with the older geometric
pair proof and consumes the intervening ratio-one boundary. Write
r_i=J_ij/Gamma_ij and r_j=J_ji/Gamma_ji for a pair. The same dispersion
conclusion holds if all off-diagonal Gamma entries are nonzero and no
unordered pair has equal ratios r_i=r_j>=1. The new boundary proof uses a
macroscopic common atom followed by the ORIGINAL query x+1 and the older
unrestricted every-cut debt bound. Equal viable ratios are exceptions to
THIS dispersion mechanism, not the remaining cases of Fin4 as a whole.
The synthesis reuses the accepted compact geometric-pair lemma; it is not
a second export of that proof. Section27 tests the two outsiders on the
equal-ratio boundary. At alpha=1 a dispersion failure also requires two
strictly opposed outsider inequalities with exactly the same limiting
finite-mass ratio, and total finite mass tending to zero.

Section23 of the method note gives a finite ambient-matrix classification
of proper cofinal support S. Test the linear feasibility problem

    y>=0, supp(y) subset S, sum y=1, Gamma y>=0.

If it is infeasible, every sufficiently late OLD legal query carries a
uniform positive fraction of all remaining finite mass. The entire late
calendar is atomic with a uniform geometric tail bound, and its RESTARTED
conditional suffix has
an actual natural-date realization with full U,B,e and each conditional N
preserved. This gives no actual realization of its earlier compact history
and no minimum property to the suffix. Conversely, vanishing relative atoms
force this ambient face problem to be feasible. A positive inverse COLUMN
alone does not exclude feasibility on every proper face.

The thirteen endpoint zero faces are a conditional refinement of this
program, not thirteen additional universal reward classes. An inherited
endpoint must improve the whole head's constrained obstacle objective,
not just its own debt. The exact objective and observer constraints are
retained in the [actual-minimum note](CODEX_ROOT__ACTUAL_MINIMUM_AND_MIXED_ENDPOINT.md).

## Reward-class work queue

For each mechanism below, admit native Z when there exist a player
permutation pi, a common scale a>0, nonnegative row raises s_i, and its
permitted auxiliary parameters such that its FULL raw premise holds for
r_i(S)=a Z_{pi(i)}(pi(S))+s_i. Use that r's actual reward bound in its tests.
Each theorem concludes A=0 for the native part a pi(Z), which implies A_Z=0.
Let S5 be the union of these five admission predicates:

| Solved predicate | What it adds |
| --- | --- |
| [Supportwise Low/Charge/Orientation](../exports/SUPPORTWISE_NEGATIVE_ORIENTATION_UNIFORM_EQUILIBRIUM.md) | Independent tests on each larger support, with the stated pair and weak-boundary rules |
| [Pair–triple cancellation](../exports/PAIRED_SUPPORT_INDEX_CANCELLATION_UNIFORM_EQUILIBRIUM.md) | Eligible pair–triple bundles with DISTINCT assigned anchor pairs |
| [Shared-anchor rectangle](../exports/SHARED_ANCHOR_RECTANGLE_UNIFORM_EQUILIBRIUM.md) | Joint counting of one pair, both adjacent triples and full support under its capture/axis/edge conditions |
| [Payoff-domain orientation](../exports/PAYOFF_DOMAIN_ORIENTATION_UNIFORM_EQUILIBRIUM.md) | Weak orientation on the relevant hull or first-action neighborhoods, without a same-sign pair premise |
| [Cyclic favorite pairs](../exports/CYCLIC_FAVORITE_PAIRS_UNIFORM_EQUILIBRIUM.md) | Complete displayed family 0<=T<=1/4, using aggregate root replacement beyond those orientation adapters |

These classes overlap and do not form a single inclusion chain. For disjoint
solved cells, assign each table to the FIRST predicate it satisfies in this
order. Let R5 be the complement of S5 in the native domain. R5 is a
conservative residual, not the complement of every result in the repository.
Conditional compilers requiring an unproduced strategy, selector, return or
box do not add a raw solved predicate.

Use the participant-positive graph G_J: ij is an edge exactly when
J_ij>0 and J_ji>0. It has 64 labelled configurations and these eleven shapes:

| Graph shape | Triples with exactly one edge |
| --- | ---: |
| Empty | 0 |
| One edge | 2 |
| Two adjacent edges | 2 |
| Two disjoint edges | 4 |
| Triangle | 3 |
| Three-edge star | 0 |
| Four-vertex path | 2 |
| Four-cycle | 0 |
| Triangle with a pendant edge | 1 |
| K4 minus one edge | 0 |
| K4 | 0 |

No whole graph shape is marked solved by this table. Triple, grand-coalition
and passive rewards remain free. Refine each edge by the directed signs of
(L_ij,L_ji); retain labels or minimize the adjacency/sign string over player
permutations. This is the participant graph, not the singleton matrix graph.

On generic R5, exclude every off-diagonal J_ij=0 and L_ij=0, i!=j,
before selecting sources. Let
T_req be the triples failing ALL of Low, Charge and Orientation in the
pair–triple theorem, applied to r=Z. Let E_A be the pairs admitting its FULL
(F1)–(F3) certificate for triple A, with all permitted ordered roles and
lambda. The following FIRST-failure arms are disjoint and exhaustive:

| Arm | Definition, after all previous arms fail | Universal target |
| --- | --- | --- |
| `R_O` | Some edge has L_ij L_ji<0 | A_Z=0 throughout this residual arm |
| `R_F` | Full support fails all three Low/Charge/Orientation tests | Same |
| `R_T` | Some A in T_req has E_A empty | Same |
| `R_S` | All required triples have an eligible anchor, but two request the same pair | Same |

Why exhaustive: outside `R_O`, every positive pair has strictly positive
joining product. Outside `R_F`, full support has its independent test.
(F1) makes an eligible anchor the UNIQUE edge inside its triple, so each
required triple has at most one eligible anchor. Outside `R_T` and `R_S`,
the assignment is injective; the paired-support theorem gives A_Z=0,
contradicting membership in R5. Only two triples can contain a fixed pair.
Thus a general matching search reduces to unsupported triples or one shared
anchor. The eligibility counts above do not verify (F2)–(F3).

For literal tables add the boundary stratum where some off-diagonal J_ij or
L_ij is zero.
Either prove it directly, or prove all generic arms and invoke the established
density/continuity argument. Each arm still contains arbitrary magnitudes,
larger-coalition rewards and source geometry. These are four research targets,
not four nearly finished lemmas. They can be intersected with `N0/N-/Nb`;
no independence or nonemptiness of the intersections is asserted.

The entire `R_S` arm has a sharper restriction. If012 and023 share anchor02,
their(F1) certificates force T1=Z1(012)>0, T3=Z3(023)>0 and both directed
participant entries on01,03,12,23 nonpositive. Only the single-edge and
matching graphs remain. Full Low fails at large anchor odds and small
central odds; full Charge fails because its middle coefficient at02 is
T1+T3>0. Thus full **Orientation is the only remaining full-support gate**
on this arm. Under A_Z>0, both anchors must additionally receive positive
joining pressure from a central owner; otherwise pure anchor Quit is
absorbing Nash. The [complete proof and exact index countermodel](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md)
also show why both triple certificates plus full Orientation cannot alone
give a nonpositive joint bundle index. The single-edge shape also admits an
exact three-root all-bad boxed countermodel, with no full root, under all
these raw gates. That game too is
already hull-covered, and its bad annotation lies outside the reward hull.
Thus both shapes need actual source geometry or further global input; neither
can be closed by those raw gates alone. No entire `R_S` closure is inferred.

### Uniform equilibrium when positive Quit offers have bounded total

A new existence criterion compares two quantities at the same original table. Suppose every nonempty native exit has total reward at least $h>0$. On every nonblank product row where all active players have strictly positive immediate Quit offers, require all four to be active and the total of their offers to be at most $h$. In addition, each triple must have a player who strictly prefers joining either of the other two at their singleton exit. Then the game has a uniform-equilibrium payoff for every signed choice of its four own singleton levels. At a hypothetical positive-gap source the three losing rows would raise the sum of continuation payoffs strictly above $h$. Their first significant date could never have that sum of Quit offers. The triple condition excludes the remaining partially zero continuation. [Raw theorem and proof](../exports/UNIFORM_EQUILIBRIUM_FROM_A_BOUND_ON_POSITIVE_QUIT_OFFERS.md)

An explicit cyclic table and an open neighborhood satisfy the criterion while admitting rows at which **every** player has a positive Quit offer. The proof checks failure of the earlier product-low, weighted upper-ledger, and both payoff-domain orientation tests. At the cyclic center with unit own levels every stationary profile has regret bounded away from zero, and no opening with a sure quitter is Nash under any bounded feasible continuation. Even four identical time-dependent private clocks have a positive regret floor at this symmetric table. An equilibrium must therefore use the calendar differently for different players. [Exact table, separation and symmetry proof](../exports/UNIFORM_EQUILIBRIUM_FROM_A_BOUND_ON_POSITIVE_QUIT_OFFERS.md)

The same cyclic family gives a quantitative limit on private calendars. At fixed $L≥10^{14}$, the probability of two or more players quitting first together lies asymptotically between $10^{-4}/L$ and $3078/L$ as regret tends to zero. At $L=10^{14}$, more than sixteen billion distinct dates are necessary to carry half the first exits, and at least 1,584 dates are necessary to carry half the joint exits. For large $L$, periods up to $cL$ have a positive regret floor for some absolute $c>0$. The period bound counts positions in a repeating calendar; the date bound also applies to nonperiodic play. [Proofs and quantifiers](CODEX_ROOT__CALENDAR_COMPLEXITY_ON_THE_CYCLIC_WELFARE_FAMILY.md)

The opening can now be tested one support at a time. For a designated absorbing player, compare the realized first exit with the outcome after each losing player individually switches to Never, using the same sampled clocks. The differences give a corrected lower bound on any weighted sum of the continuation payoffs at the native minimum. Each possible set of players with positive opening hazards may use its own weights, including negative weights, and its own upper threshold. On an explicit open family, players 0, 1 and 2 can all have positive Quit offers while 3 waits, and elsewhere all four offers can be positive. Different inequalities exclude these two openings at a purported minimum, proving uniform equilibrium for every signed choice of own levels. The grand reward in all four rows can be arbitrarily negative. [Support-specific deletion theorem](../exports/UNIFORM_EQUILIBRIUM_FROM_DELETING_LOSING_CLOCKS.md)

On the generic native frontier, the same support tests suffice without the theorem’s elementary triple joining condition. Suppose the native absorbing regret infimum $A>0$. Perturb each nonsingleton participant reward down by less than $\eta$, choosing generic pair joining increments and three-player determinants. Every positive active offer on the perturbed table was positive on the original support. Every support’s upper expression changes by at most $\eta\|w\|_1$, since taking the positive part is 1-Lipschitz. The finite lower tests change by $O(\eta)$ and the new absorbing infimum is at least $A-8\eta$. The generic finite-block argument gives positive or zero caps there. The surplus for each functional in the deletion proof is at least $(A-8\eta)(\sum c_jw_j)/(\sum c_j)$, which exceeds both errors for small enough $\eta$, including for the functional excluding the zero caps. This gives the same contradiction and proves the original-table conclusion. This extension uses the earlier ordinary-mathematics finite-block proof. [Generic cap dichotomy](CODEX_SOURCE_GATE__GIFTED_CAP_POSITIVE_OR_ZERO.md) · [Deletion proof](../exports/UNIFORM_EQUILIBRIUM_FROM_DELETING_LOSING_CLOCKS.md)

### Uniform equilibrium from a pair at the positive minimum

A second sufficient condition uses two players with positive joining increments toward one another. A regular mixed one-date equilibrium at continuation zero gives positive probability of an exit. The triple sign conditions then force a hypothetical positive-gap table's least-Never equilibrium payoff to be strictly positive in every coordinate. At that particular payoff the two players can be made indifferent by choosing each other's quitting odds. If the other two prefer to wait throughout the stated payoff region, prefixing the pair strictly improves the minimum. The theorem produces a uniform-equilibrium payoff for arbitrary signed own levels. [Raw reward test and proof](../exports/UNIFORM_EQUILIBRIUM_FROM_A_PAIR_AT_THE_POSITIVE_MINIMUM.md)

The rational example falls outside the bounded-total positive-offer test above because two active owners can both receive positive Quit offers. It also escapes every stationary equilibrium, every sure opening and all three calendars alternating two fixed disjoint pairs. With own levels ten it has an explicit period-two equilibrium. Player 0 quits with probability about 0.45681 on the first date of each period. On the second, players 1, 2 and 3 quit independently with probabilities about 0.22188, 0.24501 and 0.34746. The four comparisons on dates when a player is asked to wait are strict. The sole/triple construction and the general positive-minimum proof both persist on an open neighborhood. [Period-two construction](../exports/UNIFORM_EQUILIBRIUM_FROM_A_PAIR_AT_THE_POSITIVE_MINIMUM.md#an-explicit-equilibrium-on-the-displayed-table) · [Exact arithmetic](../experiments/CODEX_ROOT__POSITIVE_PAIR_EQUILIBRIUM.py)

### A quadratic invariant that forces absorption

A third existence proof follows successive one-date Nash payoffs backwards. Its reference singleton matrix is symmetric, positive on two disjoint pairs and negative between the pairs, with strictly positive inverse. In the reference exit rule one player takes priority over its mate when both quit. The other pair cancels when both quit. A quadratic function of the continuation payoff controls every Nash row. Throughout the backward construction at least one continuation coordinate stays strictly negative. Immediate solo Quit pays zero, so each new row must have an exit probability bounded away from zero. The probability of surviving the whole block decays geometrically. Taking limits date by date gives an exact absorbing equilibrium on the centered table. A two-date punishment also yields a fixed uniform-equilibrium payoff for every signed choice of own levels on an open neighborhood. More general reward columns can be checked by a finite system of real polynomial inequalities. [Reference rule, invariant and absorbing repair](../exports/UNIFORM_EQUILIBRIUM_FROM_A_QUADRATIC_INVARIANT_ON_CONTINUATION_PAYOFFS.md)

In a subfamily, stationary profiles have a positive regret floor on the unit raise, every sure opening fails, and the singleton switch graph has no edges. One positively paid pair has joining increments of opposite signs. This violates the earlier orientation tests even in the projected reward hull, and every proper-pair test requiring two positive increments fails under all label choices. The matched pairs also fail the bounded-total positive-offer theorem's support requirement. The version in which both pairs cancel was already covered by payoff-domain orientation. The priority choice changes that comparison. On this subfamily the same exact calendar works for every signed choice of own levels. Every unilateral replacement still faces rivals who absorb, with an exponentially decaying survival bound. [Calibration and overlap tests](../exports/UNIFORM_EQUILIBRIUM_FROM_A_QUADRATIC_INVARIANT_ON_CONTINUATION_PAYOFFS.md#a-calibration-beyond-stationary-and-continuous-singleton-profiles)

For every prescribed symmetric or positively symmetrizable $R_0$ singleton matrix, including singular ones, a priority rule gives a full-dimensional neighborhood of completions with signed UE. It also admits asymmetric matrices with the stated finite quadratic test. The proof tracks singleton weights and payoff error separately, so it needs no inverse. At each symmetric reference the hostile-pair sure equilibrium is elementary. The additional conclusion is stability under independent perturbations and, under strict hostile joining comparisons, geometric absorption after any unilateral replacement. [Prescribed singleton matrices](CODEX_ROOT__PHYSICAL_DATE_MOMENTS_AND_RATE_CUTOFFS.md#a-prescribed-singleton-matrix-and-a-neighborhood-of-priority-completions)

### A specific inverse column and an equilibrium using arbitrarily long periods

Consider singleton comparisons with the following strict signs in some
labeling, with each nonzero magnitude independent.

    0 - - +
    - 0 - +
    + + 0 -
    + - + 0

Every counterexample on this pattern would require a positive determinant
and a strictly positive **player-2 column** of the inverse. At large
positive player-2 offsets, the only competing proper support is 123.
Whenever that support survives, a three-player cycle is profitable
enough to keep player 0 quiet. This settles that branch for arbitrary
coalition rewards.

On the full-support branch the two solo phases and a limiting sequence
of 01 phases give a uniform payoff under the stated pair and outsider
inequalities. This includes every singleton magnitude for the additive
tables in which joining multiplies a player's passive singleton sum by
a common negative number. The theorem also permits different row factors.
An open set of original tables in all sixty coordinates has a uniform
payoff, has no exact terminal Nash profile, and has a positive regret
gap for each fixed upper bound on the period of the live hazards.
The positive gaps may depend on the period bound. The proof realizes the
target by actual finite-period profiles as accuracy improves.
[Sign-pattern theorem and exact-equilibrium separation](../exports/NONMATCHING_PAIR_LIMIT_RETURN_UNIFORM_EQUILIBRIUM.md)

### All proportional additive four-player games

Every real hollow singleton matrix, every common factor u>0 and every vector
of signed own levels now have a uniform-equilibrium payoff when an outsider
receives its singleton sum and a quitter receives minus u times that sum
in native coordinates. There is no sign or magnitude restriction. Thus
every set of prescribed singleton rewards has such a solved completion.
The no-mutually-positive branch uses the
[interleaved feeder return](../exports/INTERLEAVED_PAIR_RETURN_WITHOUT_MUTUALLY_POSITIVE_SINGLETONS.md).
On the other sign patterns a matching calculation and elementary
exclusions leave thirteen cases. Eleven have the same specified positive
inverse column, which yields a stationary profile or a continuation return.
The other two give UE for arbitrary higher rewards. The matching test
also gives a new finite restriction at **each** of the three pairings of
any unrestricted counterexample, stated in (1) of the full theorem.
[All proportional additive games and raw matching test](../exports/ALL_PROPORTIONAL_ADDITIVE_FOUR_PLAYER_UNIFORM_EQUILIBRIUM.md)

There is a limit to transferring this class proof to other completions
of the same singleton rewards. For a row with nonzero singleton comparisons
of both signs, retaining all additive best deadlines against all absorbing
opponent calendars forces the entire normalized raw row to be additive.
Eleven comparisons suffice to bound its distance from that row in terms
of the transfer error. The comparison concerns all calendars. A proof for
selected equilibrium calendars can exploit their particular stopping laws.
[Best-reply transfer and its quantitative bound](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md#30-which-raw-rows-preserve-all-best-replies-of-an-additive-completion)

A stronger obstruction holds on an open set of singleton matrices
containing the exact period-two example above. For every fixed completion
with some positive own level there are epsilon,eta>0 for which each
epsilon-terminal Nash profile has a finite date where some player's
first opponent exit has probability at least eta. In particular, no
sequence of strategies works across every completion of those singletons.
A diffuse limit would require a continuous path of nonnegative
continuation payoffs. The signed principal-block tests leave that path
with one eventual active owner, whose column has a negative entry.
[Atom necessity and the proof excluding a common sequence](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md#31-an-open-singleton-region-where-every-near-equilibrium-needs-an-atom)

The player-2 column test also holds with unrestricted higher rewards on a
larger singleton-sign region. It requires 01 to be mutually negative,
both 0 and 1 to favor 3, 2 to disfavor 3 while 3 favors 2, and a negative
comparison on each of the pairs 02 and 12. Every counterexample there
must have positive determinant and four strictly positive entries in
column 2 of the adjugate. Each failed inequality settles the entire
corresponding set of higher rewards.
[Unrestricted-reward test, section 29](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md#29-a-named-inverse-column-for-unrestricted-higher-rewards)

### Two unrestricted recipient rows

Two recipients may have arbitrary values on all fifteen absorbing coalitions
apiece. For an ordered assignment of the other two recipients to alternating
dates, each of those rows must satisfy one polynomial implication. For the
first assigned recipient, joining must also pay at least as much as waiting
on the three nonempty subsets of the free pair. The two unrestricted players
can act on both dates. A counterexample must fail this test under every
assignment. In particular, if two proportional additive rows both value
each of the two free singleton quitters nonpositively, arbitrary signed
own levels and all thirty entries of the free rows are covered. At the
explicit hard matrix there is a nonproportional table where stationary
sequences, sure-quitter punishment heads and all three period-two schedules
with disjoint pairs fail, yet this theorem gives a uniform payoff.
[Two unrestricted recipients and the separating table](../exports/TWO_UNRESTRICTED_RECIPIENTS_UNIFORM_EQUILIBRIUM.md)

### One recipient with 45 other entries unrestricted

Write P for a player's native expected payoff on waiting at an opening,
Q for its forced Quit offer, H for opponent survival and B=P-(1-H)Q.
If one row satisfies P>0 implies Q>=P on all independent opponent
hazards, the game has a uniform-equilibrium payoff for every completion
of the other three rows. Seven coalition inequalities or seven weighted
corner inequalities are finite sufficient tests. Both can be strict
inclusion tests, as the exact examples show. The proof permits arbitrary
signed own payoffs.

A counterexample must pass **both** of the following obstructions for
**every** recipient. First, a connected component of {P>0,B>0} whose
closure reaches zero must contain a point where Q<P. Second, for every
d strictly between zero and one there must be independent opponent
hazards with H=d and B>0. In particular the seven weighted inequalities
must fail for every scalar c>=1 in all four rows. These are additional
necessary tests on the original table. The earlier two-row and cyclic
tests still apply when all four rows fail.
[One-recipient theorem and strict comparisons](../exports/ONE_RECIPIENT_JOINING_PAYOFF_UNIFORM_EQUILIBRIUM.md)

### Subdivisions of a three-player cycle with a fourth observer

For a contracting three-player singleton cycle, the three phase tests in
the linked theorem are necessary and sufficient for dividing its phases
into dates at arbitrarily small regret. The fourth player may value part
of a phase negatively. A date with a sufficiently large probability of
the scheduled player's exit can still deter that player from joining.
The bounds depend only on singleton payoffs and joining payoffs on pairs.
Every possible counterexample must fail these tests on every eligible
oriented triple. One explicit table fails every assignment in the
two-unrestricted-row test above and all four passive triple inverse
tests. Its fixed payoff is (1,2,1,1/2), and the number of dates per
cycle needed for this construction grows as log(1/epsilon).
[Cyclic triple subdivision theorem and exact example](../exports/CYCLIC_TRIPLE_PHASE_SUBDIVISION_UNIFORM_EQUILIBRIUM.md)

### A complete test for continuous singleton paths on every matrix

For every real hollow four-player singleton matrix, first test for a
nonzero homogeneous complementary vector. If that fails, a measurable
continuous singleton path exists exactly when a geometric triangle or
quadrilateral of distinct players passes the phase inequalities. A
successful test gives a fixed original uniform payoff for every completion
of the higher rewards and arbitrary signed own levels. The homogeneous
case uses the checked non-R0 theorem. The cycle case supplies the hazards,
payoffs and opponent-divergence fields of the checked singleton cycle
compiler. The proof covers zero entries, including trajectories that
move along an edge where two continuation values vanish.
[All-matrix path test](../exports/ALL_FOUR_PLAYER_SINGLETON_PATHS_HAVE_A_FINITE_TEST.md)

With no zero off-diagonal entries, sign pruning leaves at most two
triangles and one quadrilateral. Their scale equations have respective
degrees one and two, giving at most four real scale factors to test
before linear payoff feasibility. At zero entries the full polynomial
test still applies. The [rational-input checker](../experiments/FIN4_SINGLETON_PATH_DECISION.py)
reads a hollow four-by-four JSON matrix, from standard input or a file,
and emits an exact constant or cyclic witness when one exists. It uses
Python and `z3-solver`. For a case where the only eligible cycle uses
a zero comparison, run

```sh
echo '[[0,0,-4,8],[8,0,-1,-2],[-2,8,0,-1],[-1,-2,8,0]]' | python math/experiments/FIN4_SINGLETON_PATH_DECISION.py
```

The cycle is 0123, its scale is 1/16 and its first-tour masses are
(1/2,1/4,1/8,1/16). During the second phase two continuation values
are zero. Its two opposite chords are mutually negative, so no
triangle passes even the sign test.

Failure of the test excludes aperiodic measurable singleton paths as
well. With at least one positive own level, any sufficiently accurate
profile then needs a physical date with positive, uniformly bounded-below
first-exit probability. If J_ij≥0 whenever Γ_ij<0, the first exit on
such a date must have uniformly positive probability of being
simultaneous. The rowwise security condition μ_i≥s_i implies this raw
pair test in its row, by facing a sure singleton opponent j. The two
conclusions have different scopes. The six-date diamond below has an
exact solo equilibrium even though its continuous path test fails.
[Generic finite path classification](../exports/GENERIC_FOUR_PLAYER_SINGLETON_PATH_CLASSIFICATION.md)

There is a shorter sign map for the generic singleton matrix of a
possible counterexample. A directed Hamiltonian cycle is already
excluded. If neither opposite chord is mutually negative, apply the
[no-mutually-negative-pair theorem](../exports/NO_MUTUALLY_NEGATIVE_SINGLETON_PAIR_UNIFORM_EQUILIBRIUM.md).
With exactly one such chord apply the
[negative-chord theorem](../exports/NEGATIVE_CHORD_HAMILTONIAN_UNIFORM_EQUILIBRIUM.md).
With two, each row has only one positive supplier, and each supplier is
needed for the standard Q problem at any strictly positive target y.
Its solution is full, Γx=y. Hence Γ is onto and Γ inverse is
nonnegative by taking limits of positive targets along coordinate rays. Permute columns by the Hamiltonian four-cycle to place the positive suppliers on the diagonal of a matrix $A$. Its inverse is nonnegative. For $v=A^{-1}\mathbf 1$ each $v_i>0$, since its diagonal contribution must cover 1 and the off-diagonal contributions are nonpositive. Thus $A\operatorname{diag}(v)$ is strictly diagonally dominant with positive diagonal. Reducing the off-diagonal entries to zero preserves invertibility, so $\det A>0$. The four-cycle is odd and $\det\Gamma<0$. These two hypotheses together invoke the [nonnegative-inverse criterion](../../UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean).

Thus a generic candidate has an acyclic mixed-sign graph, exactly one
directed triangle, or two directed triangles sharing an arc. In the
last case the remaining two players are mutually negative. Indeed any
orientation of their pair would give a Hamiltonian cycle, while a
mutually positive pair would leave no mutually negative pair at all.
This gives the diamond topology. Every triangle present must fail its
continuous feasibility test. These alternatives concern only singleton
data. The simultaneous rewards still determine whether the game has a
uniform equilibrium.

### The 21 remaining strict singleton sign classes

Of the 4,096 ways to sign the twelve off-diagonal singleton comparisons, **435 labeled patterns in 21 classes up to relabeling** survive the matrix and continuous-path tests. Every table with a strict sign pattern outside this list has a uniform-equilibrium payoff, for arbitrary higher-coalition rewards and arbitrary signed own levels. A positive gap at a zero comparison would persist under small perturbations, so these same 21 classes suffice for the full conjecture. The earlier reciprocal-pair, normal-core and directed-cycle exclusions account for most of the count. After those filters and the positive-inverse-column test, 29 classes remain. The index at a positive inverse column eliminates seven of them. The last elimination forces a feasible triangle, including its fourth player's payoff comparisons. Two of these eight eliminations already had arbitrary-completion proofs in the [proportional-additive paper](../exports/ALL_PROPORTIONAL_ADDITIVE_FOUR_PLAYER_UNIFORM_EQUILIBRIUM.md#the-two-direct-singleton-exclusions). Each of the 21 survivors has a matrix of integers between $-4$ and $4$ that passes the positive-determinant, positive-inverse-column and degree-one tests and has no continuous singleton path. These matrices certify the limits of those specific tests. Each of the 21 matrices also has a solved completion at which every sufficiently accurate equilibrium must allow simultaneous quitting with positive probability at a single date. Existence for overlapping classes of higher-coalition completions is recorded below. [List, proof and precise matrix hypotheses](../exports/TWENTY_ONE_SINGLETON_SIGN_CLASSES_FOR_FOUR_PLAYER_QUITTING_GAMES.md) · [Exact integer and rational checker](../experiments/FIN4_SINGLETON_SIGN_CLASSES.py)

Four or more tied off-diagonal singleton comparisons, or even two in the same recipient row, suffice for UE for every choice of higher rewards. With one, two or three ties the strict-refinement screen leaves respectively 46, 39 and 10 classes up to relabeling. Each has a small integer matrix passing the degree and inverse-column tests and failing the entire continuous singleton-path test directly on the boundary. The distance to the union of the solved sign cones also gives a quantitative upper bound on unrestricted terminal regret on every original table. [Boundary counts and distance formula](../exports/TWENTY_ONE_SINGLETON_SIGN_CLASSES_FOR_FOUR_PLAYER_QUITTING_GAMES.md#games-with-tied-singleton-payoffs)

These 21 sign classes give **two reduced families**. In twenty classes one can choose a singleton column that is negative for one rival and positive for the other two. Its zero-column translation has exactly one positive own singleton, the chosen player's own reward zero, and two strictly negative own rewards. The remaining class is the positive matching with all eight crossed comparisons negative. A race among three players there gives a translated game with the same maximal gap, one positive own reward, two zero and one negative. Thus in either family just one player can gain by waiting until after every finite date in a truncated timing game instead of choosing Never. One solved example in the first family still requires all fifteen first-quitter coalitions to have positive probability on the same date. It rules out simply deleting the player whose singleton column is zero. [Two reduced families, unrestricted target sets and the example](../exports/ZERO_SINGLETON_COLUMN_EQUIVALENCE.md#two-families-with-one-positive-own-singleton)

### When a simultaneous quit is necessary

For each player assume either a nonnegative own quitting reward or a
distinct opponent whose singleton gives that player at most its own reward.
This covers all nonnegative own levels and every full-normal-core table.
A limiting payoff is achievable with regret and simultaneous first-exit
probability both tending to zero exactly when a sequence with at most one
possible quitter at every date achieves it. This includes dates that only a
deviator can reach. Hence the set of such payoffs is fixed by the four own
levels, twelve singleton comparisons and twelve joining entries. All other
32 rewards may vary together arbitrarily. A signed example gives zero
on-path collisions but solo regret at least 1/3 when a row lacks the
required blocker. [General reduction](../exports/VANISHING_COLLISIONS_AND_SOLO_CALENDARS.md)

For another full sign class the vanishing-collision problem now has a finite decision on every raw table. Partition the owners into two pairs. A solo quit must hurt both owners of the other pair in centered units, and a player must earn strictly positive centered reward when joining its own mate. The matched singleton entries may have any sign; all 32 remaining payoffs are arbitrary. A singleton interval, a nonnegative singleton nullvector, or a four-date cycle in one of just two orientations exhausts existence when some original own level is positive. If all tests fail, every sufficiently accurate profile needs a fixed positive simultaneous first-exit probability on one physical date. This last outcome leaves unrestricted UE open. [Complete tests and target sets](../exports/FINITE_TESTS_FOR_SOLO_EQUILIBRIA_AND_COMPULSORY_SIMULTANEOUS_QUITTING.md)

The same proof computes all limiting vanishing-collision payoffs in this class. Without a simplex nullvector the cyclic targets form at most eight polygons, each with at most six vertices. Some of their interiors can only be realized by nonperiodic solo play. With a simplex nullvector the cyclic limits consist of the origin and at most four triangles. Eligible singleton columns or segments must be added on the two respective branches, then the original own levels are restored. A separate graph with at most 24 vertices gives a finite test for the stated diagonally symmetrizable matrices even outside this matching sign class. [Exit masses, singular boundary and nonperiodic example](../exports/FINITE_TESTS_FOR_SOLO_EQUILIBRIA_AND_COMPULSORY_SIMULTANEOUS_QUITTING.md#computing-every-target-on-the-crossed-four-cycle)

For the directed four-cycle with singleton payoffs 3 to the mate and −1 across pairs, the earlier four-date construction already supplied the golden-ratio hazards. The converse identifies the exact dividing value $(3+\sqrt5)/2$ for joining one mate. The dividing value varies analytically in the singleton data on a neighborhood in all other 23 singleton and joining coordinates. With completed rewards bounded, increasing that entry by $\delta$ forces maximum regret plus the largest one-date collision probability to be at least a constant times $\delta$. On the positive-slope joint branch an exact equilibrium attains the same order in collisions. [Earlier sufficient schedule](../exports/FOUR_SINGLETON_PHASE_UNIFORM_EQUILIBRIUM.md) · [Exact converse](../exports/FINITE_TESTS_FOR_SOLO_EQUILIBRIA_AND_COMPULSORY_SIMULTANEOUS_QUITTING.md#a-sharp-threshold-in-twelve-independent-singleton-coordinates) · [Sharp rate](CODEX_ROOT__PHYSICAL_DATE_MOMENTS_AND_RATE_CUTOFFS.md#the-cost-in-simultaneous-exits-just-above-the-threshold)

At the point where all four mates are indifferent to joining and the four passive matched-pair rewards vanish, a local Brouwer degree of $-3$ gives an exact four-date equilibrium under every sufficiently small perturbation of the original table. The other 28 higher rewards can have arbitrary finite values at the center. Four of them can affect the neighborhood through quiet players’ triple joining offers. In one cone of perturbations the same game has three distinct equilibrium payoffs. A separate one-joint schedule reaches every value between the golden-ratio boundary and 3 for specified completions, and fails for every completion at or above 3. These are existence results on the simultaneous side; the classification of all higher completions there is open. [Joint constructions and degree](../exports/UNIFORM_EQUILIBRIUM_WHEN_PARTNERS_JOIN_A_FOUR_DATE_QUITTING_CYCLE.md) · [Exact checks](../experiments/CODEX_ROOT__FOUR_DATE_PARTNER_ENTRY.py)

On every singleton matrix with negative crossed entries and a nonnegative vector giving all four recipients strictly positive singleton payoffs, **eight higher rewards can vary independently with either sign**. In row $i$ these are $T_i$, the passive reward when the opposite pair quits, and $R_i$, the reward for joining that pair. Put $K=\max_i(|T_i|,\sqrt{|R_i|})$. Any counterexample in this crossed-sign class must satisfy

$$K\le C_G\max\left(1,\max_{(i,S)\text{ among the other 36}} |Z_i(S)|^{1/(|S|-1)}\right).$$

The positive singleton-payoff direction is necessary on a counterexample. The constants can be chosen uniformly on compact families of the indicated matrices. When the exterior criterion holds, the game has an exact stationary equilibrium with at least three hazards comparable to $1/K$. The earlier four-dimensional theorem fixed the joining rewards or bounded them by a small multiple of $K^2$. They can now set the scale and have arbitrary signs. Bounded higher rewards and competing large rewards remain possible. [Eight-reward theorem](../exports/EIGHT_SIGNED_REWARDS_ON_MATCHED_PAIRS_AND_JOINING_TRIPLES.md) · [Earlier four-passive result](../exports/STATIONARY_EQUILIBRIUM_FOR_DOMINANT_PASSIVE_MATCHED_PAIR_REWARDS.md)

For a fixed pairing these are exactly the singleton matrices with a neighborhood admitting this eight-coordinate construction. At the standard matched matrix, each of the other 36 higher rewards can individually defeat every stationary profile whose hazards tend to zero if added to the unrestricted eight. All these sharpness examples admit uniform equilibrium by weak peeling. The earlier twelve passive examples exclude stationary play at every scale. [Robust converse and all 36 examples](../exports/EIGHT_SIGNED_REWARDS_ON_MATCHED_PAIRS_AND_JOINING_TRIPLES.md) · [Every-scale passive examples](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md#four-passive-slots-are-maximal-for-the-matched-stationary-exterior-theorem)

Alternating dates for the two matched pairs give finite-reward results that allow 24 unused nonsingleton entries to vary without any size bound. Under the packet's joining inequalities the construction covers the entire plane of groupwise-constant passive rewards, a one-high-coordinate region with the other three arbitrary, and an independently unbounded negative orthant. At mate reward 3, crossed singleton reward −1 and matched participant reward 8/3, the two spectators of one pair may take independent values in $[-1/2,1/3]$ while the other two spectators receive arbitrary rewards. This last slab needs only the two corresponding triple joining caps. [Regions and exact calendars](../exports/INDEPENDENT_PASSIVE_REWARDS_ON_MATCHED_PAIRS.md)

Within the canonical cube $[-1,2/3]^4$, assume the same mate reward 3, crossed singletons −1, matched participant reward 8/3, triple caps and directed allowance $d=1/10$. An exact two-date equilibrium exists when the mean of the two passive rewards in each matched group is at most $-2/3$. An exact four- or six-date equilibrium exists when each matched group has at least one passive reward of $1/3$ or more. Together with the earlier two-observer slabs, these predicates cover at least 57.35% of this four-dimensional cube by volume. The proofs also cover the entire middle cube $[-1/2,2/3]^4$ and both loci where one group's two rewards coincide. All 24 unused higher entries remain unrestricted. The two-date mean theorem admits the explicit heterogeneous singleton and joining bounds in the proof. In this canonical family a remaining table must have unequal rewards within each group, some group with mean above $-2/3$, and a group with both rewards below $1/3$ and at least one below $-1/2$. The tied-pair argument extends to all finite passive heights for sufficiently small directed allowance depending on the table. [Regions, hypotheses and proofs](CODEX_ROOT__BOUNDED_MATCHED_PAIR_CUBE.md) · [Short-calendar checker](../experiments/SIX_DATE_MATCHED_BOX.py) · [High-observer checker](../experiments/MATCHED_PAIR_UPPER_CONE.py)

The two-date threshold on the split family $T=(-1,-1,t,t)$ occurs at $t=τ$, where $τ$ is about $-0.333198490$. Every game in a full neighborhood of that threshold has an exact periodic private equilibrium. On the side where the proper two-date solutions disappear, a return through two solo dates and a variable number of joint dates closes one periodic block. On this line its least period is asymptotic to $3.70540727/\sqrt{t-τ}$ for the selected calendars. The certified interval includes $τ\le t\le τ+10^{-11}$ and the specific value $t=-203446/610585$. The neighborhood allows independent changes to all twenty rewards used by prescribed play, one-sided changes in twelve joining comparisons, and arbitrary values of the other twenty-four native entries. The size of this neighborhood is existential. In particular, it covers some $t>τ$ outside the earlier pair-mean, tied-pair, two-observer and high-observer regions. [Fold, return and equilibrium proof](../exports/UNIFORM_EQUILIBRIUM_ACROSS_A_MATCHED_TWO_DATE_FOLD.md) · [Reproducible interval and Sturm checks](../experiments/FOLD_RETURN_CHECK.py)

At the golden-ratio four-owner boundary, a three-dimensional backward return lets a mate enter on some visits and wait on others. Its invariant set gives exact equilibrium on full neighborhoods of a mixed strip of passive rewards, allowing arbitrary finite values of the other 30 higher entries at the center. For some of these neighborhoods and a specified perturbation, arbitrarily long minimum periods occur for exact play with small simultaneous-exit probability. Shorter exact calendars with substantial collisions remain possible. [Controlled entry](../exports/CONTROLLED_PARTNER_ENTRY_ON_A_FOUR_DATE_QUITTING_CYCLE.md) · [Period separation](CODEX_ROOT__LONG_PERIODS_NEAR_A_FOUR_OWNER_ROTATION.md)

There is also an exterior theorem beyond the matching signs. At any generic singleton matrix of positive determinant with strictly positive inverse and a mutually negative pair, one can select a recipient $i$ and two rivals $a,b$ from the matrix alone. The passive reward to $i$ on $\{a,b\}$ and its own reward for joining them may then vary independently with either sign. A sufficiently large $K=\max(|Z_i(\{a,b\})|,\sqrt{|Z_i(\{i,a,b\})|})$ produces an exact stationary equilibrium when the remaining entries satisfy the indicated weighted bounds. A three-owner and a four-owner support give opposite signs at the start of two radial equations. Their highest-degree terms have the same sign, so at least one support crosses. The proof also decides exactly which signs of a single large passive entry admit stationary hazards tending to zero on any generic $R_0$ singleton matrix. The matrix criterion for a single entry can reject a small-hazard branch while other behavior remains possible. [Selected pair and triple, single-entry classification and nonmatching examples](../exports/TWO_SIGNED_REWARDS_FROM_A_SINGLETON_MATRIX.md)

#### The analytic thresholds on the remaining matching matrices

Fix the two negative crossed singleton entries in each row and positive matched joining rewards, in the notation of the matching classification. Assume some nonnegative y satisfies Gy strictly positive componentwise. All yᵢ and every matched singleton entry are strictly positive, by each row's two negative crossed contributions and zero diagonal. Multiplication by the mate permutation turns G into a matrix with positive diagonal which becomes strictly diagonally dominant by a positive column scaling using y, so G is invertible. No simplex kernel is possible. The positive-gap reduction supplies a column $G^{-1}e_t$ that is strictly positive. For sufficiently small $\epsilon>0$, $y=G^{-1}(e_t+\epsilon\mathbf1)$ remains strictly positive and gives $Gy>0$. [Strict inverse-column reduction](../exports/FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md) The 2D polygon phenomenon in the general matching theorem is absent throughout this part of the domain.

For either orientation let …,p,j,k,l,… be consecutive owners, with l the mate of j, repeated cyclically. For a switch with incumbent j set rₙ to its unconditional complete-run exit mass. The linear switch recurrence from the matching classification gives the scalar equation

    aⱼ rₙ₊₁ = mⱼ rₙ − bⱼ rₙ₋₁,
    aⱼ=−Gₗₖ>0,   bⱼ=−Gₗₚ>0,   mⱼ=Gₗⱼ>0.

Indeed the unnormalized switch payoff in row l starts at bⱼ rₙ₋₁ by the preceding contact and ends at −aⱼrₙ₊₁ by the next contact. Set uₙ=rₙ/yⱼ. This changes the recurrence to uₙ₊₁=Aⱼuₙ−Bⱼuₙ₋₁ with Aⱼ=mⱼyⱼ/(aⱼyₖ), Bⱼ=bⱼyₚ/(aⱼyₖ). Row l of Gy>0 gives Aⱼ>1+Bⱼ. In the coordinates (uₙ,uₙ−uₙ₋₁) each one-step forward transfer is therefore strictly positive, with entries Aⱼ−Bⱼ,Bⱼ in its first row and Aⱼ−Bⱼ−1,Bⱼ in its second. It expands the first coordinate by at least minⱼ(Aⱼ−Bⱼ)>1 in the nonnegative quadrant. Each reverse step has the same property in backwards difference coordinates, since its recurrence coefficients are Aⱼ/Bⱼ and 1/Bⱼ. The Perron eigenvalue of the forward four-step return is strictly greater than one. Applying the same argument to the reverse return supplies a second forward eigenvalue strictly between zero and one. These exhaust the two-dimensional spectrum, are simple and positive, and imply the stable subspace is a ray up to sign. Its positive orientation is given explicitly by the reverse return's positive Perron eigenvector. All its forward phase values uₙ stay strictly positive: every phase lies on a positive backward Perron ray, by cyclic permutation of the backward factors and their strict positivity. The solution defines a positive mass at every date and decays geometrically.

There is consequently exactly one normalized positive tour skeleton on each orientation for every such G, independently of J and of the higher rewards. To compute it take the stable eigenvector in the original r coordinates and rescale to make the full infinite sum one. The four-step multiplier and its eigenvector are real analytic throughout this open domain (normalize one mass to one before the final rescaling), since both eigenvalues are simple everywhere. Define the phase threshold θⱼ=bⱼ rₙ₋₁/rₙ, independent of the turn number. The orientation gives a cyclic equilibrium exactly when Jₚⱼ≤0, Jₖⱼ≤Gₖⱼ, Jₗⱼ≤θⱼ at all four phases, by the already proved compression and guards. The viable return cone is then precisely the stable ray. Thus the entire cyclic target part is at most eight closed segments, obtained by prepending a single initial pulse to the uniquely specified periodic child on each passing orientation. The possible pure singleton targets come from the nonempty singleton intervals as before. If both orientations and all intervals fail, collisions have a positive one-date floor, regardless of the higher completion. These thresholds depend real-analytically on all twelve singleton comparisons throughout this domain. On the matching part of the positive-gap frontier the joint-exit question therefore remains only after two explicit orientations and the four singleton intervals have failed.

On a signed diamond with each joining entry strictly between zero and its
singleton comparison, the positivity of the four coefficients L in the twin
balance equations gives a finite raw decision for this branch. A gap between
the allowable future mass ratios for U and V bounds the number of consecutive
future twin labels needed to recover the present label. This gives a finite
list of periodic words and explicit payoff tests. At rational data the
shortest exact solo period can use nine dates, with the word X,Y,U,X,Y,U,X,Y,V.
[Finite decision and calibration](../exports/FINITE_SOLO_WORDS_ON_FOUR_PLAYER_DIAMONDS.md)

The [rational diamond checker](../experiments/FIN4_DIAMOND_SOLO_DECISION.py)
implements that decision. It tests one ordered word for each candidate
reduced fraction. For every n≥1 there is an open family with shortest exact
periodic solo word of 3(n+1) distinct-owner runs and a positive regret gap
for shorter periodic solo calendars, even if their runs are subdivided.
This sharp complexity result concerns a particular strategy class.
[Ordering proof and lower-bound family](CODEX_ROOT__ORDERED_DIAMOND_WORDS_AND_UNBOUNDED_SOLO_PERIODS.md)

Another finite raw decision applies when a player has no possible outgoing
change of solo owner in the joining graph and the stated cone kernels are
trivial. A terminal single-owner test or a three-owner cycle with a finite
polygon subdivision test decides vanishing regret and collisions for
arbitrary behavioral profiles. At the signed degree-one example the
shortest permissible subdivision of a required phase grows without bound.
A successful subdivision gives an original uniform payoff for all
completions. Failure forces a positive simultaneous first-exit atom in any
sufficiently accurate profile. [Column deletion and subdivision theorem](../exports/SINK_COLUMN_AND_SIGNED_PHASE_REFINEMENT.md)

On the symmetric calibration the low-collision test requires both twin
joining factors to lie in [8/9,16/17]. At factor 99/100 every sufficiently
accurate profile needs a date with a game-dependent positive probability
of a simultaneous first quit. A raw three-date theorem applies to two possible sign patterns
on the core pair X,Y. The two twins' six outgoing singleton comparisons
can be any real numbers. The core and four directed joining tests in the
theorem allow nonlinear higher rewards. The R0, degree-one branch has an
exact three-date profile. The existing singleton-matrix disposition
handles the other branch. This includes all asymmetric singleton magnitudes
of the additive diamond, for independent k_X,k_U,k_V in [0,1] and
k_Y in [0,1/2]. The earlier symmetric proof remains available as a shorter
specialization. [Original solo and collision classification](../exports/DIAMOND_SOLO_AND_JOINT_UNIFORM_EQUILIBRIUM.md)
and [raw three-date theorem](../exports/RAW_TWO_CORE_ORIENTATIONS_UNIFORM_EQUILIBRIUM.md)

There is also a non-diamond singleton matrix with an open set of nonlinear
completions on which three dates give exact equilibrium. Every sufficiently
accurate equilibrium needs positive simultaneous first-exit probability.
Stationary profiles, sure openings, the two-unrestricted-recipient assignments
and the named orientation predicates all fail there.
[Separating example and exact checks](CODEX_ROOT__SEPARATING_TWO_CORE_CALIBRATION.md)

A further three-date theorem removes every sign restriction on the singleton payoffs to the first core player, including a zero reciprocal entry. It gives a sufficient reward-table test using four real weight variables for the two other players and a polynomial comparison of the first core player's joining and waiting offers. On the required degree-one branch the proof constructs an exact calendar. Outside that branch the checked singleton-degree disposition gives existence. Two rational examples escape stationary and sure openings, and one has positive singleton payoffs in both directions between the two other players. These are restrictions on complete reward tables; the singleton signs alone do not imply existence. [Three-date construction and exact examples](../exports/UNRESTRICTED_CORE_SINGLETON_ROW_THREE_DATE_EQUILIBRIUM.md)

A different open class has an exact two-date equilibrium with movers
02 followed by 0123. Every exact two-date equilibrium there uses all
four players on one date and at least two on the other. For sufficiently
small common positive increases to the baseline joining rewards, every
exact equilibrium requires three or more movers arbitrarily late.
The proof bounds the sum of hazards on every intervening stretch of
dates having at most two movers, regardless of its length.
The latter conclusion concerns exact profiles. A universal
constructor for the joint phases in arbitrary games remains open.
[Sharp simultaneous activity](../exports/SHARP_SIMULTANEOUS_ACTIVITY_UNIFORM_EQUILIBRIUM.md)

### Returns at the nonpositive-payoff minimum

Two raw subsets of the opposed-pair branch now have uniform-equilibrium
payoffs, including arbitrary signed own-singleton offsets. At the minimum
over continuations with a nonpositive coordinate, the first test returns
to eligibility using 02 or 23 according to the sign of player 2's payoff.
The second follows the indifference equations at 2 and 3 until 0 mixes or
can stay quiet. Both comparisons strictly lower the original Never product.
The common hypotheses fix the singleton matrix and six participant-pair
entries. The explicit higher-reward inequalities distinguish the solved
subsets. The pointwise return tests also exclude some continuations on
tables outside both subsets. For example, an actual last 023 row supporting
a positive 03 head has Never product 1/8, and a feasible 02 prefix lowers
it to 5/84. An explicit annotation with a unique 03 response shows why the
one-stage payoff guards alone leave other tables open.
[Restricted-minimum return theorem](../exports/OPPOSED_PAIR_RESTRICTED_MINIMUM_RETURN_UNIFORM_EQUILIBRIUM.md)

An actual continuation case of `R_O` has now been removed: the
[opposed-pair source exclusion](../exports/OPPOSED_PAIR_FULL_CAP_SOURCE_EXCLUSION.md)
fixes a hard singleton matrix and thirteen higher entries, leaving31 free.
It excludes an open four-payoff region from ALL full zero-debt closure
points, without assuming positive Never. Two forced genuine heads01 then03
produce an impossible third tail. An exact ray passes two compact
Nash-continuation layers but fails the third, even though one permitted
completion has only bad auxiliary roots there. The exclusion persists
locally under perturbation of all56 native coordinates.

For this table family, a zero-debt source in the sign chamber
u=(-A,-B,C,D), A,B,C,D>0, has a UNIQUE first incoming row:

    q2=0, q3=max(0,(2B-14A-7D)/44),
    q0=(B-q3)/7, q1=A+3q3.

These formulas follow from the immediate-Quit inequalities and active
equalities; a computed row outside the hazard cube excludes the source.
The open-region theorem lies in the01 branch and then forces03.
For unrestricted E sources the013 branch genuinely survives: a permitted
completion has an exact positive-Never013 Nash source. It cannot be removed
by source feasibility alone.

The stronger [negative-source dispatch](../exports/OPPOSED_PAIR_NEGATIVE_SOURCE_DISPATCH.md)
uses the SELECTED negative least-Never source under A_Z>0. Its all-bad root
condition is produced from minimality, rather than assumed at an arbitrary
continuation. It leaves exactly these two negative-source cases. The nonnegative
m-source alternatives are also excluded on this whole family by the
[finite solo/clock comparison](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md), Section11.
Thus every selected source under A_Z>0 is in one of these two chambers:

* u=(-A,-B,C,D), A,B,C,D>0, with B<6(A-D),C>5A+4AD-D. The first actual
  row is uniquely01; the initial013 branch is excluded.
* u=(-A,B,-C,D), A,B,D>0,C>=0, with A<1/4,D>5A/(1-4A),
  B>6(D-A), C<D(1-4A)-5A.

The initial zero1 face is completely excluded by a cofinal moving-date
argument. In the first case a nonlinear charged ledger keeps owner2 positive
through every01/03 pair cut and rules out infinite pair alternation.
The [whole-head triple-entry theorem](../exports/OPPOSED_PAIR_WHOLE_HEAD_TRIPLE_ENTRY.md)
consumes EVERY inherited zero1 exit: it compresses a genuine late singleton
row, varies that row and reconstructs all preceding Nash roots, strictly
lowering the ORIGINAL source's Never. It never gives a tail minimum status.
Consequently the first case must reach013 after finitely many actual cuts.
The bound of five pair cycles belongs only to the hypothetical zero1-ending
head used in that proof. The stronger
[first-triple normal form](../exports/OPPOSED_PAIR_FIRST_TRIPLE_NORMAL_FORM.md)
now classifies the ACTUAL first013: its complete history is exactly
01,013 or01,03,01,013. A negative0 entrance to013 and every longer
preceding alternating head are excluded. This follows from exact suffix
certificates without importing outer all-bad conditions to a tail.

At the genuine tail Y=(V,-E,T,F), E>F>0, if V>=E-F stationary child roots
make the explicit01 replacement's quiet2 comparison automatic under A_Z>0. The
necessary bounds are V<0 for the two-row history and V<3(E-F) for
the four-row history. In the immediate0<=V<E-F sector the original
source bounds force T>0 and one more actual013 row; a full01 replacement
then absorbs ALL three retained rows. Thus the immediate nonnegative-V
mode is completely excluded. No separate quiet2 guard or minimizing-tail
hypothesis is supplied.

The [low nonnegative four-row consumer](../exports/OPPOSED_PAIR_LOW_NONNEGATIVE_FOUR_ROW_EXCLUSION.md)
now also excludes the ENTIRE four-row sector0<=V<E-F, including V=0.
The original global budget forces positive owner2 caps through the actual
word01,03,01,013,013,03,01,013. A complete exact interval classifier then
produces the final ratio needed for a ninth actual013 row. Its full01
replacement strictly reduces Never across ALL NINE old rows, contradicting
the ORIGINAL m. Every bracket, quiet comparison, tail sign and account is
produced; no continuation inherits a minimum or an unproved recurring cone.
The1218-line proof is self-contained, and both whole independent reviews
reproduced all four printed programs, including35087 exact nodes with zero
pending or unresolved boxes. The programs regenerate their certificates;
no coefficient or interval-leaf payload is retained.

The four-row source therefore has V<0 OR E-F<=V<3(E-F). Those sectors and
the negative-V immediate history remain open. This is a complete source-mode
exclusion, not UE for the whole31-free-entry reward family.

There is also an explicit zero2 source cone removed in the
[method note](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md), Section9. In the second
chamber put k=-Z0(02),c=Z3(23). If Z2(02),Z2(23),Z2(023)<0,
k>0, (c<=D OR c<4) and4A/k<D<(62-10k)A/(3k), cofinal pure2 compression
contradicts the ORIGINAL minimum. The strict c<4 branch uses genuine-source
feasibility to protect quiet3 after cumulative compression; it does not add
c=4 unless the old c<=D condition holds. The other zero2 sources and
strict-negative2 sources remain open.

The nonnegative-source exclusion uses exact or diffuse solo comparisons
for every proper zero set, the old two-copy comparison for all-zero payoffs,
and the old expanding clock to produce a genuine negative-payoff source
with Never<1. The clock guarantees m<1 for the ORIGINAL nonpositive-payoff
minimum, rather than substituting a different minimum. The unified raw
criterion needs only a zero-set solo cover and one negative expanding clock;
it therefore applies beyond the fixed higher-entry family. It is credited
as an application of existing producers, with no new UE reward-class claim.

The old stationary mechanism additionally forces Z2(23)>-5 on every
positive-gap table in this family, because otherwise pure3 is absorbing
Nash. Earlier geometric23 boundary examples with reward-10 fail this filter.
That observation earns no extra UE-class credit.

The second chamber has an exhaustive first-row support partition. Put
alpha=-Z0(02), v=-Z2(02), w=-Z2(23), eta=Z3(23). The actual row has
q1=0,q2>0. For C>0 only these three supports remain:

| First support | Necessary active hazards | Immediate genuine-tail information |
| --- | --- | --- |
| 02 | q0=C/v,q2=A/alpha, requiring v,alpha>0 | Y2<0; sign of Y0 is the sign of5-alpha |
| 23 | q2=D/eta,q3=C/w, requiring eta>D and0<w<5 | Y2>0; sign of Y3 is the sign ofeta-4 |
| 023 | Three active Quit equations; eliminating q0,q2 leaves a quadratic in q3, with zero-polynomial cases retained | Passive1 rewards can change the sign of Y1 in one cut; no caseI buffer is inferred |

For C=0, support2 also remains. Supports02,23 require respectively
Z2(02)=0,Z2(23)=0; support023 requires all Z2(02),Z2(23),Z2(023)=0.
These literal coefficient boundaries are retained, not removed by calling
the source generic. This is an exhaustive incoming classification, not a
consumer for those three strict-negative2 modes or their zero boundaries.
Every candidate still needs the full quiet comparisons and actual E access.

For initial23, put c=Z3(23),w=-Z2(23),K=Z1(23). On0<c<4 its genuine
tail has positive2 and negative3, forcing its payoff1 to be nonpositive.
The ORIGINAL source budget then gives the new necessary inequality

    (4+6c)w<c max(6,K+4).

The entire reverse weak-inequality regime is closed; for K<=2 this includes
w>=3c/(2+3c). A separate whole-head consumer handles a zero1 return
Y=(V,0,T,-F), V>=0,T,F>0: it closes that sector if Z0(02)<=-5,
Z0(023)<=Z0(23), and w>=8c/(c+3). It varies the forced actual pure1 row
and reconstructs the original23, lowering ORIGINAL m through every stated
equality boundary. Complete proofs are in the
[method note](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md), Section13. The c=4
face, strict-negative1 reset, and other02/023 branches remain open.

The same method note's Section14 proves a precise obstruction on the
negative-V immediate branch when k=Z0(13)<=0: at the genuine tail its
current013 is the unique child Nash root, and upstream01 is more absorbing
than every competing child root. Two-layer rerooting with owner2 quiet
cannot improve original Never. This is a proof-method boundary, not an
additional game or source exclusion; a genuine tail/full-game change is
needed there.

A different full-SUM source on this SAME fixed family now has an exact
first-head producer; see Section19 of the
[method note](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md). Fix the recipient
weights before t, choose a least-original-Never full-SUM minimum, and take
any compact first-contact factorization. For every sufficiently small t,
its first row is EXACTLY(p,0,0,s), with p,s bounded positive and proper,
and both0 and3 are current cap contacts. The genuine compact tail has
B0<0 and B3>0. The proof produces a genericity-free positive alpha-source
collar from Section11, bounds both bad FIRST hazards by O(t), and removes
them exactly by a two-contact deformation with strictly positive objective
derivatives. It neither asserts N1=N2=1 nor controls later bad-owner quits.

The row is Nash in the auxiliary game whose continuation values are the
TAIL CAPS B(Y), not its prescribed payoffs U(Y). It minimizes joint survival
among ALL such cap-Nash roots over that genuine tail: every alternative
scales both the original full-SUM objective and original Never by its
Continue factor. This supplies a whole-source comparison without giving Y
a native-m minimum. The remaining task is to consume this exact first03
head through its genuine compact negative0/positive3 tail. This full-SUM
reduction does not close or replace the distinct native-m cases below.

Along t->0 this full-SUM producer selects one global-alpha source with its
genuine first03 head. Section20 of the method note consumes its ENTIRE finite
caseI later-zero1 exit, retaining every preceding row and the outermost03.
It also consumes immediate01,013 tails with V>=-a, where a is the first
triple owner0 hazard. The source suffix is not
minimizing; the comparison lowers original Never at the global-alpha source.
Longer first013 histories, remaining V<-a tails and negative-owner2 continuations
remain open for THIS approach; native-m history bounds are not transferred.

Section26 of the [method note](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md) gives
an exhaustive alternative for the selected fixed13 positive03 sources at
EVERY fixed real k=Z0(13). For all sufficiently small raises, at least one
of the following holds in each genuinely represented tail, with a positive
lower bound depending on the table and the fixed prices.

| Surviving event | Restriction |
| --- | --- |
| Strictly ordered clocks | With probability bounded below, 0 and 1 choose Never and the finite owner2 clock rings strictly before the finite owner3 clock. The first coalition is the singleton 2. |
| Joint exit involving 2 and 3 | At least one of the exact first coalitions 023 and 123 has probability bounded below. |
| Core first coalitions | Both first-exit probabilities, exactly 13 and exactly 013, are bounded below. Some date has three substantial original atoms. |

At k>=-22/5 the first two alternatives suffice. At every such selected
source, the probability of 2 stopping at or before a finite 3 is bounded
below, including ties. Section26 extends the
[positive-head barrier](../exports/OPPOSED_PAIR_POSITIVE_HEAD_FORCES_OUTSIDE_ACTIVITY.md)
by using the conditional Never payoff ranges. For smaller k, each decrease
of the potential on a protected full013 row is bounded by a constant times
the probability of first coalition 13 on that row. Before the potential
can reach zero, the clock must accumulate that probability and a definite
probability of first coalition 013. Compactness transfers the alternative
to the selected small-raise full-SUM minima via their native E limits.

The [ordered activity theorem](../exports/ORDERED_FINITE_ACTIVITY_AND_NAMED_OWNER_DISPERSION.md)
also bounds the joint order probability after EVERY old cut from original
debt and the remaining finite owner2 mass. In particular every nonempty
zero-debt suffix assigns a fixed fraction of its finite tail mass to owner3.
If owner2 is active at native E but never strictly precedes a finite owner3
draw, all finite owner2 mass is at one shared last atom. For all k the only
possible isolated last supports at native E are 023, 123 and 0123. The open
consumers include strictly ordered finite excursions, those last supports,
and the observed core collisions at k<-22/5. These are necessary events
in this family. The general Fin4 capstones are still open.

The NATIVE-m finite-history targets still include the negative-V immediate
history, the four-row sectors V<0 or E-F<=V<3(E-F), and the surviving
negative-owner2 chamber. These targets also obey forced owner2 activity
whenever their source has the stated genuine03 head at k>=-22/5.
The literal raw matrix has an entrywise strictly positive inverse, so all
proper ambient face problems above are infeasible. Every proper nonempty
cofinal tail therefore has a uniform geometric tail bound and an actual
restarted suffix;
diffuse or vanishing-relative-atom cofinal tails require all four owners.
The cofinal pair map in Section23 is exhaustive:01 and23 are impossible;
02 requires Z0(02)<-5;12 requires Z1(12)<-4;03 and13 have the stated fixed
atom-ratio bounds. Each remaining pair has a cofinal owner with NO late
finite cap contact. Therefore a literal zero-debt E source cannot have two
cofinal owners, without any perturbation of its31 free rewards. Together
with the older one-cofinal exclusion, its nonisolated END has either three
cofinal owners on an actual suffix with geometrically decaying atom tails,
or all four cofinal owners. Section23 additionally excludes the entire
cofinal012 E mode: once owner3's finite activity has ended, owner2 strictly
prefers Never at every later query if0 or1 is cofinal, because its passive
rewards on0,1,01 are1,3,4 and all its participant rewards are nonpositive.
Positive late own mass would contradict its zero debt. Thus cofinal2
requires cofinal3, and the surviving proper E triples are013,023,123.
No stationary hazard or finite-controller representation is asserted.
The oriented-pair dispersion theorem also supplies a quantitative third
mass floor on EVERY nontrivial zero-debt old suffix, using the accepted
actual-realizer conditioning argument. Hence each surviving proper E
triple has three uniformly comparable ORIGINAL terminal tails; a third
cofinal owner with vanishing relative tail mass is excluded. For all four
cofinal owners at least three tails remain macroscopic. The older collision
floor simultaneously forces cofinal pair-macroscopic bursts; it does not
turn this into a common triple collision.
Full-SUM minima may have positive native debt, so their surviving pair
modes are NOT removed by this E-only conclusion. None of these cofinal
constraints is a bound on the first013 finite-history length.

Other opposed-pair reward tables, arbitrary-source sign chambers,
nonnegative minimum sources outside this reduction's domain and both
universal capstones remain open.
No whole `R_O` or raw reward-table class is closed by these results.

The cyclic T>1/4 family is a regression test within this map, not the whole
frontier. Current source restrictions and its larger-T hull obstruction are
in the [cyclic frontier note](CODEX_ROOT__CYCLIC_TWO_MATCHING_FRONTIER.md).

## Parallel attack priorities

The following targets are alternative routes and refinements, not additional
disjoint cases to add to the counts above. A result moves the frontier only
when its complete consumer or strict coverage change is proved.

| Target | Established boundary | Next mathematical output needed |
| --- | --- | --- |
| Positive-hazard recurrence | The generic reduced index is available. Some positive-own tables on that very branch exclude every exact profile and have a positive floor at each fixed period bound, yet admit UE | Produce cycles at each accuracy with growing periods allowed, or discharge the variable-length cases by a separate source argument |
| Both source capstones | Their common pure-pair normalization is already available. A sure pair gives zero joint and deleted reach to its later tail; that tail's escape floor is not reached charge | A renewable whole-source return or contradiction, retaining the original entrance or an explicit adapter |
| Native positive-source branch | On the generic m<1 branch, P_m is compact with one kappa_m>0. Actual cofinal extraction crosses m or reaches eligibility at m in uniformly bounded macroscopic cuts; nonzero Nash-prefix chains inside P_m have finite height | Consume finite-amplitude jumps above m and compatible whole-head/tail returns; separately address the m=1 AllNever endpoint |
| Universal all-END minimum source | A strict inverse column and fixed weight box already produce all four active native END caps at EVERY small-raise original SUM minimum, with uniform original Never collar | An unrestricted all-END consumer or renewable whole-source descent; its objective cannot be replaced by native m |
| `R_S` | Only single-edge/matching graphs and full Orientation survive. Both shapes have all-bad boxed examples already solved by the hull theorem; the single-edge example has no full root | Use actual payoff/cap geometry or additional no-UE hypotheses beyond those raw gates for both shapes |
| `R_F` / `R_T` matrix test region | An explicit open singleton-matrix region passes R0/degree/Q pencil tests but has a uniform activity bound for arbitrary homogeneous switching, including unbounded phase counts and signed states when row factors stay bounded | A genuine nonlinear or finite-amplitude mechanism, or a valid actual-source budget beyond the homogeneous state space |
| `R_O` | On the studied raw family every selected source is negative. Case1 has exactly two first013 histories, whose genuine tails satisfy V<0 or V<3(E-F), with no extra quiet2 guard. The immediate nonnegative-V mode, larger zero2 cone and initial23 budget/zero1-return sectors are excluded | Consume the negative-V immediate and bounded-V four-row sectors and surviving negative-owner2 sources; core rerooting alone is insufficient on k<=0 |

The fixed-s crossing was already in Section12 of
[bounded crossing](CODEX_COORDINATOR__BOUNDED_CROSSING_SELECTION.md). The new
actual repair extends its uniform buffer THROUGH m on the generic m<1
branch; it leaves the finite-amplitude endpoint consumer open. The activity bound and shared-index obstruction
are proved in the [method-boundary note](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md).
They rule out proposed proof steps; they do not exclude those reward tables
as counterexamples. The two universal source capstones and all four full
residual-arm targets remain open.

The reciprocal shared-anchor tilt criterion is sound, but its prospective
separating families admitted mixed stationary equilibria, including the
entire last parameter strip. It is retained internally in the method note
with no new coverage credit. The opposed-source packets provide actual
configuration exclusions and a global whole-head consumer for the zero1
exit. The single-edge and strict-security countermodels sharpen proof
boundaries, with no additional UE-class credit.

The marked price normalization also fixes the scale of the missing move.
For mu_p(r)=min_{C, d_i=0(i!=p)}(d_p+r nu), compactness gives
mu_p(r)/r->alpha and selected pivot debt o(r). A gain cr therefore requires
a fixed positive Never release; an infinitesimal Never change cannot supply
it. Summability of normalized debts over dyadic prices does not provide
chronologically linked profiles. The short proof is in the method note.

## Rules for closing a case

Every task must identify its parent predicate and all quantifiers, its exact
child predicates, an exhaustiveness argument, and a semantic output. A leaf
closes with UE against all behavioral replacements and a fixed target, or
with contradiction under the positive-gap hypothesis. A negative solution
instead needs one fixed positive exploitability gap for EVERY profile.

A return or rank step is intermediate until it supplies the complete input
of its downstream consumer. Record the actual source, minimizing objective,
law, dates, Never coordinates and gain floor that the step preserves.
Changing a source requires an explicit adapter. Every recurrent component
must be consumed or have a renewable well-founded exit; renaming or local
descent does not close a cycle.

Count progress by an entire predicate newly proved, a strict enlargement with
a separating witness, or an entire source configuration excluded. Do not count
export files, parameters sampled, stationary failures or redirected nodes as
closed classes. Before claiming new raw coverage, audit the other existing
admissions as well as S5. The next broad target is a whole residual arm or a
universal source capstone, with smaller families used to test its mechanism.
