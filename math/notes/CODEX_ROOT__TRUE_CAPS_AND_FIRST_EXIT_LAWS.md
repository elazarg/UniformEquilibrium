# Finite convex tests for original first-exit laws and unrestricted response caps

Fix **any** real four-player quitting table. For each nonempty first quitting coalition \(S\) the four absorbing rewards are \(r_i(S)\). Live play and Never pay zero. Each player randomizes privately. Write \(p(\pi)\) for the entire probability vector on the fifteen nonempty coalitions and Never, and \(B_i(\pi)\) for the supremum under complete unilateral replacement of player \(i\)'s first-quit law, including Never. Prescribed payoffs are \(r_i\cdot p(\pi)\), using zero for the Never coefficient. Choose \(M\ge1\) bounding all absolute rewards, and write \(s_i=r_i(\{i\})\). Let \(\mu_i=\inf_{\pi_{-i}}B_i(\pi_{-i})\). Each \(\mu_i\) has the stationary-punishment formula: infimize \(\max(Q_i,P_i/(1-H_i))\) on constant rival hazards with rival survival \(H_i<1\), also considering \(\max(0,s_i)\) for all rivals continuing. Here \(Q_i\) is the immediate Quit offer and \(P_i\) the expected passive reward on a rival exit on this date. In particular the data are algebraic for algebraic input. [Stationary punishment value](../../UniformEquilibrium/Quitting/Stationary/MinMax.lean)

For a probability vector \(p\) and a cap bound \(b\in[-M,M]^4\), call \((p,b)\) attainable if there are original profiles \(\pi_n\) with \(p(\pi_n)\to p\) and \(\limsup_n B_i(\pi_n)\le b_i\) for each player. The set is closed. The following criterion includes defective individual stopping laws, sure openings, signed own rewards, and arbitrary nonzero debts. In particular it tests a specified complete first-exit law at *every specified vector* of regret allowances.

## The raw compact set

A state \(x=(p,b)\) belongs to the compact set \(X\) given by \(p\) in the sixteen-coordinate probability simplex and \(\max(\mu_i,r_i\cdot p)\le b_i\le M\). The seed is \(o=(\delta_{\rm Never},(\max(0,s_i))_i)\), the state of literal AllNever. An edge from a child \(x\) to a parent \(x'=(p',b')\) uses hazards \(q\in[0,1]^4\). Write \(a=\sum_iq_i\), \(c=\prod_i(1-q_i)\), and \(e_S(q)\) for the product probability of exactly the nonempty coalition \(S\); set \(e_{\rm Never}=0\). Require \(x,x'\in X\) and
\[
 p'=c p+e(q),\qquad b'_i\ge Q_i(q),\qquad b'_i\ge P_i(q)+H_i(q)b_i,
 \qquad H_i=\prod_{j\ne i}(1-q_j).
\]
These are upper bounds throughout. In particular the trial cap can rise at a blank row. Set
\[
 l=(1+8M)a+\sum_i(b'_i-b_i).
\]
Every term \(b'_i-b_i\ge-2Ma\), hence \(l\ge a\). Moreover \(\|x'-x\|_\infty\le (1+6M)l\): negative cap increments are bounded by \(2Ma\), positive ones by \(l+6Ma\), and law increments by \(a\). Form the closure \(E\) of the tuples \((x,x',q,l,d)\) from the displayed edges with \(l>0\) and \(d=(x'-x)/l\). It is compact semialgebraic; taking the closure includes real secant directions, rather than independently guessing tangent constraints.

For a polynomial \(P\) in the state coordinates put
\[
 T_P=P(x')+[P(x')-P(x)]/l.
\]
The bracketed quotient is its polynomial extension along \(x'=x+ld\). At \(l=0\) it is \(\nabla P(x)\cdot d\). In particular \(T_1=1\).

**Theorem.** An individual target \(y\in X\) is attainable if and only if a finite positive measure \(\rho\) on \(E\) and \(h\ge0\) satisfy
\[
                  P(y)=hP(o)+\int T_P\,d\rho                  \tag{1}
\]
for every polynomial \(P\). Here \(h+\rho(E)=1\). Equivalently, at every finite degree the vector of monomials at the *specified* \(y\) belongs to the compact convex hull of their vectors at \(o\) and their \(T\)-vectors on \(E\). A single rejected degree excludes this law with these cap allowances.

A second, genuinely linear optimization uses a probability \(\Lambda\) on \(X\) in place of the point \(y\), integrating the left-hand side of (1). The possible endpoint measures are **exactly** the probabilities supported on attainable states. Consequently for any compact semialgebraic target set \(K\subseteq X\) one can restrict \(\Lambda\) to \(K\) and minimize a linear objective in its moments. For example at \(K=X\), the minimum of \(\int\sum_i (b_i-r_i\cdot p)\,d\Lambda\) is precisely the infimum of true total debt over all independent profiles. The finite-degree minima increase to this number. Above any trial strict lower bound below the true minimum some finite degree certifies it. A positive certificate at one degree for one game would disprove Fin4. The same optimization with any strictly positive row weights exposes the true cap-and-law minima: a strict cap slack on such a minimum would contradict optimality. In particular one can optimize a second law coordinate, such as Never probability, on the minimizing slice once its value has been specified.

At any finite degree each endpoint or edge moment vector belongs to a compact convex hull of an explicit semialgebraic image. Carathéodory uses at most one more atom than its ambient dimension. Finite problems therefore reduce to first-order real arithmetic on the fixed input and specified target data. Feasibility at all degrees gives the measures in (1) by nested weak compactness. No uniform degree cutoff is asserted.

## From private profiles to the moment equations

Each actual calendar can be approximated in its four first-quit laws by moving all finite mass beyond a cutoff to Never. This changes each marginal by a quantity tending to zero in total variation. Coupling gives uniform convergence of prescribed laws and of all replacement offers, including arbitrarily late deadlines and Never. A finite calendar is exactly a word over \(o\); the actual full cap at each date is the maximum of the two displayed action offers at its child cap. To realize an upper allowance at the outermost row of a word, one may increase that row's cap coordinates within \(X\). An empty word may first be padded with one blank over \(o\). Thus every attainable state is a limit of endpoints of these finite words.

In physical order along a word, the outermost edge comes first. Start with weight one, put the fraction \(l/(1+l)\) of the remaining weight on the edge, and carry the fraction \(1/(1+l)\) to the child. At a zero-charge edge the states coincide. At any positive charge, multiplying \(T_P\) by \(l/(1+l)\) gives \(P(x')-P(x)/(1+l)\). Telescoping yields (1) with the remaining weight at \(o\). Compactness proves necessity and also permits arbitrary probabilities on attainable endpoints by convex mixtures and limits.

## Recovering actual paths without a public lottery

For \(0<\varepsilon<1\) use a compact enlarged state box with each probability coordinate in \([-2,3]\), each cap in \([-M-2,M+2]\), and \(b_i\ge\mu_i-\varepsilon\). Allow an edge with its same formula for \(l\), \(a\le l\le 4(1+8M)+8M\), and
\[
 \|p'-cp-e(q)\|_\infty\le\varepsilon l,\quad
 b'_i\ge Q_i(q)-\varepsilon l,\quad
 b'_i\ge P_i(q)+H_i b_i-\varepsilon l .
\]
These inequalities impose no Nash assumption. For any interval of such a path the total charge obeys
\[
 (1+8M)\sum a-8(M+2)\ \le\ \sum l\ \le\ (1+8M)\sum a+8(M+2).
                                                               \tag{2}
\]

Fix a target \(y\). Suppose that, for every sufficiently small tolerance and radii of balls about \(o,y\), paths in this relation with outer endpoint in the target ball either reach the seed ball at their inner endpoint or have unbounded available total charge. Then \(y\) is attainable. The quantifiers here allow either alternative at each tolerance and pair of radii. To prove the assertion fix a large \(T\), select tolerance and radii at most \(T^{-3}\), and choose either such a path to the seed or a path with total hazard at least \(T\). In the former case, if its total hazard is below \(T\), use the entire word over literal AllNever. The discrepancy in the law is at most its seed error plus \(\varepsilon\sum l\), and the true caps are at most the outer trial caps plus that same bound. This is finite induction using the exact law recursion and monotonicity of the two cap actions; each update has slope at most one.

In any path whose total hazard reaches \(T\), retain the shortest *physical prefix* with total hazard at least \(T\). Its charge is at most \((1+8M)(T+4)+8(M+2)\). Choose the owner \(k\) whose total hazard is largest on this prefix; it is at least \(T/4\). At the cut attach an actual tail with cap for \(k\) at most \(\mu_k+\varepsilon\), using the definition of the punishment value and choosing any prescribed strategy for \(k\) there. The inner trial cap for \(k\) is at least \(\mu_k-\varepsilon\), so its terminal discrepancy in the harmful direction is at most \(2\varepsilon\). Every other owner's rival survival on the retained prefix is at most \(e^{-T/4}\), as is the joint survival. A cap discrepancy at a child passes to the parent with factor at most \(H_i\) in its positive part, by the two displayed inequalities. The law discrepancy passes with factor \(c\). Thus the remaining endpoint law error and the harmful cap errors are bounded by \(2\varepsilon+C_M e^{-T/4}+\varepsilon\sum l\), for a fixed box bound \(C_M\). Taking \(T\to\infty\) produces the actual target law and the four claimed upper caps. This argument chooses one actual tail per profile and controls complete replacement against those same rival strategies.

It remains to derive the path alternative from (1), also for diffuse edges and mixed endpoint measures. If \(y\) is unattainable, the implication just proved gives a tolerance and positive radii where every path with outer endpoint in its target ball has bounded total charge and no such path reaches its seed ball. Define \(V(v)\) on the enlarged state box by taking, over finite paths with outer endpoint \(v\) and inner endpoint \(z\), the infimum of
\[
 k(z)\prod_{\rm edges}(1+l)^{-1},\qquad
 k(z)=\min(1,2\|z-o\|_\infty/r),
\]
where \(r\) is the excluded seed-ball radius. Modify \(k\) to vanish on \(\|z-o\|_\infty\le r/2\) and equal one on \(\|z-o\|_\infty\ge r\), by linear interpolation on the intervening interval. Empty paths are included. For fixed length, compactness of the path relation and continuity of this last cost give a lower semicontinuous infimum (with value infinity for an empty fiber). The countable infimum is Borel. Extend by zero outside the box. The function takes values in \([0,1]\), vanishes near the seed, and is bounded below by a positive number throughout the target ball within the box, by the uniform charge bound. For any permitted edge, concatenation gives \(V(x')\le V(x)/(1+l)\).

Smooth \(V\) by averaging sufficiently small common translations of its argument, with all cap translations strictly positive. Use a smooth probability density of support in a sufficiently small positive cube in all coordinates. Denote the result by \(S\). A translated exact positive-charge edge has the same \(l\) and satisfies the enlarged relation: the law error is \((1-c)\) times the translation, bounded by \(a\) times its size, and translating a cap upward preserves both Bellman inequalities. The larger box and the tolerance in its punishment bound include these translations, even at boundary states. Therefore \(T_S=S(x')+[S(x')-S(x)]/l\le0\) on every positive-charge edge. This extends to the closure \(E\) by the secant formula and smoothness. We have \(S(o)=0\) and \(S>0\) on a relative neighborhood of \(y\) in \(X\). On a compact enclosing box one may approximate \(S\) and its first derivatives uniformly by polynomials, for example by multivariable Bernstein approximation after rescaling. The uniform bound on the secant direction extends the moment identity from polynomials to \(S\). Since \(S\ge0\), (1) now rules out any mass of \(\Lambda\) on that neighborhood. A countable subcover excludes every unattainable state from its support. This proves sufficiency, including the assertion for a single specified endpoint.

The optimized law epigraph concerns original unrestricted response caps at arbitrary positive debt levels. The charged-polynomial no-equilibrium characterization was already available, as were the homogeneous degree tests and fixed-target occupation tests on the residual branch. Those tests used one-stage Nash rows and divergence of the clock to erase an unspecified end condition. Here arbitrary rows and cap increases are allowed, with literal AllNever retained as boundary. They compute the actual global minimum and its exact minimizing-law fiber on every signed table. The total-debt and uniform-payoff endpoints have their original meanings by the checked total-debt equivalence and terminal payoff selection. No table with a positive optimized minimum and no proof that all such minima vanish are supplied. [Positive total-debt equivalence](../../UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean) · [Terminal payoff selection](../../UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean)
