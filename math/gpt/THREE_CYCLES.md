The missing point in a three-player lift is control of the fourth player’s payoff **at every continuation date**, not just its average payoff. A nonnegative row factorization supplies that control exactly.

I obtained a complete raw-table construction inside the **\(R_0,\ \kappa=+1\)** region left by the integer-degree criterion. **This does not settle arbitrary Fin4.** It excludes an open family of degree-one matrices, with arbitrary nonsingleton completions, and produces the strategies explicitly. The degree-one region is precisely where the attached degree argument stops. 

## 1. The raw-matrix theorem

Let \(I\) be any finite player set containing a three-player subset \(S\). Define

$$
s_i=r_i(\{i\}),\qquad
\Gamma_{ij}=r_i(\{j\})-s_i,\qquad
T=\Gamma_{SS}.
$$

**Theorem.** Suppose \(T\) is invertible and

$$
\boxed{
T^{-1}\ge0,\qquad
\Gamma_{kS}T^{-1}\ge0\quad\text{for every }k\notin S,
}
\tag{H}
$$

entrywise. Then the original quitting game has a fixed uniform-equilibrium payoff.

All own-singleton levels may be signed. **Every nonsingleton reward is arbitrary.** Singleton columns belonging to players outside \(S\) are also unrestricted.

When \(T^{-1}>0\), the proof gives explicit rational finite stopping laws for rational reward data. Outside players always play Never. The target is determined by singleton rewards alone; the other rewards affect how finely the schedule must be subdivided.

This is not arbitrary unchanged-child extension, which your attached obstruction rules out. The proof constructs a particular child schedule and verifies the outside player’s full response problem along it. 

For Fin4, the counterexample-facing consequence is:

$$
\boxed{
\text{No UE}\ \Longrightarrow\
\text{for every triple }S\text{ with }\Gamma_{SS}^{-1}\ge0,
\quad
\Gamma_{kS}\Gamma_{SS}^{-1}\not\ge0,
}
$$

where \(k\) is the remaining player.

## 2. An explicit example in the degree-one residual

Consider

$$
\Gamma=
\begin{pmatrix}
0&-1&2&-2\\
2&0&-1&1\\
-1&2&0&1\\
-1&2&2&0
\end{pmatrix}.
\tag{1}
$$

For \(S=\{0,1,2\}\),

$$
T^{-1}=\frac17
\begin{pmatrix}
2&4&1\\
1&2&4\\
4&1&2
\end{pmatrix}>0,
\qquad
\Gamma_{3S}T^{-1}=\frac17(8,2,11)>0.
$$

Thus (H) holds.

This matrix is genuinely in the degree-one region. Every principal minor of size at least two is nonzero, and every column contains a negative entry, proving \(R_0\). At right-hand side \(-\mathbf1\), complete support enumeration gives exactly one LCP solution:

$$
h=(1,1,1,0),\qquad
\Gamma h-\mathbf1=(0,0,0,2).
$$

Its active principal determinant is \(7>0\), so

$$
\kappa(\Gamma)=+1.
$$

The full determinant is \(3\), and the full inverse has both signs. The principal on \(\{0,3\}\) is

$$
\begin{pmatrix}0&-2\\-1&0\end{pmatrix},
$$

which is neither standard Q nor homogeneous-feasible; hence the full projective-Q-bar criterion fails. There is also no negative Hamiltonian cycle: the only negative entrance to player \(3\), and its only negative exit, both use player \(0\).

These separate (1) from the specific full-matrix and once-per-owner criteria compared in the degree packet—not from every conceivable cyclic construction. 

For **every** own-singleton vector \(s\) and **every** assignment of the 44 nonsingleton reward coordinates, the construction below gives the fixed target

$$
\boxed{v=s+(0,1,0,2/7).}
\tag{2}
$$

All the relevant inequalities are strict, so the sufficient condition persists in a neighborhood of (1). This is not an isolated matrix.

## 3. Producing the cycle from the matrix

First assume \(T^{-1}>0\).

The off-diagonal equations in \(TT^{-1}=I\) force the two off-diagonal entries in each row of \(T\) to have opposite signs. The equations in \(T^{-1}T=I\) give the same property for columns. After relabeling,

$$
T=
\begin{pmatrix}
0&-b_0&a_0\\
a_1&0&-b_1\\
-b_2&a_2&0
\end{pmatrix},
\qquad a_i,b_i>0.
$$

Positivity of an inverse diagonal entry then gives

$$
a_0a_1a_2>b_0b_1b_2.
$$

Put \(A_i=a_i/b_i\), \(P=A_0A_1A_2>1\), and define odds

$$
\begin{aligned}
t_0&=\frac{P-1}{1+A_1+A_0A_1},\\
t_1&=\frac{P-1}{1+A_2+A_1A_2},\\
t_2&=\frac{P-1}{1+A_0+A_2A_0}.
\end{aligned}
$$

Set

$$
q_i=\frac{t_i}{1+t_i},\qquad c_i=\frac1{1+t_i}.
$$

These are produced rates, not an assumed solution. Direct substitution gives

$$
t_0=A_2q_1,\qquad
t_1=A_0q_2,\qquad
t_2=A_1q_0,\qquad
C:=c_0c_1c_2=P^{-1}<1.
\tag{3}
$$

In phase \(i\), only player \(i\) is active, with Quit probability \(q_i\). Let

$$
x_0=a_0q_2,\qquad x_1=a_1q_0,\qquad x_2=a_2q_1,
$$

and define active-player surplus vectors

$$
z^0=(0,x_1,0),\qquad
z^1=(0,0,x_2),\qquad
z^2=(x_0,0,0).
$$

Equations (3) imply the exact cyclic recursion

$$
z^i=q_iTe_i+c_i z^{i+1}.
\tag{4}
$$

Every surplus is nonnegative. The active owner’s surplus is zero both before and after its phase.

For an outside player \(k\), set

$$
w_k=\Gamma_{kS}T^{-1}\ge0,\qquad z_k^i=w_kz^i.
$$

Then

$$
z_k^i=q_i\Gamma_{ki}+c_i z_k^{i+1},
\qquad z_k^i\ge0.
\tag{5}
$$

Consequently \(v^i=s+z^i\) satisfies the actual prescribed recursion for **every player**, and every player’s phase payoff is at least its own singleton. Since \(C<1\), these vectors are actual terminal continuation payoffs, not free annotations.

For (1), all three coarse hazards are \(1/2\), and the phase surpluses are

$$
\begin{aligned}
z^0&=(0,1,0,2/7),\\
z^1&=(0,0,1,11/7),\\
z^2&=(1,0,0,8/7).
\end{aligned}
$$

This proves the target formula (2).

The repository’s `BalancedSingletonCycleCertificate` already packages the required recursion, owner ties, all-player singleton floors, and opponent divergence. The calculation above **constructs those fields from the raw matrix**; the general certificate machinery is an existing dependency.

## 4. Why arbitrary collision rewards do not break the construction

The coarse cycle need not be Nash: a quiet player might profit by joining a coarse hazard. Subdivision controls this without altering the coarse payoffs.

Let \(|r_i(A)|\le M\). Choose a small hazard bound \(\delta>0\). Split phase \(i\) into \(N_i\ge t_i/\delta\) stages, using

$$
h_{i,\ell}=\frac{q_i}{N_i-\ell q_i},
\qquad 0\le\ell<N_i.
\tag{6}
$$

These are independent private hazards. Their continuation product is exactly \(c_i\), and each is at most \(\delta\).

Within a subdivided phase, the actual continuation payoff interpolates between its two coarse endpoints. Thus

$$
V_i(t)\ge s_i
$$

at every date. More importantly, for each queried player \(i\),

$$
V_i(t)=H_i(t)+\beta_i(t)V_i(t+1),
\tag{7}
$$

where the right side is its **Continue** payoff. For a quiet player this is its prescribed recursion; for the active owner it follows from the exact singleton tie.

If another player \(j\) is active with hazard \(h\le\delta\), player \(i\)’s Quit endpoint is

$$
Q_i(t)=(1-h)s_i+h\,r_i(\{i,j\})
       \le V_i(t)+2M\delta.
\tag{8}
$$

For the active owner, \(Q_i(t)=V_i(t)\).

Let \(b_i(t)\) be the probability that all opponents survive to date \(t\). Iterating (7), a pure Quit-at-\(t\) response has payoff exactly

$$
V_i(0)+b_i(t)\bigl(Q_i(t)-V_i(t)\bigr).
\tag{9}
$$

Its gain is therefore at most \(2M\delta\).

**There is no accumulation of this error over the calendar.** A stopping deviation uses a Quit endpoint once; all preceding Continue comparisons are equalities.

Opponents survive one cycle with probability

$$
\rho_i=
\begin{cases}
C/c_i,&i\in S,\\
C,&i\notin S,
\end{cases}
$$

which is strictly below one. Hence Never pays exactly \(V_i(0)\), by (7) and vanishing deleted-opponent survival. This argument allows signed singleton payoffs.

Every complete behavioral replacement is a mixture of finite quitting dates and Never. Therefore

$$
\boxed{E\le2M\delta}
\tag{10}
$$

against the unrestricted strategy class.

This preserves the distinction in the existing cyclic-patience interface: a singleton continuation floor is not itself an exact fixed-hazard joining inequality. Equation (8) supplies the missing quantitative comparison.

## 5. Actual finite laws and fixed-target delivery

Keep \(K\) complete subdivided cycles, then censor each later private clock independently to Never. Write \(\rho=\max_i\rho_i<1\).

The prescribed payoff is exactly

$$
U_i^K=(1-C^K)v_i.
$$

Uniformly over any unilateral replacement, changing the opponents to their censored laws affects the outcome only when **all opponents survive the cutoff**, an event of probability \(\rho_i^K\). Consequently

$$
\boxed{
E^K\le2M\delta+2M\rho^K+MC^K
     \le2M\delta+3M\rho^K.
}
\tag{11}
$$

This bound includes every after-support deadline and Never.

For \(0<\varepsilon\le M\), choose

$$
\delta=\frac{\varepsilon}{4M},
\qquad
\rho^K\le\frac{\varepsilon}{6M}.
$$

Then \(E^K\le\varepsilon\), with target-delivery error at most \(\varepsilon/6\). The number of dates is bounded by

$$
K\left(3+\frac{4M}{\varepsilon}(t_0+t_1+t_2)\right),
$$

so it is \(O(\varepsilon^{-1}\log(1/\varepsilon))\) for a fixed strict input table. Rational inputs yield rational laws directly; no equilibrium-search oracle is needed.

For an \(N\)-date word, full \(H\)-stage regret is at most

$$
E^K+\frac{2M(N+1)}H.
$$

For a negative late singleton, the comparison uses the Never response rather than incorrectly bounding its average payoff by its negative terminal payoff. This is the signed finite-law argument also used in the attached selector packet. 

The target \(v\) precedes the mesh, cutoff, and accuracy. Thus the construction has the required fixed-target, all-sufficiently-large-horizons quantifiers.

Zeros in \(T^{-1}\) are handled by the zero-diagonal-preserving approximation

$$
T_\eta=T-\eta(J-I).
$$

Keep \(w_k=\Gamma_{kS}T^{-1}\) fixed and replace outside rows by \(w_kT_\eta\). The strict theorem applies to these nearby tables. The full-regret reward perturbation bound then passes approximate equilibria to the original table. The strict approximation and reward-closedness ingredients are established in your inverse-positive packet. 

## 6. What this changes—and what it does not

The result supplies a finite raw-matrix test and an actual strategy producer within an open part of the degree-one residual. It does **not** prove that every remaining matrix contains such a triple. In particular, the positive-determinant paired matrix in your attachments fails this test: each principal triple has a negative diagonal entry in its inverse. Its arbitrary collision cylinder remains outside the theorem.

The proof is ordinary mathematics, **not Lean-checked**. Exact checks passed four symbolic rate identities, the complete LCP support inventory, and 192 finite profiles over 48 signed reward tables, including 768 independent full-cap scans. These checks support the calculations; the universal argument is the proof above.

[Complete proof, boundary cases, and support inventory](THREE_CYCLE_PASSIVE_INHERITANCE.md)
[Exact verification script](VERIFY_THREE_CYCLE_PASSIVE_INHERITANCE.py)

**Arbitrary Fin4 is not closed by this result. The established advance is the explicit passive-row inheritance producer, including the open degree-one cylinder above.**
