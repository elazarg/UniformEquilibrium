# Fin5 literal-Never spare support descent

**Author:** external ChatGPT submission supplied by the user  
**Status (2026-08-25):** ordinary-mathematics conditional branch theorem;
root review passes the deletion/cap/support-descent argument.  Not Lean-checked,
not independently reviewed, and not an exhaustive producer from the checked
four-role arm.

## Conjecture-facing question

In the positive-global-minimum counterexample regime on `Fin 5`, suppose the
checked non-excess four-role arm has produced literal profiles

\[
x_0\longrightarrow x_1\longrightarrow x_2
\]

and omitted player `w`.  Can one append the whole-stopping-law update

\[
y=x_2[w\leftarrow\mathrm{Never}]
\]

and obtain another global minimizer with strictly smaller positive-debt
support, without altering either prior reset or restricting unilateral
deviations?

The supplied answer is yes under the finite actual-source conditions below.
Its conclusion is a maintained well-founded support-rank decrease, so it is a
genuine conjecture-facing branch consumer rather than an equilibrium verifier
for an invented extension game.

## Finite deletion data

Write `d_i^k=B_i(x_k)-U_i(x_k)`,

\[
D_0=\sum_i d_i^0,
\qquad A_0=\{i:d_i^0>0\},
\]

and let `mu_2(S)` be the literal terminal-coalition law of `x_2`.  Extend the
reward to the empty coalition by `bar r_i(emptyset)=0`.  Define

\[
m_i^w=\min_{T\subseteq I\setminus\{w\}}
  (\bar r_i(T)-r_i(\{w\})),
\]

\[
g_i^w(x_2)=
\sum_{\varnothing\ne T\subseteq I\setminus\{w\}}
\mu_2(T\cup\{w\})[r_i(T)-r_i(T\cup\{w\})]
+\mu_2(\{w\})m_i^w,
\]

and, for `i != w`,

\[
\kappa_i^w=\max\!\left\{0,
\max_{\varnothing\ne T}[r_i(T)-r_i(T\cup\{w\})],
\max_T[\bar r_i(T)-r_i(\{w\})]\right\}.
\]

Finally put

\[
q_i^w=\max\{0,d_i^2+\kappa_i^w-g_i^w(x_2)\}.
\]

All maxima and minima range over the sixteen subsets of the four-player
complement of `w`.

## Conditional theorem

Assume:

1. the three profiles and labels are the literal composable four-role output,
   with `w` omitted from the four roles;
2. `w in A_0`;
3. `g_w^w(x_2) >= d_w^2`;
4. `U_w(x_2)` dominates player `w`'s punishment floor;
5. `sum_(i != w) q_i^w <= D_0`; and
6. `q_j^w=0` for every `j notin A_0`.

If `z_0=Sem(x_0)` is a global total-debt minimizer, then

\[
D(\operatorname{Sem}(y))=D_0
\]

and

\[
\operatorname{supp}^{+}d(\operatorname{Sem}(y))
\subseteq A_0\setminus\{w\}.
\]

Since `w in A_0`, positive-debt support cardinality decreases strictly.

## Proof audit

Couple complete stopping laws and replace only player `w`'s stopping time by
infinity.  If `w` ties a nonempty first coalition `T`, the payoff change is
`r_i(T)-r_i(T union {w})`.  If `w` is uniquely first, the later opponent
coalition is some `T`, possibly empty, and its payoff change is bounded below
by `m_i^w`.  Therefore

\[
U_i(y)-U_i(x_2)\ge g_i^w(x_2).
\]

The same pathwise comparison after fixing an arbitrary complete behavioral
deviation of player `i != w` gives

\[
B_i(y)\le B_i(x_2)+\kappa_i^w.
\]

For `w`, the opponents are unchanged, so `B_w(y)=B_w(x_2)`.  The supplied
lower bound on `w`'s prescribed-payoff gain, together with the fact that
`y` is itself one admissible deviation by `w`, pins that gain exactly to
`d_w^2`; hence `d_w(y)=0`.  For `i != w`,

\[
d_i(y)\le q_i^w.
\]

The aggregate budget gives `D(y)<=D_0`, while global minimality gives the
reverse inequality.  Equality follows.  The inactive-coordinate conditions
prevent new support outside `A_0`, and deletion of `w` makes the inclusion
strict.

The coupling fixes an arbitrary complete stopping law before comparison, so
Never, arbitrarily late stopping, random stopping laws, and all unrestricted
behavioral deviations are included.

## Whole-reset homotopy

Mixing player `w`'s complete stopping law with Never gives actual profiles
`x_2^theta`.  Prescribed payoff is affine and the other players' caps are
convex.  Player `w`'s cap is constant because its opponents are fixed.  Thus

\[
d_w(x_2^\theta)=(1-\theta)d_w^2,
\]

and

\[
d_i(x_2^\theta)
\le (1-\theta)d_i^2+\theta q_i^w
\quad(i\ne w).
\]

The prior profiles `x_0,x_1,x_2` and both earlier literal resets remain
unchanged; the cancellation is appended after them.  The punishment-floor
hypothesis keeps `w` floor-safe throughout.

## Exact remaining producer

The checked four-role theorem does **not** supply any of:

\[
w\in A_0,
\quad g_w^w(x_2)\ge d_w^2,
\quad \sum_{i\ne w}q_i^w\le D_0,
\quad q_j^w=0\ (j\notin A_0).
\]

Accordingly the exhaustive output currently proved is

\[
\text{strict support descent}
\quad\lor\quad
\text{failure of at least one of these finite spare-cap tests}.
\]

No checked consumer turns every failure into terminal approximate equilibrium,
cumulative-charge return, or another rank decrease.  That conversion is the
actual Fin5 producer gap.  This theorem must not be described as an automatic
cardinality reduction or as a consequence of omitted-label incidence alone.

## Root-review verdict

The prescribed-payoff coupling, uniform cap-lift estimate, exact closure of
`w`'s debt, global-minimum equality, inactive-coordinate exclusion, and strict
support descent are mathematically valid.  The result is genuinely
conjecture-facing because its successful arm decreases the maintained
minimum-fiber support rank inside the same five-player reward table.  It is
conditional and does not close the four-role branch; independent review is
required before export.
