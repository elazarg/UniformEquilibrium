# Nested finite response menus: terminal Nash or a distinct moving clock

Author: CODEX_SPINOZA

## Status

The tightness/escape theorem below is exact ordinary mathematics, not checked
in Lean. It concerns a literal sequence of finite-menu Nash profiles and
nested strategy menus. In the tight arm it produces an actual unrestricted
terminal Nash profile. Under a hypothetical positive global debt floor, it
therefore forces a fixed payer and a distinct prescribed player carrying a
uniform amount of finite stopping mass to moving late blocks.

Installing the payer's selected clock gives, in every relative-order case,
a literal uniformly reached finite block with unit payer hazard and a fixed
distinct-label hazard budget.  After silent marking, this exactly enters the
checked Fin4 post-mark two-cut off-minimum/paid-splice theorem.  The output is
the already known paid-port waist and is not proved renewable.

The escaping blocks occur in alternative finite-menu Nash sources, not in one
concatenated Nash--Bellman chronology. The theorem does not turn them into
two persistent marginal hazard streams on one play, and it does not claim a
uniform-equilibrium payoff in the escape arm.

## Question and algorithm

Let \(I=\operatorname{Fin}4\), let terminal rewards satisfy
\(|r_i(S)|\le M\), and let Never pay zero. Identify each complete behavioral
strategy with its stopping law on

\[
 T=\mathbb N\sqcup\{\mathsf{Never}\}.
\]

For each player \(i\), start with a nonempty finite menu \(A_i^0\) of actual
stopping laws, including Never. Inductively:

1. choose a mixed Nash equilibrium \(\lambda^n\) of the finite normal form
   with pure strategy sets \(A_i^n\);
2. compile the independent mixtures to one literal behavioral profile
   \(\sigma^n\), with marginal stopping laws \(\mu_i^n\);
3. choose a player \(p_n\) of maximal unrestricted debt at \(\sigma^n\);
4. by pure-time extremality, choose a deterministic clock
   \(q_n\in T\) whose gain is within \(\varepsilon_n\) of that debt; and
5. set

   \[
   A_{p_n}^{n+1}=A_{p_n}^n\cup\{\delta_{q_n}\},
   \qquad
   A_i^{n+1}=A_i^n\quad(i\ne p_n).                         \tag{1}
   \]

Take \(\varepsilon_n\downarrow0\). If the selected gain is positive, finite
menu Nash optimality implies \(\delta_{q_n}\notin A_{p_n}^n\).

This is a double-oracle procedure, not a strategy-revision chronology inside
one play. The source at step \(n+1\) is a newly solved finite-game Nash law;
it is not the response target from step \(n\).

## Sources inspected

Behavioral pure-time extremality is
sSup_range_quittingTerminalPayoff_update_eq_pureTime in
BehaviorPureTimeExtremality.lean. Canonical compilation between stopping
laws and behavioral strategies is in StoppingLawCanonicalization.lean.

The finite-deadline special case and its exact late-Quit/Never charge are in
TerminalSemanticFiniteDeadlineNashEscalation.lean, especially
QuittingFiniteDeadlineNashProfile.semanticDebt_le_escapeCharge and the global
floor survival bounds. The already recorded paid-Never plateau is Section 9
of CODEX_SPINOZA__POSITIVE_MINIMUM_RESPONSE_COMPACTIFICATION_BOUNDARY.md.

The exact moving-mass compactification test is checked in
PositiveDebtTerminalSemanticNonattainment.lean. The complete-clock
compactness and actuality boundary are summarized in
arch/EXECUTABLE_COMPACT_STATE.md.

## 1. Split tightness

A sequence of stopping laws \(\mu^n\) on \(T\) is **split-tight** if

\[
 \lim_{H\to\infty}
 \sup_n\mu^n(\{H,H+1,\ldots\})=0,                         \tag{2}
\]

where the set in (2) contains only finite clocks and excludes Never.
Equivalently, for every \(\eta>0\), one finite set

\[
 \{0,\ldots,H-1,\mathsf{Never}\}
\]

carries mass at least \(1-\eta\) for every \(n\).

Split tightness gives relative compactness in total variation on the discrete
space \(T\). It deliberately distinguishes finite clocks escaping to
infinity from literal Never.

For a pure response clock \(q\), write

\[
 V_i(q,\mu_{-i})
 =
 U_i(\delta_q,\mu_{-i}).                                  \tag{3}
\]

If two opponent triples have marginal total-variation distances
\(\delta_j\), the product coupling gives the response-uniform estimate

\[
 |V_i(q,\mu_{-i})-V_i(q,\nu_{-i})|
 \le 2M\sum_{j\ne i}\delta_j                               \tag{4}
\]

for every \(q\), including Never. Crucially, the modulus in (4) is
independent of the response deadline.

## 2. Tight nested menus produce a terminal Nash profile

### Theorem 2.1 (double-oracle tightness theorem)

For the construction above, suppose all four source marginal sequences
\((\mu_i^n)_n\) are split-tight. Then

\[
 D(\sigma^n)\longrightarrow0.                             \tag{5}
\]

Every total-variation cluster point of the source laws is an actual
unrestricted terminal Nash profile.

#### Proof

Assume (5) fails. Then for some \(\delta>0\), along a subsequence

\[
 D(\sigma^n)\ge\delta.                                    \tag{6}
\]

Stabilize a maximal debtor \(p\). Its debt is at least \(\delta/4\).
For all large selected indices, \(\varepsilon_n\le\delta/8\), hence

\[
 V_p(q_n,\mu_{-p}^n)-U_p(\sigma^n)\ge\delta/8.             \tag{7}
\]

Split tightness and finite-player diagonal selection give a further
subsequence on which every opponent law converges in total variation. Also
stabilize

\[
 U_p(\sigma^n)\longrightarrow u.                          \tag{8}
\]

Fix one selected index \(n_k\). Its clock \(q_{n_k}\) belongs to player
\(p\)'s menu at every later selected index \(n_\ell>n_k\). Finite-menu Nash
optimality gives

\[
 V_p(q_{n_k},\mu_{-p}^{n_\ell})
 \le U_p(\sigma^{n_\ell}).                                \tag{9}
\]

Letting \(\ell\to\infty\) in (9) and using (4), write the limiting opponent
triple as \(\mu_{-p}\). Then

\[
 V_p(q_{n_k},\mu_{-p})\le u                               \tag{10}
\]

for every \(k\). On the other hand, (4), (7), and (8), now with
\(k\to\infty\), give

\[
 V_p(q_{n_k},\mu_{-p})\ge u+\delta/8-o(1),                \tag{11}
\]

contradicting (10). This proves (5).

Split tightness of all four marginals supplies a total-variation convergent
subsequence \(\mu^n\to\mu\). Prescribed payoffs and the complete
unrestricted caps are continuous in this topology; for caps, take the
supremum after the response-uniform bound (4). Hence

\[
 D(\mu)=\lim_nD(\sigma^n)=0.
\]

Canonical stopping-law realization makes \(\mu\) an actual behavioral
profile. \(\square\)

### Corollary 2.2 (tight response menus are impossible under a gap)

If every actual profile satisfies \(D(\sigma)\ge D_*>0\), the union of the
finite response menus cannot be split-tight. Indeed, tightness of every
strategy ever admitted to a player's menus implies tightness of every convex
mixture \(\mu_i^n\), contradicting Theorem 2.1.

## 3. Positive global debt forces a distinct prescribed escape label

The previous proof only used tightness of the three opponents of the
stabilized payer.

### Theorem 3.1 (payer--opponent clock escape)

Assume

\[
 D(\sigma)\ge D_*>0                                      \tag{12}
\]

for every actual profile, and choose
\(\varepsilon_n\le D_*/8\). There are:

- a fixed payer \(p\);
- a distinct player \(j\ne p\);
- a constant \(\beta>0\);
- a strict subsequence, still denoted \(n\);
- finite intervals \([a_n,b_n]\) with \(a_n\to\infty\); and
- distinct finite response clocks \(q_n\);

such that

\[
 V_p(q_n,\mu_{-p}^n)-U_p(\sigma^n)\ge D_*/8,              \tag{13}
\]

\[
 \mu_j^n([a_n,b_n])\ge\beta/2.                            \tag{14}
\]

Moreover the marginal hazard probabilities of player \(j\) in the literal
source \(\sigma^n\) satisfy

\[
 \sum_{t=a_n}^{b_n}
 \Pr_{\sigma^n}(j\text{ Quits at }t\mid\text{live at }t)
 \ge\beta/2.                                               \tag{15}
\]

After a further subsequence, exactly one fixed relative-order alternative
holds:

\[
 q_n<a_n,\qquad
 a_n\le q_n\le b_n,\qquad\text{or}\qquad
 b_n<q_n.                                                  \tag{16}
\]

#### Proof

At each finite-menu Nash source, a maximal debtor has debt at least
\(D_*/4\), so (13) holds. Stabilize its label \(p\).

Every \(q_n\) is absent from the current menu, while every earlier selected
clock remains in all later menus. Never was in the initial menu. Hence the
\(q_n\) are distinct finite clocks; pass to a subsequence tending to
infinity.

If all three opponent sequences \((\mu_k^n)_n\), \(k\ne p\), were
split-tight, the contradiction (7)--(11), with \(\delta=D_*\), would apply.
Thus one fixed \(j\ne p\) is not split-tight. Negating (2) gives
\(\beta>0\) and, after diagonal selection, \(a_n\to\infty\) such that

\[
 \mu_j^n(\{a_n,a_n+1,\ldots\})\ge\beta.
\]

Continuity from below for each individual probability law permits a finite
\(b_n\ge a_n\) capturing at least \(\beta/2\), proving (14). A stopping-law
atom at \(t\) is its survival to \(t\) times its conditional Quit hazard, and
is therefore no larger than that hazard. Summing gives (15). Finite
pigeonhole supplies (16). \(\square\)

The same strict subsequence may be used to freeze a single payoff/semantic
target:

\[
 U(\sigma^n)\to u,\qquad B(\sigma^n)\to b,\qquad
 \nu(\sigma^n)\to\nu,                                     \tag{17}
\]

together with convergence of all four player-deleted terminal laws. These
coordinates live in finite compact boxes or simplices. The profiles
\(\sigma^n\), the selected response \(q_n\), and the prescribed \(j\)-clock
block remain literal and share one index. The limit in (17) is a carrier
point and need not be behaviorally attained.

## 4. Exact moving-clock tests

### Test 4.1 (diffuse prescribed mass)

In PositiveDebtTerminalSemanticNonattainment.lean, one player's stopping law
is uniform on

\[
 \{0,1,\ldots,n\}.
\]

For every fixed \(H\), its finite mass after \(H\) tends to one. Thus it is
maximally non-split-tight. Nevertheless its exact terminal semantic pairs
converge to a finite positive-debt carrier point which no behavioral profile
realizes. This verifies that coordinatewise semantic/law compactness cannot
replace the split-tight hypothesis in Theorem 2.1.

That checked family is not claimed to be a double-oracle Nash sequence; it is
a compactness regression only.

### Test 4.2 (a paid clock escaping from a tight source)

Fix a finite-clock Nash source whose opponents have a positive common Never
cylinder, and let \(q_L=L\) with \(L\) beyond every menu deadline. The exact
late-Quit/Never identity is

\[
 V_i(L,\mu_{-i})-V_i(\mathsf{Never},\mu_{-i})
 =
 r_i(\{i\})\prod_{j\ne i}\mu_j(\{\mathsf{Never}\}).        \tag{18}
\]

The source is split-tight, while the response clocks \(\delta_L\) are not.
Their finite endpoints can even have one identical terminal semantic pair
and still jump by the full quantity (18) at the weak Never endpoint.

This does not contradict Theorem 2.1: once one profitable \(\delta_L\) is
added, the same source is no longer a Nash equilibrium of the enlarged menu.
The later-menu inequality (9), absent from the static plateau regression, is
exactly what rules out a tight sequence of re-solved sources.

## 5. Adapter and remaining obstruction

Theorem 3.1 gives more than an unlabelled failure of compactness:

1. \(p\) is a fixed source debtor with a literal, fresh, paid pure clock
   \(q_n\);
2. \(j\ne p\) is a fixed prescribed source label;
3. one moving finite interval carries \(j\)-hazard at least \(\beta/2\);
4. the response clock has one fixed order relation to that interval; and
5. all payoff, cap, terminal-law, and player-deleted-law limits use the same
   literal source sequence.

It still falls short of the checked two-persistent-label consumer. The
\(j\)-hazard occurs in a sequence of alternative finite-menu Nash profiles,
while \(p\)'s unit clock is counterfactual at each source. Neither is yet a
marginal stream on one concatenated Nash--Bellman chronology. Applying the
response destroys joint finite-menu Nash, and re-solving the enlarged menu
does not preserve literal source ancestry.

There is nevertheless an exact one-block conversion which uses the
counterfactual clock rather than trying to re-solve around it.  The first
ingredient is the following source estimate.

### Proposition 5.1 (the paid clock is uniformly reached by its opponents)

Put

\[
 g={D_*\over8},\qquad s={g\over2M}={D_*\over16M}.
 \tag{19}
\]

Then, at every selected source in Theorem 3.1,

\[
 \Pr_{\mu^n_{-p}}(T_k\ge q_n\text{ for every }k\ne p)\ge s.
 \tag{20}
\]

Indeed, Never belongs to player \(p\)'s finite menu.  Finite-menu Nash
optimality and (13) therefore give

\[
 V_p(q_n,\mu^n_{-p})-V_p(\mathsf{Never},\mu^n_{-p})\ge g.
 \tag{21}
\]

The two pure strategies \(q_n\) and Never give exactly the same terminal
outcome if some opponent stops strictly before \(q_n\).  On the complementary
event their payoff difference has absolute value at most \(2M\).  This proves
(20).  Notice that (20) is full opponent reach, not merely the survival of
the escaping label \(j\).

### Theorem 5.2 (all three order types give a reached two-label block)

Let

\[
 \eta={\beta\over4}.
 \tag{22}
\]

Install the selected response literally,

\[
 \rho^n=\sigma^n[p\leftarrow\delta_{q_n}].
 \tag{23}
\]

There are cuts \(c_n<e_n\), chosen from
\(a_n,q_n,q_n+1,b_n+1\), such that:

\[
 \Pr_{\rho^n}(T_k\ge c_n\text{ for every }k)\ge s,
 \tag{24}
\]

\[
 \sum_{t=c_n}^{e_n-1}h^{\rho^n}_{t,p}=1,
 \qquad
 \sum_{t=c_n}^{e_n-1}h^{\rho^n}_{t,j}\ge\eta.
 \tag{25}
\]

The choices, including the middle-case split, are as follows.

1. If \(q_n<a_n\), take \(c_n=q_n\) and \(e_n=b_n+1\).
2. If \(a_n\le q_n\le b_n\), split

   \[
   \mu_j^n([a_n,b_n])=
   \mu_j^n([a_n,q_n))+\mu_j^n([q_n,b_n]).
   \]

   If the first term is at least \(\beta/4\), take
   \(c_n=a_n,e_n=q_n+1\); otherwise take
   \(c_n=q_n,e_n=b_n+1\).
3. If \(b_n<q_n\), take \(c_n=a_n\) and \(e_n=q_n+1\).

In every case \(c_n\le q_n<e_n\).  Player \(p\)'s installed clock therefore
gives the first equality in (25).  The selected part of player \(j\)'s block
has stopping-law mass at least \(\eta\).  Since a stopping-law atom equals
survival times conditional Quit hazard, its mass is no larger than that
hazard; summing proves the second inequality in (25).

If \(c_n=q_n\), (24) is exactly (20), since player \(p\) survives to its own
clock.  Otherwise \(c_n<q_n\), and opponent survival to \(q_n\) implies
opponent survival to \(c_n\), while the installed player also survives to
\(c_n\).  This again proves (24).  Thus no one of the before/inside/after
order types remains outside this aggregate two-cut construction. \(\square\)

### Corollary 5.3 (exact entry into the checked post-mark consumer)

Assume in addition the retained hard datum that one carrier point \(z_*\)
attains the positive minimum total debt \(D_*>0\).  Prefix one deterministic
all-Continue row to \(\rho^n\), shift the displayed cuts to
\(c_n+1<e_n+1\), and use row zero as the mark.  The resulting literal root
sequence is a `QuittingUniformlyReachedPostMarkTwoCutBlock` with

\[
 \text{reachFloor}=s,\qquad
 \text{hazardFloor}=\chi:=1+\eta.                  \tag{26}
\]

This is a direct match to the fields in
`TerminalSemanticPositiveMinimumTwoCutPaidSplice.lean`: the roots are the
live roots of one actual profile, the mark precedes the entry cut, (24) is
the entry-reach field, and (25) gives the total marginal-hazard field.
Consequently
`QuittingUniformlyReachedPostMarkTwoCutBlock.finFour_offMinimum_or_exists_paidSplice`
returns either

\[
 D(z_{\rm exit})\ge
 D_*+{e^\chi-1\over2}D_*                           \tag{27}
\]

or an actual paid suffix splice.  With

\[
 K_\chi=(1-e^{-\chi})D_*,                          \tag{28}
\]

the latter has suffix gain greater than \(K_\chi/16\), padded-parent gain
greater than

\[
 {sK_\chi\over16},                                 \tag{29}
\]

and the exact same-coordinate debt decrease and pre-entry identity supplied
by the checked theorem.

The ancestry is literal but two-step: \(\rho^n\) is the displayed unilateral
response target of the named finite-menu Nash source \(\sigma^n\), and the
paid splice preserves \(\rho^n\) before \(c_n\).  No independently selected
profile or semantic annotation is inserted.

This consumes the relative-order trichotomy into the already checked
off-minimum/paid-splice waist.  It does **not** make either output renewable,
does not preserve finite-menu Nash after installing \(q_n\), and does not
produce two persistent streams on one infinite chronology.  In particular,
when \(q_n<a_n\), player \(p\)'s sure stopping row absorbs before player
\(j\)'s displayed later hazard; the second label is then a literal off-path
strategy field, not a second realized terminal event.  This is admissible for
the checked aggregate two-cut structure, whose coercivity already sees the
unit payer hazard, but it supplies no deleted-survival or persistent-label
conclusion.  Moreover the chronological debt-shadowing consumer requires
Nash--Bellman/support-error fields that the installed profile need not have.
Thus
the original question below is still the missing adapter for the exact-spine
consumer, rather than for the finite two-cut coercivity theorem.

Thus the exact remaining question is:

\[
 \boxed{
 \text{Can the nested-menu payer clock be installed with positive mass while
 retaining a fixed fraction of the distinct prescribed escape block?}}
\]

A positive answer with summable re-solving seams would give two persistent
labels and enter the checked deleted-clock/chronological consumer. The
present theorem supplies the co-sourced labels, scale, order type, and fixed
target, but not that installation seam.

## 6. Cofinal dispatch and the exact limit of menu inheritance

Apply Corollary 5.3 at every selected index.  Its constants are independent
of the index.  Put

\[
 G_0={s(1-e^{-\chi})D_*\over16}>0.                 \tag{30}
\]

Two additional conclusions are available because \(q_n\) is an
\(\varepsilon_n\)-best response and because all earlier clocks remain in
later menus.

### Proposition 6.1 (the paid-splice payer is not the clock owner)

For all sufficiently large \(n\), if the checked two-cut dispatch takes its
paid-splice arm, its payer \(r_n\) is different from \(p\).

#### Proof

Suppose the payer were \(p\).  Remove the harmless deterministic silent row
from the padded parent and splice.  Since both profiles have the same
opponents \(\mu^n_{-p}\), the spliced strategy is one admissible complete
response \(\tau_p^n\) against the original source opponents.  The
parent-gain field of the checked theorem and (23) give

\[
 U_p(\tau_p^n,\mu^n_{-p})
   >V_p(q_n,\mu^n_{-p})+G_0.                       \tag{31}
\]

But \(q_n\) was selected within \(\varepsilon_n\) of the unrestricted cap,
so

\[
 B_p(\sigma^n)\le V_p(q_n,\mu^n_{-p})+\varepsilon_n.       \tag{32}
\]

Equations (31)--(32) contradict cap maximality once
\(\varepsilon_n<G_0\). \(\square\)

Thus cofinal paid splices have, after finite-label extraction, one fixed
spectator payer \(r\ne p\).  This is a genuine narrowing of the old
paid-port waist.

### Proposition 6.2 (why the two cofinal arms do not yet renew)

The nested-menu inequalities alone neither exclude cofinally many
off-minimum arms nor turn the spectator-paid arm into a return.

For the off-minimum arm, every construction in Theorem 5.2 has

\[
 c_n\le q_n<e_n,
 \qquad
 \Pr_{\rho^n}(T_k\ge e_n\text{ for every }k)=0,     \tag{33}
\]

because player \(p\) Quits surely at \(q_n\).  The semantic point
\(z_{\rm exit}^n\) in (27) is therefore the conditional suffix strictly
behind a zero-survival wall.  The checked theorem legitimately records its
off-minimum debt, but that suffix has zero weight in the installed parent's
terminal payoff.  Finite-menu Nash at any later source imposes no inequality
on this conditional suffix.

For the paid arm, write the spectator's source and installed-parent response
gains as

\[
\begin{aligned}
 A_n={}&U_r(\sigma^n[r\leftarrow\tau_r^n])-U_r(\sigma^n),\\
 \widehat A_n={}&
 U_r(\rho^n[r\leftarrow\tau_r^n])-U_r(\rho^n)>G_0.
\end{aligned}                                             \tag{34}
\]

Either \(A_n\ge G_0/2\), giving another paid response at the original
source, or

\[
 \widehat A_n-A_n>G_0/2,                           \tag{35}
\]

a fixed cross-player operational effect of replacing \(p\)'s entire source
law by \(q_n\).  Both are existing paid-port/response-curl outputs; neither
is a source return.

The only inherited inequalities are, for each fixed earlier selected clock
\(q_k\) and every later selected source \(n>k\),

\[
 V_p(q_k,\mu^n_{-p})\le U_p(\sigma^n).              \tag{36}
\]

They concern player \(p\)'s payoff against the **later** opponent tuple.
They say nothing about:

1. the zero-reach conditional suffix in (33);
2. player \(r\)'s gains in (34); or
3. any total-variation or literal-suffix relation between
   \(\mu^n_{-p}\) and \(\mu^k_{-p}\).

Indeed the escape arm was obtained precisely because those opponent tuples
are not split-tight.  Payoff continuity is uniform in a response clock only
after the opponent laws are close in total variation; (36) supplies no such
closeness.  Adding \(\tau_r^n\), or a pure-time approximation to it, to a
later menu would only reproduce (36) for player \(r\) against a newly
re-solved opponent tuple.  It would not preserve the gain in (34).

Consequently the cofinal dispatch has the exact residual

\[
 \boxed{
 \begin{array}{c}
 \text{zero-reach off-minimum suffixes}\quad\text{or}\quad
 \text{fixed spectator-paid/cross-effect ports},\\
 \text{with no cross-index opponent-law or suffix ancestry.}
 \end{array}}                                             \tag{37}
\]

This is strictly sharper than an arbitrary repetition of the old waist:
the original clock owner is excluded from the paid arm and the off-minimum
arm is localized behind the sure-clock wall.  But nested menu monotonicity is
an own-player, current-opponents inequality, not a projective coupling of the
re-solved sources.  It therefore does not supply the missing renewal seam.

## Scope and nonclaims

- No S.3 theorem or local fixed-tail root argument is used.
- The tight arm produces a terminal Nash profile, not merely a stationary or
  finite-horizon equilibrium.
- The escape arm is source-faithful at each menu index but is not one temporal
  path.
- Equation (15) is a blockwise marginal-hazard lower bound, not divergence
  for one actual strategy.
- The result does not assert that a positive global terminal-debt floor
  exists for any quitting table.
