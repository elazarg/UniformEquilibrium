# Strengthening and source audit of the zero-Never screened free-Nash reduction

Reviewer: PAIRED_HULL_REVIEW

Note reviewed:
[SOCIAL_WEIGHT_REVIEW__ZERO_NEVER_SCREENED_FREE_NASH_TO_UNIQUE_DEBTOR.md](../notes/SOCIAL_WEIGHT_REVIEW__ZERO_NEVER_SCREENED_FREE_NASH_TO_UNIQUE_DEBTOR.md).

## Verdict

**PASS as ordinary mathematics, with two bounded statement qualifications and
one quantitative strengthening.**

The screened three-player Nash construction, its unrestricted-cap estimate,
the strict/minimum dispatch, the unique-debtor conclusion, and the finite
cap-menu split in Section 7.1 are correct. The minimum arm can be regenerated
on the same literal profile subsequence as a complete causal minimum-law
source once the maintained hard residual is included in the input. It does
not yield a new renewable rank or terminal consumer.

Two qualifications should be made explicit.

1. Sections 1--5 assume only a positive semantic minimum, while the type
   FinFourMinimumAtomProducer also contains a
   FinFourQuantitativeFullSupportHardResidual. Thus “complete minimum source”
   is literal only after the maintained residual is added as an input.
   Without it, the exact conclusion is a complete source-faithful causal atom
   chronology at the same minimum point.
2. Section 9 says the unique-debtor boundary is unconsumed, while Section 7.2
   contracts it to the off-minimum paid port. The remaining unconsumed
   boundary is the off-minimum paid port, not the screened unique-debtor
   entrance.

## 1. Complete unrestricted-cap control

For a free player $i$, a pure response time $s>H_n$ differs from Never only
if the retained player $k$ survives beyond $H_n$. If another free opponent
has a finite clock, it lies at or before $H_n$ and screens the comparison.
Therefore

$$
 |V_i(s)-V_i(\infty)|
 \le 2M\Pr(T_k>H_n)
 \le 2M\varepsilon_n.
$$

Finite-game Nash controls all earlier responses and Never. Every complete
behavioral response is a mixture of pure stopping times, so

$$
 d_i(\rho_n)\le 2M\varepsilon_n\qquad(i\ne k)
$$

holds against the full behavioral class. At a minimum cluster $y$ this gives

$$
 d_i(y)=0\quad(i\ne k),\qquad d_k(y)=D_*>0.
$$

The unchanged $k$-clock also makes the joint Never mass tend to zero.

## 2. Exact source regeneration and atom strength

The source regeneration added after the prior review is sound. A Fin4
terminal law has fifteen finite nonempty-coalition coordinates. If its Never
mass is zero, some fixed finite coalition $S$ satisfies

$$
 \nu(S)\ge\frac1{15}.
$$

Apply nonempty_sourceFaithfulMinimumCausalChronology from
Research/Quitting/SourceFaithfulMinimumLawCausalization.lean to the same
joint-law subsequence of the profiles $\rho_n$. It selects only further
indices, exact finite cap--Nash root words, finite windows, and positive dates;
it does not replace the suffix profiles. Its causal field gives eventually

$$
 \sum_{t<\operatorname{cutoff}_n}
 \Pr_{\rho_n}(\text{first coalition }S\text{ at }t)
 >\frac{\nu(S)}2\ge\frac1{30}.
$$

The selected individual marked date has positive mass, but need not have a
uniform per-date lower bound because this window mass may diffuse over more
dates.

The conversion to QuittingMinimumLawCausalSuffixAtom is literal, exactly as
in FinFourSourceFaithfulReselectedMarkRegeneration.atom and
FinFourFullReplacementSourceRegeneration.atom. With a fixed hard residual on
the same table these data assemble a FinFourMinimumAtomProducer with:

- the same minimum joint point;
- the same residual;
- suffix profiles equal to the selected $\rho_n$;
- limiting finite-atom mass at least $1/15$; and
- finite-window mass greater than $1/30$ eventually.

The marginal Never passport survives every finite prefix:

$$
 \Pr_{W_n\triangleright\rho_n,k}(T_k=\infty)
 =S_k(W_n)\Pr_{\rho_n,k}(T_k=\infty)
 \le\Pr_{\rho_n,k}(T_k=\infty)\to0.
$$

Joint prefix survival tends to one, hence every player-deleted opponent
survival does too. The exact identity
quittingTerminalPayoff_shiftedBehavioralResponse_sub_eq transports the
actual-reach $k$-response through the same words. This is a horizontal
complete-strategy response, not a temporal Nash--Bellman edge.

## 3. Section 7.1 cap menu

Let

$$
 a_n=\prod_{i\ne k}\Pr(T_i=\infty),
 \qquad s_k=r_k(\{k\}).
$$

All free clocks lie in $\{0,\ldots,H_n,\infty\}$. Thus every finite
$k$-response after $H_n$ has the same payoff, and

$$
 V_k(H_n+1)-V_k(\infty)=a_ns_k.
$$

The unrestricted cap is attained on
$\{0,\ldots,H_n+1,\infty\}$. The stated split is exhaustive:

- a finite maximizer kills $k$'s debt exactly;
- if Never maximizes and $a_n(-s_k)\to0$, the late finite response is
  $o(1)$-optimal and leaves $k$-debt $o(1)$;
- otherwise $s_k<0$ and, on a subsequence,
  $a_n(-s_k)\ge\delta>0$, so the exact Never target has joint Never mass
  at least $\delta/M$.

Re-solving the complementary finite game around a finite host again makes
the three free debts exactly zero. Bounded host deadlines yield an attained
finite-host minimum; unbounded deadlines yield only deadline escape.

## 4. Rank, consumer, and duplication audit

The regenerated source has debt support exactly $\{k\}$. It can enter the
checked positive-minimum tangent lane, but its support-cardinality rank is
already minimal. A strict nonempty-support child below $\{k\}$ is impossible.
Thus the recursive support-descent arm cannot recur; the generic dispatch
must leave through positive slope, support entry, or an off-minimum output.
Those outputs are maintained open waists, not terminal consumers.

Section 7.1 gives no host-label or deadline rank. Re-equilibrating the free
players can reactivate old clocks and can move the next best response earlier,
later, or to Never.

The exact overlap is:

- the finite cap menu, finite-host response, and failure of host-label rank
  duplicate the mathematics of
  CODEX_AMPERE__FINITE_FIXATION_SPECTATOR_COMPRESSION_AND_HOST_ROTATION.md;
- the present note is stronger only at the entrance: it selects the host from
  the supplied zero-Never minimum family and preserves that stopping-law
  ancestry;
- it is not the checked singleton-base same-law reset producer, which installs
  a new stationary sure owner and obtains a same-law reset packet;
- implication (7.7) already follows directly from
  ARBITRARY_CLOCK_MINIMUM_PURIFICATION_TO_OFF_MINIMUM_PAID_PORT.md.

Section 7.2 is compatible with the reviewed positive-Never late-release
packet, but adds no independent conjecture-facing endpoint. It explains how
the signed Never subarm returns to the known off-minimum waist; it is not a
new rank or consumer.

## Recommended exact statement

With a maintained hard residual, the clean new part is:

$$
\begin{aligned}
&\text{zero-Never positive-minimum realizing family}\\
&\quad\Longrightarrow\quad
\text{off-minimum paid port}\\
&\qquad\text{or a same-residual causal minimum source with}\\
&\qquad\operatorname{supp}^+d=\{k\},\\
&\qquad\nu(S)\ge1/15,\\
\Pr(T_k=\infty)\to0,\\
&\qquad\text{and a source-matched }k\text{-response.}
\end{aligned}
$$

Section 7.1 plus the already formalized arbitrary-clock purification contracts
the second output to the same off-minimum paid-port waist. That waist remains
unconsumed.

## Delta review: Section 7.3

### Verdict

**PASS after two bounded wording repairs, with a material strengthening of the
escaping arm.** The bad-clock mass estimate, first-disagreement survival and
joint-reach bounds, and fixed-row free-regret limit are correct. No step
reselects the three-player Nash targets or changes the retained strategy of
player \(k\).

The bounded repairs are:

1. define \(p_n\) as the earliest **positive-\(\pi_n\)-mass finite member** of
   the bad set, not merely its earliest finite member;
2. remove the duplicated sentence before (7.13), and restore the lost inline
   mathematical delimiters throughout Section 7.3.

### Bad mass and constants

Write \(C_n=B_k(\rho_n)\) and let

\[
\mathcal B_n=\{t:C_n-V_n(t)\ge D_*/2\}.
\]

Since \(C_n,V_n(t)\in[-M,M]\),

\[
\begin{aligned}
\frac{3D_*}{4}
&\le \sum_t\pi_n(t)(C_n-V_n(t))\\
&\le \frac{D_*}{2}+2M\,\pi_n(\mathcal B_n),
\end{aligned}
\]

so

\[
\pi_n(\mathcal B_n)\ge\frac{D_*}{8M}.
\]

Because \(\pi_n(\infty)\to0\), the finite supported bad clocks eventually
have mass at least \(D_*/(16M)\). Choose their earliest time \(p_n\), and
choose the exact cap clock \(q_n\) from the unchanged menu of Section 7.1.
Then

\[
V_n(q_n)-V_n(p_n)\ge\frac{D_*}{2}.
\]

At \(a_n=\min\{p_n,q_n\}\), the two pure clocks agree before the row. A payoff
contrast of at least \(D_*/2\) and a conditional range of \(2M\) give

\[
H_{-k,n}(a_n)\ge\frac{D_*}{4M}.
\]

Every finite bad support time is at least \(p_n\), and \(a_n\le p_n\).
Therefore the literal prescribed \(k\)-survival at \(a_n\) is at least the
entire finite bad mass:

\[
S_{k,n}(a_n)\ge\frac{D_*}{16M}.
\]

Multiplication yields the stated bound

\[
J_n(a_n)\ge\frac{D_*^2}{64M^2}.
\]

Here \(J_n\) is the probability that the original profile \(\rho_n\) reaches
the row. The paid pure-time comparison is between a positive-support source
clock \(p_n\) and the cap clock \(q_n\). It should not be described as the
probability mass of the single pure-clock component \(p_n\), whose atom may
tend to zero.

### Fixed-row free regret

If \(a_n=a\) is fixed, a free player \(i\ne k\) can change only its action at
that reached row and then resume its literal prescribed continuation. If its
conditional one-row gain is \(g_{i,n}\ge0\), the corresponding complete
behavioral deviation has unconditional gain

\[
J_n(a)\,g_{i,n}.
\]

Since every such gain is at most \(d_i(\rho_n)\le2M\varepsilon_n\), the joint
reach floor gives

\[
g_{i,n}\le
\frac{128M^3}{D_*^2}\,\varepsilon_n\longrightarrow0.
\]

Thus all three free root coordinates are asymptotically Nash at the same
literal row, against the original \(\rho_n\) continuation. This uses the
same free-Nash target and the same retained \(k\)-clock throughout.

### The escaping arm is an all-player escape

If \(a_n\to\infty\), then both \(p_n\) and \(q_n\) escape. More strongly than
the note states, (7.13) is already a fixed all-player joint-survival floor:

\[
\Pr_{\rho_n}(T_i\ge a_n\text{ for every }i)
\ge \frac{D_*^2}{64M^2}.
\]

After one common weak compactification of the four marginal stopping laws,
the reconstructed product profile therefore has Never mass at least
\(D_*^2/(64M^2)\). The limiting terminal law of \(\rho_n\) has Never mass
zero. Hence this arm directly supplies a quantitative instance of the checked
all-player escape account, with escaped total mass at least that same
constant. The existing escape/debt-jump and social-surplus consequences may
be invoked. They are not a general terminal consumer outside their sign
chambers, but this is stronger and more accurately typed than merely “two
labelled survival clocks.”

The displayed single free label in (7.14) is also valid: from the product
opponent-survival floor, one of the three free marginals is at least its cube
root, and finite subselection fixes the label. In fact each free marginal is
at least \(D_*/(4M)\), since the product is no larger than any factor; the
cube-root statement gives the stronger floor for at least one label.

### Fixed-row one-root closure does not follow

The fixed-row arm does **not** produce an exact four-coordinate root after
changing \(k\). The free regrets above are computed against the original
prescribed \(k\)-strategy and original continuation. The large
\(p_n\)-versus-\(q_n\) contrast is a complete pure-time contrast, not
necessarily the one-stage endpoint defect against that same prescribed
continuation. Replacing \(k\) by \(q_n\) can change all three free endpoint
comparisons by order one.

An exact local regression makes the mismatch concrete. At date zero let
player \(k\) mix equally between Quit now and Never. Let a free player \(j\)
Continue, let another free player \(h\) Quit surely at date one, and let the
fourth player Never stop. Set the relevant \(k\)-payoffs to

\[
r_k(\{k\})=0,\qquad r_k(\{h\})=1.
\]

Thus Never is a cap clock for \(k\), while Quit-at-zero is a bad supported
clock with gap one. For \(j\), set

\[
r_j(\{k\})=1,\quad
r_j(\{k,j\})=0,\quad
r_j(\{j\})=1,\quad
r_j(\{h\})=0.
\]

Against the original half-Quit \(k\)-root, \(j\)'s Continue and Quit actions
at date zero both yield payoff \(1/2\), so its one-row regret is zero. After
replacing \(k\) by Never, Continue yields \(r_j(\{h\})=0\), while Quit yields
\(r_j(\{j\})=1\). The formerly solved free coordinate is reactivated by one.
The remaining reward coordinates can be chosen so that \(h\)'s date-one
clock and the fourth player's Never clock are best responses. This is a
local strategy-change regression, not a positive-minimum counterexample.

Therefore the strongest honest fixed-row output is:

\[
\boxed{
\text{three free coordinates asymptotically root-Nash on the original source}
+\text{ one reached complete }k\text{-response row}.
}
\]

Turning it into one exact product root or a Nash--Bellman edge still requires
control of the free-coordinate changes after the \(k\)-replacement.

## Delta review of Sections 7.12--7.13

Verdict: **PASS as a conditional source contraction, with one typographical
repair and one important scope boundary.**

Assume the reconstructed product profile \(\bar\rho\) has already been
accepted as the current actual positive-Never global-minimum source.  The
common-quantile profiles are actual independent behavioral profiles, preserve
the four marginal Never atoms, and approximate complete terminal semantics;
their finite supports permit a cutoff \(T_n\) strictly beyond every finite
atom.  Capping owner \(i\) at \(T_n\) then changes only the joint-Never event:
it creates an exact singleton-\(i\) stage of mass \(q_n\to q>0\) and an exact
owner gain \(q_ns_i\).  Capping the punishment-normal partner \(j\) at the
same date changes only that same event from \(\{i\}\) to \(\{i,j\}\), with
exact gain

\[
 q_n\bigl(r_j(\{i,j\})-r_j(\{i\})\bigr)\ge q_n\Gamma.
\]

If the singleton endpoint is off minimum, this is already the paid-port arm.
If it is on the minimum fibre, its literal singleton-release profiles and
moving dates can themselves be causalized into the incoming
`FinFourMinimumAtomProducer`; the table-level hard residual is copied.  With

\[
 X_n=\text{singleton-release target},\qquad
 Y_n=\text{pair-release target},\qquad q=j,
\]

all hypotheses of Section 17 of the repaired oriented-pair note are met on
one common sequence: exact pure root \(K=\{i\}\) conditional on reach, exact
opposite endpoint \(K'=\{i,j\}\), unconditional mass floor, literal
one-player update at the same mark, and a fixed positive reward difference.
Thus the residual/off-minimum/minimum-support-drop trichotomy is correctly
invoked.  No date-zero or Never-tail normalization is being substituted.

Section 7.13 also correctly identifies the exact remaining reconstruction
seam.  Replacing the four marginal laws one at a time gives literal finite
behavioral ancestry, and if all intermediate limits remain minimal, convexity
and the global lower bound make each marginal chord flat.  Those edges need
not be profitable or Nash--Bellman admissible.  Consequently this finite
phase is valid producer ancestry only after \(\bar\rho\) is accepted; it does
not make \(\bar\rho\) a literal suffix or admissible descendant of the
original escaping family.  The moving pair contraction therefore does not
repair the all-player-escape reconstruction seam and does not consume its
paid-row/off-minimum outputs.

The display following (7.48) currently contains `ge q\Gamma`; it should be
the TeX relation `\\ge q\\Gamma` (or simply \(\ge q\Gamma\)).  This is
mechanical and does not affect the verdict.

## Delta review of Section 7.14

Verdict: **PASS.**  In the equality branch, acceptance of the reconstructed
product profile as a fresh minimum source is automatic; ancestry from the old
escape family is unnecessary unless a later consumer intends to spend the old
escape passport.

The decisive distinction is that \(\bar\rho\) is not merely a compact law.
It is an actual product behavioral profile, and the hypothesis
\(D(\bar\rho)=D_*\) makes

\[
\bar z=(\operatorname{Sem}(\bar\rho),\operatorname{Law}(\bar\rho))
\]

an actual joint-law global minimum.  The table-level hard residual applies at
that exact point.  Hence
exists_positive_finiteLawAtom_of_finFourHardResidual_minimum supplies a
positive finite coalition coordinate there, while the reconstructed marginal
laws give the positive joint-Never coordinate at the same point.

The explicit constant-suffix source is valid.  A positive finite coalition
coordinate is the sum of its nonnegative stage masses, so a finite window and
one positive date exist.  The minimum singleton moat gives

\[
B_i(\bar\rho)>r_i(\{i\})\qquad(i<4).
\]

Thus the all-Continue product root is exact against \(B(\bar\rho)\).  Prefixing
that root does not absorb, leaves the terminal semantics and law unchanged,
and repeats the same cap comparison.  Words of \(n+1\) all-Continue roots,
the constant suffix \(\bar\rho\), and the fixed finite-window atom therefore
inhabit the causal-source fields literally, with Continue product one and
debt exactly \(D_*\).

The reviewed positive-Never late-release theorem can consequently restart at
\(\bar z\) using fresh law-matched finite-clock compressions and fresh exact
cap--Nash prefixes.  Its later singleton row, partner pair row, and moving-pair
dispatch depend only on this new source.  They do not require an oriented
replacement path from the original escape realizers to \(\bar\rho\).

What Section 7.14 does **not** prove is equally important.  The restart is not
a profitable or Nash--Bellman edge from the old source, and no old marked row,
charge, or response passport crosses it.  Therefore it removes the
reconstruction conditionality for producer-state outputs such as a new
off-minimum port or strict-support child, but not for any chronology consumer
which explicitly requires the original escape passport.  Under that boundary,
(7.57) is a sound source-level contraction.

## Delta review of Section 7.15

Verdict: **PASS as a one-way producer-state rank, not as a chronological or
outer-atlas rank.**

The four displayed transition classes are exhaustive after the branchwise
subsequence selections already proved:

1. the reconstructed product profile is either off minimum, recorded as an
   exit, or is the accepted product-minimum source of Section 7.14;
2. the positive-Never late release is either off minimum, again an exit, or
   has a minimum singleton endpoint which is freshly causalized;
3. the same-date partner release enters the moving-pair trichotomy, whose
   positive-residual and off-minimum arms are exits and whose minimum arm is a
   regenerated strict-support child; and
4. the checked tangent trace either exits or regenerates a child with strictly
   smaller nonempty positive-debt support.

In items 2--4 the source is not merely a semantic label.  The positive-Never
packet retains the literal singleton-release profiles; the moving-pair
minimum arm causalizes its actual copied target family into a complete
same-residual source; and every later tangent descent carries its checked
full-replacement source regeneration.  Thus the support cardinality in the
rank is the support of the regenerated source point at every recursive node.

With \(B=5\), the rank ranges are disjoint:

\[
\begin{array}{c|c}
\text{phase}&\text{possible nonterminal ranks}\\ \hline
\mathsf{tangentMinimum}&1,\ldots,4\\
\mathsf{singletonMinimum}&6,\ldots,9\\
\mathsf{productMinimum}&11,\ldots,14\\
\mathsf{escapeOrigin}&16,\ldots,19.
\end{array}
\]

Every phase change therefore strictly decreases rank regardless of support
cardinality, and every recursive tangent edge decreases support cardinality.
The phase cannot recur because the transition relation is deliberately
one-way: all fresh construction after the product restart uses only that new
source, and no proved constructor returns a tangent or singleton node to an
earlier reconstruction phase.

This last sentence is also the exact scope boundary.  The rank does not prove
that an arbitrary outer atlas can never choose a new all-player escape packet
after an exit.  Nor does the escape-to-product restart become a profitable,
Nash--Bellman, or temporal edge.  Section 7.15 is valid for the closed
producer lane (7.60); it is not a global rank on every possible conference
construction.  Within that stated lane, no rank reset remains.
