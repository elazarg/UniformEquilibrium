# Mathematical audit of `gpt/DEBT.md`

Reviewer: `SOCIAL_WEIGHT_REVIEW`  
Date: 2026-08-31  
Verdict: **REVISE.**  One useful new rigidity lemma is correct, but the
headline reduction has a real quantifier error and most other ingredients
duplicate stronger existing interfaces.

## 1. Root calculus

Equations (1)--(3) are correct.  If `q` is a product root, `F_i(q;v)` is the
prescribed one-row payoff and `G_i(q_{-i};v_i)` is the best one-row endpoint,
then

\[
 d_i(q\star(u,b))
 =\bigl(G_i(q_{-i};b_i)-F_i(q;b)\bigr)+c(q)(b_i-u_i).
\]

For an exact cap--Nash root the local term is zero, giving common joint-
survival scaling.  This is already present in the checked arbitrary-root and
exact-cap-prefix debt ledgers; it is not a new consumer.

The distinction between joint survival `c(q)` and deleted-player survival
`s_i(q)` is handled correctly.

## 2. The debt-box rigidity lemma is correct and appears genuinely new

Let `x=(u,b)` be a global minimum with `D_*>0` and every coordinate debt
`d_i=b_i-u_i` strictly positive.  The singleton moat gives

\[
 u_i-r_i(\{i\})
 \ge D_*-d_i
 =\sum_{k\ne i}d_k>0.
\]

Thus all Continue is a strict root against every continuation vector
`v` with `u<=v<=b`.

For any exact product root `q` against such a `v`, the note's estimate

\[
 d_i(q\star x)
 \le s_i(q)(b_i-v_i)+c(q)(v_i-u_i)
 \le s_i(q)d_i
\]

is correct.  If some player `k` Quits with positive probability, then
`s_i(q)<1` for every `i!=k`.  Since all those debts are positive and Fin4 has
more than one player,

\[
 D(q\star x)<D_* ,
\]

contradicting global minimality.  Hence all Continue is the unique root on
the entire order interval `[u,b]`.

I found the known unique-root theorem at the displayed cap, the full-debt
moat, and exact-prefix persistence, but not this whole debt-box extension.
It is worth extracting as a standalone theorem.  Its statement should include
`|I|>=2` (or remain Fin4), coordinatewise full debt, and global carrier
minimality.  It is a rigidity/no-go result, not a Fin4 chamber consumer.

## 3. The maximal-orbit reduction has a substantive quantifier error

Section 3 fixes one endpoint `R^(0)` and recursively prefixes exact roots.  It
correctly obtains

\[
 D(R^{(m)})=P_mD(R^{(0)}),
 \qquad
 d_j(R^{(m)})=P_m d_j(R^{(0)}),
\]

with `P_m` bounded below by a positive constant.  Therefore, if

\[
 D(R^{(m)})\to D_* ,
\]

then in fact

\[
 P_m\to {D_*\over D(R^{(0)})}>0,
 \qquad
 d_j(R^{(m)})\to
 {D_*\over D(R^{(0)})}d_j(R^{(0)}).
\]

This does **not** tend to zero merely because the initial debt is “small.”
It tends to zero only if the initial debt is exactly zero, or if there is a
second outer index along which the initial debts tend to zero and a coherent
diagonal construction is supplied.  Consequently the sentence

> `D(R^(m))->D_*`, in which `d_j->0`, giving the reset-rigid limit

is false for the displayed one-orbit quantifiers.

This is not a cosmetic issue.  Reset-rigid entry requires an attained minimum
with an exactly zero selected debt and positive opponent incidence.  A fixed
small positive limit debt supplies neither.

The repository already has the correctly quantified alternative:

* the vanishing-response maximal-root/reset trichotomy works with a source
  sequence whose selected debts tend to zero;
* the paired signed-atom saturation retains the sibling law passport and
  neutralizes roots born at a limiting cap.

To repair Section 3, the author would need to reintroduce that outer sequence,
perform one coherent common subsequence/paired-hull construction, and state
exactly which source labels survive.  Doing so would reproduce those existing
results rather than establish a new reduction.

The other scalar calculations in Section 3 are correct:

\[
 P_m\ge D_*/D(R^{(0)})>0,
 \quad
 \sum_m(1-c_m)<\infty,
\]

the exact charges telescope, and a signed terminal-law difference scales by
the same common survival factor.  They show why the real-valued charge is not
a well-founded rank.  They do not repair the zero-debt quantifier.

There is a second provenance qualification.  Recursively adding new roots on
the outside produces actual finite common-prefix descendants, but it is not a
forward extension-compatible one-sided chronology: the date-zero root changes
at every outward-prefix step.  Compact recurrence of this orbit therefore
does not itself give a replayable child source.

## 4. Actual-payoff root descent is correct but already checked

For an exact root against the actual prescribed payoff `u`, equation (14)

\[
 d_i(q\star y)\le s_i(q)d_i(y)

\]

is correct.  In particular no previously zero debt coordinate enters.  The
global-minimum consequence

\[
 \sum_i(1-s_i(q))d_i(y)\le D(y)-D_*

\]

follows immediately and is a useful scalar corollary.

However the coordinatewise deleted-survival inequality is already the
checked actual-payoff endpoint-Nash prefix descent used in
`TerminalDebtPrefixDescent.lean`.  The one-debtor self-clock regression is
also mathematically sound: if only the debtor Quits at the root and is
indifferent at the actual payoff, its own deleted-player survival is one, so
its complete cap debt can remain exactly unchanged even while joint reach is
multiplied by `1-h`.  This is a local algebraic regression, not a positive-
minimum reward-table counterexample.

## 5. Support entry and renewable conclusions

Section 4 correctly avoids support entry for roots exact against `u`, because
the upper bound is coordinatewise.  Section 3 does not obtain that property:
its roots are exact against the cap of the response endpoint, and the sibling
is prefixed only to transport the law difference.  No root exactness or debt
support statement is available on the sibling.

The final implication (17) is not proved as written.  The symbols `(F1)--
(F3)` are not defined in the file, and the transition from one fixed “small
debt” endpoint to a sequence with `d_j(R_n)->0` is precisely the missing
quantifier discussed above.  Likewise, calling the output “same-source” must
not be read as renewable ancestry or a backward compiler.

The stated `Off-minimum inert-collapse lemma` is an honest open consumer, but
it is a list of possible sufficient outputs rather than a theorem derived in
the note.  Formula (16) correctly explains why positive joint reach alone is
insufficient and why cap leakage/deleted clocks remain central.

## Novelty/disposition

* **Genuinely useful and apparently new:** full-debt global-minimum uniqueness
  of all Continue for every continuation vector in the whole coordinate box
  `[u,b]`.
* **Correct but already available:** arbitrary-root/exact-root debt ledger,
  exact-prefix charge telescope, actual-payoff deleted-survival descent, and
  the self-clock obstruction.
* **Already handled more strongly elsewhere:** the vanishing-response
  maximal-root reset/two-level-inert split and paired signed-atom saturation.
* **Incorrect as quantified:** fixed-orbit minimum landing implies
  `d_j->0`, and therefore the claimed reduction of alternative 1 to reset or
  the stated packet.

The debt-box lemma should be retained as a separate note/export candidate
after independent review.  `gpt/DEBT.md` as a whole is not an actual Fin4
consumer and should not be exported in its present form.

