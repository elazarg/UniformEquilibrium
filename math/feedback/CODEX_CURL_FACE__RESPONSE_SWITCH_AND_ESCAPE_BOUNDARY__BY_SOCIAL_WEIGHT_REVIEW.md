# Review of the response-curl face and escape boundary

Reviewer: `SOCIAL_WEIGHT_REVIEW`  
Date: 2026-08-31  
Verdict: **REVISE**

## Claim reviewed

The note starts from one source-coherent four-profile sequence

\[
(R_n,Q_n,E_n,S_n)
\]

with a common observer response on the two horizontal response edges, observer
debt tending to zero at (R_n), and a uniformly positive alternating payoff
curl.  It claims an exact split into:

1. a stable-response arm, in which the same response remains asymptotically
   optimal against both opponent backgrounds while prescribed regret rises;
   or
2. an optimizer-switch arm, in which a positive fraction of the common
   response's stopping law is nearly optimal on the (E_n) background and is
   uniformly beaten on the (S_n) background.

It then refines the switch arm into bounded response-face witnesses or an
escaping stopping-time bubble.  I checked the identities, constants,
subsequence quantifiers, first-disagreement interpretation, and the exact
zero-minimum regression.  I also compared the conclusions with the existing
cap-switch/full-chord and response-switch notes.

The main reduction is correct.  One provenance sentence is too strong and
must be repaired: the pure-time decoder produces an edge between two
counterfactual pure-time profiles over the literal (S_n) opponent
background; its source endpoint is not generally the prescribed profile
(S_n).

## 1. The alternating-cap and debt identities are exact

Since (R_n) differs from (E_n) only in player (j)'s own complete
strategy,

\[
B_j(R_n)=B_j(E_n).
\]

The identical argument gives (B_j(Q_n)=B_j(S_n)).  Therefore the alternating
cap term is identically zero and

\[
\begin{aligned}
\mathcal C_n
 &= [U_j(R_n)-U_j(E_n)]-[U_j(Q_n)-U_j(S_n)]\\
 &=d_j(E_n)-d_j(R_n)-d_j(S_n)+d_j(Q_n).
\end{aligned}
\]

No cap continuity or optimizer selection is used here.  If
(d_j(Q_n)\to q), the (q=0) conclusion

\[
\liminf_n(d_j(E_n)-d_j(S_n))\ge\chi
\]

follows immediately from this identity, (mathcal C_n\ge\chi), and
(d_j(R_n)\to0).

## 2. The (q>0) localization and constant are correct

Let (mu_n) be the stopping law of the common response.  Pure-time
extremality and the stopping-law expectation formula give exactly

\[
\int (B_j(E_n)-V_n^E(t))\,d\mu_n(t)=d_j(R_n)
\]

and

\[
\int V_n^S(t)\,d\mu_n(t)=U_j(Q_n).
\]

For an (arepsilon_n)-optimal pure time (b_n) at (S_n), put

\[
e_n(t)=B_j(E_n)-V_n^E(t),\qquad
h_n(t)=V_n^S(b_n)-V_n^S(t).
\]

Then (e_n\ge0), its expectation tends to zero, and, on a sufficiently late
tail,

\[
\int h_n\,d\mu_n\ge q/3.
\]

With rewards bounded by (M), (|h_n|\le2M).  If the bad (e_n)-mass is
small enough, then

\[
q/3
 \le 2M\mu_n(A_n)+q/12+o(1),
\]

where (A_n=\{e_n\le\tau_n,,h_n\ge q/12\}).  This in fact eventually gives
(mu_n(A_n)\ge q/(12M)) after choosing the error tail tightly enough; the
stated safer bound (q/(24M)) is valid.

This is a genuine positive-mass **response-performance switch**: supported
pure times are asymptotically active against (E_n) and uniformly inferior
to (b_n) against (S_n).  It need not mean that a single exact pure-time
argmax is attained at either finite rank.

## 3. Required correction: the decoded edge does not start at (S_n)

For (t_n\in A_n), one has

\[
V_n^S(b_n)-V_n^S(t_n)\ge q/12.
\]

The checked theorem
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` may indeed be
applied with ambient/receiving profile (S_n), source witness (t_n), and
receiving witness (b_n).  It returns a row whose opponent root sequence is
the literal one from (S_n).

However, the actual payoff edge is

\[
S_n[j\leftarrow\operatorname{QuitAt}t_n]
 \longrightarrow
S_n[j\leftarrow\operatorname{QuitAt}b_n],
\]

not in general

\[
S_n\longrightarrow S_n[j\leftarrow\operatorname{QuitAt}b_n].
\]

The prescribed (j)-strategy in (S_n) is (c_n), and no hypothesis says
(c_n=\operatorname{QuitAt}t_n).  Thus the sentence saying that the decoder
gives an actual paid row "at the literal source (S_n)" is ambiguous in a
load-bearing way.  It is correct only if "at" means **over the literal
opponent background of (S_n)**.  It is false if it means that the row is a
unilateral edge out of the displayed prescribed profile (S_n).

This repair preserves source-table and opponent-background attachment, but it
does not preserve the prescribed source corner.  That distinction matters
for any later chronological or renewable-source consumer.

## 4. Bounded witness compactification is valid with the stated enrichment

After the usual diagonal subsequence split, if a fixed finite set carries a
uniform positive amount of (A_n)-mass, one fixed time (t) belongs to
(A_n) cofinally.  Then (e_n(t)\to0).  For finite (t), the value of
`QuitAt t` depends on finitely many roots.  For (t=\infty), one must retain
the relevant player-deleted law.  With those coordinates included, passage
to the limit gives the claimed active-face equality.

The notation (V^E(t)=B_j(e)) should not be read as a function of the bare
terminal semantic pair (e).  The left side is defined by the enriched root
or deleted-law cluster.  The note says this in prose; an eventual theorem
statement should expose the enrichment explicitly.

If (b_n) is also bounded, it freezes and gives the stated finite separation.
If exactly one witness escapes, the first-disagreement date is bounded, but
the continuing branch needs counterfactual/deleted-law data.  No finite-rank
descent follows.

For exact exhaustiveness, the phrase "a fixed finite set captures positive
mass cofinally" should mean a **uniform positive limsup**.  One then passes to
a subsequence on which every finite-set mass converges.  Either one such set
has positive limiting mass, or all its mass vanishes and the escape statement
follows.  This is a presentational quantifier repair, not a mathematical
obstruction.

## 5. The escaping-witness conclusions are correctly limited

On the escaping subsequence,

\[
\forall H,qquad
\liminf_n\mu_n(A_n\cap\{t>H\})\ge q/(24M).
\]

Hence every weak limit on the one-point compactification has (j)-Never mass
at least (q/(24M)).

For every selected (t\in A_n), the pure-time payoff difference is at least
(q/12).  The first-disagreement identity and the reward bound therefore
give opponent survival to the disagreement of at least (q/(24M)).  If
(b_n) also escapes, then for every fixed (H) the joint product stopping
law gives probability at least

\[
\left(q/(24M)\right)^2
\]

that player (j)'s common-response time is after (H) and all opponents
survive through (H).  Independence is legitimate here: before absorption
the live public history is unique and the four behavioral randomizations are
independent.  A common compactification therefore has positive all-player
Never mass.

The note correctly does **not** infer:

- positive Never mass in the date-forgetting terminal outcome law;
- two divergent quitting-hazard sums;
- a late opponent quit event when one witness is Never; or
- an executable terminal consumer.

For two finite witness times the payoff difference can localize opponent
absorption to their intervening window.  The finite/Never case cannot be
merged with it.

## 6. Stable arm and regression

The (kappa=1) table in
`CODEX_DESCENDANT__ASYMPTOTIC_PROJECTIVE_PASSPORT_AND_ROOT_BARRIER.md`
does realize

\[
d_3(R)=d_3(Q)=0,qquad d_3(S)=1,qquad d_3(E)=2,qquad \mathcal C=1,
\]

with Never optimal against both backgrounds and all Continue the unique
exact product root at the displayed first-corner cap.  The same table has an
all-Never equilibrium and global minimum debt zero.  It is therefore an exact
local regression, not a regression against a theorem using positive global
minimum provenance.

This supports the note's central fence: positive payoff curl and cap-root
uniqueness do not alone force optimizer switching or a clock.

## 7. Positive-minimum provenance and novelty

The optimizer/stable split, positive-mass localization, and timing escape use
no positive-minimum hypothesis.  Positive-minimum ancestry enters only in the
common-prefix reach estimate

\[
c_n\ge \theta D_*/\mathcal C_0.
\]

That estimate is correct provided the supplied descendant sequence really has
(mathcal C_n=c_n\mathcal C_0) and
(mathcal C_n\ge\theta D(R_n)\ge\theta D_*), as assumed.  It proves that the
original quartet is uniformly reached.  It does not orient the counterfactual
pure-time edge from Section 3 or exclude the stable arm.

The work overlaps substantially with:

- pure-time extremality and paid first-disagreement decoding;
- `TerminalSemanticCapSwitchFullChord`, which already turns a supplied
  cap-switch gap into a full-endpoint paid row and survival floor;
- the Jensen response-switch trace dichotomy; and
- `CODEX_RESPONSE_SWITCH__ADJACENT_REACTIVATION_CLOCK_OR_BUBBLE.md`, which
  already separates bounded response dates from a remote Never bubble under
  stronger iterative/source-coherence hypotheses.

The genuinely useful new contribution is the elementary but exact
(q=d_j(Q)) decomposition of the **common-response payoff curl**, together
with positive-mass localization inside the actual common-response law and
the explicit stable-response regression.  It is not a new cap-curvature
consumer, an active-face rank, or a Fin4 branch elimination.

## Required revisions

1. Replace the claim of a paid row "at the literal source (S_n)" by the
   exact statement that the decoder produces the pure-time edge
   (S_n[j\leftarrow t_n]\to S_n[j\leftarrow b_n]) over the literal
   (S_n{}_{-j}) background.
2. State the bounded/escaping subsequence split with a uniform limsup and a
   diagonal convergence of finite-set masses.
3. In any theorem-facing version, include the finite-root/deleted-law
   enrichment as data rather than writing (V^E(t)) as though it were
   determined by the bare semantic point.
4. Advertise positive-minimum provenance only for the uniform reach floor;
   it is not used by the local response split and does not consume either
   arm.

## Export recommendation

Do not export in its current form.  After the source-endpoint correction, the
note is a valid internal reduction and a useful diagnostic of the response
curl.  It still leaves both the stable-response and timing-bubble arms
unconsumed and overlaps existing response-switch machinery, so it is not by
itself a complete export packet.
