# Anchored erasure and finite clock rank send every pure Fin4 minimum to a paid port

Identity: `SOCIAL_WEIGHT_REVIEW`  
Date: 2026-08-31  
Status: **ordinary-mathematics proof draft; revised after independent review;
not Lean checked.**

## 1. Result

Let a Fin4 quitting game be in the positive hard-residual regime, and write

\[
D_*>0
\]

for the global minimum of complete terminal-semantic debt.  Let \(\sigma\)
be one actual profile in which every player uses one pure stopping time or
Never, with

\[
D(\operatorname{Sem}(\sigma))=D_*.
\]

Assume its earliest finite stopping date is \(t\), with no earlier positive
stopping probability, with exactly the nonempty coalition \(S\) Quitting
surely at \(t\), and every player outside \(S\) Continuing surely there.
Then a finite sequence of literal one-player pure-clock changes reaches an
actual off-minimum pure-time profile from an actual global minimum.  The last
minimum-to-target transition is either one anchored same-date endpoint change
or the exact response of a singleton owner.  The off-minimum target has an
outgoing complete behavioral response of gain strictly larger than
\(D_*/4\), realized by two pure times with a literal first disagreement.

Thus, after finite-clock purification, a pure horizontal strict-toggle cycle
is not a new terminal component.  It can be bypassed by an anchored erasure
face.  The apparent reset-rigid equality branch is consumed by the strictly
decreasing number of distinct finite prescribed stopping dates.  No
horizontal face is interpreted as chronological play.

## 2. The positive minimum is not all Never

Put \(s_i=r_i(\{i\})\).  At every global minimum the checked singleton moat
is

\[
B_i-s_i\ge D_*>0.                                      \tag{2.1}
\]

The all-Never profile cannot satisfy (2.1) with positive total debt.  Its
prescribed payoff is zero and its cap is \(\max\{0,s_i\}\).  If some
\(s_i\ge0\), then its cap-minus-singleton margin is zero; if every
\(s_i<0\), all Never is already an exact equilibrium and has zero debt.
Hence the assumed pure-time minimum has an earliest finite date \(t\).

## 3. Delete all but one anchored quitter

Fix any anchor \(b\in S\), enumerate

\[
S\setminus\{b\}=\{p_1,\ldots,p_m\},\qquad m\le3,
\]

and put

\[
S_k=S\setminus\{p_1,\ldots,p_k\}.
\]

Define \(\sigma^k\) by making exactly the players in \(S_k\) Quit at date
\(t\), making the deleted players Continue there, and retaining every
strategy literally at all other dates.  The anchor \(b\) Quits surely at
\(t\) in every profile, so every \(\sigma^k\) absorbs at \(t\), has terminal
coalition \(S_k\), and retains the complete post-date tail.  Consecutive
profiles differ only in player \(p_k\)'s date-\(t\) action.

Suppose \(\sigma^{k-1}\) is a global minimum.  Against its fixed opponents,
player \(p_k\)'s complete response values lie in the following three-element
set:

* Quit strictly before \(t\), when such a date exists, giving \(s_{p_k}\);
* Quit at \(t\), giving \(r_{p_k}(S_{k-1})\); and
* Continue at \(t\), giving \(r_{p_k}(S_k)\), because \(b\) still Quits.

Behavior after \(t\) is screened by \(b\).  If \(t=0\), the singleton value
is not attained and only the two marked-date endpoints remain.  If \(t>0\),
equation (2.1) says that the singleton value is strictly below the complete
cap.  Therefore in either case

\[
B_{p_k}
=\max\{r_{p_k}(S_{k-1}),r_{p_k}(S_k)\}.              \tag{3.1}
\]

The same cap applies at both adjacent profiles because only \(p_k\)'s own
strategy changes.  Hence the better of the two date-\(t\) endpoints is a
complete behavioral best response at the worse endpoint; equality makes
both endpoints cap-attaining.  This includes Never and arbitrarily late
behavior automatically, since \(b\)'s date-\(t\) Quit screens all of it.

Global minimality gives

\[
D(\operatorname{Sem}(\sigma^k))\ge D_*               \tag{3.2}
\]

for every \(k\).

## 4. The first strict face exit is a literal paid port

Let \(k\) be the first index for which

\[
D(\operatorname{Sem}(\sigma^k))>D_*.
\]

Then \(\sigma^{k-1}\) is an actual global minimum and \(\sigma^k\) is an
actual off-minimum profile.  Equation (3.1) orients their common endpoint
comparison exactly:

* if Continue is better, the minimum-to-off-minimum change is a complete
  best response;
* if Quit is better, the off-minimum-to-minimum reverse change is a complete
  best response; and
* if they tie, the two profiles are joined by a zero-gain complete best
  response in either direction.

In addition, choose a maximum-debt player \(h\) at \(\sigma^k\).  Since

\[
D(\operatorname{Sem}(\sigma^k))>D_*,
\]

one has

\[
d_h(\operatorname{Sem}(\sigma^k))
  \ge {D(\operatorname{Sem}(\sigma^k))\over4}
  > {D_*\over4}.                                      \tag{4.1}
\]

Against pure-time opponents the complete cap is attained by one pure date or
Never.  Since the prescribed strategy of \(h\) is itself a pure date or Never,
the source and the selected cap attainer have a literal first-disagreement
date whenever the gain is positive.  Replacing \(h\) by that response is an
actual unilateral behavioral edge of gain (4.1), with its literal
first-disagreement row.  This pure-time passport conclusion is asserted only
for this fully purified input; finite support of the opponents alone would
not make an arbitrary prescribed strategy pure.

Thus the strict face exit is not merely an unrelated off-minimum point: it
comes with a literal adjacent minimum sibling, an exactly oriented endpoint
comparison, the common post-date tail, and a fixed-gain paid response on the
off-minimum profile.

## 5. If the face stays minimum, use the singleton owner's exact response

Suppose no strict index exists.  Then every \(\sigma^k\) is a global minimum.
The last profile \(\sigma^m\) terminates in \(\{b\}\), so

\[
U_b(\sigma^m)=s_b.
\]

The singleton moat gives

\[
d_b(\sigma^m)=B_b(\sigma^m)-s_b\ge D_*.
\]

Since total debt is exactly \(D_*\), necessarily

\[
d_b(\sigma^m)=D_*,
\qquad
d_i(\sigma^m)=0\quad(i\ne b).                        \tag{5.1}
\]

Against the pure-time/Never opponents, player \(b\)'s complete cap is attained
at one pure date or Never.  Replace \(b\) by such a response and call the
literal target \(\rho\).  Its payoff gain is exactly \(D_*\).  Since only
\(b\)'s own strategy changes, its cap is unchanged, and hence

\[
d_b(\rho)=0.                                          \tag{5.2}
\]

Global minimality gives the exact split

\[
D(\operatorname{Sem}(\rho))>D_*
\quad\lor\quad
D(\operatorname{Sem}(\rho))=D_*.                    \tag{5.3}
\]

In the strict arm, \(\rho\) is an actual off-minimum target of a paid response
of gain \(D_*\).  As in Section 4, it also has an outgoing pure-time cap
response of gain strictly greater than \(D_*/4\).

In the equality arm, the joint semantic/law point of \(\rho\) is an attained
global minimum with zero \(b\)-debt.  The checked direct opponent-incidence
theorem gives positive total terminal incidence in opponents of \(b\) at this
same literal law.  Re-anchor the law-tight saturation construction with

\[
\text{origin}=\text{minimum}=\text{point}
  =\text{the literal joint target of }\rho.           \tag{5.4}
\]

Use the singleton pair \(\operatorname{Sem}(\sigma^m)\) as the retained source
of the killed owner debt.  The checked law-tight reset theorem then produces
a reset-rigid chamber on the exact target law.  Its returned same-law
semantic pair need not equal \(\operatorname{Sem}(\rho)\); only the chamber's
origin/minimum/point is identified with the literal response target.

The hard residual by itself does **not** eliminate this arm.  At a singleton
it supplies the disjunction

\[
\Gamma\le-r_b(\{b\})
\quad\lor\quad
\exists c\ne b,\quad
r_c(\{b,c\})\ge r_c(\{b\})+\Gamma.                  \tag{5.5}
\]

Only the collision arm would contradict (5.1) directly.  The refusal arm is
compatible with the retained tail and cannot be replaced by a same-date
collision argument.

## 6. The equality response strictly decreases finite clock rank

The reset-rigid re-anchor is sound, but it is not necessary to stop there.
The literal target \(\rho\) is still a pure-time/Never profile.  Let

\[
R(\tau)
=\left|\{s\in\mathbb N:\text{some player in }\tau
                   \text{ has pure stopping time }s\}\right|.       \tag{6.1}
\]

At the singleton source \(\sigma^m\), every opponent of \(b\) Continues
through \(t\).  Let \(u>t\) be their earliest finite stopping date, if one
exists, and let \(T\) be the corresponding nonempty opponent coalition.
Every pure response of \(b\) has one of only three values:

\[
\begin{array}{c|c}
\text{response time}&\text{payoff}\\ \hline
s<u&r_b(\{b\}),\\
s=u&r_b(T\cup\{b\}),\\
s>u\text{ or Never}&r_b(T).
\end{array}                                                   \tag{6.2}
\]

If no such \(u\) exists, the only non-singleton response value is the Never
payoff.  Since the chosen response gains \(D_*>0\), it cannot stop before
\(u\).  We may therefore choose the cap attainer to be Quit-at-\(u\) or
Never.  No new finite date is introduced, and the old earliest date \(t\)
disappears.  Hence every equality response satisfies

\[
R(\rho)<R(\sigma^m).                                  \tag{6.3}
\]

The preceding anchored erasures never introduce a finite date.  Consequently
the whole construction may be repeated at the new literal global minimum
\(\rho\), and every passage through the equality/reset-rigid arm strictly
decreases the natural-valued rank \(R\).  For four players, \(R\le4\).

Rank zero is the all-Never profile, which cannot be a positive global minimum
by Section 2.  Thus after at most four singleton-owner equality responses,
one of the strict off-minimum exits in Sections 4--5 must occur.  This is a
renewable finite rank on the actual pure profiles; it does not use the
reset-rigid returned same-law pair and does not serialize any horizontal
erasure face.

## 7. Consequence for finite-clock purification

The finite-clock purification theorem already gives

\[
\text{off-minimum paid response}
\quad\lor\quad
\text{an actual global minimum with every strategy pure-time/Never}. \tag{7.1}
\]

Apply Sections 2--6 to the second arm.  One obtains directly

\[
\boxed{
\text{finite-clock purification branch}
\Longrightarrow
\text{off-minimum paid port}.}                        \tag{7.2}
\]

Therefore the later max-debt recurrence and strict Boolean-cycle
classification are not needed to contract the fully purified branch to the
known off-minimum waist.  They remain useful finite descriptions, but not a
separate obligation class.

The off-minimum side of the exact remaining waist has two source-attached
entrances.

* At an erasure exit, an actual global-minimum sibling \(x\) and the actual
  off-minimum sibling \(y\) differ only in one player's action at the retained
  earliest date.  They have the same continuation after that date and an
  exact complete endpoint comparison across the horizontal seam.
* At a singleton-owner exit, \(x\) is the actual singleton minimum and \(y\)
  is obtained by replacing the owner's whole QuitAt-\(t\) clock by QuitAt-\(u\)
  or Never.  This edge is oriented toward \(y\) and has gain exactly \(D_*\),
  but it is not a one-date seam.

In both cases \(y\) has an outgoing pure-time best response of gain strictly
larger than \(D_*/4\), with a literal first-disagreement date.  The first
entrance additionally retains the common post-date tail; the second retains
the complete pure-time clock replacement instead.

What is still missing is a consumer turning this object into a charged exact
chronology, a renewable well-founded child, or a uniform-equilibrium payoff.
The present theorem consumes the pure equality/reset-rigid branch, but not
the resulting off-minimum paid port.

## 8. Exact boundary and nonclaims

1. The anchor is essential.  Removing the last sure quitter would expose the
   continuation and invalidate the two-endpoint cap identity (3.1).
2. Positive global minimality is essential twice: it excludes the singleton
   option from the cap at every retained minimum sibling and prevents any
   face profile from lying below \(D_*\).
3. The sequence \(\sigma^0,\ldots,\sigma^m\) is a literal common-tail face,
   not a directed chronology.  Only each adjacent comparison is oriented as
   one complete unilateral best response at its worse endpoint.
4. The result does not consume the off-minimum paid port.  It eliminates the
   pure-cycle and pure reset-equality branches as separate components by
   sending them to that existing open waist.
5. A source wrapper must retain the selected minimum sibling at the first
   strict exit.  It must not claim that the entire erasure list is a forward
   best-response path.

6. The clock-rank step uses the literal pure-time target, not the possibly
   different same-law pair returned by the reset-rigid chamber.

## 9. Narrow formalization targets

The reusable mathematical declarations should express:

```text
pureMinimum_anchorErase_cap_eq_max_adjacentEndpoints
pureMinimum_anchorErase_firstOffMinimum_paidPort
pureMinimum_anchorErase_singleton_ownerResponse_split
pureMinimum_anchorErase_equalityTarget_resetRigid
pureMinimum_ownerEqualityResponse_clockRank_lt
finiteClockMinimum_offMinimumPaidPort
```

The first lemma is game-independent for any finite player type.  The
\(D_*/4\) gain, direct opponent-incidence conclusion, and reset-rigid chamber
are the Fin4 specializations.

## 10. Sources inspected

The proof uses the checked global-minimum singleton moat, finite-clock
pure-time cap attainment and first-disagreement decoder, the direct positive
opponent-incidence theorem at a zero-debt minimum coordinate, and the
law-tight reset-rigid chamber theorem.  The reviewed finite-clock
purification entrance is Proposition 9.3 of
`CODEX_SINGLETON_SOURCE__ONE_SURE_OWNER_EXACT_RESPONSE_HANDOFF.md`.  The
relevant checked declarations are
`totalOpponentIncidence_pos_of_minimumLaw_of_debt_eq_zero`,
`quittingLawTightCapNashSaturationHull_origin_mem`, and
`exists_quittingLawTightResetRigidChamber`.  Equation (5.5) is the exact
hard-residual singleton disjunction
`QuittingTerminalExploitabilityWitness.singleton_refusal_or_exists_collision_gain`.

The narrow search found pure nonsingleton routing, profitable selected
singleton routes, and persistent-base induced-Nash compilers, but no theorem
performing this fixed-anchor deletion through the minimum face or using the
first strict face exit as the paid-port handoff.
