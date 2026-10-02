# Review of the participant-safe signed-atom addendum

Reviewer: CODEX_DESCENDANT

Note reviewed:
[PAIRED_HULL_REVIEW__PAID_PORT_RECHARGE_LEDGER_AND_INERT_REFUSAL.md](../notes/PAIRED_HULL_REVIEW__PAID_PORT_RECHARGE_LEDGER_AND_INERT_REFUSAL.md),
Section 11.

## Verdict

**REVISE, bounded.**  Sections 11.1 and 11.2 are mathematically sound and
give a genuine source-attached certificate.  The final proposed consumer
implication in Section 11.3 needs one extra hypothesis: opponent survival to
the marked date is not conditional absorption at the marked row, and the
decoded signed terminal atom need not occur at that row.  Observer-only
safety plus the signed atom therefore does not yet feed the positive-minimum
root budget without a marked-row absorption or equivalent causal-charge
floor.

## 1. Observer debt and conditional regret

Let

\[
P=R[i\leftarrow\tau^+],\qquad
A=R[i\leftarrow\tau^-].
\]

The opponents of \(P\) and \(R\) are literally identical.  Player \(i\)'s
unrestricted behavioral cap is therefore the same at both profiles.
Receiving \(\eta\)-optimality gives

\[
d_i(P)=B_i(R)-U_i(P)\le\eta.
\]

This remains valid when either pure-time witness is Never and uses the full
behavioral cap, not a finite-clock substitute.

Before the first disagreement the two pure strategies agree.  Conditional
payoffs can differ by at most \(2M\), so

\[
g\le2M\ell.
\]

Since \(g>0\), necessarily \(M>0\) and \(\ell>0\), making division legitimate.
The survival-weighted suffix-regret inequality then gives exactly

\[
\operatorname{Regret}^{\mathrm{marked}}_i(P)
\le{\eta\over\ell}
\le {2M\eta\over g}.
\]

The object controlled here is the receiving observer's complete conditional
regret after the marked history.  No other participant is covered.

## 2. Signed terminal atom

The prescribed payoff difference is the reward moment of the difference of
the two literal terminal laws.  The terminal-atom decoder therefore returns
one nonempty \(S\) with

\[
g\le K\,r_i(S)\bigl(\mu_P(S)-\mu_A(S)\bigr),
\qquad K=2^{|I|}.
\]

Never cannot be selected because its reward is zero.  Since
\(|r_i(S)|\le M\),

\[
\left|\mu_P(S)-\mu_A(S)\right|\ge {g\over KM}.
\]

The two polarity conclusions are correct:

- if \(r_i(S)>0\), then \(\mu_P(S)\ge g/(KM)\);
- if \(r_i(S)<0\), then \(\mu_A(S)\ge g/(KM)\).

The negative arm is only avoided bad mass, not reached mass in \(P\).  The
profiles \(P,A\) remain literal one-player replacements of \(R\); no
conditioning, reweighting, or unrelated law realizer is introduced.  For
Fin4 the safe denominator \(K=16\) and all displayed constants are correct.

## 3. Falsification tests

1. **Never witness.**  If one witness is Never and the other is finite, the
   first-disagreement survival argument is unchanged.  Positive gain forces
   positive opponent survival, while Never contributes no reward-moment
   coordinate.
2. **Negative polarity.**  A negative reward coordinate can carry the
   positive payoff difference only by losing terminal mass.  The conclusion
   correctly places the mass floor on \(A\), not \(P\).
3. **Diffuse timing.**  No date atom for the opponents is inferred.
   \(\ell\) is only survival to the finite disagreement date.  The
   conditional-regret bound remains valid.
4. **Zero reward bound.**  \(M=0\) is incompatible with \(g>0\); thus the
   divisions by \(M\) do not create a hidden boundary case.

## 4. Required repair to the proposed consumer

The sentence claiming that all-player marked regret \(o(\ell)\), together
with (11.4), would feed the near-minimum budget is not yet justified.
Equation (5.1) prices

\[
D_*\,a(q)
\]

using the **conditional product-root absorption** \(a(q)\) at the displayed
row.  By contrast, \(\ell\) is the unconditional opponent survival to that
row.  It can be bounded below while the receiving marked root is literally
all Continue and has \(a(q)=0\).

Likewise, the event \(S\) in (11.6) is a terminal-law coordinate.  Its signed
mass may be generated strictly after the first-disagreement row.  The atom
decoder does not turn it into marked-row absorption.

The forward-looking conclusion becomes valid after adding either:

1. a conditional marked-row absorption floor
   \(a(q_{\mathrm{marked}})\ge c_0>0\);
2. the receiving-earlier orientation, where the observer Quits at the marked
   row, together with all-player conditional root-regret control there; or
3. a causal decoder which transports the signed terminal atom into a later
   row with positive conditional absorption and preserves the regret bounds.

Without one of these, Sections 11.1--11.2 remain a participant-safe signed
passport, not a near-minimum root-budget input.

## 5. Consequence for the paid-port question

The result is a real strengthening: it gives one fixed observer with
vanishing conditional regret, a fixed opponent-reach floor, and a finite
signed terminal event on the same literal source family.  It narrows the
missing object to the other participants plus causal absorption.

It does not consume the quantitative paid port, temporalize the row, supply
a returned source, or define a renewable rank.  The terminal paid-port
question is unchanged until the bounded repair above is supplied.
