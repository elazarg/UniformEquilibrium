# Review of the linked-sibling barrier/capacity criterion

Reviewer: `CODEX_GROMOV`

Reviewed frozen SHA-256:
`966f9159275f795926b0ab2ca3fdce98613ab864c88351c0cf614a315db906b0`.

## Verdict

**REVISE (core conditional theorem passes; the audit overstates the number of
missing source estimates).**

Theorem 2.1 and its summable-error variant are correct.  With
`Psi = Phi + lambda Q`, (2) and (7) give the displayed vertical decrement,
(8) makes the horizontal increment nonpositive, and boundedness below of
`Psi` makes the phase charges summable.  The signs in (11)--(15) and the
telescope are correct.  The two-state abstract regression also correctly
shows that a positive level floor for `Q` cannot substitute for a signed
horizontal comparison.

## Substantive correction

For the renewed application actually discussed in the note, the vertical
leakage bound (7) is automatic once the already supplied uniform charge floor

\[
 A_m\ge a_0>0
\]

and boundedness of `Q` are used.  If `osc(Q)` denotes any uniform bound for
`Q(p)-Q(s)` on the relevant state space and `osc(Q)>0`, choose for example

\[
 \theta=\frac12,
 \qquad
 \lambda=\frac{a_0}{2\,\operatorname{osc}(Q)}.
\]

Then Bellman monotonicity and boundedness give

\[
 \lambda\bigl(Q(p_m)-Q(s_m)\bigr)
 \le \frac{a_0}{2}
 \le \frac{A_m}{2}.
\]

If `osc(Q)=0`, (7) holds for every positive `lambda` with `theta=0`.
Thus the collar is not needed for this estimate, and the sentence in Section
4 saying that the fixed absorption/debt expenditure does not imply (7) is
false in the fixed-charge renewal regime.  It would be correct only for the
more general theorem where `A_m` may tend to zero.

The genuine missing source inequality is therefore just the horizontal
linked-sibling estimate (8), after choosing a sufficiently small fixed
`lambda` as above.  This makes the reduction sharper, though it does not
provide (8).

## Collar check

The off-minimum collar supplies no evident route to (8).  Its exact root
controls the vertical drop in total debt and gives `A_m >= a_0`; as just
observed this is enough for (7).  The cap installation is a horizontal
complete-strategy replacement between common-tail siblings.  The collar
fixes a cap coordinate and separates the entire installation segment from
the global minimum fibre, but neither `Phi` nor `Q` is a function of that
coordinate or of total debt alone.  The deterministic cap child is a
universal-prefix descendant only for the first stationary source.  After
renewal the parent and child are merely sibling prefixes, so universal-prefix
monotonicity gives `Q(z_m) <= Q(p_m), Q(s_(m+1))` and no signed sibling
difference.  Hence no displayed collar statement implies (8).

## Scope

The theorem remains a conditional scalarization, not a Fin4 consumer.  The
abstract regression is not a quitting-game realization and should retain
that qualification.  After the correction above, the exact falsifiable
target should emphasize (20) alone in the uniform-charge application; (19)
is bookkeeping already supplied by boundedness and the charge floor.

## Delta review of the repaired version

Reviewed exact SHA-256
`7324d9c85fe7ad4663895eec3c4597d80ad1218576074b90da77b8f1bb3a83e7`.

**PASS.**  The note now makes the vertical estimate automatic and leaves only
the horizontal linked-sibling inequality.  The choice
`lambda = a_0 / (2 B_Q)` when `B_Q > 0` gives
`lambda (Q(p_m)-Q(s_m)) <= a_0/2 <= A_m/2`; when `B_Q=0`, the difference is
zero and `lambda=1` is valid.  The signs in the `Psi = Phi + lambda Q`
telescope and the summable-error estimate are unchanged and correct.  The
collar audit now states exactly what it supplies and does not promote the
conditional criterion to a Fin4 consumer.
