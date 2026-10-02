# Review of finite cap-child barrier ancestry and flatness

Reviewer: `CODEX_HAHN`

Reviewed SHA-256:
`1e53b6b85cfa7d7fdaf2749418d8b9c713d6ec69498dd63c804c32dac86e99f6`.

## Verdict

**PASS.**  The sibling-prefix identities, the one-step stationary barrier
monotonicity, and the strictness regression are mathematically correct.  The
note does not overstate their use in the renewed nonstationary construction.

## Claim checked

If player `k` is changed to deterministic Quit at a finite date `T`, the
actual parent and cap child are two finite prefix words over the same literal
post-`T` tail.  This gives only a common lower bound for the target-free word
barrier.  When the parent is stationary, the common tail is the parent itself,
so the cap child is its universal-prefix descendant and its barrier value is
weakly larger.  A positive cap gain need not make that inequality strict.

## Mathematical audit

The complete-semantic sibling identity is valid, including unrestricted
behavioral caps.  For an outsider, player `k`'s sure Quit at date `T` screens
the later tail under every unilateral outsider deviation.  For player `k`,
the only deviation that can reach beyond `T` faces exactly the opponents in
the shifted parent tail; player `k`'s own prescribed post-`T` behavior does
not enter its cap.  Thus both cap coordinates and prescribed payoffs are
computed by the displayed prefix words over the same shifted semantic tail.

For `Q(z)=inf_a d(T_a z)`, the descendants of a finite prefix descendant form
a subset of the descendants available from `z`.  Hence `Q(z) <= Q(T_w z)`.
Stationarity identifies the shifted tail with the parent semantic pair and
gives exactly the orientation in (4).  Without stationarity, common-tail
siblinghood gives no ordering between the two children, exactly as stated.

The four-player regression is correct.  At all Never, player 0 has cap one
and gain one from Quit0.  After installing Quit0, player 0 receives its global
maximum one and every outsider is screened with both payoff and cap zero, so
the child has zero debt.  Since that child is itself a one-root universal
prefix of all Never, both barrier values are zero.  This refutes a strict
gain-to-barrier modulus from the local hypotheses, while correctly making no
claim about the positive-minimum hard residual.

## Scope

The result covers only finite deterministic cap clocks.  It does not compare
nonstationary sibling barriers, does not treat a Never cap witness as a finite
word, and does not turn weak barrier monotonicity into an admissible charged
chronology or a renewable rank.  Those limitations are explicit in the note.
