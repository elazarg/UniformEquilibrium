# Independent check of the all-player MAX tie proof

Reviewer: `CODEX_FRECHET_CYCLE`.

Verdict: **PASS of the complete frozen ordinary-mathematics proof.** No
mathematical objection found. This is not a Lean-checked designation or an
export decision.

The full 204-line submission
`notes/CODEX_HILBERT__GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES.md` was read
before recording this verdict, at SHA-256

```text
42cf56a4a354823a3a17e379715dac61bd6c1ccd62aeb277bb32b99844a06166.
```

No other review of that submission was read. My related lowered-root
research supplied independent context, but the calculation below checks
this author's different slack-aware solo-prefix mechanism.

## Claims checked

For bounded rewards, if `U≥s`, all debts are at most `m>0`, and one
coordinate k has slack `ζ=m−d_k>0`, a new initial solo-k Quit hazard

```text
h=min(ζ/(4M),m/(16M))
```

reduces the full maximum regret to at most `(1−h)m`. For a canonical
global geometric-repair optimizer, this gives the stated N+1 comparison,
including the relaxed α=0<λ boundary. At every positive unrestricted
maximum-debt carrier minimum, every player's debt therefore equals the
maximum. The last statement is not asserted for arbitrary finite m_N
optimizers.

## Independent calculation and falsification checks

The new prefix has exact own-coordinate formulas
`U′_k=hs_k+(1−h)U_k` and `B′_k=max(s_k,B_k)`. For a nonowner j its
complete cap is the maximum of immediate Quit and Continue followed by a
full old response. Subtracting prescribed payoff yields exactly

```text
d′_k=d_k+h(U_k−s_k),
d′_j=max((1−h)(s_j−U_j)+h[r_j({k,j})−r_j({k})],
          (1−h)d_j).
```

This includes all finite-date and Never deviations. It needs neither cap
attainment nor conditioning on a positive-reach event. In particular the
immediate-Quit branch, which could invalidate an old-active-cap-only
argument, is explicitly retained and bounded by `2Mh`.

The constants check: `h≤1/8`, `2Mh≤ζ/2`, and `hm≤ζ/2`, so the owner
is at most `m−hm`. Also `2Mh≤m/8≤(1−h)m`, which bounds both nonowner
branches. Equality and zero-hazard cases do not create a missing branch;
ζ>0 and m>0 make h positive.

Literal prefixing shifts every old nonpivot date by one and adds only
date zero for a selected nonpivot. The pivot's shifted and possibly scaled
tail remains geometric at cutoff N+1. This works at N=0 and when the
selected player is the pivot. Positive-α implementations preserve U and
increase each relaxed debt by at most ε; the same fixed k and h then give
the competitor with an additional ε at the same N+1. Taking ε to zero
proves the value comparison without assigning a law to α=0<λ.

For the unrestricted theorem, the existing
`minimumTerminalSemantic_exploitabilitySingletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`
does give `B_i−s_i≥m`, hence `U_i≥s_i`. The fixed-root prefix is a
continuous carrier-preserving operation. Thus any strict debt slack
would give a carrier point below the global minimum by the calculation
above, even when the original pair is not attained by an actual profile.

The finite-to-unrestricted limit comparison is also correctly scoped:
censoring only late finite nonpivot mass has vanishing total variation,
and geometric compression preserves payoffs while weakly decreasing
caps. This proves convergence of the global values; it does not identify
each finite optimizer with an unrestricted minimizer.

## Limits retained

At an all-tied pair the moved owner's debt rises by `h(U_k−s_k)`, so the
same solo-prefix estimate does not consume that region. No improving
survival-preserving swap, new equilibrium tail, or full-conjecture result
is inferred. The source comparison correctly separates maximum-debt and
total-debt minima. These limitations are substantive and are preserved
in the frozen statement.
