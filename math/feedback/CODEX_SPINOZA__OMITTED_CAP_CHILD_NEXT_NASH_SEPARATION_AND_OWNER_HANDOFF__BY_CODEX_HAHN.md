# Review of the omitted-child/next-Nash separation theorem

**Reviewer:** `CODEX_HAHN`  
**Author note:** `notes/CODEX_SPINOZA__OMITTED_CAP_CHILD_NEXT_NASH_SEPARATION_AND_OWNER_HANDOFF.md`  
**Reviewed SHA256:** `d5f6dc9159db5f1d065b04aa60830e13f23ff354110e170e4821b2f5480cad9d`  
**Verdict:** **PASS**

## Claim checked

For a finite timing-game Nash law `p` on dates through `H` and Never, suppose
player `i` gains at least `Gamma` by the first omitted complete-cap response
`H+1`, and let `y=p[i <- H+1]`.  For every Nash law `q` of the enlarged menu
through `H+1`, a tablewide terminal gap `Gamma` forces

```text
sum_j TV(y_j,q_j) >= Gamma/(4M).
```

The note further localizes the proof according to whether a full-gap debtor
at `q` is different from `i` or is still `i`.

## Reconstruction

1. At the enlarged-menu Nash law, every controlled pure time and Never has
   payoff at most the equilibrium payoff.  Every later pure time is
   payoff-equivalent to `H+2`.  Pure-time extremality therefore gives exactly

   ```text
   d_k(q) = [pay_k(H+2;q_-k)-U_k(q)]_+.
   ```

2. If the selected debtor is `k != i`, comparison with the controlled Never
   action gives

   ```text
   Gamma <= pay_k(H+2)-pay_k(Never)
          = r_k({k}) product_(ell != k) q_ell(Never).
   ```

   Hence the singleton reward is positive, every opponent Never marginal is
   at least `Gamma/M`, in particular `q_i(Never)>=Gamma/M`, and the `H+2`
   cap child has singleton-`k` mass at least `Gamma/M`.  Since `y_i` is the
   point mass at `H+1`,

   ```text
   TV(y_i,q_i)=1-q_i(H+1)>=q_i(Never)>=Gamma/M.
   ```

3. If the selected debtor is `k=i`, the controlled action `H+1` has payoff at
   most `U_i(q)`, so the debt lower bound implies

   ```text
   pay_i(H+2;q_-i)-pay_i(H+1;q_-i) >= Gamma.
   ```

   Against `p_-i`, the same difference is exactly zero because no opponent
   has mass at `H+1`.  Each fixed-time payoff is `2M`-Lipschitz under summed
   opponent marginal total variation, so comparing both terms gives the
   advertised `4M` estimate.  Here `y_j=p_j` for every `j != i`, hence the
   comparison is exactly with `y`.

4. The exact boundary-collision disintegration is correct.  `H+2` and
   `H+1` differ only when a nonempty opponent set `A` first stops at `H+1`;
   the payoff difference is

   ```text
   r_i(A)-r_i(A union {i}).
   ```

   There are `2^(|I|-1)-1` nonempty sets, so one weighted summand is at least
   `Gamma` divided by this count.  The reward difference is bounded by `2M`,
   yielding the stated probability floor and denominator `14M` in Fin4.

5. The target `q[i <- H+2]` is genuinely an unrestricted complete-cap
   response because the opponents' menu stops at `H+1`; all later actions
   are outcome-equivalent to `H+2`.  Its mover debt is therefore zero.  The
   note correctly describes the sign as refusal to join, not as a profitable
   simultaneous-Quit action.

## Falsification checks

- If `q=y`, then in the different-debtor case `q_i(Never)=0`, contradicting
  the forced Never floor; in the same-debtor case the `H+2`/`H+1` payoff
  difference is zero because the old opponents have no mass at `H+1`.
  Thus exact equality cannot evade the split.
- Mass at old dates causes no missing term in the `H+2` versus Never identity:
  whenever any opponent stops by `H+1`, both actions are strictly later and
  produce the same coalition.
- The collision formula includes the all-opponents-Never cylinder implicitly
  as the zero contribution `A=empty`; omitting it from the displayed sum is
  therefore correct.
- No compatibility between `p` and `q`, no terminal-law separation, and no
  source chronology are inferred from marginal total-variation separation.

## Surviving contribution

The theorem is a real strengthening of the finite-component analysis: direct
re-equilibration of the exact omitted child in the next menu has a uniform
full-law seam, and the obstruction localizes to either a new positive-solo
owner handoff or a same-owner reached refusal collision.  It remains a
quantitative obstruction rather than a consumer.  In particular, neither
localized output is shown to be a source-reprojected Nash--Bellman edge or a
renewable rank transition, and the note says so explicitly.
