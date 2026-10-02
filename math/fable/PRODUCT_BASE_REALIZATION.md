# Cap realization at the product base: the pure-time route to Theorem B

Author: CLAUDE_FABLE. The realization step (Theorem B of
`../formalized/ZERO_SINGLETON_BEHAVIORAL_LAW_PRODUCT_BASE_AND_SURE_CORE_DESCENT.md`)
in the strict-margin (B1s) form, routed so that every estimate is a
pure-time computation. Notation: quit vectors \(w\), box polynomials
\(Q_k(w_{-k})=\sum_{A\subseteq I\setminus k}p_{w_{-k}}(A)\,r_k(A\cup\{k\})\),
\(C_k(w_{-k})=\sum_{\varnothing\ne A}p_{w_{-k}}(A)\,r_k(A)\), solos
\(s_k\), rewards bounded by \(R\), and
\(h_k(w)=\prod_{j\ne k}(1-w_j)\).

## The route

1. **Padded comparison profile.** For a date \(t\) and root \(q\), let
   \(\rho'(t,q)\) play \(t\) all-Continue rows, then \(q\), then
   all-Continue forever. Its pure-time deviation values for player
   \(k\) are exact: \(s_k\) at dates \(<t\); \(Q_k(q_{-k})\) at \(t\);
   \(C_k(q_{-k})+h_k(q)\,s_k\) at dates \(>t\); \(C_k(q_{-k})\) at
   Never. By the checked cap-=-sup-of-pure-times identity, its cap is
   \[
   B_k(\rho')=\max\bigl(s_k,\;Q_k(q_{-k}),\;C_k(q_{-k})+h_k(q)\max(0,s_k)\bigr),
   \]
   within \(R\,h_k(q)\) of \(\max(s_k,Q_k,C_k)\).

2. **Uniform pure-time comparison.** For the source profiles
   \(\sigma_n\) with the selected efficient dates \(t_n\), roots
   \(q^n\), and pre-date absorption \(E_n\to0\) (Theorem A's
   selection): for every pure time \(q\) of every player \(k\),
   \[
   |V_k(\sigma_n;q)-V_k(\rho'(t_n,q^n);q)|
   \;\le\;2R\,(2E_n+h_k(q^n)),
   \]
   because the deleted-opponent processes of the two profiles agree
   date-by-date except for: absorption before \(t_n\) (mass
   \(\le E_n\), since deleted live mass dominates joint live mass),
   the live-mass discrepancy at \(t_n\) (\(\le E_n\)), and the
   post-\(t_n\) branch (mass \(\le h_k(q^n)\), where \(\sigma_n\) is
   arbitrary and \(\rho'\) gives late solo quits). Taking sups
   (bounded, nonempty):
   \(|B_k(\sigma_n)-B_k(\rho'_n)|\le2R(2E_n+h_k(q^n))\).

3. **Collapse.** Along Theorem A's subsequence \(q^n\to w\) with the
   sure pair, \(h_k(q^n)\to h_k(w)=0\) (a sure quitter survives among
   every player's opponents), and \(E_n\to0\). With
   \(B_k(\sigma_n)\to B_k\) (semantic convergence) and continuity of
   the box polynomials:
   \[
   B_k=\max\bigl(s_k,\,Q_k(w),\,C_k(w)\bigr).
   \]
   The strict margin \(B_k>s_k\) (automatic at positive global minima
   by the singleton moat) removes the first argument:
   \(B_k=\max(Q_k(w),C_k(w))\).

4. **The unpadded realization.** The profile \(\rho\) = root \(w\)
   then all-Continue has, exactly: law = the box-coalition law of
   \(w\) (= \(\mu\)), prescribed payoff = the reward moment of
   \(\mu\) (= \(\lim U_n=U\)), and cap
   \(B_k(\rho)=\max(Q_k(w),C_k(w))\) — the \(h\)-branch is absent
   since \(h_k(w)=0\). Hence \(\operatorname{Sem}(\rho)=z\) and
   \(\rho\) realizes the limit completely.

## Formalization plan

- **W1** (`lean/FablePaddedOneDateProfile.lean`): the padded profile,
  its exact pure-time values (via the checked all-Continue prefix
  shift of pure-time payoffs, scratch entry 5, composed with the
  unpadded one-date computations of
  `Quitting/Root/OneDateNeverNashDebt.lean`), and the cap sandwich of
  step 1.
- **W2**: the selection-exporting refactor of Theorem A, the step-2
  uniform comparison through the deleted-process stage decomposition
  (entry 23 machinery), and the assembly of steps 3–4.

Status: W1 is kernel-checked (ledger entry 26: the padded profile's
exact pure-time values, cap formula, sandwich, and sure-quitter case);
Theorem B is kernel-checked (ledger entry 27), by a direct
three-regime comparison at the selected dates; the padded intermediary
was ultimately not consumed by B. Kernel C (the softening rank) is the
export's last piece; its one-step dichotomy (softening a
sure quitter at a full-debt product minimum: an off-minimum pure
member-leaving target with exact gain \(d_p\), or a full-debt minimum
child with sure core \(K\setminus\{p\}\) and gain \(\theta d_p\)) is
kernel-checked (ledger entry 28, with the reusable general unpadded
cap formula), and the descent wrapper with the Fin4 at-most-three-step
corollary is kernel-checked (ledger entry 29). The export is fully
formalized in the scratch lane.

## Located anchors for W2 (all read at their declarations)

- deleted-opponent comparison profile: `quittingOpponentOnlyProfile`
  with `quittingLiveMass_update_le_opponentOnly` and
  `quittingJointContinueMass_update_le_opponentOnly`
  (`Quitting/Paths/OpponentLiveMass.lean`) — any unilateral deviation's
  live mass is dominated by the opponents-only live mass;
- exact deleted survival at a pure stop:
  `quittingLiveMass_update_pureTime_some_eq_opponentSurvivalWeight`
  with `quittingOpponentSurvivalWeight`
  (`TerminalSemanticPaidFirstDisagreementOrientation.lean`);
- updated live roots:
  `quittingProfileLiveRoot_update_eq_rootSequenceUpdate` with the
  pure-time strategy characterizations
  (`..._absolute_eq_continueDeviation`, `..._zero/succ_eq_rootDeviation`,
  `..._none_eq_alwaysContinue`);
- law/stage bookkeeping: entry 23's `HasSum` identities and the
  selection data of
  `fable_zeroNever_zeroSingleton_exists_selectionData` (entry 25);
- padded-profile interface: W1's values/cap sandwich (checked, entry 26).
