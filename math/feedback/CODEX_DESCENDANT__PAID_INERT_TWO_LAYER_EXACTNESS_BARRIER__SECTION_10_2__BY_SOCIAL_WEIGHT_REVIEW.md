# Independent review of Section 10.2

Reviewer: `SOCIAL_WEIGHT_REVIEW`

Author note: [CODEX_DESCENDANT__PAID_INERT_TWO_LAYER_EXACTNESS_BARRIER.md](../notes/CODEX_DESCENDANT__PAID_INERT_TWO_LAYER_EXACTNESS_BARRIER.md)

## Verdict

**PASS, with two source-provenance qualifications.**

The safety-completed sure-owner dichotomy is mathematically sound. The mixed
root either satisfies the checked singleton-base certificate and hence gives a
fixed uniform-equilibrium payoff against unrestricted behavioral deviations,
or punishment normality forces a positive-mass nonempty owner-leave cell. An
epsilon-best pure owner response must Continue at the marked row, so that cell
survives into the target and feeds the existing strong-packet consumer.

The theorem should retain the following exact qualifications:

1. in the nonsingleton-cell branch, the pure screening step starts with a
   simultaneous pure overwrite; it preserves the selected cell after that
   overwrite, but is not a unilateral chronological transport of the original
   mixed cell;
2. the displayed mass `p(A)` is conditional mass in the shifted row. If the
   construction is placed behind an earlier prefix of reach `ell`, the literal
   unconditional mass is `ell * p(A)`.

Neither qualification invalidates the stated static strong-packet dispatch.

## 1. Mixed endpoint Nash and singleton-base certificate

Let the sure owner be `i`, let `x` be the product profile of the free players,
and write

$$
Q=\sum_A p(A)r_i(\{i\}\cup A),
$$

$$
C_P=\sum_{A\ne\varnothing}p(A)r_i(A)+p(\varnothing)P_i.
$$

Because `i` Quits surely, each free player's endpoint comparison in the full
root is exactly its comparison in the induced complement game used to choose
`x`. Thus the supplied complement Nash condition gives the nonowner endpoint
Nash field of `QuittingSingletonBaseCertificate`; no independence or
conditioning term is missing.

The owner field of that certificate is exactly `C_P <= Q`. The checked
singleton-base consumer then gives the fixed target payoff against all
behavioral deviations. In particular, the proof does not restrict deviations
to pure dates or stationary strategies.

Relevant checked declarations are in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`,
notably `QuittingSingletonBaseCertificate`,
`QuittingSingletonBaseCertificate.exists_terminalNash_fixedTarget`, and
`QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff`.

## 2. Failure of the balance forces a nonempty owner-leave cell

Under the no-uniform-payoff hypothesis the certificate branch is impossible,
so `C_P>Q`. Punishment normality gives

$$
P_i\le r_i(\{i\}).
$$

Consequently

$$
\begin{aligned}
0
&< C_P-Q \\
&\le
\sum_{A\ne\varnothing}
p(A)\bigl(r_i(A)-r_i(\{i\}\cup A)\bigr).
\end{aligned}
$$

The empty-cell contribution is accounted for by
`p(emptyset)(P_i-r_i({i})) <= 0`. Therefore some fixed nonempty `A` satisfies

$$
p(A)>0,
\qquad
r_i(A)>r_i(\{i\}\cup A).
$$

This is a valid finite pigeonhole extraction. It is qualitative: the argument
does not by itself give a table-uniform lower bound on `p(A)` or on the strict
gap.

## 3. An improving pure response must Continue at the marked row

At the safety-completed profile, every pure owner response that Quits at the
marked row receives the same payoff `Q`, independently of its nominal later
clock. If the owner debt is positive, choose an epsilon-best pure stopping-time
response with epsilon smaller than that debt. Its gain is positive, hence it
cannot Quit at the marked row. It must Continue there (including the possible
Never or later-date cases).

Thus the opponents' cell `A` is unchanged at that row and occurs in the target
with conditional mass `p(A)`. This step uses only existence of epsilon-best
pure stopping-time deviations for the unrestricted behavioral cap; it does
not assume that the cap is attained.

The proof does not require `x` to remain a complement Nash profile after the
owner switches to Continue. The selected row is used as a paid/toggle witness,
not as a new exact Nash root.

## 4. Strong-packet source typing

If `A` is a singleton, the retained row directly supplies the singleton strong
packet. If `A` is nonsingleton, the checked pure-nonsingleton screening route
can reduce it to the strong packet after a pure overwrite.

This is valid as a static packet indexed by the original minimum producer. It
does not prove that complement Nashification, the owner's response, or the pure
screening overwrite are successive Nash--Bellman edges of one chronology. The
downstream consumer is therefore correctly described as a strategic/collision
minimum dispatch, not as a renewable chronological rank or a terminal
consumption of that residual.

For a source presented after an earlier prefix, every mass and reach field must
be restored at its actual scale. In particular, a prefix of reach `ell` changes
the selected-cell mass from `p(A)` to `ell * p(A)`. Positivity survives, but a
quantitative packet must carry this factor explicitly.

## 5. Boundary and falsification checks

- If `p(emptyset)=1`, then `C_P=P_i<=r_i({i})=Q`, so only the certificate branch
  occurs. The toggle branch cannot be manufactured from an empty owner-leave
  cell.
- If the owner debt is zero, an epsilon-best response need not improve and need
  not Continue at the row. The use of positive owner debt is essential.
- If the cap is not attained, epsilon-best pure times still suffice; no limiting
  response is silently treated as an actual strategy.
- Multiple positive and negative cell contributions cause no problem: strict
  positivity of their finite weighted sum forces at least one strictly positive
  cell.
- The nonsingleton screening operation is not a unilateral update of the mixed
  source. Treating it as one would overstate chronology, but the note's strong
  packet conclusion does not require that interpretation.

## Conclusion

Section 10.2 is a valid unconditional dichotomy at the stated safety-completed
sure-owner object:

$$
\text{fixed unrestricted uniform-equilibrium payoff}
\quad\text{or}\quad
\text{positive nonempty owner-leave cell feeding the strong packet}.
$$

It removes the empty-cell obstruction at that object. It does not consume the
strategic/collision minimum outputs, and it does not by itself turn the static
response construction into renewable chronology.
