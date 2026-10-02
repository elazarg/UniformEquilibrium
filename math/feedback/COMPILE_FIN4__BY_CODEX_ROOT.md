# Source and boundary audit of `COMPILE_FIN4.md`

Reviewer: Codex Root

## Verdict

The note contains a valid exportable core, but the export should not reproduce
the whole seven-instruction architecture.  The architecture and the tight-port
realization lemma substantially overlap the already exported executable
stopping-law grammar.  The genuinely new conjecture-facing content is:

1. a positive-minimum, source-attached theorem showing that every infinite
   outward exact cap--Nash prefix chain which retains a positive finite suffix
   atom necessarily loses stopping mass at infinity in the strategic
   total-variation topology;
2. a rational Fin4 example showing nonclosedness of the **globally**
   absorption-maximal exact-root graph, strengthening the earlier
   constrained-face example; and
3. a rational constant-decoration example showing that the actual normalized
   passport coordinates do not imply stopping-law tightness or an
   ancestry-preserving behavioral limit.

Items 1 and 3 directly answer the accepted negative form of
`questions/FIN4_RECURRENT_COMPONENT_CONSUMER_OR_MODEL.md`: they exclude a
precisely specified compact-trace operation and identify the missing passport.
Item 1 is the main result.  Item 2 is an independently useful strengthening
and an exact boundary test.

This review is ordinary mathematics.  It does not confer Lean status.

## Exact checks

### Global maximal-root example

For the displayed table and tail `tau_t`, the prescribed payoff and cap are

```text
U(tau_t) = (t,-t,0,-1/2),
B(tau_t) = (t,0,0,0).
```

Player 0 obtains `t` by waiting and cannot improve it by quitting.  Each of
players 1, 2 and 3 can obtain zero by Never and every outcome in which that
player quits pays at most zero.  Thus the total debt is `t+1/2`.

At cap `(t,0,0,0)`, players 1, 2 and 3 strictly prefer Continue at every root.
With them continuing, player 0 compares `t` from Continue with zero from Quit.
For `t>0`, all Continue is therefore the unique exact root.  At `t=0`, player
0 is indifferent and global absorption is uniquely maximized by its sure-Quit
root.  Hence the graph of global absorption-maximal exact roots is not closed
along a total-variation convergent curve of actual tails.

The example has global minimum debt zero.  It proves no failure of uniform
equilibrium and no positive-minimum nonclosedness theorem.  The final packet
must retain that limitation.

### Positive-minimum prefix escape

Let `sigma_(n+1) = x_n star sigma_n`, with `x_n` an exact cap--Nash root, and
write `c_n` for its joint Continue mass.  The checked identity
`quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash` gives

```text
D(sigma_n) = C_n D(sigma_0),
C_n = product_{k<n} c_k.
```

If every debt is at least `D_* > 0`, then `C_n >= q := D_*/D_0`.  The checked
literal prefix transport in
`quittingStageCoalitionMass_maximalCapSemanticPrefixProfile_add` is the
maximal-ray specialization of the elementary fact that a suffix coalition
atom of mass `m` is shifted to date `n+s` with mass `C_n m`.  Thus each member
of the coalition has at least `qm` finite stopping mass beyond every fixed
cutoff.  This already proves failure of a common finite-tail envelope.

Because `C_n` decreases to a positive limit, `c_n -> 1`.  At each fixed date
`t`, the relevant outer root recedes along the sequence, and the probability
that a fixed player stops there is bounded by the corresponding root
absorption `1-c_(n-1-t)`, which tends to zero.  Individual prefix-survival
products converge, so the Never coordinate also converges.  For a player in
the retained coalition the limiting finite-plus-Never coordinates have total
mass at most `1-qm`.

The theorem is therefore correct, with one terminology restriction: it rules
out an ancestry-preserving limit in the strategic total-variation (equivalently
coordinate-plus-Never plus tightness) category.  It does **not** say that the
laws have no weak limit in the one-point compactification; the escaped dates
can converge weakly to infinity.  That weak limit does not preserve the Never
coordinate or the retained finite terminal event and is exactly why it cannot
be used as the requested behavioral trace source.

There is a useful quantitative strengthening.  Put
`h_i = 1 - p_i Pr_tau(T_i=infinity)`.  For every fixed actual stopping law
`mu_i`, a finite-head test containing the Never point gives

```text
liminf_n d_TV(Law_sigma_n(T_i), mu_i) >= h_i >= q m.
```

Thus the sequence is not merely nontight: every actual candidate source is
separated from it by the fixed strategic-TV floor `qm` in each retained-atom
coordinate.  This sharper form follows from the same proof and is preferable
in the final statement.

This applies to the current canonical maximal-prefix ray because the Research
modules expose both exact debt scaling and exact shifted marked-mass scaling.
It does not consume the strict ray; it proves that treating its infinite end
as an actual compact-trace source is invalid.

### Constant-decoration escape

For the displayed reward table, the endpoint profile with player 0 quitting
surely at date `n` has constant whole semantic/law point, constant all-Never
postmark tail, marked mass one, marked-owner root defect zero, and payoff gain
one over the comparison in which player 2 quits at the same date.  These are
exactly the four coordinates of `QuittingMarkedPairDecoration` in
`Research/Quitting/NormalizedPassportPrefixOrbit.lean`.

Player 0's stopping laws are `delta_n`.  Every finite coordinate and the Never
coordinate converge to zero, while the finite-tail supremum is one for every
cutoff.  No subsequence is tight.  An unrelated date-zero profile realizes the
same time-forgetting decoration, but not the selected ancestry.  This is a
valid counterexample to actualization from those decoration fields alone.

### Relaxed-root comparison transport

The compact approximate-feasible-set argument is correct.  If
`delta_n = ||b_n-b||_infinity` and

```text
N_n = {x : g(b_n,x) <= 2 delta_n},
```

then every exact root at `b` lies in `N_n`, and every cluster point of an
absorption maximizer on `N_n` is an absorption-maximal exact root at `b`.
This is only a selector/decoder lemma.  It does not supply the one-step payoff,
cap, law and debt error ledger, the approximate same-tail dispatch, or a
terminal consumer.  It should be recorded as the surviving repair, not as a
completed uniform-escape construction.

## Source and novelty audit

The following declarations/files were inspected:

- `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetExcursionReturn.lean`;
- `quittingStageCoalitionMass_maximalCapSemanticPrefixProfile_add` and the
  literal-root-stack accessors in
  `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`;
- `rawDecoration_markedMass_eq_prefixSurvival_mul` and
  `rawDecoration_actualGain_eq_prefixSurvival_mul` in
  `Research/Quitting/NormalizedPassportPrefixOrbit.lean`;
- the strict-ray status in `docs/TOOLKIT.md`; and
- `exports/EXECUTABLE_ADAPTER_GRAMMAR_AND_CONSTRAINED_ROOT_NO_GO.md`.

The tight-port realization theorem is already present in substance in the
executable-grammar export and should be cited rather than re-exported as new.
The old maximal-root example is explicitly constrained to one root face; the
new rational example is genuinely global.  The existing maximal-ray modules
retain time-forgetting law and semantic clusters but do not prove the
positive-minimum stopping-clock escape theorem above.  The constant-decoration
example targets the exact four-coordinate normalized decoration used by the
current minimizer, rather than an abstract smaller carrier.

## Required export form

The final packet should:

- lead with the positive-minimum prefix-escape theorem;
- state the strategic topology and the weaker one-point weak limit explicitly;
- include the two rational boundary examples;
- cite, rather than duplicate, the generic tight-port realization proof;
- state the relaxed-root lemma only as a viable remaining construction;
- name `FIN4_RECURRENT_COMPONENT_CONSUMER_OR_MODEL.md` as the narrowed live
  obligation; and
- make no claim of consuming uniform escape, minimum return, the strict ray,
  or Fin4 UE.

Subject to those scope choices and any independent-review corrections, I
recommend export.
