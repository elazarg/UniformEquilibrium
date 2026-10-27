# Review of the observer attractor with arbitrary higher rewards

**Verdict: PASS as a reusable internal producer component.** No unresolved
mathematical objection. Reviewed the entire 274-line canonical note
`math/notes/CODEX_COORDINATOR__OBSERVER_ORTHANT_ATTRACTOR.md`, SHA256
`3fcf145336ee4a2eedbc78198570fabd50f5f5ab4439260ed7bfbda6d7a5e61a`.

The generalized theorem retains explicit singleton and participant-pair
conditions, while all three passive pair rewards and all three participant
triple rewards may be arbitrary finite signed numbers. It produces observer
Nash prefixes from every specified sufficiently small seed in the sign
orthant. Its additional corollary proves quiet-pivot safety for an arbitrary
fourth-player row after explicit further smallness restrictions. Producing
entry from a nonnegative seed, recurrent returns and UE remain outside its
conclusion.
I independently audited this extension; I authored the earlier specialized
premium observer-process lemma, so this remains a contributor/component
review rather than an independent whole-UE review or export admission.

## Complete audit

1. The raw table gives the displayed Ccap polynomials with
   r_i=p_i-K_i, and gives the passive quadratic terms in the diagonal
   output exactly. Signed r_i are not silently treated as nonnegative.
2. All delta right sides are positive. The pair guards give
   0<l/F<k/E<1, so mu lies in(0,1) and both displayed margins b_t,b_a
   are strictly positive. The explicit epsilon bounds every trial scalar
   point, not only its eventual root. They also bound the face root,
   including u=0. All denominator bounds follow from the same delta.
3. At a failed face test, w/F<S/A; the full scalar interval is nonempty.
   The signed derivative numerators are bounded below by AB/2 and FE/2.
   The derivative f' has both positive terms because C-r1*z>=C/2 and
   D+r1*a>=D/2. Both endpoint signs are strict. This supplies one unique
   positive interior root without a numerical or supplied-root assumption.
4. I checked the exact row0 and row1 identities. The row0 bound remains
   strict because t>0. Both row1 coefficient numerators are positive, so
   its nonnegativity also holds at u=0 and z=0. For row3, the key step is
   valid: w>=max(Ccap3,0) implies w>=mu*Ccap3 for0<mu<1. This handles
   the quiet observer on the face and negative Ccap3. The resulting
   b_t*t+b_a*a margin controls either sign of its passive quadratic term,
   and is strict even when a=0. No division by a,t,z,u or w is used to
   establish these boundary comparisons.
5. The Lyapunov identity includes the passive quadratic contribution.
   Its absolute bound is at most half the sum of all odds by the explicit
   delta condition. The remaining discarded sum is nonnegative because
   each d_i*N_i is nonnegative. Thus V' remains nonnegative and satisfies
   V'<=V-sum(x)/2. Iteration stays in the same domain and all odds are
   summable.
6. The enforced first two comparisons give S,u tending to zero. For the
   third increment, the stated coefficient is valid using
   1-1/((1+a)(1+t))<=a+t and at<=delta(a+t). Hence w converges. A
   positive limit forces eventual face01 selections, where the exact
   recurrence S'=(A+g)S/(A+S) expands every0<S<g. This contradicts
   S tending to zero. All three observer annotations therefore vanish.
7. Each finite selected prefix word is exactly diagonal Nash from the
   fixed synthetic seed. Summable odds give positive limiting marginal
   survivals. Closure of these finite words supplies the endpoint; it
   does not execute a continuation after infinitely many dates.

I independently verified with exact SymPy identities both signed scalar
selection derivatives, the row0 and row1 formulas, and the row3 mu-margin
identity. The full argument above also checks the inequalities and boundary
quantifiers that symbolic identity checks alone would not establish.

The final statement correctly says roots are **supported on**01 or013.
When u=0 and the face test holds, a0=0 and the actual support is just1;
the construction and all sign arguments explicitly cover this case.

## Raw singleton equivalence and the four-player corollary

I reviewed the complete determinant/sign equivalence, including the exact
formulas for alpha,beta,gamma. Direct multiplication gives dG=-1 and
D0=det G=h*i*l-g*j*k. Positivity of all three weight magnitudes is exactly
D0>0 in this strict sign chamber; the alpha numerator is correctly stated.
The earlier exact SymPy determinant and signed-weight checks apply to these
unchanged formulas.

The added local four-player corollary is valid. The further delta and epsilon
restrictions can be imposed together with all earlier bounds. With the pivot
prescribed quiet, the observer root equations use exactly the restricted
table; arbitrary observer rewards on coalitions containing the pivot never
enter their deviations. The passive pivot update is a convex combination,
so its absolute value stays at most B before any Nash comparison is assumed.
Its total variation is at most2(K+B)V_initial<=bmin/4. This proves the lower
value bound3bmin/4 without circularly assuming pivot optimality.

Own pivot singleton zero removes the constant term from its joining offer.
All seven remaining coefficients are bounded by K. Since each odds is at
most delta<=1, D-1<=3delta+3delta^2+delta^3<=7delta<=12delta. Hence the
joining offer has absolute value at most bmin/4, strictly below the pivot's
continuation value. All constructed roots are therefore full four-player
Nash. Summability gives convergence of the pivot value and the complete
payoff/cap/survival tuple. The asserted endpoint interval[3bmin/4,B] follows.

This is a return from the specified signed orthant near a positive axis,
not a statement about all nearby annotations. The corollary produces neither
an initial entry from a nonnegative proxy seed nor a recurrent collection of
entries with a uniform survival contraction. The note states these limits
explicitly, so the stronger corollary does not become an unsupported UE claim.

## Semantic correspondence and scope

The relevant existing source declarations are
`quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash` and
`continuous_quittingTerminalSemanticPrefix` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, and
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
Their arbitrary-reward finite-prefix semantics support the formulas used
here, including the passive pair terms. The fixed synthetic-seed closure
is ordinary mathematics; no membership of an arbitrary negative seed in
the actual-profile carrier is assumed. No Lean compilation was run.

The six higher observer rewards and arbitrary fourth-player rewards affect
the size of the produced entry region, not the strict singleton/participant-
pair guards. This strengthens the local return component, but does not by
itself exclude a four-player counterexample class. Internal status and the
contributor/component review disclosure remain appropriate.
