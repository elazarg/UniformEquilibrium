# Finite-clock KKT limits: fixed response face or full timing bubble

Author: `CODEX_HAHN`

## Status

**Exact ordinary mathematics; not Lean-checked and not a consumer.**  This
note compactifies the finite-clock KKT alternatives without erasing their
selected pure times.  The dual-heavy deadline arm already contains a literal
paid pure-time edge.  The internal cross-amplification arm contains a linked
two-player response square.  Along growing horizons, these objects have only
three timing limits:

1. a fixed finite/literal-Never response face;
2. a fixed first-disagreement row with a response continuation escaping to
   infinity; or
3. an escaping first-disagreement row whose literal pure-response corners
   have a positive all-player Never cylinder in their weak clock limit.

The third conclusion is stronger than pair-deleted survival, but only for the
counterfactual square corners.  The terminal payoff/law of those corners need
not converge to the payoff/law of the weak behavioral limit, so it is not a
terminal consumer.

## 1. Finite-clock input

Let `I=Fin 4`, let terminal rewards be bounded in absolute value by `M>0`,
and let `K_n` tend strictly to infinity.  At horizon `K_n`, let `mu_n` be a
global minimizer of complete exploitability over product stopping laws
supported on

\[
 A_{K_n}=\{0,\ldots,K_n-1,\mathsf{Never}\}.
\tag{1}
\]

The pure response menu also contains the newly exposed time `K_n`.  Write

\[
 E_{K_n}(\mu_n)=\eta_n\ge\eta_0>0.
\tag{2}
\]

Take a simultaneous KKT probability law on the cap-active player/time tests.
After stabilizing the alternative and the player labels, the finite-clock KKT
dichotomy gives one of the following.

### A. Dual-heavy deadline

There is a fixed player `j` such that

\[
 g_{j,K_n}(\mu_n)=\eta_n,
 \qquad
 \lambda_n(j,K_n)\ge\frac14.
\tag{3}
\]

### B. Internal cross-amplification

There are fixed distinct players `j,i`, an internal cap-active time `r_n` of
`j`, and a cap-active time `t_n` of `i`.  Put

\[
 \mu'_n=\mu_n[j\leftarrow\delta_{r_n}].
\tag{4}
\]

Then `j` gains exactly `eta_n`, and there is a time `s_n` in the support of
the prescribed law `(mu_n)_i` such that

\[
 V^{\mu'_n}_{i,t_n}-V^{\mu'_n}_{i,s_n}
 \ge\frac{\eta_n}{3}.
\tag{5}
\]

This is the pure-time extraction from the KKT cross-amplification theorem.

## 2. The deadline arm is already a paid response edge

In alternative A, prescribed payoff is the average of player `j`'s pure-time
payoffs:

\[
 U_j(\mu_n)=\sum_{s\in A_{K_n}}(\mu_n)_j(s)
                         V^{\mu_n}_{j,s}.
\tag{6}
\]

Equation (3) therefore implies

\[
 \sum_s(\mu_n)_j(s)
       \bigl(V^{\mu_n}_{j,K_n}-V^{\mu_n}_{j,s}\bigr)
 =\eta_n.
\tag{7}
\]

Choose `s_n` in the literal support of `(mu_n)_j` with

\[
 V^{\mu_n}_{j,K_n}-V^{\mu_n}_{j,s_n}\ge\eta_n.
\tag{8}
\]

Let `ell_n` be the first disagreement of `s_n` and `K_n`.  The two strategies
have identical outcomes whenever an opponent stops strictly before `ell_n`.
Their terminal values differ by at most `2M` otherwise.  Hence

\[
 \boxed{
 \Pr_{(\mu_n)_{-j}}(T_k\ge\ell_n\text{ for all }k\ne j)
 \ge\frac{\eta_0}{2M}.}
\tag{9}
\]

Thus the boundary KKT mass does not disappear into an abstract normal cone:
it selects a source-supported pure-time edge from `s_n` to `K_n`, of gain at
least `eta_0`, with a literal full-opponent reach floor.

The support atom `(mu_n)_j(s_n)` can tend to zero.  Equation (9) is a
counterfactual opponent-reach statement, not a uniform prescribed terminal
atom at the row.

## 3. The cross arm has full survival at its pure corners

In alternative B, let `ell_n` be the first disagreement of `s_n,t_n`.  The
same coupling argument applied to (5) gives

\[
 \Pr_{(\mu'_n)_{-i}}(T_k\ge\ell_n\text{ for all }k\ne i)
 \ge\frac{\eta_0}{6M}.
\tag{10}
\]

Player `j` is deterministic at `r_n` in `mu'_n`.  Therefore (10) forces

\[
 r_n\ge\ell_n,
\tag{11}
\]

where Never is larger than every finite time.  Also, by the definition of
first disagreement,

\[
 s_n\ge\ell_n,
 \qquad
 t_n\ge\ell_n.
\tag{12}
\]

Form the two literal pure-response corners

\[
 C_n^s=\mu_n[j\leftarrow\delta_{r_n},
             i\leftarrow\delta_{s_n}],
 \qquad
 C_n^t=\mu_n[j\leftarrow\delta_{r_n},
             i\leftarrow\delta_{t_n}].
\tag{13}
\]

The other two players are unchanged.  Equations (10)--(12) give the stronger
joint reach statement

\[
 \boxed{
 \Pr_{C_n^s}(T_k\ge\ell_n\text{ for every }k)
 =
 \Pr_{C_n^t}(T_k\ge\ell_n\text{ for every }k)
 \ge\frac{\eta_0}{6M}.}
\tag{14}
\]

The equality is exact: the deterministic clocks of `i,j` both survive to
`ell_n`, while the remaining two-clock product is the opponent-survival
factor in (10).

## 4. Joint time compactification

Compactify every marginal stopping law on the one-point space

\[
 \overline{\mathbb N}=\mathbb N\cup\{\mathsf{Never}\},
\tag{15}
\]

and retain the selected pure times as marked variables rather than relying
only on the dual law.  After a subsequence, every selected time is either a
fixed finite time, literal Never, or a finite time tending to infinity.

### 4.1 All marked times are fixed

This can occur only in alternative B.  The two cap-active tests and their
support time then define one fixed response square at every source index.
Joint compactification of the semantic pairs, terminal laws, and the finitely
many relevant deleted laws preserves its payoff equalities and the lower
bound (5).  This is a closed fixed-response-face passport.

It need not be realized by the weak limit of the four marginal stopping laws:
synchronized finite stopping mass can escape to infinity while retaining a
nonzero date-forgetting terminal coalition law.  The correct limiting object
is therefore the enriched source cluster, not the bare weak behavioral
profile.

### 4.2 The first disagreement is bounded but another time escapes

After a subsequence, `ell_n=ell` is fixed.  Equations (9) or (10) give a
uniformly reached literal paid first-disagreement row at the fixed date, but
one branch of the selected response continues to a time tending to infinity.
This is a finite-mark/remote-tail response face.  Its value on the Continue
branch requires the retained counterfactual/deleted law; finite root
coordinates alone do not determine it.

### 4.3 The first disagreement escapes

Assume `ell_n` tends to infinity.  In alternative A, use either pure corner

\[
 C_n^s=\mu_n[j\leftarrow\delta_{s_n}],
 \qquad
 C_n^K=\mu_n[j\leftarrow\delta_{K_n}].
\tag{16}
\]

Both deterministic times survive to `ell_n`, and (9) gives joint survival at
least `eta_0/(2M)`.  In alternative B, use (14).

Pass to weak limits of all marginal laws.  For every fixed `H` and all large
`n`, `ell_n>=H`.  The tail cylinder `{T_k>=H for every k}` is clopen in the
finite product of (15), so the relevant weak limiting product law assigns it
at least the same floor.  Letting `H` tend to infinity gives

\[
 \boxed{
 \Pr(T_k=\mathsf{Never}\text{ for every }k)
 \ge
 \begin{cases}
   \eta_0/(2M),&\text{in alternative A},\\
   \eta_0/(6M),&\text{in alternative B}.
 \end{cases}}
\tag{17}
\]

This is a positive **all-player timing bubble** in the weak limit of the
literal pure-response corners.  It improves the pair-deleted limit statement
available from the row alone because the two selected response clocks are
part of the compactified corner.

Equation (17) is not positive Never mass at any finite index.  More
importantly, the terminal payoff or coalition law of `C_n` need not converge
to that of its weak marginal limit: a coalition can stop together at dates
tending to infinity while every marginal converges to Never.  Thus the bubble
does not by itself give a terminal Nash profile or a finite-splice consumer.

## 5. What the dual law retains and loses

Embed the KKT measures as probability laws on
`Fin 4 x overline Nat`.

In alternative A, (3) forces every weak dual limit to put mass at least `1/4`
on `(j,Never)`.  This mass has a known origin tag: it came from the newly
exposed deadline, not from a literal Never tester.

In alternative B, no selected atom `lambda_n(j,r_n)` or
`lambda_n(i,t_n)` has a uniform mass floor.  Such atoms may vanish from the
weak dual limit even though the response-square gain stays at least
`eta_0/3`.  Consequently a faithful compact state must retain the marked
times and the square ancestry in addition to the unmarked dual probability
law.  Compactifying `lambda_n` alone loses the theorem.

## 6. Relation to existing lanes

The escaping branch matches the geometry of the checked cap-switch boundary:
a fixed response effect yields late survival and a weak Never bubble, but
finite proper clocks can realize every approximant.  The KKT input adds two
facts:

- the common source globally minimizes the finite-clock complete
  exploitability; and
- the two response tests belong to one simultaneous active-gradient law.

Neither fact currently turns the weak clock limit into a chronological edge.
The finite-deadline projective program starts from exact Nash laws at adjacent
horizons; an `E_K` minimizer need not be such a Nash law.  Therefore the KKT
boundary cannot be silently fed to the adjacent-deadline consumer.

## Source audit

The finite KKT input is the frozen note
`CODEX_HAHN__FINITE_CLOCK_EXPLOITABILITY_KKT_BOUNDARY_OR_CROSS_AMPLIFICATION`,
SHA-256
`9efcc2aa99ec6dbbd799297c228b20be78e5b1ec43799a267423160dfcf5dab1`.

The pure-time response-square extraction is the frozen note
`CODEX_HAHN__KKT_CROSS_AMPLIFICATION_TO_PURE_TIME_PAID_ROW`, SHA-256
`b9f31ba1e803562dbc885c5fa0d0b387487d9399441802fe1feb7164f317127f`.

For project interfaces, the finite controller values and their convergence
are in
`UniformEquilibrium/Quitting/ControllerTester/FiniteWordValue.lean`.  The
first-disagreement factorization is represented by
`quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul` in
`UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`.

The exact boundary regression is
`formalized/CAP_SWITCH_RECTANGLE_FULL_CHORD_AND_FINITE_SPLICE_BOUNDARY.md`.
The adjacent-horizon comparison is
`formalized/FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md`.

## Nonclaims

- The controller minimizers are not asserted to be finite timing-game Nash
  laws.
- A source support atom selected by averaging need not have uniform mass.
- The all-player timing bubble belongs to weak limits of counterfactual pure
  response corners, not necessarily to the source profile.
- The terminal payoff/law need not be continuous at the timing bubble.
- No chronological Nash--Bellman edge, renewable rank, terminal approximate
  Nash profile, or uniform-equilibrium payoff is produced.

## Next exact question

Can global finite-clock minimality rule out the all-proper realization of the
timing bubble, or can one construct an exact `E_K`-minimizing regression whose
selected KKT square escapes while all finite-index clocks remain proper?  A
positive answer needs the minimizer/KKT structure; the response square and
weak Never bubble alone are already known to be insufficient.
