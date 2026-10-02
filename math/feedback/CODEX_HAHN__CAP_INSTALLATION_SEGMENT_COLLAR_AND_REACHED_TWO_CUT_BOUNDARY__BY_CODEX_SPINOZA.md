# Review of the cap-installation collar and reached two-cut boundary

Reviewer: CODEX_SPINOZA

Reviewed artifact:
notes/CODEX_HAHN__CAP_INSTALLATION_SEGMENT_COLLAR_AND_REACHED_TWO_CUT_BOUNDARY.md

Reviewed SHA-256:
36bc91b4db9322f843489fb3cb4c372fa7b9e58795f1cb93cced5111c5431b9e

## Verdict

**PASS mathematically.** I found no failure in the cap-invariance identity,
the compact separation argument, the uniform exact-root expenditure, the
literal two-cut chronology, or the law-displacement estimate. The conclusion
is correctly limited to a sharper return to the already-known off-minimum
port; it does not claim renewal or a terminal consumer.

There are two formatting-only missing display closers after equations (12)
and (16). They should be repaired before an export-format freeze, but neither
omission changes the mathematical content reviewed here.

## Cap segment and compact collar

Changing only player \(b\)'s prescribed stopping law leaves all opponents
fixed, so its unrestricted behavioral cap is constant on the entire private
mixture segment. Expected prescribed payoff is affine in that stopping-law
mixture. Since the endpoint law \(A_n\) attains the common cap, the exact
identity

\[
 d_b(X_n^t)=(1-t)d_b(\sigma_n)
\]

is correct, including at \(t=1\).

For any cluster point of the full moving segments, the same cap coordinate
converges to \(s_b\). On the global minimum fibre,
minimumTerminalSemantic_singletonMargin gives

\[
 B_b\ge s_b+D_*.
\]

Thus the cluster set and minimum fibre are disjoint. Both are compact, and
total debt is continuous, so the positive separation upgrades exactly to one
uniform eventual excess

\[
 D(X_n^t)\ge D_*+\delta_{\mathrm{seg}}
\]

for every \(t\in[0,1]\). No unjustified explicit lower bound on
\(\delta_{\mathrm{seg}}\) is claimed.

## Root expenditure and positive-survival transport

At the fixed proper parameter \(t_*=1-\lambda\), the owner debt is at least
\(g=\lambda\gamma\), while its cap is eventually within \(g/4\) of the
singleton payoff. These are precisely the fixed-cap-pin hypotheses. The
displayed debt-drop constant

\[
 c_0=\min\{g/2,g^2/(16M)\}
\]

is correct and uniform over every exact product root.

The absorption floor is also correct. If the probability that some opponent
of \(b\) Quits is at least \(g/(16M)\), joint absorption has that lower bound.
Otherwise the fixed-cap-pin comparison makes Quit strictly better than
Continue for \(b\), and exact complementarity forces \(q_b=1\). Hence

\[
 \operatorname{Abs}(q_n)\ge
 \min\{1,g/(16M)\}.
\]

If the joint Continue probability is bounded below, copying \(b\)'s
prescribed action in the new root and switching only after joint Continue to
the cap response at the literal segment tail transports at least
\(c_ng\) gain. This is a source-attached response built from the tail cap;
the note does not incorrectly call it a cap attainer at the prefixed child.

## Literal two-cut audit

For the structured source, every original coordinate is stationary and
\(A_n\) is Quit0. In the private law mixture, survival of the first segment
row excludes the Quit0 branch. Conditional on that survival, the remaining
owner law is the original stationary law conditioned on one Continue, hence
is the original law again by memorylessness. All opponents are unchanged and
stationary. Therefore

\[
 \operatorname{suffix}_2(q_n::\sigma_n^{t_*})=\sigma_n
\]

is a literal profile identity, not merely equality in distribution or
semantic coordinates.

The first root supplies the reached weight \(c_n\); the segment row has owner
Quit probability at least \(t_*\). Thus the proposed entry and exit cuts are
genuine and meet the quantitative two-cut hypotheses. Since the exact exit
is the already uniformly off-minimum source, the inclusive checked consumer
may select its off-minimum-exit arm. The note correctly refuses to infer the
paid-splice arm.

## Law-displacement falsification attempt

Let \(\nu_n^0\) and \(\nu_n^1\) be the terminal laws before and after
installing \(A_n\). Mixing player \(b\)'s private stopping law commutes with
forming the joint independent law and with the terminal-outcome pushforward.
Therefore

\[
 \nu_n^t=(1-t)\nu_n^0+t\nu_n^1
\]

is exact.

Player \(b\)'s cap gain is the difference of expectations of one
\([-M,M]\)-valued terminal reward function under \(\nu_n^1\) and
\(\nu_n^0\). Under the convention
\(\|\mu-\nu\|_{\mathrm{TV}}=\sup_A|\mu(A)-\nu(A)|\), the standard bound is

\[
 |\mathbb E_\mu f-\mathbb E_\nu f|
 \le 2M\|\mu-\nu\|_{\mathrm{TV}}.
\]

Hence the claimed lower bound

\[
 \|\nu_n^1-\nu_n^0\|_{\mathrm{TV}}\ge\gamma/(2M)
\]

has the correct direction and constant. It remains unsigned. Nothing in the
argument makes these total-variation displacements additive or monotone
around repeated response seams, and the note explicitly declines that
inference.

## Scope

The cap response in the abstract theorem must be an actual cap-attaining
behavioral law; this is supplied by the structured Quit0 source. A mere
near-best response would add an endpoint error to the affine debt formula.
The proof uses unrestricted behavioral caps throughout.

The note does not preserve the singleton cap pin after the exact prefix,
does not turn the segment row into an exact Nash row, and does not identify a
return from the off-minimum exit to the minimum fibre. Those are exactly the
remaining seams rather than hidden assumptions.

## Delta review

Repaired artifact SHA-256:
0c312909400abaf01c89851b9fc6017a3373657cd40582383d241c019279fa6f

**Mathematical delta PASS; exact bytes still REVISE for the two previously
reported display closers.** The new wording correctly calls the shifted tail
object a feasible response built from a cap-attaining tail response, without
claiming it attains the prefixed cap. The two-cut scale

\[
 h_0=\min\left\{t_*,
 \frac12\log\left(1+\frac{2\delta}{D_*}\right)\right\}
\]

is positive, is no larger than the actual one-row marginal hazard \(t_*\),
and satisfies

\[
 \frac{e^{h_0}-1}{2}D_*\le\delta.
\]

Thus it legitimately instantiates the off-minimum-exit arm at a compatible
lower hazard threshold. I found no mathematical change requiring further
review.

However, inspection of the exact repaired bytes shows that equations (12)
and (16) still have an opening display delimiter and no closing display
delimiter. The lines following their tags begin prose directly. Therefore
the mathematical note remains PASS, but this SHA should not be treated as
format-clean or staged for export until those two literal closing delimiters
are inserted and delta-checked.

## Final formatting delta

Final artifact SHA-256:
f69b6f7b167d81789add1e48e77220ad6418d7cff3715169b276649063f51be5

**PASS.** The two missing closing display delimiters now occur immediately
after (12) and (16). The file has balanced inline delimiters \(80/80\) and
display delimiters \(24/24\), with no control bytes. The mathematical text,
including the corrected \(h_0\) scale and feasible-response wording reviewed
above, has not drifted. This exact hash is covered by my mathematical and
formatting review.

## Standalone export gate

Candidate:
`/tmp/FIN4_CAP_INSTALLATION_SEGMENT_COLLAR_AND_TWO_CUT_PORT_RETURN.md`

Exact SHA-256:
`65909c7782d9f32a526f3c948a81786eb162262fd094ecf807ae0017cd76ed00`

**PASS.** The standalone packet faithfully carries the reviewed result.  In
particular, it retains the corrected

\[
 h_0=\min\left\{t_*,
 \frac12\log\left(1+\frac{2\delta}{D_*}\right)\right\},
\]

keeps cap attainment at the stationary source distinct from feasibility of
the transported child response, and states the collar branch as an
off-minimum exit rather than as a paid-splice or renewal conclusion.  The
segment identities, uniform exact-root debt expenditure and absorption
floor, reached two-cut construction, and total-variation displacement have
the same hypotheses, constants, and orientations as the reviewed note.  Its
nonclaims explicitly preserve the unresolved horizontal recharge/source
return seam.

The exact hash matches, all required export headings are present, all links
resolve from the intended future `exports/` location, the control-byte scan is
clean, and `../scripts/check_docs.py` passes.  No mathematical or lifecycle
objection remains for this exact candidate.
