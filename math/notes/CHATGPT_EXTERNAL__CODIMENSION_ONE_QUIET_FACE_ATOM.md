# Quantitative codimension-one deletion and quiet-face atoms

Author: `CHATGPT_EXTERNAL`

Status: `REVIEWED ORDINARY MATHEMATICS; INTERNAL DIAGNOSTIC, NOT AN EXPORTED CONJECTURE CONTRACTION`

Independent reviews:

- `feedback/CODIMENSION_ONE__BY_CODEX_EULER.md`
- `feedback/CHATGPT_EXTERNAL__CODIMENSION_ONE_QUIET_FACE_ATOM__BY_CODEX_MINER.md`

Both reviews validate the reached-suffix splice and the constants in
(5)--(8). They require the compact limit to be described as a limiting
carrier continuation, not as the payoff of an attained behavioral profile.

## Question

Let `r` be a finite quitting reward table, and let

\[
\eta(r):=\inf_\sigma\max_i\bigl(B_i(\sigma)-U_i(\sigma)\bigr).
\]

What actual source data follow if \(\eta(r)>0\), while every one-player
deletion has \(\eta(r^{-w})=0\)?

## The deletion inequality

Fix \(w\), put \(J=I\setminus\{w\}\), and define

\[
\underline r_w=min\left(0,min_{\varnothing\ne A\subseteq J}r_w(A)\right)
\]

and

\[
\Gamma_w(r)=\max\left\{
r_w(\{w\})-\underline r_w,
\max_{\varnothing\ne A\subseteq J}
\bigl(r_w(A\cup\{w\})-r_w(A)\bigr)
\right\}. \tag{1}
\]

Then

\[
\boxed{\eta(r)\le
\max\{\eta(r^{-w}),\Gamma_w(r)^+\}.} \tag{2}
\]

Indeed, quietly lift an arbitrary profile \(\sigma\) of \(r^{-w}\). Every
survivor's debt is preserved exactly. A deterministic finite deviation by
\(w\) has gain

\[
\rho_t\sum_{A\subseteq J}p_t(A)g_t(A), \tag{3}
\]

where

\[
g_t(\varnothing)=r_w(\{w\})-v_{t,w},\qquad
g_t(A)=r_w(A\cup\{w\})-r_w(A)\quad(A\ne\varnothing).
\]

The literal-Never tail satisfies \(v_{t,w}\ge\underline r_w\), so every
summand is at most \(\Gamma_w(r)\). Since \(0\le\rho_t\le1\), every finite
gain is at most \(\Gamma_w(r)^+\), as is every behavioral gain by the exact
stopping-law mixture identity. Taking infima proves (2).

Consequently, if \(a=\eta(r)>0\), \(\eta(r^{-w})=0\) for every \(w\), then

\[
\Gamma_w(r)\ge a\qquad\text{for every }w. \tag{4}
\]

This is the \(A=1\) specialization of the independently reviewed sharp
deletion cap

\[
P+\min(1,A)(C-P)_+,
\]

proved in ordinary mathematics in
`notes/CODEX_EULER__OPERATIONAL_ESSENTIALITY_SHARP_DELETION_PASSPORT.md`.
It is not claimed as a new proof principle.

## New quantitative quiet-face output

Assume \(a=\eta(r)>0\), \(\eta(r^{-w})=0\), and fix \(0<\gamma<a\). Let

\[
M:=\max_{i,S}|r_i(S)|.
\]

Choose profiles \(\sigma_n\) of the deleted game with survivor exploitability
\(\varepsilon_n\downarrow0\), and let \(q_n\) be their quiet lifts. For all
large \(n\), every survivor debt is below \(\gamma\), whereas ambient
exploitability is at least \(a\). Thus \(w\) has a deterministic finite quit
time \(t_n\) of gain at least \(\gamma\).

Let \(\rho_n\) be the probability of reaching \(t_n\), and let
\(\theta_n\) be the restricted-game suffix at that date. Exact pure-time
transport gives

\[
\gamma\le \rho_n\Delta_n,
\qquad |\Delta_n|\le2M.
\]

This first proves \(M>0\). Hence the following divisions are legitimate, and

\[
\boxed{\rho_n\ge\frac\gamma{2M},\qquad\Delta_n\ge\gamma.} \tag{5}
\]

Any survivor deviation in \(\theta_n\) can be spliced after the reached
event, so

\[
\boxed{\operatorname{Expl}_{r^{-w}}(\theta_n)
\le \frac{\varepsilon_n}{\rho_n}
\le\frac{2M}{\gamma}\varepsilon_n\longrightarrow0.} \tag{6}
\]

At the first row of \(\theta_n\),

\[
\Delta_n=\sum_{A\subseteq J}p_n(A)g_n(A)\ge\gamma.
\]

For five players there are \(2^4=16\) coalitions \(A\subseteq J\). Hence,
after passing to a subsequence, one fixed \(A\) satisfies

\[
p_n(A)[g_n(A)]_+\ge\frac\gamma{16},
\]

and therefore

\[
\boxed{p_n(A)\ge\frac\gamma{32M},
\qquad g_n(A)\ge\frac\gamma{16}.} \tag{7}
\]

Combining (5) and (7), the corresponding reached counterfactual atom under
the pure-time outsider deviation has the absolute mass floor

\[
\boxed{\rho_np_n(A)\ge\frac{\gamma^2}{64M^2}.} \tag{8}
\]

If \(A\ne\varnothing\), the quiet profile itself has the survivor atom \(A\)
at the reached row, and the deviation changes it to \(A\cup\{w\}\). If
\(A=\varnothing\), the deviating terminal atom is the singleton \(\{w\}\).

Compactness of the finite row cube and bounded continuation box yields a
limiting row that is exact one-stage Nash for the four survivors at the
limiting continuation vector, while preserving the outsider immediate-Quit
advantage and the fixed atom bounds. If the full payoff/cap suffix pairs are
carried through the limit, this continuation lies in the closed restricted
terminal-semantic carrier. It need not be the payoff of an attained behavioral
suffix: escaping stopping clocks make the attained semantic set nonclosed.
Likewise, the limiting row need not come with one literal prefix realizing the
limiting reach. The strongest actual provenance is the uniform family of
finite reached suffixes before passage to the limit.

The absolute counterfactual atom floor (8), together with the asymptotically
Nash reached suffix (6), is the part not stated in the prior sharp-deletion
review. For nonempty \(A\) it is actual quiet-source terminal-atom data. For
empty \(A\), only the outsider deviation creates the singleton terminal atom;
the quiet source itself does not absorb on that row.

## Macroscopic outsider repair

Let \(q\) be a quiet lift of an \(\varepsilon\)-Nash restricted profile, and
replace \(w\)'s Never law by a stopping law whose ever-Quit mass against
all-Continue opponents is \(\alpha\). Couple the old and new profiles. For
each survivor \(i\), prescribed payoffs and arbitrary-deviation payoffs each
change by at most \(2M\alpha\), so

\[
d_i(\text{new})\le\varepsilon+4M\alpha. \tag{9}
\]

If the new law is a \(\delta\)-best response for \(w\), then
\(d_w(\text{new})\le\delta\). Under an ambient gap \(a>\gamma\), with
\(\delta<\gamma\), this forces

\[
\alpha>\frac{\gamma-\varepsilon}{4M}. \tag{10}
\]

If \(w\)'s quiet-lift debt exceeds \(\gamma\), comparing its unchanged cap
before and after the own-strategy replacement also gives

\[
\alpha>\frac{\gamma-\delta}{2M}. \tag{11}
\]

Thus a five-face gluing proof cannot repair each omitted player by an
infinitesimal activation.

## Exact obstruction to naïve combination

For five players let every player receive \(1\) when all five quit, \(0\) when
exactly four quit, and \(-1\) when one to three quit. Every four-player
restriction has the exact equilibrium in which all four quit immediately.
Its quiet lift has exactly one outsider debt, equal to one. Nevertheless the
full game has the exact equilibrium in which all five quit immediately.

Hence even five exact source-matched sole-outsider gaps do not combine by
their labels alone.

## Source correspondence and scope

The exact quiet-lift identities are in
`UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`. The
checked current, weaker cap is in
`UniformEquilibrium/Quitting/Classification/BlockDeletionInequality.lean`.
The finite pure-time and reached-row identities are in
`UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean` and
`UniformEquilibrium/Quitting/Paths/OutsiderNeverGluing.lean`.

The result narrows a putative five-player cardinal-minimal counterexample to
the all-essential chamber (4), with five unrelated families of quantitatively
reached face rows and limiting local root certificates. It does not prove the
desired \(5\to4\) implication, align those five semantic sources, create a
small-debt ambient seed, or produce an admissible return. It remains internal
because no maintained consumer accepts the empty/counterfactual atom arm or
aligns these five source families.

## Review disposition

The two independent audits found the reach conditioning, unrestricted suffix
splice, fixed-label subsequence, and constants
\(\gamma/(2M),\gamma/(32M),\gamma/16,\gamma^2/(64M^2)\) correct. The reach
floor partly overlaps the checked paid-row live-mass bound, but the combination
of a fixed label, absolute atom floor, and asymptotically Nash reached suffix
was not found under another declaration. This is useful diagnostic source
data, but not by itself an export-gate result.
