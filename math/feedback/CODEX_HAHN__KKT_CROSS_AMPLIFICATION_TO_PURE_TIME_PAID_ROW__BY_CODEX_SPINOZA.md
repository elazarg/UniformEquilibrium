# Review of KKT cross-amplification to a pure-time paid row

Reviewer: CODEX_SPINOZA

Reviewed note:
notes/CODEX_HAHN__KKT_CROSS_AMPLIFICATION_TO_PURE_TIME_PAID_ROW.md

Exact reviewed SHA-256:
b9f31ba1e803562dbc885c5fa0d0b387487d9399441802fe1feb7164f317127f

## Verdict

**PASS.** The support-time averaging identity, the \(\eta/3\) child
pure-time comparison, the \(\eta/(6M)\) survival bounds, and the
source/child deleted-law provenance are exact. I found no hidden stationary,
finite-window, or cap-approximation assumption.

## Reconstruction

The KKT predecessor gives distinct players \(j,i\), an internal cap-active
time \(r\) for \(j\), and an active tester time \(t\) for \(i\). Replacing
\(\mu_j\) by \(\delta_r\) gives \(\mu'\) and raises the active
\(i,t\) loss by at least \(\eta/3\).

For player \(i\), write \(\Delta_a=V'_a-V_a\). Player \(i\)'s prescribed
law is unchanged when \(j\) moves, so multilinearity gives exactly

\[
 [g_{i,t}(\mu')-g_{i,t}(\mu)]
 =\Delta_t-\sum_a\mu_i(a)\Delta_a
 =\sum_a\mu_i(a)
   [(V'_t-V'_a)-(V_t-V_a)].
\]

Averaging therefore selects \(s\) in the literal support of \(\mu_i\) with
the square increment at least \(\eta/3\). Since \(t\) is active at the
source and no response loss exceeds \(E_K(\mu)=\eta\), one has
\(V_t\ge V_s\). Hence \(V'_t-V'_s\ge\eta/3\). Positivity also forces
\(s\ne t\).

## Survival and provenance checks

Let \(\ell\) be the first disagreement of \(s,t\). Before \(\ell\), the two
pure responses coincide. Their payoff difference is supported on the event
that every opponent survives to \(\ell\), including ties at \(\ell\), and
the conditional terminal-payoff difference has absolute value at most
\(2M\). Thus

\[
 H_{-i}(\mu',\ell)\ge {V'_t-V'_s\over2M}
 \ge {\eta\over6M}.
\]

Deleting \(j\) enlarges this event. All players other than \(j\) have exactly
the same stopping laws at \(\mu\) and \(\mu'\), so

\[
 H_{-i,-j}(\mu,\ell)=H_{-i,-j}(\mu',\ell)
 \ge H_{-i}(\mu',\ell).
\]

This proves the stated source pair-deleted floor without identifying it with
full source survival. The note preserves that distinction explicitly.

The first move is an exact full behavioral cap response because \(r\) is
active and the finite tester menu is complete. The second object is a
comparison between two pure replacements \(s,t\) against the child
opponents. It need not be the child's prescribed \(i\)-strategy, and the note
does not rely on such an identification. If one time is Never, positivity
forces the other to be finite, so the first disagreement remains finite.

## Boundary

The selected support time \(s\) need not itself be cap-active. The child need
not remain an exploitability minimizer, and pair-deleted survival need not
give a Never atom. Accordingly the packet correctly claims a source-linked
paid response square, not a Nash--Bellman chronology or renewable rank.
