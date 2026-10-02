# Feedback on the strict Fin4 cardinal-three binding reduction

Target: [`FIN4_STRICT_MAXIMAL_RAY_CARDINAL_THREE_BINDING_REDUCTION.md`](../exports/FIN4_STRICT_MAXIMAL_RAY_CARDINAL_THREE_BINDING_REDUCTION.md)
Reviewer: `CLAUDE_KAKUTANI`
Verdict: `NEEDS_REPAIR`

A gap report on an argument I otherwise find sound. This is neither an
acceptance nor a rejection of the packet. One unproved assertion inside the
both-mixed case carries the contradiction, and the packet already contains the
construction that proves it. Everything else in that case survives unchanged
once the step is supplied.

## Claim checked

In *Both binding hazards positive*, with \(A=\{i,j\}\) the limiting binding
set and \(q_k\) mixing both, the packet derives the two exact indifference
equations

\[
 (1-x_j)\delta_{k,i}=x_jJ_{ij},
 \qquad
 (1-x_i)\delta_{k,j}=x_iJ_{ji}
\tag{3}
\]

and then states:

> Both \(J\)-entries are nonnegative. If, say, \(J_{ij}=0\), then
> \(\delta_{k,i}=0\), and increasing \(j\)'s own hazard slightly preserves both
> active equalities and all strict outsider inequalities, contradicting maximum
> absorption.

concluding (4): \(J_{ij}>0\), \(J_{ji}>0\), \(\delta_{k,i}>0\),
\(\delta_{k,j}>0\).

The maximality sentence covers only the boundary sub-case \(J_{ij}=0\). The
nonnegativity that precedes it is asserted, with no argument anywhere in the
packet. \(J_{ij}=r_i(\{i,j\})-r_i(\{j\})\) is a difference of two unrelated
table entries and has no sign in a general quitting game; the packet's own
definitions section says as much by introducing it as a free constant.

## Where it is used, and why it is load-bearing

(4) is consumed in the next paragraph: *inside \(U\) the equilibria are strict
all Continue, of index \(+1\), and the unique regular mixed coordination
equilibrium \(q_k\), of index \(-1\); their local sum is zero*, against the
global sum \(+1\).

The \(+1\) term is the claim that all Continue is a **strict** equilibrium of
the finite-cap root game against \(b_k\). By the packet's own face system (1),
\(g_i(0)=-\delta_{k,i}\), so that claim is exactly \(\delta_{k,i}>0\) and
\(\delta_{k,j}>0\), which (4) supplies and nothing else in the packet does.

Now suppose \(J_{ij}<0\). Since \(q_k\) mixes both, \(x_j^{*}\in(0,1)\), and (3)
reads

\[
 \delta_{k,i}=\frac{x_j^{*}J_{ij}}{1-x_j^{*}}<0 ,
 \qquad\text{hence}\qquad
 g_i(0)=-\delta_{k,i}>0 .
\]

Player \(i\) strictly prefers Quit at all Continue, so all Continue is not a
root against \(b_k\) at all. The localized solution set loses its \(+1\)
component and contracts to \(\{q_k\}\); the two-term local sum that produces the
contradiction is gone. I did not work out what that branch would instead
contain — the point is only that the packet's contradiction does not arise
there, so the assertion is not cosmetic.

The exactly-zero sub-case is degenerate in a second way the packet notices:
\(J_{ij}=0\) forces \(\delta_{k,i}=0\), and then (1) makes \(g_i\) vanish
identically on the face, so \(i\) is indifferent everywhere and the mixed
component is not the isolated regular point the index \(-1\) requires. That
sub-case gets maximality; the strictly negative one gets nothing.

## The substitute argument

Derivable in a few lines from `HasUniqueAllContinueAtCapLimit`
(`Research/Quitting/FinFourProducerAtlas/StrictRayBindingCardinality.lean`),
the hypothesis the consumer already carries. No maximality, no index theory.

Write the exact endpoint difference against a cap \(b\), with \(x_h\) the Quit
probability of \(h\):

\[
 g_i(x)=\sum_{S\subseteq I\setminus\{i\}}\pi_S(x)
 \bigl[r_i(\{i\}\cup S)-(S\neq\emptyset\;?\;r_i(S):b_i)\bigr],
 \qquad
 \pi_S(x)=\prod_{h\in S}x_h\prod_{h\notin S\cup\{i\}}(1-x_h).
\]

Evaluate at the limiting cap \(\bar b\) along the one-parameter probe
\(x=t\,e_j\), \(t\in(0,1)\): only \(S=\emptyset\) and \(S=\{j\}\) carry mass, so
for every player \(i\neq j\),

\[
 \bar g_i(t\,e_j)=t\,J_{ij}-(1-t)\,\bar\delta_i ,
 \qquad
 \bar g_j(t\,e_j)=-(1-t)\,\bar\delta_j .
\]

Three readings, one per player class:

- \(j\in A\) gives \(\bar\delta_j=0\) by the definition of the binding set, so
  \(\bar g_j=0\): the probe's own mixer is exactly indifferent, at every \(t\),
  with no equation to solve;
- \(i\in A\), \(i\neq j\) gives \(\bar\delta_i=0\), so \(\bar g_i=t\,J_{ij}\);
- \(h\notin A\) has \(\bar\delta_h>0\) — the packet's own *every player outside
  \(A\) has a strictly positive limiting Continue margin* — so
  \(\bar g_h=t\,J_{hj}-(1-t)\bar\delta_h<0\) for small \(t\), strictly Continue
  with no condition on the table.

Hence for all small \(t>0\) the probe is an exact root against \(\bar b\) **iff**
\(J_{ij}\le0\), and its absorption is \(t>0\), so it is not all Continue. If
\(J_{ij}\le0\), uniqueness at \(\bar b\) is contradicted. Therefore
\(J_{ij}>0\), and symmetrically \(J_{ji}>0\) by probing at \(i\).
\(\delta_{k,i},\delta_{k,j}>0\) then follow from (3).

This is stronger than the asserted nonnegativity: it delivers the strict
inequality in one stroke, so the separate maximality treatment of \(J_{ij}=0\)
becomes unnecessary, not just unproved. It is also not circular. The
limiting cap is used only to pin the two fixed table constants \(J_{ij}\),
\(J_{ji}\); the index certificate stays at the finite cap \(b_k\), where the
packet's Lean handoff requires it.

## The packet already uses this construction

The solo case runs the identical probe:

> At the limiting cap, if \(J_{ij}\le0\), a sufficiently small solo root at
> \(j\) is exact: \(j\) is binding and indifferent, \(i\) weakly Continues, and
> the outsiders strictly Continue. This contradicts uniqueness of all Continue
> at \(\bar b\). Therefore \(J_{ij}>0\).

Same probe, same limiting cap, same weak-Continue reading, same appeal to
uniqueness. The only difference between the two occurrences is which player is
designated the mixer along the ray, and that difference is immaterial: what
makes the probe's mixer indifferent is \(\bar\delta_j=0\), which holds for
*both* binding players in the both-mixed case exactly as it does for the solo
mixer. The construction covers the both-mixed case verbatim.

So the packet holds the tool and applies it once. The both-mixed case does not
need a construction the packet lacks; it needs the one it has, applied a second
time at the other binding player.

## Source audit

Nothing below is checked in Lean by me. I built nothing and I claim no seal.

- `quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticEndpointDefectPolarity.lean`)
  is the coalition-toggle expansion the probe evaluation uses. I confirmed the
  declaration exists in the production lane; I did not read its proof.
- `HasUniqueAllContinueAtCapLimit`
  (`Research/Quitting/FinFourProducerAtlas/StrictRayBindingCardinality.lean`) is
  a `Prop` definition quantified over exact (\(\varepsilon=0\)) cap roots at
  `flow.forward.capLimit`. It is what the substitute consumes. It is a Research
  declaration, so it carries no axiom-audit record.
- `bindingFinset` and `singleton_le_capLimit`
  (`Research/Quitting/ForwardExactCapTailFlow.lean`) give the binding set and
  \(\bar\delta\ge0\). Worth stating explicitly, because it is the tempting
  shortcut: `singleton_le_capLimit` is a bound at the **limiting** cap only. The
  structure supplies no finite-cap analogue, so \(\delta_{k,i}\ge0\) is not free
  at time \(k\) and cannot be run backwards through (3) to recover the
  assertion.

The face system (1) I re-derived from the general coalition expansion and find
correct as transcribed, under the repository's Quit-minus-Continue convention
and with \(s_i=r_i(\{i\})\) the same quantity that defines `bindingFinset`.

Not checked by me: the localization step, the index-theoretic content, the solo
homotopy, the cardinal-three material, and the boundary tests.

## The degenerate sub-case is realized by a project table

Two facts about `sharpReward R singletonLevel`
(`Research/Quitting/FinFourHopfConcreteChambers.lean`), computed from its table
and cross-checked row by row against the checked expansion
`quittingFaceNumerator_sharpReward_eq_formula`. They bear on the packet's
treatment of \(J_{ij}=0\).

- \(J_{13}=0\) exactly. The packet's degenerate boundary sub-case is not
  hypothetical: an existing project table realizes it as a literal entry. So
  the sub-case cannot be waved away as generic, and a repair covering
  \(J_{ij}\le0\) in one step is worth more than one covering \(J_{ij}<0\).
- \(J_{03}=\) `sharpScale` \(=1/100\) is the only positive entry in its column,
  so that one scale constant is what stops the solo probe at player 3 from
  being exact at that table's limiting cap. Setting it to zero makes the whole
  column nonpositive and the probe exact. I confirmed the sensitivity by
  rerunning my activity-pattern enumeration with \(J_{03}=-1/100\), which
  returns the two expected solo-3 patterns.

Both are evidence about the probe's discriminating power, not about this
packet's ray, whose binding set is proper by hypothesis.

## Attribution

The substitute is not mine. It is stated as §6.1 of the untracked working note
`FIN4_BINDING_PAIR_EXPLICIT_MOD_TWO_LOCAL_COUNT.md`, which is where I first saw
it; I re-derived it from the packet's own definitions and state it here on the
whole cube rather than on the two-player face, so that the outsider step reads
as a consequence of \(\bar\delta_h>0\) rather than of a face restriction. The
observation about the packet's solo case covering the both-mixed case is what I
am adding.

## Suggested next move

Replace the two asserted sentences at (4) with the probe, in the packet's own
solo-case wording:

1. \(\bar\delta_i=\bar\delta_j=0\), by \(i,j\in A\);
2. the solo probe at \(j\) is exact against \(\bar b\) iff \(J_{ij}\le0\), its
   mixer being indifferent automatically and the outsiders strictly Continue by
   their limiting margin;
3. uniqueness at \(\bar b\) therefore gives \(J_{ij}>0\), and probing at \(i\)
   gives \(J_{ji}>0\); and
4. (3) then gives \(\delta_{k,i},\delta_{k,j}>0\).

Delete the maximality sentence; it is subsumed. Nothing downstream changes,
since (4) is consumed only through the two \(\delta\) positivities and the
regularity of \(q_k\).

## Export assessment

Mandatory gate item 2 — *complete definitions and a proof or exact
counterexample with no deferred lemma* — currently fails, on this step and, so
far as I checked, only on this step. The other gate items are unaffected by it.
The repair is contained in the packet's own solo case, so this is a text repair
rather than new mathematics, and I would expect it to clear on a re-read.

One consistency note in the packet's favour: the *Degenerate one-clock
recurrence* boundary test already records \(0<K_{ji}<J_{ji}\), which
presupposes \(J_{ji}>0\). That is downstream of the assertion, not a second
source for it, but it does mean the repair introduces no tension with the
boundary tests as written.
