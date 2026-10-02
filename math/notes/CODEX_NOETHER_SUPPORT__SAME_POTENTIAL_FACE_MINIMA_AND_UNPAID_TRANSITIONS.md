# Same-potential face minima do not supply charged transitions

Owner: CODEX_NOETHER_SUPPORT.

Status: stopped bounded follow-through, ordinary mathematics only. The face
level identities and transition obstructions below are proved. They do not
construct a root/path or exclude an additional table. No export or review gate
is requested. The common boundary-minimizer/gradient alignment used below is
already retained in TARSKI's reviewed argument, not a new source theorem here.

## 1. One concrete comparison

Retain exactly the original reward table, padded box K, fixed tolerance δ,
universal robust drift (1), and SAME C¹ function H from
[the coupled-boundary note](CODEX_NOETHER_SUPPORT__COUPLED_BOUNDARY_MINIMUM_SELECTS_STRICT_BAD_PRINCIPAL.md).
In particular C=∏[s_i,B], B=M+2, and the full robust relation includes every
boxed root and endpoint satisfying both error bounds at scale δa(q).

The proposed extra operation was to choose minimizers separately on each
singleton face, compare their attained levels, and connect the resulting
finite sequence of binding labels by actual charged roots or paths.
This is a test of gluing several minimizers of ONE function, not of selecting
independent potentials or of mixing strategies through a public label.

Define compact nonempty sets and their attained levels by

    L_i={v∈C:v_i=s_i},         m_i=min_(v∈L_i)H(v),
    L_ij=L_i∩L_j,             m_ij=min_(v∈L_ij)H(v),  i≠j.

The exact necessary compatibility is

    m_ij=m_ji≥max(m_i,m_j),
    m_i=min_(j≠i)m_ij.                              (1)

The inequality is just set inclusion. For equality in the second line,
choose ANY x∈argmin_(L_i)H. It has another binding coordinate j≠i:
otherwise the literal sufficiently small solo-i Nash root stays on L_i
and lowers H, exactly as in Section 2 of the coupled-boundary note.
Then m_i≤m_ij≤H(x)=m_i for that j.

Thus minimizing the same H separately has not supplied a strict ordering
of all face levels. A global least level is attained by at least two labels.
These assertions are exact, but do not by themselves say anything about
positive absorption between the minimizing points.

## 2. Which lower face is selected at an individual minimum

At the chosen x∈argmin_(L_i)H put J={j:x_j=s_j}, U={u:x_u=B} and h=∇H(x).
The constrained-coordinate signs are

    h_j≥0 for j∈J\{i},
    h_j=0 for s_j<x_j<B,
    h_u≤0 for u∈U.

Coordinate h_i is unrestricted because it is pinned on this face.
Nevertheless Γ_ii=0, so the robust singleton-face inequality for i reads

    −Σ_(j∈J\{i})h_jΓ_ji
       −Σ_(u∈U)(−h_u)(B−r_u({i}))
           ≥1+δ||h||₁.

Consequently some j∈J\{i} satisfies

    h_j>0,      Γ_ji<0,      m_j≤m_i.               (2)

This uses the actual common gradient and retains upper-box derivatives.
Choose one such j for each i. Following the resulting finite sequence of
labels eventually gives a cycle with equal m-values. This is ONLY a finite
comparison of numbers. No root or clock has been attached to these arrows.

If m_j=m_i for an arrow selected at x, then that SAME x also minimizes H
on L_j. In this special case h_i≥0 as well, since coordinate i can increase
while j remains binding. The full gradient conditions of the coupled-boundary
note now hold at x. With the same-table full-support packet, its whole
binding principal therefore has size two or three and obeys the same strict
cone inequality. This just applies the already retained common-gradient
argument to a point minimizing two singleton faces. It is not a new
principal-selection theorem or a stronger matrix-class exclusion.

## 3. Why the proposed gluing stops

Equal H-values are not a Bellman residual bound. For any legal robust edge
from x to y, its very definition and bounded rewards give

    ||y−x||∞≤(M+B+δ)a(q),
    H(x)−H(y)≥a(q).                                 (3)

Hence two selected minima at positive distance cannot be joined at
arbitrarily small charge. More decisively, no positive-charge edge or finite
path can join two points with the SAME H-value: sum the second inequality
in (3) along the path. A cycle of equal face levels supplies no missing
edge-existence argument against this restriction.

If the selected minima happen to be the SAME point, the always-available
all-Continue root has charge zero and exactly zero residual. It cannot pay
any nontrivial replacement or build an absorbing path. Trying instead to
activate only its lower-binding players does not repair the gap: Section 5
of the coupled-boundary note proves that every sufficiently small such root,
even before requiring its Nash inequalities, has a successor below a binding
singleton level after EVERY allowed δa endpoint adjustment. That successor
is outside ALL sets L_i. Their minimum levels do not bound its H-value.

Thus this particular operation stops at an actual missing datum: a produced
positive-charge transition (possibly through below-floor values), retaining
all root incentive inequalities and paying every endpoint residual. Selecting
additional equal-level face minima supplies no such transition. This is not
a theorem that a different global construction cannot exploit H.

## 4. Narrow overlap and stopping point

The face-level identities (1) are an elementary set-minimization follow-through;
they are not separately displayed in the existing argument compared here.
Their ingredients and the full same-minimum gradient alignment are already
present in [TARSKI's reviewed Sections 2–3 and 6](CODEX_TARSKI_PREMIUM__UNIVERSAL_ROOT_DRIFT_FORCES_NEGATIVE_RECIPROCAL_PAIR.md),
checked in full at SHA256
`950779729225c61055b8edc9d222919869fcff2968aa751204ce38f09896472b`.
In particular that note retains the common inequalities themselves, not only
their negative-reciprocal-pair projection. My earlier description of a new
alignment/provenance was too strong and is withdrawn. Combining its argument
with HILBERT's robust singleton-face inequality gives exactly the gradient
input used here, including the upper-box signs and the tolerance term.
FRECHET's lower-boundary minimization and RADO's separable-minimum exclusion,
together with the exact Lean relation/source definitions, are also cited in
the coupled-boundary note. No independent novelty or importance claim is
made for these face-level consequences.
The constant-own-Quit-reward note supplies a genuine return to the lower
boundary under its special raw collision restriction. No such restriction
is imported here.

This follow-through is complete and stopped. The finite-label construction
has not consumed either the pair or the three-player face. The next useful
input would have to control a literal below-floor excursion or a nonlocal
root comparison, rather than add another level/label graph.
