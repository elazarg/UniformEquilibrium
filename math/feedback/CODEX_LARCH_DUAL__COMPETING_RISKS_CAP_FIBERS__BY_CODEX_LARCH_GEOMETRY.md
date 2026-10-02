# Review of finite dated-law identification and cap fibers

Reviewer: CODEX_LARCH_GEOMETRY. Date: 2026-09-07.

The [competing-risks sketch](../notes/CODEX_LARCH_DUAL__COMPETING_RISKS_CAP_FIBERS.md)
passes this independent ordinary-mathematical review. I checked its finite
compatibility, one-coordinate identification, interval closure, and
same-law completion arguments. No Lean compilation or paper-attribution
audit was performed.

At a positive-reach date, summing observed root masses over coalitions
containing i gives the player's conditional quitting hazard, so qᵢ=mᵢ/R
is correctly identified. The nonempty product tests also recover Continue
probability by normalization, giving the required telescoping reach. Their
denominator-cleared version is exact for n≥2, including zero-reach rows
whose masses vanish by nonnegativity. After a positive Never limit, the
zero observed tail forces all later hazards zero; thus the complete laws
are identified in that case.

When Never mass is zero, the last positive-reach row has at least one sure
quitter. If it has two, each unilateral deletion retains a sure quitter and
hidden suffixes cannot affect caps. If it has a unique sure player o, every
other player's deletion is still blocked by o. No second ambiguous cap
coordinate can be created through a different player's off-path suffix.

In the unique-owner case, the opponents' joint survival through the final
root is strictly positive: every earlier reach is positive and no opponent
quits surely at the final root. Conditioning on that event preserves
independence because it is an intersection of separate clock-survival
events. Thus the conditional opponent suffix can be chosen arbitrarily as
a product of stopping laws without changing any observed terminal mass.

The owner's early deterministic responses have exactly the cap C. For
every later response, events of the opponents by the final root contribute
the same A, and the surviving opponent suffix contributes its response
value multiplied by ρ. Never belongs to this second class. This checks
B_o=max(C,A+ρb), including the order of conditioning and supremum. The
remaining caps and all prescribed payoffs remain fixed under the suffix
replacement.

The upper endpoint R_o^+ is attainable as stated: choose a maximizing
coalition's opponent members to Quit together and let o join or Never.
Every cap remains bounded by the largest reward, so the resulting test
attains the cap as well. If zero is maximal, all opponents Never gives
cap zero. Convex interpolation of each opponent's law is a continuous path
in product total variation. Uniform bounded-test control makes the complete
cap continuous along that path, despite the potentially infinite response
menu. Its scalar range is therefore an interval, whose closure has exactly
the proposed endpoints. No exact lower-endpoint attainment is inferred.

The stationary-punishment completion has the right semantic interface:
an ε-accurate suffix minimizer changes the owner's cap by at most ρε
above the infimum while preserving the full dated law and all nonowner
caps. The note appropriately credits the actual punishment producer to
the existing stationary/behavioral minimax theorem. Its new organizing
content is the finite-law identification and exact fiber description, not
construction of punishment from a new hypothesis.

Both positive tests and the rejected one-date singleton mixture check out.
The latter unmarked mixture can indeed be realized chronologically by one
player mixing an early Quit with Never and the other Quitting surely later;
its dated law is different, exactly as required.

No unresolved mathematical objection was found. The classification is for
exact finite dated laws; it does not imply a quantitative extension near
vanishing reach, preservation of whole response graphs, or an arbitrary-game
producer of useful observed laws.
