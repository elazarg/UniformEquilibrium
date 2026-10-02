# Through-mark ledger adapters: floor-to-defect, exact-stack no-go, option split

Author: CLAUDE_FABLE. These are the three formalization-sized adapters
requested by
`../notes/CODEX_DESCENDANT__PREMARK_ABSORPTION_EXACTIFICATION_MOAT.md`
(its (2.6)–(2.9), (3.2)–(3.3), (5.2)–(5.5)), composed from ledger
entries 16–18 and checked production/Research inputs. Notation: for a
profile \(\pi\) with mark \(m\): live weights \(L_t\), per-date joint
continue masses with product \(S=\prod_{t\le m}c_t\), absorption
\(A=1-S\), tails \(\tau=\pi^{(m+1)}\), and the reached cap-defect
ledger \(C=\sum_{t\le m}L_t\,\Delta_t\) with \(\Delta_t\) the total
one-stage Nash defect of the live root against the next spine cap.

**Adapter 1a (floor-to-defect).** Under the hypotheses of the eventual
pre-mark floor (limit tightness at a coordinate, tail debts
\(\to D_*\)), with \(h=(2M+\sigma)/(2M+\gamma)\) and \(a_0=1-h\): for
every \(\varepsilon>0\), eventually

\[
a_0D_*-\varepsilon\;\le\;C_n .
\]

Proof: the summed spine ledger gives \(C=D(\pi)-S\,D(\tau)\); global
minimality gives \(C\ge D_*-S\,D(\tau)\); the floor bounds
\(S\le\prod\text{opp}\le h\) (joint continue mass per date is at most
the opponents-only mass); \(D(\tau_n)\to D_*\) absorbs the error.

**Adapter 1b (charge-normalized moat, hypothesis-light).** With only
global minimality and \(D(\tau_n)\to D_*\): for every
\(\varepsilon>0\), eventually

\[
A_n\,D_*-\varepsilon\;\le\;C_n ,
\]

from \(C-A\,D_*\ge S\,(D_*-D(\tau))=-S\,e\). This is the
defect-per-absorption rate \(\ge D_*\) with no tightness input.

**Adapter 2 (exact-stack no-go).** For any word of exact cap–Nash
roots over a base whose pair debt is at most \(D_*+e\): the word's
joint continue product is at least \(D_*/(D_*+e)\) and its absorption
at most \(e/(D_*+e)\). Exactification over near-minimum tails cannot
retain absorption.

**Adapter 3 (option-budget split).** Summing the checked one-row
inequality (cap defect minus own-Quit option budget \(\le\) literal
defect) with live weights, and identifying the option weight with the
singleton stage mass:

\[
C\;\le\;2M\cdot\mathrm{Sing}+E,
\]

where \(\mathrm{Sing}\) is the total singleton stage mass through the
mark and \(E\) the live-weighted literal (prescribed-side) defect sum.
Corollary: for \(0\le c\le C\) and \(M>0\), either
\(\mathrm{Sing}\ge c/(4M)\) or \(E\ge c/2\).

Together with Adapter 1a this yields the exhaustive split (the
exactification note's (5.4)): positive singleton law mass through the
mark at scale \(a_0D_*/(8M)\), or literal endpoint work at scale
\(a_0D_*/4\) — each summand of \(E\) being an actual one-date
best-endpoint deviation gain.

Status: kernel-checked in the scratch lane (`lean/FableThroughMarkLedger.lean`;
independently verified: clean compile through the scratch olean chain,
lexical scan clean, axioms propext/Classical.choice/Quot.sound only on
all five theorems).
