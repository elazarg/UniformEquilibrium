# Candidate table B

Status: **REFUTED** (by an external review; verified by exact hand
arithmetic below). Retained as a worked negative example. Fact base:
`FIN4_COUNTEREXAMPLE_DOSSIER.md`.

## Refutation

\(B\) has a continuum of stationary exact terminal Nash profiles. Let only
player \(2\) quit, at stationary rate \(q\), all others Never. Absorption is
almost sure at \(\{2\}\); the payoff is \(r(\{2\})=(0,0,1,4)\).

- Player \(2\): any eventual quit yields \(1\), Never yields \(0\); cap
  \(=1\), attained.
- Players \(0,1\): quitting at any live date is worth
  \(q\,r_i(\{i,2\})+(1-q)\,r_i(\{i\}) = q\cdot(-1)+(1-q)\cdot1 = 1-2q\),
  Never is worth \(r_i(\{2\})=0\); cap \(=\max(0,\,1-2q)=0\) for
  \(q\ge\tfrac12\), attained.
- Player \(3\): quitting is worth \(q\cdot5+(1-q)\cdot1 = 1+4q\), Never is
  worth \(r_3(\{2\})=4\); cap \(=\max(4,\,1+4q)=4\) for \(q\le\tfrac34\),
  attained.

So every \(q\in[\tfrac12,\tfrac34]\) gives an exact equilibrium with payoff
\((0,0,1,4)\), and \(B\) has a uniform-equilibrium payoff.

## Post-mortem

The audits below covered **pure** profiles only; the clearing profile is
stationary mixed with one-player support — the simplest class above pure.
The exact reason for the failure is the covering criterion of
`NONLOCAL_RECENTERING_ATTACK.md` §2: at owner \(2\), the three affine
outsider functions \(g_{2,o}(q)\) are \(1-2q\), \(1-2q\), \(4q-3\), whose
maximum is \(\le0\) exactly on \(q\in[\tfrac12,\tfrac34]\). The colliders
of the design are only the \(q=1\) endpoints of that covering requirement,
and the preemption signs only the \(q\to0\) endpoints; the middle of the
interval was left uncovered.

Requirements for any future candidate \(B'\), before any dynamic analysis:

1. solos \(\ge0\) and, at every owner \(j\), the covering criterion with a
   margin: \(\max_{o\ne j} g_{j,o}(q)\ge\gamma'\) for **all**
   \(q\in(0,1]\);
2. exact infeasibility of the stationary-equilibrium system for **all**
   fifteen support patterns (a finite semialgebraic check, decidable in
   exact arithmetic);
3. only then the audits below and the known nonstationary compilers.

The construction and audits are kept for reference; no claim below
survives beyond what the refutation leaves intact.

## Design rules

A candidate must satisfy every table-level necessary condition (R3, R4,
normality) while defeating the known pure and stationary mechanisms:

1. solos \(\equiv1\): all players punishment-normal; all-Continue is
   exploitable by \(1\);
2. singleton comparison matrix in regime 5 — reused from \(W\), inheriting
   full core, Q, no homogeneous solution, \(\bar Q\)-failure;
3. a fixed-point-free collider cycle with, on each designed pair
   \(\{j,o\}\), the collider \(o\) gaining
   (\(r_o(\{j,o\})\ge r_o(\{j\})+1\)) while the other member flees
   (\(r_j(\{o\})>r_j(\{j,o\})\)): every pure row has an entrance and an
   exit that never match;
4. triples and the quad bad for members, neutral for outsiders;
5. the known sufficient conditions violated: some \(r_i(S)>r_i(\{i\})\)
   with \(i\in S\); membership gains not affine; passive rewards nonzero;
   preemption cycles present.

## The table

Collider cycle \(0\to1\to2\to3\to0\).

| Coalition | \(r_0\) | \(r_1\) | \(r_2\) | \(r_3\) |
|---|---|---|---|---|
| \(\{0\}\) | 1 | 4 | 0 | 0 |
| \(\{1\}\) | 4 | 1 | 0 | 0 |
| \(\{2\}\) | 0 | 0 | 1 | 4 |
| \(\{3\}\) | 0 | 0 | 4 | 1 |
| \(\{0,1\}\) | 0 | **5** | 0 | 0 |
| \(\{1,2\}\) | 0 | −1 | **2** | 0 |
| \(\{2,3\}\) | 0 | 0 | −1 | **5** |
| \(\{0,3\}\) | **2** | 0 | 0 | −1 |
| \(\{0,2\}\) | −1 | 0 | −1 | 0 |
| \(\{1,3\}\) | 0 | −1 | 0 | −1 |
| \(\{0,1,2\}\) | −5 | −5 | −5 | 0 |
| \(\{0,1,3\}\) | −5 | −5 | 0 | −5 |
| \(\{0,2,3\}\) | −5 | 0 | −5 | −5 |
| \(\{1,2,3\}\) | 0 | −5 | −5 | −5 |
| \(\{0,1,2,3\}\) | −6 | −6 | −6 | −6 |

## Audits (exact arithmetic)

- **Matrix side** (inherited, machine-checked for the matrix itself):
  singleton rows equal those of \(W\), so \(M_B=M_W\): regime 5, full
  normal core, Q, no homogeneous solution, \(\bar Q\) failing on four
  mutual pairs.
- **Normality:** solos \(=1>0\), so every player is punishment-normal by
  the ceiling of dossier §4.4.
- **Colliders** (margin \(\ge1\)): \(1\) joins \(0\) (\(5>4\)); \(2\)
  joins \(1\) (\(2>0\)); \(3\) joins \(2\) (\(5>4\)); \(0\) joins \(3\)
  (\(2>0\)). The map \(0\mapsto1\mapsto2\mapsto3\mapsto0\) is
  fixed-point-free.
- **Every pure profile strictly unstable:**
  - Never: any solo quit gains \(1\);
  - each singleton row is entered by its collider (gain \(\ge1\));
  - each pair row is fled by one member: \(0\) leaves \(\{0,1\}\) for
    \(r_0(\{1\})=4>0\); \(1\) leaves \(\{1,2\}\) for \(0>-1\); \(2\)
    leaves \(\{2,3\}\) for \(0>-1\); \(3\) leaves \(\{0,3\}\) for
    \(0>-1\); on \(\{0,2\}\) and \(\{1,3\}\) either member gains \(1\) by
    leaving;
  - each triple is fled to the outsider payoff \(0>-5\); the quad to
    \(0>-6\);
  - joining a designed pair is never profitable (triples pay members
    \(-5\)).
- **Known sufficient conditions violated:** \(r_1(\{0,1\})=5>1\)
  (solo-exit preference fails); membership gains not affine (for player
  \(1\): gains \(1,1,-1,-1\) on backgrounds
  \(\varnothing,\{0\},\{2\},\{3\}\) predict \(-1\) on \(\{0,2\}\), actual
  \(-5\)); passive rewards nonzero (\(r_1(\{0\})=4\)); preemption
  2-cycles present between the blocks \(\{0,1\}\) and \(\{2,3\}\).

## Former open list (superseded)

Item 1 of the former open list — "no stationary mixed exact terminal Nash
profile (a finite polynomial system in four quit rates; unchecked)" — is
now answered negatively by the refutation above; the remaining items are
moot for \(B\) and become the entry requirements for \(B'\) in the
post-mortem.
