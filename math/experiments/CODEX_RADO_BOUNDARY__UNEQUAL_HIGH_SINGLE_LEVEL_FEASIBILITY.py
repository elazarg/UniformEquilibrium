"""One exact finite feasibility test; no optimizer or lower-bound search.

Reuses the existing finite-law full-cap checker. Prints results only. The
twenty-date laws are a truncation of NOETHER's published rational profile.
"""

from fractions import Fraction as Q
from pathlib import Path
import sys

sys.dont_write_bytecode = True
PROJECT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(PROJECT / "Experiments" / "fin4_exact_search"))
from fin4_exact_search.engine import ProfileCertificate, RationalLaw, RewardTable
from fin4_exact_search.engine import terminal_semantics
from fin4_exact_search.direct_oracle import hazards_to_law

ROWS = {
    1: (1, 4, 0, 0), 2: (4, 1, 0, 0),
    4: (0, 0, 1, 4), 8: (0, 0, 4, 1),
    3: (2, 2, 1, 1), 5: (Q(8, 5), 1, 1, 0),
    9: (1, 0, 1, 2), 6: (0, 1, Q(8, 5), 1),
    10: (1, 2, 0, 1), 12: (1, 1, 2, 2),
    7: (1, 0, 0, 0), 11: (0, 1, 0, 0),
    13: (0, 0, 0, 1), 14: (0, 0, 1, 0),
    15: (-1, -1, -1, -1),
}
RATES = (
    (283943, 275040, 293677, 266055),
    (288138, 279248, 298184, 270014),
    (297843, 289542, 308761, 279333),
    (0, 0, 0, 0),
)


def main():
    reward = RewardTable(tuple(tuple(Q(x) / 4 for x in ROWS[s])
                               for s in range(1, 16)))
    reward.validate_normalized()
    laws = tuple(hazards_to_law(tuple(Q(RATES[t % 4][i], 10**6)
                                     for t in range(20)))
                 for i in range(4))
    certificate = ProfileCertificate.build(reward, laws, Q(1, 25000))
    certificate.verify()
    assert Q(1, 32000) < certificate.exploitability < Q(1, 25000)
    assert all(law.never > 0 for law in laws)
    midpoint = tuple((u + b) / 2 for u, b in
                     zip(certificate.payoff, certificate.cap))
    assert all(b >= u for u, b in zip(certificate.payoff, certificate.cap))
    assert max(abs(midpoint[i] - coordinate[i])
               for coordinate in (certificate.payoff, certificate.cap)
               for i in range(4)) < Q(12, 100000)
    assert 20 <= 8 * 3 + 1

    # The same center fits every m=3,...,100000. For the two small shells,
    # an actual all-Never center fits instead; no compressed-law realization
    # is asserted for the common diagonal semantic point itself.
    never = tuple(RationalLaw.pure(1, None) for _ in range(4))
    never_u, never_b, _, _ = terminal_semantics(reward, never)
    for level in (1, 2):
        assert max(abs(midpoint[i] - coordinate[i])
                   for coordinate in (never_u, never_b)
                   for i in range(4)) <= Q(12, level)

    print("NORMALIZED_TABLE_SHA256", reward.digest)
    print("EXACT_PROFILE_CHECK_PASS: 20 dates, independent marginals, positive Never")
    print("FULL_REGRET_BOUNDS: 1/32000 < E < 1/25000")
    print("HIERARCHY_LEVEL", 100000)
    print("SINGLE_SHELL_AND_CUMULATIVE_LOWER_VALUE", 0)
    print("No all-accuracy upper sequence or original zero-gap conclusion.")


if __name__ == "__main__":
    main()
