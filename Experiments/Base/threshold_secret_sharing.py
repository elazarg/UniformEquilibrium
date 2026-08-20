"""E32: exact Shamir threshold privacy and its public-channel failure."""

from __future__ import annotations

from collections import Counter, defaultdict
import json


PRIME = 5
PLAYERS = (1, 2, 3)


def share(secret: int, slope: int, player: int) -> int:
    return (secret + slope * player) % PRIME


def inverse(value: int) -> int:
    return pow(value % PRIME, -1, PRIME)


def reconstruct(x1: int, y1: int, x2: int, y2: int) -> int:
    # Evaluate the unique affine polynomial through the two shares at x=0.
    return (y1 * x2 * inverse(x2 - x1) + y2 * x1 * inverse(x1 - x2)) % PRIME


def run() -> dict[str, object]:
    worlds = []
    for secret in range(PRIME):
        for slope in range(PRIME):
            shares = tuple(share(secret, slope, player) for player in PLAYERS)
            worlds.append((secret, slope, shares))

    single_view_tables = {}
    for player_index, player in enumerate(PLAYERS):
        table: dict[int, Counter[int]] = defaultdict(Counter)
        for secret, _slope, shares in worlds:
            table[shares[player_index]][secret] += 1
        for counts in table.values():
            assert set(counts.values()) == {1}
            assert set(counts) == set(range(PRIME))
        single_view_tables[str(player)] = {str(view): dict(counts) for view, counts in table.items()}

    pairs_checked = 0
    for first in range(len(PLAYERS)):
        for second in range(first + 1, len(PLAYERS)):
            for secret, _slope, shares in worlds:
                recovered = reconstruct(
                    PLAYERS[first], shares[first], PLAYERS[second], shares[second]
                )
                assert recovered == secret
                pairs_checked += 1

    public_transcripts = {}
    for secret, _slope, shares in worlds:
        public_transcripts.setdefault(shares, set()).add(secret)
    assert all(len(secrets) == 1 for secrets in public_transcripts.values())

    return {
        "experiment": "E32",
        "status": "passed",
        "field_size": PRIME,
        "worlds_checked": len(worlds),
        "single_share_views_per_player": PRIME,
        "secrets_consistent_with_each_single_view": PRIME,
        "pair_reconstructions_checked": pairs_checked,
        "public_transcripts": len(public_transcripts),
        "conclusion": (
            "A 2-of-3 Shamir sharing gives perfect one-share privacy and exact reconstruction from every pair.  Publishing the shares turns every transcript into a complete revelation of the secret, isolating private channels as the essential resource."
        ),
        "limitation": (
            "Secret sharing supplies information privacy, not incentive compatibility or a credible punishment for malformed shares."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
