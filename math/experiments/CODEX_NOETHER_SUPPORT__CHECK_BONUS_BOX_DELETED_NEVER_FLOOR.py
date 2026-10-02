"""Exact small-calendar checks for the deleted-Never floor; writes no files."""

from fractions import Fraction as F
from functools import lru_cache
from itertools import product


def reward(coalition):
    pivot = F(0) if 0 not in coalition else F(1) if len(coalition) == 1 else F(2)
    followers = []
    for j in range(1, 4):
        if j in coalition:
            followers.append(F(-1) if len(coalition) > 1 else F(0))
        else:
            followers.append(F(1) if 0 in coalition else F(0))
    return (pivot, *followers)


def pure_reward(times):
    finite = [time for time in times if time is not None]
    if not finite:
        return (F(0),) * 4
    first = min(finite)
    return reward({i for i, time in enumerate(times) if time == first})


def half_grid(size):
    return [tuple(F(count, 2) for count in counts)
            for counts in product(range(3), repeat=size) if sum(counts) == 2]


def check(horizon):
    actions = (*range(horizon), None)
    laws = half_grid(len(actions))
    supported = [tuple((actions[t], mass) for t, mass in enumerate(law) if mass)
                 for law in laws]

    @lru_cache(None)
    def responses(player, opponent_ids):
        opponents = [i for i in range(4) if i != player]
        values = []
        for action in actions:
            value = F(0)
            for atoms in product(*(supported[index] for index in opponent_ids)):
                times = [None] * 4
                times[player] = action
                probability = F(1)
                for who, (time, mass) in zip(opponents, atoms):
                    times[who] = time
                    probability *= mass
                value += probability * pure_reward(times)[player]
            values.append(value)
        return tuple(values)

    bonus_vectors = ((F(0),) * 4, (F(1, 2),) * 4,
                     (F(3, 4), F(0), F(1, 4), F(1, 2)))
    equilibrium_counts = [0] * len(bonus_vectors)
    for indices in product(range(len(laws)), repeat=4):
        original_responses = [responses(i, tuple(indices[j] for j in range(4) if j != i))
                              for i in range(4)]
        original_values = [sum((mass * value for mass, value in zip(laws[indices[i]], original_responses[i])), F(0))
                           for i in range(4)]
        expected_form = (laws[indices[0]][-1] == 0 and
                         all(laws[indices[j]][-1] == 1 for j in range(1, 4)))
        for b, bonuses in enumerate(bonus_vectors):
            is_nash = True
            for i in range(4):
                auxiliary_value = original_values[i] + bonuses[i] * laws[indices[i]][-1]
                auxiliary_cap = max(value + (bonuses[i] if a is None else 0)
                                    for a, value in zip(actions, original_responses[i]))
                if auxiliary_cap != auxiliary_value:
                    is_nash = False
                    break
            assert is_nash == expected_form
            if is_nash:
                equilibrium_counts[b] += 1
                assert original_values == [F(1)] * 4
                deleted_never = F(1)
                for j in range(1, 4):
                    deleted_never *= laws[indices[j]][-1]
                late = original_responses[0][-1] + deleted_never - original_values[0]
                assert deleted_never == 1 and late == 0
    assert equilibrium_counts == [horizon * (horizon + 1) // 2] * len(bonus_vectors)
    print(f"N={horizon}: {len(laws) ** 4} exact grid profiles; auxiliary NE counts={equilibrium_counts}; every D0=1 and L0=0")


if __name__ == "__main__":
    for n in (1, 2, 3):
        check(n)
