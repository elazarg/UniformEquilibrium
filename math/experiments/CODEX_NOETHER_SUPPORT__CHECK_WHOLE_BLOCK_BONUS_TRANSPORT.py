"""Exact bounded checks for the owned whole timing-block competition note.

Run from math/: python experiments/CODEX_NOETHER_SUPPORT__CHECK_WHOLE_BLOCK_BONUS_TRANSPORT.py
No files are read or written. Finite enumeration checks the two named fixtures;
it is not a general theorem or a search over auxiliary Nash correspondences.
"""

from fractions import Fraction as F
from itertools import product
from math import prod


ZERO = (F(0),) * 4


def terminal(reward, times, boundary=ZERO):
    finite = [t for t in times if t is not None]
    if not finite:
        return boundary
    first = min(finite)
    coalition = frozenset(i for i, t in enumerate(times) if t == first)
    return tuple(map(F, reward(coalition)))


def payoff(reward, laws, boundary=ZERO):
    out = [F(0)] * 4
    for atoms in product(*(tuple(law.items()) for law in laws)):
        times, weights = zip(*atoms)
        weight = prod(weights)
        values = terminal(reward, times, boundary)
        for i in range(4):
            out[i] += weight * values[i]
    return tuple(out)


def responses(reward, laws, i, deadline, boundary=ZERO):
    result = {}
    for t in list(range(deadline)) + [None]:
        replaced = list(laws)
        replaced[i] = {t: F(1)}
        result[t] = payoff(reward, replaced, boundary)[i]
    return result


def check_nash(reward, laws, deadline, bonuses=ZERO, boundary=ZERO):
    values = payoff(reward, laws, boundary)
    for i in range(4):
        pure = responses(reward, laws, i, deadline, boundary)
        pure[None] += bonuses[i]
        prescribed = values[i] + laws[i].get(None, F(0)) * bonuses[i]
        assert prescribed == max(pure.values()), (i, prescribed, pure)
    return tuple(values[i] + laws[i].get(None, F(0)) * bonuses[i]
                 for i in range(4))


def check_transport(label, reward, source, bonuses, n, block, length):
    u = check_nash(reward, source, n, bonuses)
    values = payoff(reward, source)
    caps = tuple(max(responses(reward, source, i, n + 1).values())
                 for i in range(4))
    debt = tuple(caps[i] - values[i] for i in range(4))
    credit = tuple(bonuses[i] * source[i].get(None, F(0)) for i in range(4))
    block_values = check_nash(reward, block, length, boundary=u)
    y = tuple(block[i].get(None, F(0)) for i in range(4))
    deleted = tuple(prod(y[j] for j in range(4) if j != i) for i in range(4))
    joint = prod(y)
    new_bonuses = tuple(deleted[i] * bonuses[i] for i in range(4))
    combined = []
    for i in range(4):
        law = {t: mass for t, mass in block[i].items() if t is not None}
        for t, mass in source[i].items():
            shifted = None if t is None else t + length
            law[shifted] = law.get(shifted, F(0)) + y[i] * mass
        combined.append({t: mass for t, mass in law.items() if mass})
    new_u = check_nash(reward, combined, n + length, new_bonuses)
    new_values = payoff(reward, combined)
    new_caps = tuple(max(responses(reward, combined, i, n + length + 1).values())
                     for i in range(4))
    new_debt = tuple(new_caps[i] - new_values[i] for i in range(4))
    assert new_u == block_values
    for i in range(4):
        block_pure = responses(reward, block, i, length, boundary=u)
        q = max(block_pure[t] for t in range(length))
        continuation = block_pure[None]
        h = continuation - deleted[i] * u[i]
        assert new_values[i] == block_values[i] - joint * credit[i]
        assert new_caps[i] == max(q, h + deleted[i] * caps[i])
        assert new_debt[i] == max(
            joint * credit[i] - (block_values[i] - q),
            deleted[i] * debt[i] - (deleted[i] - joint) * credit[i]
            - (block_values[i] - continuation),
        )
    assert max(new_debt) <= max(joint * max(credit), deleted[0] * max(debt))
    old_never = responses(reward, source, 0, n)[None]
    old_deleted_never = prod(source[j].get(None, F(0)) for j in range(1, 4))
    late = old_never + old_deleted_never - values[0]
    new_never = responses(reward, combined, 0, n + length)[None]
    new_deleted_never = prod(combined[j].get(None, F(0)) for j in range(1, 4))
    new_late = new_never + new_deleted_never - new_values[0]
    c0 = responses(reward, block, 0, length, boundary=u)[None]
    assert new_late == (deleted[0] * late - (deleted[0] - joint) * credit[0]
                        - (block_values[0] - c0))
    print(f"PASS {label}: E={max(debt)} -> {max(new_debt)}, bonuses={new_bonuses}")


def off_path_reward(s):
    return (1 if 0 in s else 2 if 1 in s else 0,
            -1 if 0 in s and 1 not in s else 0,
            0 if 2 in s else 1,
            0 if 3 in s else 1)


def simultaneous_reward(s):
    return (int(0 in s and 1 not in s), int(0 in s and 1 in s), 0, 0)


never = {None: F(1)}
half = {0: F(1, 2), None: F(1, 2)}

check_transport(
    "two-date off-path block", off_path_reward,
    [never] * 4, (F(2), F(1), F(1), F(1)), 1,
    [{1: F(1)}, {0: F(1)}, never, never], 2,
)
check_transport(
    "positive surviving unused bonus", simultaneous_reward,
    [half, half, never, never], (F(1, 2), F(1, 2), F(0), F(0)), 1,
    [half, {0: F(1)}, never, never], 1,
)
