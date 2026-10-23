"""Exact properness control for the generic analytic global-barrier no-go.

No numerical linear algebra or external libraries are used. All 256 complete
cap branch patterns are checked by integer determinant calculations.
This is a polynomial-identity control, not a positive-gap reward example.
"""

from itertools import product


GAMMA = (
    (0, -9, -6, 7),
    (-6, 0, 4, 7),
    (7, 8, 0, -1),
    (-1, -3, 9, 0),
)
MASKS = (3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15)
HIGHER = (
    (5, 6, -3, -1, 6, -7, -6, 3, -9, 3, 7),
    (-6, 5, -8, 9, -7, -8, 2, -9, -2, 6, -8),
    (3, -1, 1, 9, -5, 9, 0, 3, 9, 5, 8),
    (8, 4, 5, 4, -5, -3, -6, -9, 7, -7, 3),
)
REWARD = {}
for who in range(4):
    for owner in range(4):
        REWARD[who, 1 << owner] = GAMMA[who][owner]
    for mask, value in zip(MASKS, HIGHER[who]):
        REWARD[who, mask] = value


def outcome_reward(who, draws):
    first = min(draws.values())
    coalition = sum(1 << player for player, date in draws.items() if date == first)
    return REWARD[who, coalition]


def scaled_expectation(who, fixed):
    """Return 4^n times expectation over n unfixed base-law players.

    Each unfixed player uses probabilities 1/4, 1/4, 1/2 at 0,1,2.
    Fixed date 3 is equivalent to literal Never when others finish by 2.
    """
    free = [player for player in range(4) if player not in fixed]
    answer = 0
    for dates in product((0, 1, 2), repeat=len(free)):
        draws = dict(fixed)
        draws.update(zip(free, dates))
        weight = 1
        for date in dates:
            weight *= 2 if date == 2 else 1
        answer += weight * outcome_reward(who, draws)
    return answer


def scaled_jacobian_rows():
    """Form every row of 64 times the exact derivative at x*.

    A derivative in a_j replaces j's law by delta_0-delta_2;
    a derivative in b_j replaces it by delta_1-delta_2.
    This is exact because outcomes are affine in each marginal law.
    """
    payoff_rows = []
    query_rows = {}
    for who in range(4):
        payoff_row = []
        for player in range(4):
            for date in (0, 1):
                payoff_row.append(
                    scaled_expectation(who, {player: date})
                    - scaled_expectation(who, {player: 2})
                )
        payoff_rows.append(payoff_row)
        for query in range(4):
            query_row = []
            for player in range(4):
                for date in (0, 1):
                    if player == who:
                        query_row.append(0)
                    else:
                        query_row.append(
                            4
                            * (
                                scaled_expectation(who, {who: query, player: date})
                                - scaled_expectation(who, {who: query, player: 2})
                            )
                        )
            query_rows[who, query] = query_row
    return payoff_rows, query_rows


def determinant(matrix):
    """Exact integer determinant by fraction-free Bareiss elimination."""
    work = [list(row) for row in matrix]
    size = len(work)
    assert all(len(row) == size for row in work)
    denominator = 1
    sign = 1
    for column in range(size - 1):
        pivot_row = next((row for row in range(column, size) if work[row][column]), None)
        if pivot_row is None:
            return 0
        if pivot_row != column:
            work[column], work[pivot_row] = work[pivot_row], work[column]
            sign = -sign
        pivot = work[column][column]
        for row in range(column + 1, size):
            for other in range(column + 1, size):
                numerator = pivot * work[row][other] - work[row][column] * work[column][other]
                quotient, remainder = divmod(numerator, denominator)
                assert remainder == 0
                work[row][other] = quotient
            work[row][column] = 0
        denominator = pivot
    return sign * work[-1][-1]


def main():
    assert len(REWARD) == 60
    assert all(REWARD[i, 1 << i] == 0 for i in range(4))
    assert tuple(mask for mask in range(1, 16) if mask.bit_count() >= 2) == MASKS
    payoff_rows, query_rows = scaled_jacobian_rows()
    residue = 1
    count = 0
    for branch in product(range(4), repeat=4):
        matrix = payoff_rows + [query_rows[i, branch[i]] for i in range(4)]
        value = determinant(matrix)
        assert value != 0, branch
        residue = residue * value % 1000003
        count += 1
    assert count == 256
    assert residue == 989105
    assert determinant(GAMMA) == 7345
    inverse_column_numerator = (777, 308, 189, 558)
    assert all(value > 0 for value in inverse_column_numerator)
    assert tuple(
        sum(GAMMA[i][j] * inverse_column_numerator[j] for j in range(4))
        for i in range(4)
    ) == (0, 0, 7345, 0)

    print("PASS: all sixty native rewards, fixed singleton matrix and own singletons zero")
    print("PASS: complete response classes 0,1,2 and after-support/Never retained")
    print("PASS: all 256 exact 8x8 branch determinants are nonzero")
    print("PASS: degree-2048 guard product = 989105 mod 1000003")
    print("This certifies polynomial properness only; no positive-gap example is claimed.")


if __name__ == "__main__":
    main()
