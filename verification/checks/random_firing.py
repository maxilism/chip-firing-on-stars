"""Exact finite checks for the random-firing paper."""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import comb


def legal_moves(board, site):
    # Site 0 is the center. Sites 1..3, 4..6, 7..9 are consecutive arms.
    at_center = site == 0
    count = 3 if at_center else 2
    for chips in combinations(board[site], count):
        if at_center:
            targets = (1, 4, 7)
        else:
            assert site not in (3, 6, 9), "firing beyond the tested rectangle"
            inward = 0 if site in (1, 4, 7) else site - 1
            targets = (inward, site + 1)
        state = list(board)
        state[site] = tuple(x for x in board[site] if x not in chips)
        for x, target in zip(chips, targets):
            state[target] = tuple(sorted((*state[target], x)))
        yield tuple(state)


def endpoints():
    start = (tuple(range(1, 10)),) + ((),) * 9
    active = {start: Fraction(1)}
    done = defaultdict(Fraction)
    while active:
        next_round = defaultdict(Fraction)
        for board, probability in active.items():
            sites = [i for i, pile in enumerate(board)
                     if len(pile) >= (3 if i == 0 else 2)]
            if not sites:
                assert not board[0] and all(len(pile) == 1 for pile in board[1:])
                rows = tuple(tuple(board[i+j][0] for j in range(3)) for i in (1, 4, 7))
                done[rows] += probability
                continue
            for site in sites:
                moves = list(legal_moves(board, site))
                share = probability / (len(sites) * len(moves))
                for successor in moves:
                    next_round[successor] += share
        assert sum(next_round.values()) + sum(done.values()) == 1
        active = next_round
    return done


def two_chip_fibers(k):
    labels = set(range(1, 2*k + 1))
    counts = Counter()
    for batch in combinations(sorted(labels), k):
        other = sorted(labels - set(batch))
        board = tuple(tuple(sorted(pair)) for pair in zip(batch, other))
        counts[board] += 1
    for board, count in counts.items():
        blocks = 1 + sum(left[1] < right[0] for left, right in zip(board, board[1:]))
        assert count == 2**blocks
    fully_sorted = tuple((2*i+1, 2*i+2) for i in range(k))
    assert [board for board, count in counts.items() if count == 2**k] == [fully_sorted]


def batch_endpoint(a, b, t, remaining, late, choices):
    # Types 0, 1, 2 respectively compare AB, AT, BT first.
    types = dict(zip(late, choices))
    fourth = set(remaining)
    winners, unused = [], []
    for i in range(3):
        pairs = ((a[i], b[i], t[i]), (a[i], t[i], b[i]), (b[i], t[i], a[i]))
        first, second, other = pairs[types.get(i, 0)]
        if i in types:
            fourth.add(min(first, second))
        winners.append(max(first, second))
        unused.append(other)
    assert len(fourth) == 3
    second_pairs = list(zip(unused, sorted(fourth)))
    fifth = sorted(min(pair) for pair in second_pairs)
    outer_pairs = list(zip(winners, (max(pair) for pair in second_pairs)))
    inner_pairs = list(zip(fifth, (min(pair) for pair in outer_pairs)))
    first_column = sorted(min(pair) for pair in inner_pairs)
    middle = [max(pair) for pair in inner_pairs]
    last = [max(pair) for pair in outer_pairs]
    return tuple(zip(first_column, middle, last))


def batch_probabilities():
    labels = set(range(1, 10))
    arms = range(3)
    counts = [Counter() for _ in range(4)]
    for a in combinations(sorted(labels), 3):
        for b in combinations(sorted(labels - set(a)), 3):
            fresh = labels - set(a) - set(b)
            for r, counts_r in enumerate(counts):
                for early in combinations(arms, r):
                    late = tuple(i for i in arms if i not in early)
                    pool = fresh | {min(a[i], b[i]) for i in early}
                    for t in combinations(sorted(pool), 3):
                        remaining = pool - set(t)
                        for choices in product(range(3), repeat=len(late)):
                            board = batch_endpoint(a, b, t, remaining, late, choices)
                            counts_r[board] += 1

    result = Counter()
    for r, counts_r in enumerate(counts):
        # r is uniform on 0..3. Given r, schedules within this class have equal weight.
        weight = Fraction(1, 4 * comb(9, 3) * comb(6, 3) * comb(3, r)
                          * comb(3 + r, 3) * 3**(3-r))
        for board, count in counts_r.items():
            result[board] += weight * count
    return result, sum(sum(group.values()) for group in counts)


if __name__ == "__main__":
    for k in range(1, 11):
        two_chip_fibers(k)
    print("Two-chip endpoint probabilities agree with every first batch through ten arms")

    direct = endpoints()
    batches, count = batch_probabilities()
    assert direct == batches and len(direct) == 47 and count == 411600
    standard = [b for b in direct if all(b[0][j] < b[1][j] < b[2][j] for j in range(3))]
    assert len(standard) == 42 and sum(direct[b] for b in standard) == Fraction(2509, 2520)
    print(count, "batch descriptions match all 47 exact endpoint probabilities on three arms")
