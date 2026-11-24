"""Finite checks for batch insertion and the five-cell construction."""
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import factorial, prod


def terminal_boards(arms, depth):
    """Search every legal firing. Each site is a bit mask of chip labels."""
    first_sites = tuple(range(1, arms * depth + 1, depth))

    @lru_cache(None)
    def visit(board):
        ends = set()
        for site, pile in enumerate(board):
            if pile.bit_count() < (arms if site == 0 else 2):
                continue
            if site == 0:
                targets = first_sites
            else:
                assert site % depth != 0, "firing beyond the tested rectangle"
                inward = 0 if site in first_sites else site - 1
                targets = (inward, site + 1)
            chips = [1 << i for i in range(pile.bit_length()) if pile & (1 << i)]
            for group in combinations(chips, len(targets)):
                following = list(board)
                following[site] -= sum(group)
                for target, chip in zip(targets, group):
                    following[target] |= chip
                ends.update(visit(tuple(following)))
        return frozenset(ends or {board})

    return visit


def check_insertions(k, m):
    size = k * m
    original = terminal_boards(k, m)((2**size - 1,) + (0,) * size)
    labels = range(size + k)
    checked = 0
    for batch in combinations(labels, k):
        old_labels = sorted(set(labels) - set(batch))
        visit = terminal_boards(k, m + 1)
        for old in original:
            start = [sum(1 << x for x in batch)]
            expected = [0]
            for arm, new_label in enumerate(batch):
                row = old[1 + arm*m : 1 + (arm+1)*m]
                relabeled = [1 << old_labels[chip.bit_length()-1] for chip in row]
                start.extend([*relabeled, 0])
                expected.extend(sorted([*relabeled, 1 << new_label]))
            assert visit(tuple(start)) == {tuple(expected)}
            checked += 1
        visit.cache_clear()
    return checked


def dimension(rows):
    hooks = (length - j + sum(lower > j for lower in rows[i+1:])
             for i, length in enumerate(rows) for j in range(length))
    return factorial(sum(rows)) // prod(hooks)


def complement(k, m):
    # Rotate the complement of (2,2,1) in the rectangle through 180 degrees.
    return (m,) * (k-3) + (m-1, m-2, m-2)


def corner_tableaux(k, m):
    rows = [[0] * m for _ in range(k)]
    rows[0][:2], rows[1][:2], rows[2][0] = [1, 4], [2, 5], 3

    def fill(label):
        if label > k*m:
            yield tuple(tuple(row) for row in rows)
            return
        for i, row in enumerate(rows):
            for j, cell in enumerate(row):
                if cell or (i and not rows[i-1][j]) or (j and not row[j-1]):
                    continue
                row[j] = label
                yield from fill(label + 1)
                row[j] = 0

    yield from fill(6)


def exchange_three_and_five(tableau):
    k, m = len(tableau), len(tableau[0])
    a, b, c, *remaining = zip(*tableau)
    center = set(range(1, k*m + 1))
    sites = [[[] for _ in row] for row in tableau]
    reserved = {chip for column in remaining for chip in column}

    def dispatch(chips):
        assert len(chips) == k and list(chips) == sorted(set(chips))
        for row, chip in zip(sites, chips):
            center.remove(chip)
            row[0].append(chip)

    def fire(arm, site, pair=None):
        row = sites[arm]
        low, high = sorted(row[site] if pair is None else pair)
        row[site].remove(low)
        row[site].remove(high)
        if site == 0:
            center.add(low)
        else:
            row[site-1].append(low)
        row[site+1].append(high)

    for column in (a, b, c):
        dispatch(column)
    for i in range(k):
        fire(i, 0, (b[i] if i == 1 else a[i], c[i]))
    dispatch(sorted(center - reserved))

    def sweep(length):
        for i in range(k):
            for j in range(length):
                fire(i, j)
        dispatch(sorted(center - reserved))

    sweep(2)
    sweep(1)
    for old_width, column in enumerate(remaining, 3):
        reserved.difference_update(column)
        dispatch(column)
        for length in range(old_width, 0, -1):
            sweep(length)
    assert not center and all(len(pile) == 1 for row in sites for pile in row)
    result = tuple(tuple(pile[0] for pile in row) for row in sites)
    swap = {3: 5, 5: 3}
    assert result == tuple(tuple(swap.get(x, x) for x in row) for row in tableau)
    return result


if __name__ == "__main__":
    small = [(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2)]
    total = sum(check_insertions(k, m) for k, m in small)
    assert total == 625
    print(total, "augmented boards have the predicted unique endpoint")

    images = 0
    for k, m in [(3, 3), (3, 4), (4, 3), (3, 5), (5, 3), (4, 4)]:
        endpoints = {exchange_three_and_five(t) for t in corner_tableaux(k, m)}
        assert len(endpoints) == dimension(complement(k, m))
        images += len(endpoints)
    assert images == 2039
    print(images, "distinct nonstandard tableaux reached by the five-cell construction")

    for k in range(3, 26):
        for m in range(3, 26):
            n = k*m
            ratio = Fraction(dimension(complement(k, m)), dimension((m,) * k))
            formula = Fraction(k*k * (k*k-1) * (k-2) * m*m * (m*m-1) * (m+2),
                               24 * prod(range(n-4, n+1)))
            assert ratio == formula and ratio >= Fraction(1, 81)
    print("529 hook ratios agree with the formula and its lower bound")
