"""Replay the three-chip star witnesses and check the descent and probability calculations."""

from bisect import bisect_right
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path
import gzip
import json

from random_firing import batch_probabilities, endpoints


WITNESSES = Path(__file__).resolve().parents[1] / "witnesses"
FIRST_PAIRS = ((0, 1), (0, 2), (1, 2))  # AB, AT, BT.
SECOND_PAIRS = ((2, 3), (1, 3), (0, 3))  # TD, BD, AD, respectively.


def verify_partitions():
    """For each two-low signature, identify both the low-middle and return types."""
    partitions = {}
    for low in combinations(range(4), 2):
        return_types = set()
        middle_types = []
        for kind, (first, second) in enumerate(zip(FIRST_PAIRS, SECOND_PAIRS)):
            if any(column in low for column in second):
                return_types.add(kind)
            if low == first or low == second:
                middle_types.append(kind)
        assert len(middle_types) == 1 and len(return_types) >= 2
        partitions[low] = (middle_types[0], return_types)
    return partitions


def verify_sampled_ranks():
    """Count low labels selected at uniform ranks of a sorted independent sample."""
    cases = 0
    for k in range(1, 11):
        for q in range(k + 1):
            subsets = list(combinations(range(k), q))
            for a in range(k + 1):
                # Choose a low labels before sorting, then q ranks after sorting.
                ranks = Counter(sum(i < a for i in sample) for sample in subsets)
                for r in range(min(a, q) + 1):
                    # Equivalent count by choosing q identities before sorting.
                    others = a - r
                    rest = comb(k - q, others) if others <= k - q else 0
                    assert comb(k, a) * ranks[r] == comb(k, q) * comb(q, r) * rest
                cases += 1
    return cases


def verify_history(rows, moves, partitions, totals):
    k = len(rows)
    center = [move[1:] for move in moves if move[0] == 0]
    assert len(center) == 6
    a_col, b_col, third = center[:3]
    seen_batches = 0
    kinds = {}
    early = {}
    first_returns = []
    for site, *chips in moves:
        if site == 0:
            seen_batches += 1
        elif site % 3 == 1:
            i = (site - 1) // 3
            if i in kinds:
                continue
            arrivals = (a_col[i], b_col[i], third[i])
            if seen_batches == 2:
                assert chips == sorted(arrivals[:2])
                early[i] = chips[0]
                kinds[i] = 0
            else:
                assert seen_batches == 3 and len(set(arrivals)) == 3
                kinds[i] = FIRST_PAIRS.index(tuple(j for j, x in enumerate(arrivals) if x in chips))
            first_returns.append(chips[0])
    assert len(kinds) == k
    replays = set(third) & set(a_col + b_col)
    assert replays <= set(early.values())
    selected_arms = [i for i, chip in early.items() if chip in replays]
    fresh = sorted(set(third) - replays)
    spares = sorted(set(range(1, 3*k + 1)) - set(a_col + b_col + third))
    assert len(spares) == len(replays)
    middle = [row[1] for row in rows]
    descents = [i for i in range(k-1) if middle[i] > middle[i+1]]
    assert all(kinds[i] != kinds[i+1] for i in descents)
    ab_middles = [middle[i] for i in range(k) if kinds[i] == 0]
    assert all(left < right for left, right in zip(ab_middles, ab_middles[1:]))
    assert len(descents) <= sum(kind != 0 for kind in kinds.values())
    for cut in range(3*k + 1):
        # Low means rank <= cut, equivalent to a threshold in the next label gap.
        a, b, t, d, e = (bisect_right(column, cut) for column in center[:5])
        s = sum(i < max(a, b) for i in selected_arms)
        assert s == sum(chip <= cut for chip in replays)
        fresh_count = bisect_right(fresh, cut)
        assert t == s + fresh_count
        from_a = sum(i < a for i in selected_arms)
        from_b = sum(i < b for i in selected_arms)
        assert t == max(fresh_count + from_a, fresh_count + from_b)
        assert d == sum(chip <= cut for chip in first_returns) - s + bisect_right(spares, cut)
        totals["cuts"] += 1
        counts = (a, b, t, d)
        _, u, v, _ = sorted(counts)
        if u == v:
            continue
        signature = tuple(j for j, count in enumerate(counts) if count > u)
        low_type, return_types = partitions[signature]
        supplied = sum(kinds[i] in return_types for i in range(u, v))
        assert e >= u + supplied
        end = min(e, v)
        for i in range(u, end):
            assert (middle[i] <= cut) == (kinds[i] == low_type)
        for i in range(u + u % 2, end - 1, 2):
            predicted = kinds[i] != low_type and kinds[i+1] == low_type
            assert predicted == (middle[i] > cut >= middle[i+1])
            totals["observed pair crossings"] += predicted
        totals["nonempty bands"] += 1
    totals["boards"] += 1


def replay(rows, moves):
    """Apply each move at its physical site and check the terminal labels."""
    # Sites are (arm, depth); None represents the center.
    k = len(rows)
    board = defaultdict(set)
    board[None] = set(range(1, 3*k+1))
    for move in moves:
        v, *labels = move
        assert labels == sorted(set(labels)), ('not strictly increasing', move)
        if v == 0:
            source = None
            assert len(labels) == k
            destinations = [(arm, 1) for arm in range(1, k+1)]
        else:
            assert 1 <= v <= 3*k and len(labels) == 2
            arm, depth = 1+(v-1)//3, 1+(v-1)%3
            source = (arm, depth)
            destinations = [None if depth == 1 else (arm, depth-1), (arm, depth+1)]
        assert board[source] >= set(labels), ('chips missing', move)
        board[source].difference_update(labels)
        for label, destination in zip(labels, destinations):
            board[destination].add(label)
    assert not board[None]
    for pos, labels in board.items():
        if pos is not None and labels:
            arm, depth = pos
            assert 1 <= depth <= 3 and labels == {rows[arm-1][depth-1]}
    assert all(len(row)==3 for row in rows)
    assert all(board[(i,d)] == {rows[i-1][d-1]} for i in range(1,k+1) for d in (1,2,3))
    return tuple(tuple(row) for row in rows)


def verify_archive():
    partitions = verify_partitions()
    totals = Counter()
    expected_boards = (1, 5, 47, 655, 12019)
    for k, expected in enumerate(expected_boards, start=1):
        boards = set()
        with gzip.open(WITNESSES / f"k{k}.jsonl.gz", "rt", encoding="ascii") as source:
            for line in source:
                record = json.loads(line)
                rows = replay(**record)
                assert len(rows) == k and rows not in boards
                boards.add(rows)
                verify_history(rows, record["moves"], partitions, totals)
        assert len(boards) == expected
    assert totals["boards"] == 12727 and totals["cuts"] == 201328
    assert totals["nonempty bands"] == 109934 and totals["observed pair crossings"] == 6432
    return totals


def verify_probabilities():
    """Compare full endpoint masses under the batch model and the physical Markov chain."""
    law, paths = batch_probabilities()
    assert law == endpoints() and sum(law.values()) == 1
    assert len(law) == 47 and paths == 411600
    has_descent = sum(prob for board, prob in law.items()
                      if any(left[1] > right[1] for left, right in zip(board, board[1:])))
    assert has_descent == Fraction(11, 2520)
    return paths, len(law), has_descent


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run with assertions enabled.")
    print(f"Uniform rank sampling agrees with identity sampling in {verify_sampled_ranks()} size cases.")
    totals = verify_archive()
    print(", ".join(f"{count:,} {name}" for name, count in sorted(totals.items())))
    paths, boards, prob = verify_probabilities()
    print(f"{paths:,} weighted batch choices; exact probabilities agree on all {boards} boards.")
    print(f"Three-arm probability of an adjacent descent = {prob}.")
