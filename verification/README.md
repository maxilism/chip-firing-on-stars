# Verification

## Lean proofs

The development starts with individual legal firings. Its main results are

- [Reachability](StarFiring/Classification.lean) — a stable board is reachable exactly when it has a firing certificate.
- [321-avoidance](StarFiring/Avoidance.lean) — every reachable middle order avoids 321.
- [Identity padding](StarFiring/Padding.lean) — if a nonempty permutation `w` avoids 321, appending `t` new largest entries in increasing order gives a reachable order for every `t ≥ U(w)`, where `U` is the excedance-gap bound. Conversely, any permutation with a reachable extension of this form avoids 321.

The decision procedure and its complexity, the enumeration at inversion outdegree at most two, and the probabilistic and Catalan estimates are proved in the [papers](../papers/).

From this directory, with Elan installed, run

```sh
lake build
lake env lean Axioms.lean
lake env lean PaddingCases.lean
```

The first command builds the proofs with the pinned Lean toolchain. The other two report the axioms used and check concrete padding examples.

## Finite checks

Run these from this directory with Python 3.10 or later. They use the standard library.

- `python3 checks/insertion.py` explores every legal continuation of 625 small augmented boards, replays the five-cell construction on 2,039 tableaux, and checks the hook formula for 529 rectangles.
- `python3 checks/random_firing.py` enumerates every first batch for two chips per arm through ten arms. For three arms with three chips each, it compares direct random firing with the paper's batch description at all 47 endpoints.
- `python3 checks/verify_descents.py` checks uniform rank sampling in 505 size cases and replays the five witness archives. The 12,727 distinct endpoints give 201,328 rank cuts and 6,432 adjacent crossings counted across histories and cuts. It also checks all 47 three-arm endpoint probabilities and obtains an exact descent probability of 11/2520.

Each compressed JSON Lines record in `witnesses/` gives the terminal rows and a legal move sequence from the initial board. A move begins with its vertex index, followed by its selected labels. Vertex zero is the center. The next three indices are depths one to three on the first arm, and numbering continues in arm order. Each file contains one history per endpoint for its number of arms.

The general insertion theorem and the probability limit are proved in the [insertion](../papers/column-insertion.pdf) and [random-firing](../papers/random-firing.pdf) papers.
