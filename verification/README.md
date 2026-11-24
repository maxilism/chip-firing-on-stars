# Lean verification

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
