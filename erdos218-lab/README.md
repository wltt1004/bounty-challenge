# Erdős 218 Lean laboratory

This scratch branch tests the exact Conjectures.io target

```lean
{n | primeGap (n + 1) ≤ primeGap n}.HasDensity (1 / 2)
```

against Lean 4.27.0 and the disclosed kernel soundness defects. It is isolated from the default branch and is not a claimed mathematical proof.

The full laboratory checks the exact pinned static policy scanner, Formal Conjectures revision, and axiom closure for the minimized `run_meta` construction.
