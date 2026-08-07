# Erdős 218 Lean laboratory

This scratch branch tests the exact Conjectures.io target

```lean
{n | primeGap (n + 1) ≤ primeGap n}.HasDensity (1 / 2)
```

against Lean 4.27.0 and the disclosed wrong-projection kernel soundness bug. It is isolated from the default branch and is not a claimed mathematical proof.
