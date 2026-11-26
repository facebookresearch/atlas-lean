# Circuits for transient depths, cycle labels, reachability and hitting times

Let $f:\{0,1\}^n\to\{0,1\}^n$ have a circuit of size $s$. The following functions have circuits whose size is a constant times the optimized fixed-power bound $s+(n+1)^3+\sqrt{(n+1)^3 2^n (s+(n+1)^3)}$:

- the *transient depth* of $x$ (the least $t$ such that $f^t(x)$ lies on a cycle);
- a *canonical cycle label* of $x$ (the lexicographically least state on the cycle eventually reached, with the phase of $x$ relative to it);
- on pairs $(x,y)$, the *reachability bit* $[\exists t\ge 0: f^t(x)=y]$ together with the *first hitting time* $\min\{t: f^t(x)=y\}$ written in $n+1$ bits.

## Proof sketch

Transient depths are found by binary search with one fixed-power query per bit. Cycle labels combine a fixed power landing on the cycle with a scan for the least state over a window. Reachability uses a compressed forest of checkpoints storing subtree intervals, so that membership of $y$ on the forward orbit of $x$ reduces to interval containment and a comparison of phases.

## Depends on

- [Circuits for fixed powers of a circuit-computable map](circuits-for-fixed-powers-of-a-map.md)

## Proof depends on

- [Square-root circuit bound for fixed powers](square-root-bound-for-fixed-powers.md)

## Sources

- Samuel Schlesinger, "Square-root circuit bounds for iterated functions", 2026.
