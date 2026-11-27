# Feasible INEQUIVALENCE OF PROGRAMS WITH ASSIGNMENTS instances

An INEQUIVALENCE OF PROGRAMS WITH ASSIGNMENTS instance is feasible when some initial assignment $a$ makes the two programs end with different values in some variable $x < n$. Both programs start from the **same** zero-extended [initial store](initial-store.md), $a(j)$ at $j < n$ and $0$ elsewhere, and run left to right. A raw program may read an address outside $X$ into an in-range output; validation excludes such programs.
