# The fixed-distribution counting barrier for the fusion method

There is an explicit distribution on pairs of subsets of $\{0,1\}^n$ that covers (defeats) each semifilter accepting the literals of a positive input with probability at least $1/(8n+8)$. Consequently, for any fixed nonnegative weighting of witnesses, some single pair defeats at least a $1/(8n+8)$ fraction of the total weight; so lower bounds on cover complexity obtained by bounding, for a fixed distribution on witnesses, the mass defeated by any single pair can never exceed $8n+8$.

## Proof sketch

Take a random cylinder pair determined by a random coordinate and polarity; an averaging argument over coordinates shows each semifilter accepting the literals of an input is defeated with probability at least $1/(8n+8)$. Averaging against the fixed witness distribution then exhibits a heavy pair.

## Depends on

- [Semifilters and semifilter (fusion) covers](semifilters-and-fusion-covers.md)

## Sources

- Alexander A. Razborov, "On the Method of Approximations", Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing, 1989.
- Igor Carboni Oliveira, "Notes on the Method of Approximations and the Emergence of the Fusion Method", 2018.
