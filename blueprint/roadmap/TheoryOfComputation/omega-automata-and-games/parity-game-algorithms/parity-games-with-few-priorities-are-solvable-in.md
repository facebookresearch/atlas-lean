# Parity games with few priorities are solvable in polynomial time

If $d < \log_2 n$, then the winner of a finite [parity game](../parity-games/parity-game.md) with $n$ positions and priorities in
$\{1, \dots, d\}$ can be decided in time $O(n^5)$. Consequently, parity games parameterized by the number of priorities are fixed-parameter
tractable: they are solvable in time $O(n^5) + g(d)$ for some function $g$ (Calude, Jain, Khoussainov, Li and Stephan).

## Depends on

- [Parity game](../parity-games/parity-game.md)

## Proof depends on

- [Parity games are solvable in quasipolynomial time](parity-games-are-solvable-in-quasipolynomial-time.md)

## Sources

- C. S. Calude, S. Jain, B. Khoussainov, W. Li and F. Stephan, "Deciding parity games in quasipolynomial time", *Proceedings of the 49th ACM STOC*, 2017 (numbering of the authors' preprint, <http://www.cmap.polytechnique.fr/~gaubert/COURSM2/PARITYGAMES/paritygame.pdf>): Theorem 6 and its proof, and the abstract (the fixed-parameter bound).
