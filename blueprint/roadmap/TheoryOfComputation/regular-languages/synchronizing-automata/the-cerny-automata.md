# The Černý automata reach reset threshold $(n-1)^2$

For $n \ge 2$ let $\mathcal{C}_n$ be the automaton on the residues modulo $n$ with two letters acting by $0 \cdot a = 1$, $m \cdot a = m$ for $0 < m < n$, and
$m \cdot b = m + 1 \pmod n$. Then $\mathcal{C}_n$ is [synchronizing](synchronizing-automata-and-reset-words.md) and its shortest reset word is $(ab^{n-1})^{n-2} a$, of length $(n - 1)^2$ (Černý).
Hence $C(n) \ge (n - 1)^2$ for every $n \ge 2$.

## Depends on

- [Synchronizing automata and reset words](synchronizing-automata-and-reset-words.md)

## Sources

- M. V. Volkov, "List of results on the Černý conjecture and reset thresholds for synchronizing automata", arXiv:2508.15655v4, January 2026: Section 1.2, the series $\{\mathcal{C}_n\}$, Figure 1 and the statement that $(ab^{n-1})^{n-2}a$ is the shortest reset word, crediting J. Černý (1964).
