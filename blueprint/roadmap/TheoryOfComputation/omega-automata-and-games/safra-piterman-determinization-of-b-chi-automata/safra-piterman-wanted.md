# Safra–Piterman determinization of Büchi automata: state bound

Statement: there is a constant $c \in \mathbb{N}$ such that for all $n, k \in \mathbb{N}$ and every nondeterministic Büchi automaton $\mathcal{A}$ with state set $\{0, \dots, n-1\}$ over the alphabet $\{0, \dots, k-1\}$, there are $m \in \mathbb{N}$ with

$$m \le 2^{\,c \cdot n \cdot (\lfloor \log_2 (n + 1) \rfloor + 1)}$$

and a deterministic parity automaton with state set $\{0, \dots, m-1\}$ over the same alphabet whose language (the infinite words whose unique run has even maximal recurring priority) equals the ω-language accepted by $\mathcal{A}$ under the Büchi condition. This bounds the number of states, $2^{O(n \log n)}$, and puts no bound on the priorities.

## Sources

- S. Safra, "On the complexity of ω-automata", Proceedings of FOCS 1988, 319-327 (determinization to deterministic Rabin automata).
- N. Piterman, "From nondeterministic Büchi and Streett automata to deterministic parity automata", Proceedings of LICS 2006, 255-264.
- N. Piterman, "From nondeterministic Büchi and Streett automata to deterministic parity automata", Logical Methods in Computer Science 3 (2007) (deterministic parity automata with $2^{O(n \log n)}$ states).
