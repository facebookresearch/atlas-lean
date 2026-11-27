# Rank-based Büchi complementation with an explicit state bound

The following holds: there is a constant $c \in \mathbb{N}$ such that for all $n, k \in \mathbb{N}$ and every nondeterministic Büchi automaton $A$ with state set $\{0, \dots, n-1\}$ over the alphabet $\{0, \dots, k-1\}$, there are a number

$$m \le 2^{\,c\, n\, (\lfloor \log_2 (n+1) \rfloor + 1)}$$

and a nondeterministic Büchi automaton $B$ with state set $\{0, \dots, m-1\}$ over the same alphabet whose ω-language is the complement of that of $A$:

$$L_\omega(B) = \{0, \dots, k-1\}^{\omega} \setminus L_\omega(A).$$

So Büchi automata can be complemented with $2^{O(n \log n)}$ states, with one constant $c$ for all alphabet sizes and state counts.

## Sources

- O. Kupferman and M. Y. Vardi, "Weak alternating automata are not that weak", *ACM Transactions on Computational Logic* 2 (2001), 408-429 (rank-based complementation).
- S. Schewe, "Büchi complementation made tight", *Proceedings of STACS 2009*, LIPIcs 3 (2009), 661-672.
