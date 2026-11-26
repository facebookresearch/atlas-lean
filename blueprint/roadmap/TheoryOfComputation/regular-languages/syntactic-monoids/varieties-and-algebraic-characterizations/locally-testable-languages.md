# Locally testable languages

For $k > 0$, words $u$ and $v$ over $A$ are $\sim_k$-equivalent, in the local sense, if they have the same prefixes of length less than $k$, the same
suffixes of length less than $k$ and the same factors of length $k$; this is a congruence of finite index. A language is *$k$-testable* if it is a union
of $\sim_k$-classes, and *locally testable* if it is $k$-testable for some $k$. Equivalently, a language is locally testable if and only if it is a Boolean
combination of languages $pA^*$, $A^* u A^*$ and $A^* s$ with $p, u, s \in A^+$.

## Sources

- J.-É. Pin, *Mathematical Foundations of Automata Theory*, lecture notes, version of March 24, 2025, <https://www.irif.fr/~jep/PDF/MPRI/MPRI.pdf>: Chapter VIII, the definition of $\sim_k$ and of $k$-testable and locally testable languages, and Proposition VIII.2.2.
