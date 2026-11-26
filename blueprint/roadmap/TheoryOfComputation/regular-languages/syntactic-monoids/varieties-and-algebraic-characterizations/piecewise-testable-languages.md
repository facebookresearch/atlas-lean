# Piecewise testable languages

A word $u = a_1 \cdots a_k$ is a *subword* of $v$ if $v = v_0 a_1 v_1 \cdots a_k v_k$ for some words $v_i$. For $n > 0$, words $u$ and $v$ over $A$ are
$\sim_n$-equivalent if they have the same subwords of length at most $n$; $\sim_n$ is a congruence of finite index on $A^*$. A language is *piecewise
testable* if it is a union of $\sim_n$-classes for some $n > 0$, equivalently a Boolean combination of languages $A^* a_1 A^* a_2 \cdots A^* a_k A^*$ of the
words that contain a given subword $a_1 \cdots a_k$.

## Sources

- J.-É. Pin, *Mathematical Foundations of Automata Theory*, lecture notes, version of March 24, 2025, <https://www.irif.fr/~jep/PDF/MPRI/MPRI.pdf>: Section VII.1 (the subword ordering, the congruence $\sim_n$ and Proposition VII.1.2), Section VII.3 (the definition of piecewise testable languages) and Proposition VII.3.11.
