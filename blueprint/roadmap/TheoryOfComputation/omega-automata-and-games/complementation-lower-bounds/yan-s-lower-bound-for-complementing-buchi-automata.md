# Yan's lower bound for complementing Büchi automata

Let $C(n)$ be the least number such that every nondeterministic [Büchi automaton](../emptiness-of-b-chi-automata/mem-language-iff.md) with $n$ states has a complement, recognizing
$\Sigma^\omega$ minus its language, by a Büchi automaton with at most $C(n)$ states. Then $C(n) \ge L(n)$ for every $n > 1$, where
$L(n) = \Theta((0.76 n)^n)$; moreover for each $n > 1$ some Büchi automaton with $n$ states over a seven-letter alphabet already needs
$L(n)$ states for its complement (Yan). The proof first considers *full automata*, which have every possible transition as a letter, and
then reduces the alphabet by substitutions.

## Depends on

- [Büchi acceptance condition](../emptiness-of-b-chi-automata/mem-language-iff.md)

## Sources

- Q. Yan, "Lower bounds for complementation of $\omega$-automata via the full automata technique", *Logical Methods in Computer Science* 4(1), 2008, arXiv:0802.1226: the abstract, Theorem 3.5 (reduction to full automata), Theorem 4.7 and Theorem 4.9.
