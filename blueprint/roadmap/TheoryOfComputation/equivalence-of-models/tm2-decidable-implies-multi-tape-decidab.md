# Computable predicates are decidable by multi-tape machines

Let $\alpha$ be a type with an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is primitive recursive, and write $\mathrm{bin}(m)$ for the binary word of $m$, least significant bit first and unpadded: $\mathrm{bin}(0) = \varepsilon$, and for $m > 0$ the last bit is $1$. A multi-tape machine here is a deterministic Turing machine with finitely many states, a read-only input tape, finitely many work tapes and a write-only output tape, all over the alphabet $\{0, 1\}$.

The following holds. Let $p$ be a predicate on $\alpha$ that is decidable by a multi-stack machine: some function $f : \mathbb{N} \to \mathbb{N}$ computed by a multi-stack Turing machine on binary numbers satisfies $f(\mathrm{encode}(a)) = 1 \iff p(a)$ for all $a \in \alpha$. Then $p$ is decidable by a multi-tape machine: there is a multi-tape machine $M$ such that for every $a \in \alpha$ the run of $M$ on $\mathrm{bin}(\mathrm{encode}(a))$ halts with a single bit $b$ on its output tape, and $b = 1$ exactly when $p(a)$ holds.

## Sources

- M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, Corollary 3.15.
- J. E. Hopcroft, R. Motwani, and J. D. Ullman, *Introduction to Automata Theory, Languages, and Computation*, 3rd ed., Pearson, 2007, §8.4.
