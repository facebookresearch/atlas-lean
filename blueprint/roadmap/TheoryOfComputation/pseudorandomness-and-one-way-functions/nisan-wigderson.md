# Impagliazzo-Wigderson: exponential circuit hardness in E derandomizes BPP

Suppose there are a decision
problem $f$ in E and a natural number $c > 0$ such that, for every $n$, every well-formed flat
Boolean circuit $C$ on $n$ inputs without mod gates that computes $f$ on all bitstrings of length
$n$ (for every bitstring $x$ of length $n$, the value of its last gate on input $x$ is $f(x)$)
satisfies $|C|^c \ge 2^n$, where $|C|$ is its number of gates; that is, $C$ has at least $2^{n/c}$
gates. Then BPP equals P.

The hypothesis is *worst-case* hardness: no small circuit computes $f$ correctly on every input.
In this form the theorem is due to Impagliazzo and Wigderson (1997); Vadhan states it as
Corollary 7.64 (1) and attributes it to them in the chapter notes (Section 7.9). Their proof
converts worst-case hardness into average-case hardness by a derandomized XOR lemma and then
applies the Nisan-Wigderson generator. Nisan and Wigderson (1994) derived $\mathrm{BPP} = \mathrm{P}$
from exponential *average-case* hardness: a function in E that no circuit of size $2^{\varepsilon n}$
computes correctly on more than a $1/2 + 2^{-\varepsilon n}$ fraction of the inputs, that is,
$(s, 1/2 - 1/s)$ average-case hardness with $s = 2^{\varepsilon n}$ (Vadhan, Theorem 7.19 and
Corollary 7.20).

The Nisan-Wigderson generator itself evaluates the hard function $f$ on the restrictions
$x|_{S_1}, \dots, x|_{S_m}$ of a short random seed $x$ to the sets of a combinatorial design
(sets of size $\ell$ with pairwise intersections of size at most $a$); if $f$ is
$(s, 1/2 - \varepsilon/m)$ average-case hard, the output fools circuits of size
$s - m a 2^a$ up to error $\varepsilon$ (Vadhan, Construction 7.23 and Theorem 7.24).

## Background

- [Yao's XOR lemma](yao-s-xor-lemma/README.md): Impagliazzo and Wigderson amplify worst-case
  hardness to average-case hardness with a derandomized version of the XOR lemma before applying
  the Nisan-Wigderson generator.

- [Undirected ST-connectivity is in L (Reingold)](../polynomial-time-problems/undirected-s-t-connectivity/ustcon-in-l.md):
  the other derandomization landmark of the same circle of ideas, unconditional but for space,
  obtained from expander graphs rather than from hardness.

## Sources

- R. Impagliazzo and A. Wigderson, "P = BPP if E requires exponential circuits: Derandomizing the XOR lemma", Proceedings of the 29th Annual ACM Symposium on Theory of Computing (STOC 1997), 220-229.
- N. Nisan and A. Wigderson, "Hardness vs randomness", Journal of Computer and System Sciences 49 (1994), 149-167 (FOCS 1988).
- S. Vadhan, *Pseudorandomness*, Foundations and Trends in Theoretical Computer Science 7 (2012), Construction 7.23, Theorems 7.19 and 7.24, Corollaries 7.20 and 7.64, Section 7.9.
