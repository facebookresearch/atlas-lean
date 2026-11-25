# Yao's XOR lemma: hardness amplification by XOR

There is a natural number $c$ such that
the following holds for all natural numbers $n \ge 1$ and $k$, every rational $\delta$ with
$0 < \delta \le 1/2$, every Boolean function $f$ on $n$ bits and every natural number $s$.
Suppose every circuit given as a list of at most $s$ encoded gates has agreement at most
$1 - \delta$ with $f$, where an input $x \in \{0,1\}^n$ is given to the circuit as its $n$ bits.
Then every circuit $C$ given as a list of encoded gates, whose number of gates $|C|$ satisfies
$|C| \cdot (k + 1)^c \le s$, has agreement at most $1/2 + (1 - 2\delta)^k / 2 + 1/(k + 1)$ with
the XOR $f^{\oplus k}$ of $k$ independent copies of $f$, where a $k$-tuple of $n$-bit blocks is
given to the circuit as its $nk$-bit flattening.

## Sources

- A. C. Yao, "Theory and applications of trapdoor functions", Proceedings of the Twenty-Third Annual Symposium on Foundations of Computer Science (FOCS 1982), 80-91. The lemma is attributed to this work; according to Goldreich, Nisan and Wigderson (below, Section 1), it was presented in Yao's talks on it rather than in the paper.
- L. Levin, "One-way functions and pseudorandom generators", Combinatorica 7 (1987), 357-363: the first published proof, according to Goldreich, Nisan and Wigderson.
- O. Goldreich, N. Nisan and A. Wigderson, "On Yao's XOR-Lemma", ECCC TR95-050, revision 2: Lemma 1 (Yao's version) and Lemma 2 (Levin's version), stated asymptotically for families of circuits.
- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, Theorem 17.2: a version with concrete parameters, proved from Impagliazzo's hardcore lemma.

The concrete form above (size loss $(k + 1)^c$, additive error $1/(k + 1)$, advantage $(1 - 2\delta)^k / 2$) differs in its parameters from these statements.
