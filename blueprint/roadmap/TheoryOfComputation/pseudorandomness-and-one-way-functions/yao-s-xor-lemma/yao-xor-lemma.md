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

- A. C. Yao, "Theory and applications of trapdoor functions", Proceedings of the Twenty-Third Annual Symposium on Foundations of Computer Science (FOCS 1982), 80-91.
