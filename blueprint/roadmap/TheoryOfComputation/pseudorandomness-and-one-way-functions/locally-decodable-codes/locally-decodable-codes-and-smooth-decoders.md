# Locally decodable codes and smooth decoders

Let $C : \{0,1\}^k \to \Gamma^n$ be a code over a finite alphabet. A *$(q, \delta, \varepsilon)$-local decoder* is a randomized oracle algorithm $D$ that, on input $i \in [k]$ and oracle access to a word $w \in \Gamma^n$, makes at most $q$ queries and satisfies $\Pr[D^w(i) = x_i] \ge \frac12 + \varepsilon$ for every message $x$, every $i$ and every $w$ within Hamming distance $\delta n$ of $C(x)$. $C$ is a *$(q, \delta, \varepsilon)$-LDC* if such a decoder exists. A decoder is *$(q, c, \varepsilon)$-smooth* if on every input $i$ each position $j \in [n]$ is queried with expected number of reads at most $c/n$, and on the codeword $C(x)$ itself it outputs $x_i$ with probability at least $\frac12 + \varepsilon$. The Hadamard code is a $(2, \delta, \frac12 - 2\delta)$-LDC.

## Depends on

- [Local decoding of the Hadamard code](../../../InformationTheory/error-correcting-codes/hadamard-code-local-decoding.md)
- [Linear code](../../../InformationTheory/error-correcting-codes/linear-codes/linear-code.md)

## Sources

- J. Katz and L. Trevisan, "On the Efficiency of Local Decoding Procedures for Error-Correcting Codes", STOC 2000.
- S. Yekhanin, "Locally Decodable Codes", Foundations and Trends in Theoretical Computer Science 6(3), 2012.
