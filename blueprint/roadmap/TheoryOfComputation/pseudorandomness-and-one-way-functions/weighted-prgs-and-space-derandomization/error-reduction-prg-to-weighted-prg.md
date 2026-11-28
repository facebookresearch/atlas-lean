# Cohen–Doron–Renard–Sberlo–Ta-Shma: black-box error reduction from PRGs to weighted PRGs via Richardson iteration

Let $G_0$ be an explicit PRG with seed length $s_0$ that fools width-$w$ length-$n$ standard-order ROBPs with error $n^{-2}$ and is computable in space $m$. Then for every $0\lt\varepsilon\lt 1/(4n)$ there is an explicit $\varepsilon$-WPRG for the same class, computable in space $O\bigl(m+(\log\log(w/\varepsilon))^3\bigr)$, with seed length at most

$$
s_0+O\bigl(\log(w/\varepsilon)\cdot\log\log_n(1/\varepsilon)\bigr).
$$

Instantiating $G_0$ with Nisan's generator gives an explicit $\varepsilon$-WPRG for width-$w$ length-$n$ ROBPs with seed length $O\bigl(\log n\cdot\log(nw)+\log(w/\varepsilon)\cdot\log\log_n(1/\varepsilon)\bigr)$, computable in space $O\bigl(\log(nw)+(\log\log(w/\varepsilon))^3\bigr)$.

## Proof sketch

View acceptance probabilities through the block matrix $L=I-W$ built from the transition matrices of the program, so that the true probabilities are entries of $L^{-1}$, while a moderate-error PRG supplies an approximate inverse $A$ with $\|I-AL\|\le n^{-1}$. Richardson iteration $\sum_{j=0}^{k}(I-AL)^jA$ reduces the error to $n^{-\Omega(k)}$, and each term expands into a signed combination of products of PRG-approximated blocks, which is realized as a weighted generator whose seed adds only $O(\log(w/\varepsilon)\log\log_n(1/\varepsilon))$ bits. The same idea, discovered independently by Pyne and Vadhan, gives a simple proof of the Braverman–Cohen–Garg result.

## Depends on

- [Weighted pseudorandom generators (pseudorandom pseudodistributions)](weighted-pseudorandom-generators.md)

## Sources

- Gil Cohen, Dean Doron, Oren Renard, Ori Sberlo and Amnon Ta-Shma, "Error Reduction for Weighted PRGs Against Read Once Branching Programs", CCC (2021), ECCC TR21-020.
- Edward Pyne and Salil Vadhan, "Pseudodistributions That Beat All Pseudorandom Generators", CCC (2021); Theory of Computing 22(3) (2026), ECCC TR21-019.
