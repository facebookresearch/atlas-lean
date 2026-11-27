# Average-case hardness in E implies MA = NP

Suppose some $f\in\mathsf{E}$ is average-case hard: for some constant $c>0$ and all large $n$, every De Morgan circuit of size $2^{n/c}$ agrees with $f$ on at most a $\tfrac12+2^{-n/c}$ fraction of inputs of length $n$. Then $\mathsf{MA}=\mathsf{NP}$.

## Proof sketch

The hardness yields a Nisan–Wigderson generator with logarithmic seed fooling polynomial-size circuits. Arthur's random coins in an MA protocol, after Merlin's message is fixed, feed a polynomial-size circuit, so enumerating all seeds gives a deterministic verifier for the Merlin message: an NP verification.

## Depends on

- [The class MA (Merlin–Arthur)](../../../complexity-classes/time-and-space-complexity-classes/ma.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [The class E](../../../complexity-classes/time-and-space-complexity-classes/e.md)

## Proof depends on

- [Nisan–Wigderson generator](../../../pseudorandomness-and-one-way-functions/derandomization/nisanwigderson-generator.md)
- [Average-case hardness in E derandomizes BPP](../../../pseudorandomness-and-one-way-functions/derandomization/average-case-hardness-in-e-derandomizes-bpp.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapter 20 (Chapter 16, Exercise 4 of the January 2007 web draft, with hardness $H_{\mathrm{avg}}(f)(n)\ge2^{\varepsilon n}$ for every $n$).
- Russell Impagliazzo and Avi Wigderson, "P = BPP if E Requires Exponential Circuits: Derandomizing the XOR Lemma", Proceedings of the 29th Annual ACM Symposium on Theory of Computing, 220–229, 1997.
