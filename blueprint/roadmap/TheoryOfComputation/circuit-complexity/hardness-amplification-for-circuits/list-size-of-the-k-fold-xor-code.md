# The k-fold XOR code has short lists

For $g:\{0,1\}^n\to\{0,1\}$ let $g^{\oplus k}(x_1,\dots,x_k)=g(x_1)\oplus\cdots\oplus g(x_k)$, an encoding of the truth table of $g$ ($2^n$ bits) into $2^{kn}$ bits. In $\pm1$ notation the correlation of two encodings is the $k$-th power of the correlation of the messages: $\mathbb{E}[(-1)^{g^{\oplus k}}(-1)^{h^{\oplus k}}]=\bigl(\mathbb{E}[(-1)^{g}(-1)^{h}]\bigr)^k$. Consequently, for every $\eta\in(0,1]$ and every word $w:\{0,1\}^{kn}\to\{\pm1\}$: among any family of messages whose pairwise correlations are at most $(\eta^2/2)^{1/k}$ in absolute value, at most $2/\eta^2$ have an encoding whose correlation with $w$ is at least $\eta$. The bound is independent of $n$.

## Proof sketch

The blocks of a uniform input are independent, so the expectation of the product factors into $k$ equal factors; hence the encodings $v_1,\dots,v_N$ of such messages are unit vectors with $\langle v_i,v_j\rangle\le\eta^2/2$. If $\langle w,v_i\rangle\ge\eta$ for all $i$ then $\eta N\le\|\sum_i v_i\|\le\sqrt{N+N^2\eta^2/2}$, which gives $N\le 2/\eta^2$.

## Depends on

- [XOR of independent copies of a function](../../pseudorandomness-and-one-way-functions/yao-s-xor-lemma/xor-of.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Sources

- Andrew C. Yao, "Theory and Application of Trapdoor Functions", Proceedings of the 23rd Annual Symposium on Foundations of Computer Science (FOCS 1982), 1982 (the $k$-fold XOR).
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009 (Johnson bound: a binary code of relative distance at least $\tfrac12-\gamma$ has at most $1/(2\beta^2)$ codewords within relative distance $\tfrac12-\beta$ of any word when $\beta\ge\sqrt\gamma$, applied with $\beta=\eta/2$ and $\gamma=\eta^2/4$; Theorem 17.26 in the 2007 web draft).
- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008 (Chapters 7–8).
