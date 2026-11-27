# Small-bias sample spaces correspond to balanced binary linear codes

For a sample space $G : \sigma \to \{0,1\}^\ell$ with $\sigma$ finite and nonempty, $N = |\sigma|$, define the linear code $C_G : \{0,1\}^\ell \to \{0,1\}^\sigma$, $C_G(v)_s = \langle v, G(s)\rangle$. Every $\mathbb{F}_2$-linear map $\{0,1\}^\ell \to \{0,1\}^\sigma$ is $C_G$ for exactly one $G$. Moreover, $G$ with a uniform seed is $\varepsilon$-biased if and only if for all distinct messages $u \ne v$ the Hamming distance satisfies

$$
\frac{(1-\varepsilon)N}{2} \le d_H\bigl(C_G(u), C_G(v)\bigr) \le \frac{(1+\varepsilon)N}{2}.
$$

With $\sigma = \{0,1\}^k$ this matches $\varepsilon$-bias generators of stretch $\ell$ with binary linear codes from $\ell$ to $2^k$ bits whose codewords are pairwise at distance $(1 \pm \varepsilon)2^{k-1}$ (Goldreich 2008, Exercise 8.41).

## Proof sketch

The distance between $C_G(u)$ and $C_G(v)$ counts seeds where the parity of $G(s)$ on the nonempty set $\{i : u_i \ne v_i\}$ is odd, and the bias there is $1 - 2d_H/N$. A linear map is determined by the images of unit vectors, which give the coordinates of $G$.

## Depends on

- [Small-bias distribution and generator](../space-bounded-and-small-bias-generators/small-bias-distributions.md)
- [Linear code](../../../InformationTheory/error-correcting-codes/linear-codes/linear-code.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercise 8.41 (numbering of the 2007 public draft).
- J. Naor and M. Naor, "Small-Bias Probability Spaces: Efficient Constructions and Applications", SIAM Journal on Computing 22(4), 838–856, 1993.
