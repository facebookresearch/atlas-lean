# Real sample entropy of a function

Let $F : \alpha \to \beta$ be a function on a finite set $\alpha$ with the uniform distribution. The *real sample entropy* of $x \in \alpha$ is

$$H_F(x) = \log_2 \bigl|F^{-1}(F(x))\bigr|.$$

Its expectation over uniform $X \leftarrow \alpha$ equals the conditional Shannon entropy $H(X \mid F(X))$.

## Depends on

- [Conditional entropy of a finite joint law](../../../InformationTheory/entropy-and-mutual-information/conditional-entropy-and-mutual-information/finite-conditional-entropy.md)

## Sources

- I. Haitner, T. Holenstein, O. Reingold, S. Vadhan and H. Wee, "Inaccessible Entropy II: IE Functions and Universal One-Way Hashing", Theory of Computing 16, 2020.
- I. Haitner and S. Vadhan, "The Many Entropies in One-Way Functions", in Tutorials on the Foundations of Cryptography, Springer, 2017.
