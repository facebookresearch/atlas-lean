# Gap amplification for inaccessible entropy by parallel repetition

Let $f_0$ have real sample entropy $H_0$ in expectation and accessible sets $L_0$ with expected log-size at most $H_0 - \Delta$, and let $f_0^t$ be its $t$-fold direct product. Then (i) the real sample entropy of $f_0^t$ is at least $t H_0 - \lambda$ except with probability $e^{-2\lambda^2/(t\,n_0^2)}$, and (ii) every efficient collision finder for $f_0^t$ stays, except with negligible probability, inside sets of log-size at most $t(H_0 - \Delta) + \lambda$, outside a small bad set, where $n_0$ is the input length of $f_0$. Choosing $t = \Theta(n\,n_0^2/\Delta^2)$ with a large enough implied constant and $\lambda = n_0\sqrt{t n}$ makes the gap $t\Delta - 2\lambda$ between real and accessible entropy at least $n$, with Hoeffding error at most $e^{-2n}$.

## Proof sketch

Fiber sizes multiply across coordinates, turning both entropies into sums of $t$ independent bounded scores; Hoeffding's inequality concentrates them. For the accessible side, a collision finder for the product induces one for each coordinate by embedding.

## Depends on

- [Collision finders and accessible average max-entropy](accessible-average-max-entropy.md)

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- I. Haitner, T. Holenstein, O. Reingold, S. Vadhan and H. Wee, "Inaccessible Entropy II: IE Functions and Universal One-Way Hashing", Theory of Computing 16, 2020.
