# Blum's speedup theorem

Statement: for every Blum complexity measure $\Phi$ and every total computable function $r : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$, there is a total computable function $g : \mathbb{N} \to \mathbb{N}$ such that for every program $c$ computing $g$ there is another program $c'$ computing $g$ with

$$r\big(n, \Phi_{c'}(n)\big) < \Phi_c(n) \quad \text{for all but finitely many } n.$$

Here programs are codes $c$ of partial recursive functions $\varphi_c : \mathbb{N} \rightharpoonup \mathbb{N}$, and a Blum measure $\Phi$ assigns to each program $c$ and input $n$ a partial cost $\Phi_c(n) \in \mathbb{N}$ that is defined exactly when $\varphi_c(n)$ halts, with the relation $\Phi_c(n) = m$ decidable in $(c, n, m)$.

## Sources

- Blum, A machine-independent theory of the complexity of recursive functions, Journal of the ACM 14 (1967), 322–336, Theorem 5.
