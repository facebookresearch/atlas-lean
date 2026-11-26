# The Borodin–Trakhtenbrot gap theorem

Statement: for every Blum complexity measure $\Phi$ and every total computable function $r : \mathbb{N} \to \mathbb{N}$ with $r(n) \ge n$ for all $n$, there is a total computable function $g : \mathbb{N} \to \mathbb{N}$ such that

$$C_\Phi(g) = C_\Phi(r \circ g).$$

So there is a gap in cost between $g$ and the larger bound $n \mapsto r(g(n))$ in which no new functions appear. Here programs are codes $c$ of partial recursive functions $\varphi_c : \mathbb{N} \rightharpoonup \mathbb{N}$, and a Blum measure $\Phi$ assigns to each program $c$ and input $n$ a partial cost $\Phi_c(n) \in \mathbb{N}$ that is defined exactly when $\varphi_c(n)$ halts, with the relation $\Phi_c(n) = m$ decidable in $(c, n, m)$. For a total $t : \mathbb{N} \to \mathbb{N}$, the Blum class $C_\Phi(t)$ is the set of partial functions $f$ computed by some program $c$ with $\Phi_c(n)$ defined and $\Phi_c(n) \le t(n)$ for all but finitely many $n$.

## Sources

- A. Borodin, Computational complexity and the existence of complexity gaps, Journal of the ACM 19 (1972), 158–174; found independently by B. A. Trakhtenbrot.
- Blum, A machine-independent theory of the complexity of recursive functions, Journal of the ACM 14 (1967), 322–336, for the axioms of a complexity measure.
