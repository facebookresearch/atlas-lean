# The McCreight–Meyer union theorem

Statement: let $\Phi$ be a Blum complexity measure and let $t : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$, $(i, n) \mapsto t_i(n)$, be computable as a function of the pair $(i, n)$ with $t_i(n) \le t_{i+1}(n)$ for all $i, n$. Then there is a total computable $g : \mathbb{N} \to \mathbb{N}$ with

$$\bigcup_{i \in \mathbb{N}} C_\Phi(t_i) = C_\Phi(g).$$

Here programs are codes $c$ of partial recursive functions $\varphi_c : \mathbb{N} \rightharpoonup \mathbb{N}$, and a Blum measure $\Phi$ assigns to each program $c$ and input $n$ a partial cost $\Phi_c(n) \in \mathbb{N}$ that is defined exactly when $\varphi_c(n)$ halts, with the relation $\Phi_c(n) = m$ decidable in $(c, n, m)$. For a total $t : \mathbb{N} \to \mathbb{N}$, the Blum class $C_\Phi(t)$ is the set of partial functions $f$ computed by some program $c$ with $\Phi_c(n)$ defined and $\Phi_c(n) \le t(n)$ for all but finitely many $n$.

## Sources

- McCreight and Meyer, Classes of computable functions defined by bounds on computation, Proceedings of the ACM Symposium on Theory of Computing (1969), 79–88.
- Blum, A machine-independent theory of the complexity of recursive functions, Journal of the ACM 14 (1967), 322–336, for the axioms of a complexity measure.
