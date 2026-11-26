# The Tree Evaluation problem

Fix a fan-in $d\ge 2$, a height $H\ge 1$ and a value length $\ell\ge 1$. An instance of **Tree Evaluation** $\mathrm{TreeEval}_{d}(H,\ell)$ is the complete $d$-ary tree of height $H$ in which every leaf $u$ is labelled by a value $v_u\in\{0,1\}^{\ell}$ and every internal node $u$ is labelled by a function $f_u:(\{0,1\}^{\ell})^{d}\to\{0,1\}^{\ell}$, given by its full truth table of $2^{d\ell}\cdot\ell$ bits. Values propagate upward by $\mathrm{val}(u)=v_u$ at leaves and $\mathrm{val}(u)=f_u(\mathrm{val}(u_1),\dots,\mathrm{val}(u_d))$ at an internal node with children $u_1,\dots,u_d$. The task is to output $\mathrm{val}(\mathrm{root})$. The encoded input has length $n=\Theta(d^{H}2^{d\ell}\ell)$, so for nontrivial instances $H,\ell=O(\log n)$.

## Sources

- James Cook and Ian Mertz, "Tree Evaluation is in Space O(log n · log log n)", Proceedings of the 56th Annual ACM Symposium on Theory of Computing (STOC 2024), pp. 1268–1278 (ECCC TR23-174).
