# The Cook–Mertz register procedure for Tree Evaluation

Consider binary Tree Evaluation $\mathrm{TreeEval}_2(H,\ell)$. Let $K$ be a finite field, $m=|K|-1$ with $m>2\ell$, and $\omega\in K$ a primitive root of unity of order $m$ ($\omega^m=1$ and $\omega^k\ne1$ for $0<k<m$; one exists since $K^{\times}$ is cyclic); embed $\{0,1\}\subseteq K$. A *register program* over $K$ is a list of instructions $R_i\leftarrow R_i+p(\text{other registers})$ on registers holding elements of $K$, and it *cleanly computes* a value $v$ into a block of registers if, **for all initial register contents** $\tau$, at the end that block holds $\tau+v$ and every other register holds its initial value. Let $u$ be an internal node with children $u_1,u_2$, and let $P_{u_1},P_{u_2}$ be register programs that cleanly compute $\mathrm{val}(u_1),\mathrm{val}(u_2)\in\{0,1\}^{\ell}$ into blocks $R_1,R_2\in K^{\ell}$, with inverse programs $P_{u_1}^{-1},P_{u_2}^{-1}$. Let $q_u$ be the multilinear polynomial map of degree at most $2\ell$ that agrees with $f_u$ on $\{0,1\}^{2\ell}$. Then the following program $P_u$ cleanly computes $f_u(\mathrm{val}(u_1),\mathrm{val}(u_2))=\mathrm{val}(u)$ into a block $R_u\in K^{\ell}$: for $j=1,\dots,m$, multiply every register of $R_1,R_2$ by $\omega^{j}$; run $P_{u_1},P_{u_2}$; add $m^{-1}\,q_u(R_1,R_2)$ to $R_u$; run $P_{u_1}^{-1},P_{u_2}^{-1}$; multiply every register of $R_1,R_2$ by $\omega^{-j}$. Replacing the addition by a subtraction gives an inverse program $P_u^{-1}$. Each of $P_u,P_u^{-1}$ makes $m$ calls to each of $P_{u_1},P_{u_2},P_{u_1}^{-1},P_{u_2}^{-1}$ and uses $5m\ell$ other basic instructions.

## Proof sketch

During round $j$ the child blocks hold $y+\omega^{j}\tau$, where $y=(\mathrm{val}(u_1),\mathrm{val}(u_2))$ and $\tau$ is their initial content. For a polynomial $p$ of degree $<m$, $\sum_{j=1}^{m}m^{-1}p(\omega^{j}\tau+y)=p(y)$, because $\sum_{j=1}^{m}\omega^{jk}=0$ for $0<k<m$ and the $k=0$ term contributes $m\cdot m^{-1}=1$. So the rounds together add exactly $q_u(y)=f_u(y)$ to $R_u$, and the inverse calls and the multiplications by $\omega^{-j}$ restore all other registers.

Derived here (not stated in the cited source in this form): the same construction works for fan-in $d$ with $d+1$ register blocks and any field containing a primitive $m$-th root of unity with $m>d\ell$ (the source generalizes to fan-in $d$ through a separate, more general lemma), and the program that adds $c\cdot\mathrm{val}(u)$ for an arbitrary coefficient $c\in K$, obtained by scaling the added term, is undone by the program for $-c$.

## Depends on

- [The Tree Evaluation problem](tree-evaluation-problem.md)

## Sources

- James Cook and Ian Mertz, "Tree Evaluation is in Space O(log n · log log n)", Proceedings of the 56th Annual ACM Symposium on Theory of Computing (STOC 2024), pp. 1268–1278 (ECCC TR23-174); in the ECCC numbering, Definitions 1, 2 and 4, Proposition 7, Corollary 9, Lemma 12 and Lemma 13 (Section 6.2 for fan-in $d$).
