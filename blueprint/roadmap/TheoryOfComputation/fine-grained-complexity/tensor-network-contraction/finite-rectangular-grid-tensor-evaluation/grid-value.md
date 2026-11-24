# Finite grid tensor evaluation

Let $\rho$ and $\gamma$ be finite linear orders, $\Lambda, \Delta$ finite sets of labels in $A$,
$R$ a complete-graph tensor instance on the cells $\rho \times \gamma$ with labels in $A$, and
$G_\omega$ an integer-valued kernel of four labels for each $\omega \in (\rho \times \rho) \times
(\gamma \times \gamma)$. The grid value is the sum, over the directed grid labelings $\ell$ with
edge labels $\Lambda$ and diagonal labels $\Delta$, of the product of

- $\prod_w R_w(\ell(w, \cdot))$ over all cells $w$;
- $[\ell((a, q_1), (a, q_2)) = \ell((a, q_2), (a, q_1))]$ over all rows $a$ and columns $q_1 < q_2$;
- $[\ell((p_1, i), (p_2, i)) = \ell((p_2, i), (p_1, i))]$ over all columns $i$ and rows $p_1 < p_2$;
- the kernel $G_\omega$ applied to the diagonal ends of $\omega$, over all ordered rectangles
  $\omega$,

where $[\cdot]$ is $1$ if the equality holds and $0$ otherwise.
