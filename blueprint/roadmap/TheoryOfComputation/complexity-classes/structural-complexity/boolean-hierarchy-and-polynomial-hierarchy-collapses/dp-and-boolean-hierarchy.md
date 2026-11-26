# The difference class DP and the Boolean hierarchy over NP

$\mathsf{DP}=\{L_1\cap L_2 : L_1\in\mathsf{NP},\ L_2\in\mathsf{coNP}\}$, equivalently the differences $L_1\setminus L_2$ of two $\mathsf{NP}$ languages; $\mathsf{coDP}$ consists of unions of an $\mathsf{NP}$ and a $\mathsf{coNP}$ language. The **Boolean hierarchy** is $\mathsf{BH}_1=\mathsf{NP}$, $\mathsf{BH}_{2k}=\{L\cap \overline{M}: L\in\mathsf{BH}_{2k-1}, M\in\mathsf{NP}\}$, $\mathsf{BH}_{2k+1}=\{L\cup M : L\in\mathsf{BH}_{2k}, M\in\mathsf{NP}\}$, so $\mathsf{BH}_2=\mathsf{DP}$, and $\mathsf{BH}=\bigcup_k\mathsf{BH}_k$ is the Boolean closure of $\mathsf{NP}$. For any $\mathsf{NP}$-complete $A$ and $\mathsf{coNP}$-complete $B$, the product $\{\langle x,y\rangle: x\in A, y\in B\}$ (e.g. SAT–UNSAT) is $\mathsf{DP}$-complete.

## Depends on

- [The complexity class NP](../../the-classes-p-np-and-conp/np.md)
- [The class coNP](../../the-classes-p-np-and-conp/co-np.md)

## Sources

- Christos H. Papadimitriou, "Computational Complexity", Addison-Wesley, 1994.
- Jin-Yi Cai et al., "The Boolean Hierarchy I: Structural Properties", SIAM Journal on Computing 17(6), 1988.
