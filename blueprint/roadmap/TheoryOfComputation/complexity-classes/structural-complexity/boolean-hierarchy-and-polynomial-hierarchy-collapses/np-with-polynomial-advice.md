# NP/poly

$\mathsf{NP}/\mathrm{poly}$ is the class of languages $L$ for which there are a polynomially bounded advice sequence $(\alpha_n)$ and a polynomial-time verifier $V$ with $x\in L\iff\exists w,\ |w|\le p(|x|),\ V(\alpha_{|x|},x,w)=1$. $\mathsf{coNP}/\mathrm{poly}$ consists of complements of such languages; $\mathsf{NP}\subseteq\mathsf{coNP}/\mathrm{poly}$ iff $\mathsf{coNP}\subseteq\mathsf{NP}/\mathrm{poly}$.

## Depends on

- [The complexity class NP](../../the-classes-p-np-and-conp/np.md)
- [Polynomial time with polynomial advice](../../time-and-space-complexity-classes/ppoly.md)

## Sources

- Chee K. Yap, "Some Consequences of Non-Uniform Conditions on Uniform Classes", Theoretical Computer Science 26(3), 1983.
