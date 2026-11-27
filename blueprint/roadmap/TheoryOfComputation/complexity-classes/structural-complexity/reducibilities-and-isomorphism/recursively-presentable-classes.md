# Recursively presentable complexity classes

A class $\mathcal{C}$ of decidable languages is **recursively presentable** if there is an effective enumeration $M_0,M_1,\dots$ of total deciders with $\mathcal{C}=\{L(M_i): i\in\mathbb{N}\}$. $\mathcal{C}$ is **closed under finite variations** if $L\in\mathcal{C}$ and $L\triangle L'$ finite imply $L'\in\mathcal{C}$. The classes $\mathsf{P}$, $\mathsf{NP}$, $\{L: L\le^{p}_{m}A\}$ for decidable $A\notin\{\emptyset,\{0,1\}^*\}$, and the decidable members of $\{L : B\le^p_m L\}$ for decidable $B\notin\mathsf{P}$ (the classes used in Ladner's argument) are recursively presentable and closed under finite variations; the restriction on $A$ is needed, since $\{L : L\le^p_m\emptyset\}=\{\emptyset\}$ is not closed under finite variations.

## Depends on

- [The complexity class P](../../the-classes-p-np-and-conp/p.md)

## Sources

- Uwe Schöning, "A Uniform Approach to Obtain Diagonal Sets in Complexity Classes", Theoretical Computer Science 18(1), 1982.
