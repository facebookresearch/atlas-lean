# Recursively presentable complexity classes

A class $\mathcal{C}$ of decidable languages is **recursively presentable** if there is an effective enumeration $M_0,M_1,\dots$ of total deciders with $\mathcal{C}=\{L(M_i): i\in\mathbb{N}\}$. $\mathcal{C}$ is **closed under finite variations** if $L\in\mathcal{C}$ and $L\triangle L'$ finite imply $L'\in\mathcal{C}$. The classes $\mathsf{P}$, $\mathsf{NP}\cap\mathrm{DEC}$, $\{L: L\le^{p}_{m}A\}$ for decidable $A$, and $\{L : B\not\le^p_m L\}$-type complements used in Ladner's argument are recursively presentable and closed under finite variations.

## Depends on

- [The complexity class P](../../the-classes-p-np-and-conp/p.md)

## Sources

- Uwe Schöning, "A Uniform Approach to Obtain Diagonal Sets in Complexity Classes", Theoretical Computer Science 18(1), 1982.
