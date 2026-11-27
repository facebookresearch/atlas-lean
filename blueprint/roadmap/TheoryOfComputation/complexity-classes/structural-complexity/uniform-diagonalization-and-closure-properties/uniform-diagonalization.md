# Schöning's uniform diagonalization theorem

Let $\mathcal{C}_1,\mathcal{C}_2$ be recursively presentable classes of languages, both closed under finite variations, and let $A_1\notin\mathcal{C}_1$, $A_2\notin\mathcal{C}_2$ be decidable. Then there is a set $G\in\mathsf{P}$ such that the language

$$
A=(A_1\cap G)\cup(A_2\cap\overline{G})
$$

lies in neither $\mathcal{C}_1$ nor $\mathcal{C}_2$. Moreover $A$ is decidable and $A\le^{p}_{m}A_1\oplus A_2$ via $x\mapsto(0,x)$ for $x\in G$ and $(1,x)$ otherwise.

## Proof sketch

$G$ consists of long blocks of consecutive input lengths; a block ends only after the slow, clocked enumeration has found, for the next machine of $\mathcal{C}_1$ (resp. $\mathcal{C}_2$), an input on which it differs from $A_1$ (resp. $A_2$). Such inputs exist beyond any given length because $A_1\notin\mathcal{C}_1$ (resp. $A_2\notin\mathcal{C}_2$) and the classes are closed under finite variations, so no member of the class can agree with $A_1$ (resp. $A_2$) on all long inputs. Because block boundaries are computed by a clocked search, $G$ is polynomial-time decidable.

## Depends on

- [Recursively presentable complexity classes](../reducibilities-and-isomorphism/recursively-presentable-classes.md)
- [The complexity class P](../../the-classes-p-np-and-conp/p.md)

## Sources

- Uwe Schöning, "A Uniform Approach to Obtain Diagonal Sets in Complexity Classes", Theoretical Computer Science 18(1), 1982.
