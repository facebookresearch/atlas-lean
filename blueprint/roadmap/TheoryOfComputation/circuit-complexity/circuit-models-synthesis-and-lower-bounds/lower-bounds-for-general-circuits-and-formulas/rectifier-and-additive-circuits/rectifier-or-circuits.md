# Rectifier (OR) circuits for Boolean matrices

A *rectifier $(p,q)$-circuit* is a directed graph with $p$ input poles and $q$ output poles; it *realizes* a Boolean $p\times q$ matrix $A$ if for all $i,j$ there is a directed path from input $i$ to output $j$ exactly when $A_{ij}=1$. Equivalently, it is a circuit of unbounded fan-in OR gates computing the linear Boolean operator $y_j=\bigvee_{i:A_{ij}=1}x_i$. Its size is its number of edges. The *OR-complexity* $\mathrm{OR}(A)$ is the least size of a rectifier circuit realizing $A$, and $\mathrm{OR}_d(A)$ restricts to circuits of depth at most $d$. The *weight* $|A|$ is the number of ones of $A$; trivially $\mathrm{OR}(A)\le\mathrm{OR}_1(A)=|A|$.

## Depends on

- [Straight-line programs and circuits over a basis](../../circuit-models-and-classes/circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)

## Sources

- O. B. Lupanov, "On Rectifier and Switching-and-Rectifier Schemes", Doklady Akademii Nauk SSSR, 1956.
- Stasys Jukna, Igor Sergeev, "Complexity of Linear Boolean Operators", Foundations and Trends in Theoretical Computer Science, 2013.
