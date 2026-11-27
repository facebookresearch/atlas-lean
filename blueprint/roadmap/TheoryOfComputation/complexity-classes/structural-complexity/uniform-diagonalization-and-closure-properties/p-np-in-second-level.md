# P^NP ⊆ Σ₂ ∩ Π₂

For every $A\in\mathsf{NP}$, $\mathsf{P}^{A}\subseteq\Sigma_2^p\cap\Pi_2^p$. Consequently $\mathsf{P}^{\mathsf{NP}}\subseteq\Sigma_2^p\cap\Pi_2^p$ and $\mathsf{P}^{\mathsf{NP}[O(\log n)]}\subseteq\mathsf{PH}$.

## Proof sketch

A $\Sigma_2$ machine guesses the transcript of oracle answers together with NP witnesses for all 'yes' answers, and universally verifies that every 'no' answer is correct (a coNP condition); the guessed transcript is then the true one, and the polynomial-time computation is replayed. Closure of $\mathsf{P}^A$ under complement gives the $\Pi_2$ bound.

## Depends on

- [Polynomial time with an oracle](../../time-and-space-complexity-classes/pwith-oracle.md)
- [The class $\Sigma_k^p$](../../time-and-space-complexity-classes/sigma-k.md)
- [The universal levels of the polynomial hierarchy](../../time-and-space-complexity-classes/pi-k.md)
- [The complexity class NP](../../the-classes-p-np-and-conp/np.md)

## Sources

- Larry J. Stockmeyer, "The Polynomial-Time Hierarchy", Theoretical Computer Science 3(1), 1976.
- Lane A. Hemaspaandra and Mitsunori Ogihara, "The Complexity Theory Companion", Springer, 2002.
