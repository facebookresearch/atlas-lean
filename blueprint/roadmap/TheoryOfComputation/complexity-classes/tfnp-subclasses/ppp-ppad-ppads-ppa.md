# The classes PPP, PPAD, PPADS and PPA

$\mathsf{PPP}$, $\mathsf{PPAD}$, $\mathsf{PPADS}$ and $\mathsf{PPA}$ are the classes of total search problems polynomial-time search-reducible to PIGEON, END-OF-LINE, SINK-OF-LINE and LEAF respectively, where a search reduction from $R$ to $R'$ consists of polynomial-time maps $f$ on instances and $g$ on solutions with $(f(x),y')\in R'\Rightarrow(x,g(x,y'))\in R$. Each defining problem is complete for its class, for problems over arbitrary encoded instance types (uniform polynomial-time function families compile to circuit codes).

## Depends on

- [The canonical total search problems LOCALOPT, PIGEON, END-OF-LINE, SINK-OF-LINE and LEAF](canonical-total-search-problems.md)

## Sources

- Christos H. Papadimitriou, "On the Complexity of the Parity Argument and Other Inefficient Proofs of Existence", Journal of Computer and System Sciences 48(3), 1994.
- Paul Beame et al., "The Relative Complexity of NP Search Problems", Journal of Computer and System Sciences 57(1), 1998.
