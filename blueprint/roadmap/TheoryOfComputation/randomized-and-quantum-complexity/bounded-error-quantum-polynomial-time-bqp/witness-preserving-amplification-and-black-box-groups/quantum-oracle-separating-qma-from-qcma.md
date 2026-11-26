# Aaronson-Kuperberg: a quantum oracle separates QMA from QCMA

There is a quantum oracle (a family of unitaries $U_\psi$ reflecting about an unknown Haar-random $n$-qubit state $|\psi\rangle$, or the identity) relative to which $\mathrm{QMA} \not\subseteq \mathrm{QCMA}$: deciding which case holds needs $\Omega(\sqrt{2^n/(m+1)})$ oracle queries for any QCMA verifier receiving an $m$-bit classical witness, while the quantum witness $|\psi\rangle$ allows verification with one query.

## Proof sketch

A classical witness of $m$ bits partitions the space of candidate states into $2^m$ cells, so some witness $w^*$ has a cell of Haar measure at least $2^{-m}$; fix it. A concentration-of-measure lemma shows that for any fixed query state $\phi$, the average of $|\langle \phi|\psi\rangle|^2$ over $|\psi\rangle$ in a set of measure at least $2^{-m}$ is $O((m+1)/2^n)$. A hybrid argument generalizing the BBBV lower bound for search then shows that each query changes the final state by $O(\sqrt{(m+1)/2^n})$ on average, so $\Omega(\sqrt{2^n/(m+1)})$ queries are needed.

## Depends on

- [The class QCMA of quantum verification with classical witnesses](quantum-classical-merlin-arthur.md)

## Sources

- Scott Aaronson, Greg Kuperberg, "Quantum versus classical proofs and advice", Theory of Computing 3 (2007), CCC (2007); arXiv:quant-ph/0604056.
