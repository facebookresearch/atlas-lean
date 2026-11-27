# Most conjectured polynomial-time separations are automatically constructive

Chen, Jin, Santhanam and Williams show that if a class such as NP, PP, PSPACE, EXP or NEXP is not contained in P, ZPP or BPP, then every paddable complete language of that class has a constructive separation: counterexamples for each weak algorithm can be printed efficiently.

Let $\mathcal{C} \in \{\mathsf{P}, \mathsf{ZPP}, \mathsf{BPP}\}$ and $\mathcal{D} \in \{\mathsf{NP}, \Sigma_2\mathsf{P}, \dots, \Sigma_k\mathsf{P}, \dots, \mathsf{PP}, \mathsf{PSPACE}, \mathsf{EXP}, \mathsf{NEXP}, \mathsf{EXP}^{\mathsf{NP}}\}$. Then $\mathcal{D} \not\subseteq \mathcal{C}$ implies that for every paddable $\mathcal{D}$-complete language $L$ there is a $\mathcal{C}$-constructive separation of $L \notin \mathcal{C}$. Furthermore, $\oplus\mathsf{P} \not\subseteq \mathcal{C}$ implies that for every paddable $\oplus\mathsf{P}$-complete language $L$ there is a $\mathsf{BPP}$-constructive separation of $L \notin \mathcal{C}$. Completeness is under polynomial-time many-one reductions, and $L$ is paddable if a polynomial-time algorithm maps $(x, 1^n)$ with $|x| \le n - 1$ to $y \in \{0,1\}^n$ with $L(x) = L(y)$.

## Expansion

This generalizes the theorem of Gutfreund, Shaltiel and Ta-Shma that $\mathsf{P} \ne \mathsf{NP}$ yields polynomial-time refuters for SAT, and the analogous result of Dolev, Fandina and Gutfreund for $\mathsf{BPP} \ne \mathsf{NEXP}$. For classes beyond NP the refuters cannot check their own outputs, which makes the statement counterintuitive: for instance, if $\mathsf{PSPACE} \ne \mathsf{P}$ then polynomial-time algorithms print hard QBF instances for every polynomial-time algorithm claiming to solve QBF. The proofs build constant-size list-refuters, which use the assumed separation to locate an error, and then reduce the list to a single string using paddability and completeness.

## Depends on

- [Refuters and constructive separations](constructive-separation.md)
- [Polynomial space for decision problems](../../../complexity-classes/time-and-space-complexity-classes/pspace.md)
- [The class EXP](../../../complexity-classes/time-and-space-complexity-classes/exp.md)
- [The complexity class NEXP](../../../complexity-classes/time-and-space-complexity-classes/nexp.md)
- [Probabilistic polynomial time with unbounded error](../../../complexity-classes/time-and-space-complexity-classes/pp.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

None.

## Sources

- Lijie Chen, Ce Jin, Rahul Santhanam and Ryan Williams, "Constructive Separations and Their Consequences", *TheoretiCS* 3, 2024 (conference version FOCS 2022), DOI 10.46298/theoretics.24.3, arXiv:2203.14379v5 (theorem on uniform separations in Section 1.1, with its footnote on completeness and paddability; proof in Section 5).
