# The logical unitaries of a code form a group

Let $P$ be the orthogonal projector onto a code subspace of a finite-dimensional space. Call a unitary $U$ *logical* if it
preserves the code, $P U P = U P$. The logical unitaries form a group: $I$ is logical, $P U V P = P U P V P = U P V P = U V P$
for logical $U, V$, and for logical $U$ the inverse $U^{*}$ is logical, because $P U^{*} P$ inverts $P U P$ on the code
subspace, which gives $U^{*} P = P U^{*} P$. The set of logical unitaries is closed, being the preimage of $0$ under the
continuous map $U \mapsto (I - P) U P$.

## Sources

- B. Eastin and E. Knill, *Restrictions on transversal encoded quantum gate sets*, Phys. Rev. Lett. 102 (2009), 110502, arXiv:0811.4262, Lemma 1 and its proof, and the proof of Lemma 2 (closedness, "from Eq. 1").
