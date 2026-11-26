# Black-box groups, Group Non-Membership and Order Verification

A *black-box group* of encoding length $n$ is a finite group $G$ whose elements are represented by strings in $\{0,1\}^n$, with oracles for multiplication and inversion; it has *unique encoding* if every element has exactly one representation, and otherwise an identity-testing oracle is also given. Quantum results in this model (Watrous; Le Gall, Nishimura and Thakkar) assume unique encoding, with the oracles applicable in superposition. A subgroup is specified by a list of generators. *Group Non-Membership* asks, given generators of $H \le G$ and $g \in G$, whether $g \notin H$. *Order Verification* asks, given generators of $H$ and an integer $N$ (with its prime factorization), whether $|H| = N$.

## Sources

- Laszlo Babai, Endre Szemeredi, "On the complexity of matrix group problems I", FOCS (1984).
- John Watrous, "Succinct quantum proofs for properties of finite groups", FOCS (2000); arXiv:cs/0009002.
- Francois Le Gall, Harumichi Nishimura, Dhara Thakkar, "Group order is in QCMA", FOCS (2025); arXiv:2504.05547.
