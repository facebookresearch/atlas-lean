# Black-box groups, Group Non-Membership and Order Verification

A *black-box group* of encoding length $n$ is a finite group $G$ whose elements are represented (not necessarily uniquely) by strings in $\{0,1\}^n$, with oracles for multiplication, inversion and identity testing. A subgroup is specified by a list of generators. *Group Non-Membership* asks, given generators of $H \le G$ and $g \in G$, whether $g \notin H$. *Order Verification* asks, given generators of $H$ and an integer $N$ (with its prime factorization), whether $|H| = N$.

## Sources

- Laszlo Babai, Endre Szemeredi, "On the complexity of matrix group problems I", FOCS (1984).
- John Watrous, "Succinct quantum proofs for properties of finite groups", FOCS (2000); arXiv:cs/0009002.
