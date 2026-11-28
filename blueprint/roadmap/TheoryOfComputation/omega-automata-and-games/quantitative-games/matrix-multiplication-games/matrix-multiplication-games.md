# Matrix multiplication games

In a matrix multiplication game two players alternately write matrices from two fixed sets, Adam first, and Adam pays Eve the exponential growth rate of the norm of the resulting infinite product.

**Definition.** Let $\mathcal{A}$ be a set of $M \times N$ real matrices and $\mathcal{E}$ a set of $N \times M$ real matrices. In the *matrix multiplication game* (MMG) on $(\mathcal{A}, \mathcal{E})$, at each round $i = 1, 2, \dots$ Adam writes $A_i \in \mathcal{A}$ and then Eve writes $E_i \in \mathcal{E}$; a *play* is the infinite sequence $A_1 E_1 A_2 E_2 \cdots$. A strategy of Adam is a map $\sigma : (\mathcal{A} \mathcal{E})^* \to \mathcal{A}$ and a strategy of Eve is a map $\tau : (\mathcal{A} \mathcal{E})^* \mathcal{A} \to \mathcal{E}$; a pair $(\sigma, \tau)$ determines a unique play, and Adam pays Eve

$$
P(\sigma, \tau) = \limsup_{k \to \infty} \Big\lVert \prod_{i=1}^{k} A_i E_i \Big\rVert^{1/k},
$$

where $\lVert \cdot \rVert$ is the $1$-norm (any other norm gives the same growth rate). The game is *determined with value $V$* if Adam has a strategy $\sigma_0$ with $P(\sigma_0, \tau) \le V$ for every $\tau$ and Eve has a strategy $\tau_0$ with $P(\sigma, \tau_0) \ge V$ for every $\sigma$. A player *ensures* a bound if some strategy of theirs guarantees it against every strategy of the opponent.

When Adam's set is $\{I\}$, the value is the joint spectral radius $\hat\rho(\mathcal{E}) = \lim_{n \to \infty} \sup \{ \lVert E_1 \cdots E_n \rVert^{1/n} : E_i \in \mathcal{E} \}$. MMGs whose sets are compact sets of non-negative matrices with independent row uncertainty are determined, with optimal strategies that always play the same matrix (Theorem 13 of the source), and each entropy game of the same source takes its value and optimal positional strategies from the MMG of its arena (Section 3.4, Lemma 15 and Theorem 16).

## Depends on

None.

## Proof depends on

None.

## Sources

- E. Asarin, J. Cervelle, A. Degorre, C. Dima, F. Horn and V. Kozyakin, "Entropy Games and Matrix Multiplication Games", *33rd Symposium on Theoretical Aspects of Computer Science (STACS 2016)*, Leibniz International Proceedings in Informatics 47, 2016, Article 11, doi:[10.4230/LIPIcs.STACS.2016.11](https://doi.org/10.4230/LIPIcs.STACS.2016.11); numbering of arXiv:1506.04885v3: the definition of matrix multiplication games and their payoff in Section 3 (the two games), the notion of determinacy with a value in the proofs of Lemmas 3 and 4, and the joint spectral radius in Section 2.
