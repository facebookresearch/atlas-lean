# Partition gadget for Set Cover hardness

Let $\gamma$ be a finite set and $t \ge 1$. A *partition gadget* over $\gamma$ is a finite universe $U$ with subsets $S_b \subseteq U$ for $b \in \gamma$. It *separates up to $t$ labels* if for all disjoint $P, Q \subseteq \gamma$ with $|P| + |Q| \le t$ some point of $U$ lies in every $S_b$ with $b \in P$ and in no $S_b$ with $b \in Q$. Equivalently, no family of at most $t$ sets, each of the form $S_b$ or $U \setminus S_{b'}$, with no index used both ways, covers $U$.

## Sources

- C. Lund and M. Yannakakis, "On the Hardness of Approximating Minimization Problems", Journal of the ACM 41(5), 1994.
- U. Feige, "A Threshold of ln n for Approximating Set Cover", Journal of the ACM 45(4), 1998.
