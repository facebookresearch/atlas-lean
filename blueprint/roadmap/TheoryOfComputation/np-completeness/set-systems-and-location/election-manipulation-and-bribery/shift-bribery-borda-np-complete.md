# SHIFT BRIBERY for Borda is NP-complete

The SHIFT BRIBERY for Borda decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: an election $E = (C, V)$ with candidates $C = \{c_1, \dots, c_m\}$, a preferred candidate $p \in C$, and voters $V = (v_1, \dots, v_n)$, each a strict linear order over $C$; for each voter $v_i$, in which $p$ is preceded by $j_i$ candidates (so $p$ can move up at most $j_i$ places), a shift-bribery price function $\rho_i$ with $\rho_i(0) = 0$ and finite natural prices $\rho_i(1) \le \rho_i(2) \le \dots \le \rho_i(j_i)$ for every shift up to $j_i$ places, a shift by more than $j_i$ places being unavailable (infinite price); and a nonnegative integer $B$ (the budget). Question: is there a sequence $(k_1, \dots, k_n)$ of nonnegative integers with $k_i \le j_i$ for each $i$ such that $\sum_i \rho_i(k_i) \le B$ and bribing each voter $v_i$ to shift $p$ up by $k_i$ places ensures that $p$ is a Borda winner (a candidate with the highest Borda score, ties allowed) of the resulting election?

## Sources

- E. Elkind, P. Faliszewski and A. Slinko, "Swap bribery", Algorithmic Game Theory (SAGT 2009), Lecture Notes in Computer Science 5814, Springer (2009), 299-310, doi:10.1007/978-3-642-04645-2_27, Theorem 7 in this conference version; in the preprint arXiv:0905.3885 the problem is Definition 3.7 and the result is Theorem 5.1.
