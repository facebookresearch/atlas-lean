# Generalized constraint satisfaction problems with payoff functions

Fix a finite domain $[q]$, an arity $k$ and a finite family $\Lambda$ of **payoff functions** $P : [q]^k \to [0, 1]$. An instance $\Im$ of $\mathrm{GCSP}(\Lambda)$ on variables $V$ is a probability distribution over constraints $(P, (v_1, \dots, v_k))$ with $P \in \Lambda$ and $v_i \in V$. An assignment $x : V \to [q]$ has value

$$
\operatorname{val}_\Im(x) = \mathbb{E}_{(P, v) \sim \Im} P\bigl(x(v_1), \dots, x(v_k)\bigr),
$$

and $\operatorname{opt}(\Im) = \max_x \operatorname{val}_\Im(x)$. The **Max-$P$** problem for a predicate $P \subseteq [q]^k$ is the special case $\Lambda = \{1_P\}$ with arbitrary literal patterns (all shifts of $P$).

## Sources

- P. Raghavendra, "Optimal algorithms and inapproximability results for every CSP?", STOC (2008).
- P. Raghavendra, D. Steurer, "How to round any CSP", FOCS (2009).
