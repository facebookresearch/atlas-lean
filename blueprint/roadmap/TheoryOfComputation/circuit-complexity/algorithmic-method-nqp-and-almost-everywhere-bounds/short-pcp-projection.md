# Short PCPs with projection queries for nondeterministic time

Let $M$ be an algorithm running in time $T = T(n) \ge n$ on inputs $(x, y)$ with $|x| = n$. Given $x \in \{0,1\}^n$, one can output in time $\mathrm{poly}(n, \log T)$ circuits $\mathrm{Query} : \{0,1\}^r \to [2^r]^t$ with $t = \mathrm{poly}(r)$ and $\mathrm{Dec} : \{0,1\}^t \to \{0,1\}$ such that:

- **proof length**: $2^r \le T \cdot \operatorname{polylog} T$, so the verifier uses $r \le \log T + O(\log\log T)$ random bits and reads $t = \mathrm{poly}(r)$, at most $\operatorname{polylog}(T)$, proof bits;
- **completeness**: if some $y$ makes $M(x, y)$ accept, there is a proof $\pi : [2^r] \to \{0,1\}$ with $\mathrm{Dec}(\pi(q_1), \dots, \pi(q_t)) = 1$ for every $z \in \{0,1\}^r$, where $(q_1, \dots, q_t) = \mathrm{Query}(z)$;
- **soundness**: if no $y$ makes $M(x, y)$ accept, then for every $\pi$ at most a $1/n^{10}$ fraction of the $z \in \{0,1\}^r$ give $\mathrm{Dec}(\pi(q_1), \dots, \pi(q_t)) = 1$;
- **projection queries**: $\mathrm{Query}$ is a projection (1-local): each of its output bits is one bit of the random string $z$, the negation of one bit, or a constant; and $\mathrm{Dec}$ is a 3CNF.

## Proof sketch

Start from a quasi-linear-size PCP of proximity for circuit satisfiability based on Reed-Solomon codes over additive subgroups of binary fields. Choosing the evaluation domains as subspaces of $\mathbb{F}_2^m$ with coordinates aligned to the random bits makes every query address an affine, and after re-encoding a projection, function of the randomness, which is what the algorithmic method needs to check PCP queries with simple circuits.

## Proof depends on

- [The PCP theorem: NP = PCP(O(log n), O(1))](../../pcp-and-inapproximability/pcp-theorem.md)

## Sources

- E. Ben-Sasson, E. Viola, "Short PCPs with projection queries", ICALP (2014), ECCC TR14-017 (Theorem 1.1).
- C. Murray, R. Williams, "Circuit lower bounds for nondeterministic quasi-polytime: an easy witness lemma for NP and NQP", STOC (2018); SIAM Journal on Computing 49 (2020).
