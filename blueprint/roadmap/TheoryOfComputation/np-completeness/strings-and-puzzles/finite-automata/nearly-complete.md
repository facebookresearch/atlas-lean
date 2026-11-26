# Nearly complete samples

For natural numbers $p$ and $q$ and a sample $(S, T)$ over an alphabet of $m$ letters, let $|\Sigma^{(n)}|$ be the number of strings of length at most $n$ over that alphabet. The sample is nearly complete for $(p, q)$ when for some $n$ every string of $S$ and $T$ has length at most $n$ and

$$\big(|\Sigma^{(n)}| - |S \cup T|\big)^q \le |\Sigma^{(n)}|^p,$$

where $|S \cup T|$ counts distinct strings and the difference of the two cardinalities is truncated at $0$. Length alone does not make $S \cup T$ a subset of $\Sigma^{(n)}$, since a string of $S$ or $T$ may use a letter outside the alphabet. When $S \cup T \subseteq \Sigma^{(n)}$ and $q > 0$, the condition reads $|\Sigma^{(n)} \setminus (S \cup T)| \le |\Sigma^{(n)}|^{\varepsilon}$ with $\varepsilon = p/q$. For $q = 0$ the inequality reads $1 \le |\Sigma^{(n)}|^p$, which always holds since $|\Sigma^{(n)}| \ge 1$, so every sample is nearly complete.
