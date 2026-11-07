# NP relative to an oracle

Let $O$ be a function from bitstrings to booleans. The class
$\mathrm{NP}^O$ is the set of decision problems $L$ for which there are polynomials $p$ and $q$
with natural-number coefficients and polynomial-time computable functions $\mathrm{nextQ}$ and
$\mathrm{final}$, each taking a bitstring and a list of query/answer pairs, such that for every
bitstring $x$, $L(x)$ is true if and only if there is a bitstring $w$ of length at most $p(|x|)$,
where $|x|$ is the length of $x$, for which the oracle computation that chooses queries with
$\mathrm{nextQ}$ and decides with $\mathrm{final}$, run with oracle $O$, query-length cap $q(|x|)$
and $p(|x|)$ adaptive queries on the bitstring encoding of the pair $(x, w)$ from the empty
history, returns true.
