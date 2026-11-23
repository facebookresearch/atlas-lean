# The class $\mathsf{AM}$ (Arthur–Merlin)

A decision problem $L$ on bitstrings is in
$\mathsf{AM}$ when there are polynomials $p$ and $q$ with natural-number coefficients and a
polynomial-time computable Boolean function $R(x, r, w)$ of three bitstrings such that, for every
bitstring $x$, writing $A_x$ for the set of strings $r \in \{0,1\}^{p(|x|)}$ for which some
bitstring $w$ of length at most $q(|x|)$ makes $R(x, r, w)$ true: if $L(x)$ is true then
$3|A_x| \ge 2 \cdot 2^{p(|x|)}$, and if $L(x)$ is false then $3|A_x| \le 2^{p(|x|)}$.

Here $r$ is Arthur's random string and $w$ is Merlin's reply, so for uniformly random $r$ the
acceptance probability is at least $2/3$ on yes-instances and at most $1/3$ on no-instances.
