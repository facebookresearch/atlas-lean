# Probabilistically checkable proofs

For functions $r, q : \mathbb{N} \to \mathbb{N}$, the
class $\mathrm{PCP}(r, q)$ consists of the decision problems $L$ for which there are
polynomial-time computable functions $Q$ and $D$ such that $Q(x, \rho)$ is a list of at most
$q(|x|)$ natural numbers for all bitstrings $x$ and $\rho$, and such that for every bitstring $x$
the following holds. For a proof $\pi : \mathbb{N} \to \{\mathrm{true}, \mathrm{false}\}$, let
$\pi(Q(x, \rho))$ be the list of values of $\pi$ at the entries of $Q(x, \rho)$, and let
$P_\pi(x)$ be the probability, over a uniformly random bitstring $\rho$ of length $r(|x|)$, that
$D(x, \rho, \pi(Q(x, \rho)))$ is true. If $L(x)$ is true, then $P_\pi(x) \ge 2/3$ for some proof
$\pi$; if $L(x)$ is false, then $P_\pi(x) \le 1/3$ for every proof $\pi$.

The verifier is non-adaptive: the queried positions depend only on $x$ and $\rho$.
