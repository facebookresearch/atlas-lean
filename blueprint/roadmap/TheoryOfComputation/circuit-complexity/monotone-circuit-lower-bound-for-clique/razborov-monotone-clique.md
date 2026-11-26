# Razborov: monotone circuits for clique need superpolynomial size

For every polynomial
$p$ with natural-number coefficients there is a natural number $n$ with the following property.
Let $C$ be a well-formed monotone flat circuit on $n^2$ inputs, that is, every gate of $C$ is an
input variable, an and gate or an or gate (of any fan-in), and refers only to earlier gates. Suppose that for
every bitstring $x$ of length $n^2$, when input variable $i$ is given the $i$-th bit of $x$, $C$
has a last gate with value true if and only if the $n \times n$ matrix read from $x$ in
row-major order has a clique of size $\lfloor n/3 \rfloor$, that is, a set
$S \subseteq \{0, \dots, n - 1\}$ of $\lfloor n/3 \rfloor$ vertices whose entries $(a, b)$ are
true for all distinct $a, b \in S$. Then $C$ has more than $p(n^2)$ gates.

Razborov's theorem concerns $\mathrm{CLIQUE}(m, s)$, the existence of an $s$-clique in a graph on $m$ vertices: monotone circuits of fan-in two need size $m^{\Omega(\log m)}$ when $s$ is about $(\log m)/4$, and size $\Omega(m^s/(\log m)^{2s})$ for fixed $s$. His *approximation method* replaces every gate by an approximator from a small lattice of monotone functions and shows that each replacement errs on few test inputs (cliques and complete $(s-1)$-partite graphs), while every approximator errs on many of them. Alon and Boppana sharpened the method to the exponential bound $\exp(\Omega((m/\log m)^{1/3}))$ for $s$ about $(m/(8\log m))^{2/3}$.

The statement above, for cliques of size $\lfloor n/3 \rfloor$, follows by padding. Setting to true every input bit that involves $\lfloor n/3 \rfloor - s$ chosen vertices makes them universal, and turns a monotone circuit for the $\lfloor n/3 \rfloor$-clique function on $n$ vertices into one, no larger after constant propagation, for $s$-cliques on the remaining $m \ge 2n/3$ vertices. Gates here have unbounded fan-in. Inputs are themselves gates of the list, so a gate refers to at most $g$ distinct earlier gates, and a circuit with $g$ gates has a fan-in-two equivalent with at most $g^2$ gates; superpolynomial bounds transfer.

## Background

- [Erdős–Rado sunflower lemma](../../../Combinatorics/extremal-set-theory/intersecting-families/sunflower-lemma/exists-is-delta-system.md): bounds the errors of the approximators in the approximation method.
- [Shannon's circuit-size lower bound](../shannon-s-circuit-size-lower-bound/README.md): almost all Boolean functions need large circuits, while no superpolynomial bound is known for an explicit function in unrestricted circuits; monotone circuits are the restricted model where Razborov's method succeeds.

## Sources

- A. A. Razborov, "Lower bounds on the monotone complexity of some Boolean functions", Soviet Mathematics Doklady 31 (1985), 354-357.
- N. Alon and R. B. Boppana, "The monotone circuit complexity of Boolean functions", Combinatorica 7 (1987), 1-22, Section 1 (statement of Razborov's bounds) and Section 3 (exponential bound for clique).
