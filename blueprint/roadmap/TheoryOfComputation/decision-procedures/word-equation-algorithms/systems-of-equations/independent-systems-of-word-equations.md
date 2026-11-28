# Independent systems of constant-free word equations

A system of word equations is independent when it is not equivalent to any of its proper subsystems, that is, when each equation excludes some solution that the others allow.

Let $\Xi$ be a finite set of $n$ unknowns and $\Sigma^*$ the free monoid over an alphabet $\Sigma$. A constant-free word equation is a pair $E = (u, v)$ of words $u, v \in \Xi^*$, written $u = v$; a morphism $h : \Xi^* \to \Sigma^*$, possibly erasing, is a solution of $E$ if $h(u) = h(v)$, and of a finite or infinite system of equations if it solves each of them. Write $|E| = |uv|$ for the length of $E$ and $|E|_x = |uv|_x$ for the number of occurrences of an unknown $x$ on both sides. The equation is trivial if $u = v$ and balanced if $|u|_x = |v|_x$ for every $x \in \Xi$.

- Two systems are equivalent if they have the same solutions.
- A system is independent if it is not equivalent to any of its proper subsystems; equivalently, for every equation $E$ of the system some morphism solves all the other equations but not $E$.
- A solution $h$ is periodic if there is a word $t$ with $h(x) \in t^*$ for every $x \in \Xi$, and nonperiodic otherwise.
- A finite sequence of equations $E_1, \dots, E_m$ is a decreasing chain if for every $i \in \{0, \dots, m - 1\}$ the system $E_1, \dots, E_i$ is not equivalent to $E_1, \dots, E_{i+1}$; an infinite sequence $E_1, E_2, \dots$ is a decreasing chain if the same is true for every $i \ge 0$.

For $\Sigma$ with at least two letters, the maximal size $\mathrm{IS}(n)$ of an independent system over $n$ unknowns takes values in $\mathbb{N} \cup \{\mathrm{ub}, \infty\}$, ordered by $k < \mathrm{ub} < \infty$ for $k \in \mathbb{N}$: it is $\infty$ if there is an infinite independent system, $\mathrm{ub}$ if all independent systems are finite but their sizes are unbounded, and otherwise the largest size. $\mathrm{IS}'(n)$ is defined in the same way for independent systems that have a nonperiodic solution, and $\mathrm{DC}(n)$ for decreasing chains. A free monoid has the compactness property if every system of equations is equivalent to one of its finite subsystems.

## Depends on

- [Solution of a word equation](../../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)

## Proof depends on

None.

## Expansion

A trivial equation is equivalent to the empty system, so it belongs to no independent system. With two unknowns every nontrivial equation has only periodic solutions, so the first nontrivial case is $n = 3$. Karhumäki and Saarela record the inequalities $\mathrm{IS}'(n) \le \mathrm{IS}(n) \le \mathrm{IS}'(n) + 1$, with $\mathrm{ub} + 1 = \mathrm{ub}$ and $\infty + 1 = \infty$.

## Sources

- Juhani Karhumäki, Aleksi Saarela, "On maximal chains of systems of word equations", Proceedings of the Steklov Institute of Mathematics 274 (2011), 116–123, https://doi.org/10.1134/S0081543811060083; read as arXiv:1506.02913v1, https://arxiv.org/abs/1506.02913v1, Section 2 ("Systems and Chains of Word Equations") for systems, independence, decreasing chains and the values $\mathrm{ub}$ and $\infty$, and Section 4 ("Free Monoids") for periodic solutions, balanced equations, $\mathrm{IS}'$ and the inequalities
- Štěpán Holub, Jan Žemlička, "Algebraic properties of word equations", Journal of Algebra 434 (2015), 283–301, https://doi.org/10.1016/j.jalgebra.2015.03.021; read as arXiv:1403.1951v2, https://arxiv.org/abs/1403.1951v2, Section 2 (equations and solutions) and Section 4 (equivalence, independence, compactness property)
