# Krokhin–Opršal–Wrochna–Živný: adjunction reductions for approximate graph colouring

(i) If there is an integer $k\ge 3$ such that $\mathrm{PCSP}(\mathbb{K}_k,\mathbb{K}_c)$ is NP-hard for all $c\ge k$, then $\mathrm{PCSP}(\mathbb{K}_3,\mathbb{K}_c)$ is NP-hard for all $c\ge 3$. (ii) For every $k\ge 4$ and

$$
c=\binom{k}{\lfloor k/2\rfloor}-1,
$$

$\mathrm{PCSP}(\mathbb{K}_k,\mathbb{K}_c)$ is NP-hard, an exponential improvement over the bound $c=2k-1$ for large $k$. Both statements rest on the observation that pairs of **adjoint** functors between categories of graphs (thin graph constructions $\Lambda$ with right adjoint $\Gamma$, so that $\Lambda X\to Y$ iff $X\to\Gamma Y$) always yield reductions between PCSPs.

## Proof sketch

If $\Lambda$ is left adjoint to $\Gamma$, then $\Lambda$ maps instances of $\mathrm{PCSP}(\mathbb{A},\Gamma\mathbb{B})$ to instances of $\mathrm{PCSP}(\Lambda\mathbb{A},\mathbb{B})$ preserving both the YES and the NO side. Using the arc-graph construction $\delta$ and its adjoint, whose chromatic numbers behave like $\chi(\delta G)\approx\log_2\chi(G)$, one moves hardness between colouring templates; for (ii) the Sperner-type bound $\binom{k}{\lfloor k/2\rfloor}$ appears as the chromatic number threshold of iterated arc graphs.

## Depends on

- [Promise constraint satisfaction PCSP(A,B) for a pair of finite templates](promise-csp-of-a-template-pair.md)

## Proof depends on

- [Barto–Bulín–Krokhin–Opršal: it is NP-hard to (2k−1)-colour a k-colourable graph, in particular to 5-colour a 3-colourable graph](bbko-np-hard-2k-minus-1-colour-k-colourable.md)
- [Barto–Bulín–Krokhin–Opršal: minion homomorphisms between polymorphism minions give log-space PCSP reductions](bbko-minion-homomorphism-log-space-reduction.md)

## Sources

- Andrei Krokhin, Jakub Opršal, Marcin Wrochna and Stanislav Živný, "Topology and adjunction in promise constraint satisfaction", SIAM Journal on Computing 52(1) (2023), arXiv:2003.11351.
