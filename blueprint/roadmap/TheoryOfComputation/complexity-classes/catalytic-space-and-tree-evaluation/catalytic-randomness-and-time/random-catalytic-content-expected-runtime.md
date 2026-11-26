# Buhrman et al.: a random catalytic content gives expected running time 2^{O(s)}, hence CL is in ZPP

Let $M$ be a deterministic catalytic machine with free space $s\ge\log n$ and catalytic space $c$, and let $T_M(x,\tau)$ be its running time on input $x$ with initial catalytic content $\tau$. Then for every $x$,

$$
\mathbb{E}_{\tau\in\{0,1\}^c}\bigl[T_M(x,\tau)\bigr]\le 2^{O(s)}.
$$

Consequently $\mathsf{CL}\subseteq\mathsf{ZPP}$: a polynomial-time machine fills a simulated catalytic tape with random bits, runs $M$ for $4\cdot 2^{O(s)}=\mathrm{poly}(n)$ steps, and outputs $\bot$ if it has not halted.

## Proof sketch

The computation paths from distinct initial contents are vertex-disjoint in the configuration graph: a deterministic path is determined by any of its configurations onward, and a shared configuration would force both paths to halt in the same configuration, whose catalytic part equals the restored content. Hence $\sum_\tau T_M(x,\tau)$ is at most the number $2^{c}\cdot 2^{O(s)}$ of configurations, and averaging gives the bound. Markov's inequality bounds the probability of $\bot$ by $1/4$.

## Depends on

- [Polynomial-time catalytic logspace CLP and zero-error polynomial-time catalytic logspace CZPLP](polynomial-time-catalytic-logspace-classes.md)
- [ZPP](../../time-and-space-complexity-classes/zpp.md)

## Proof depends on

- [Configuration graph of a space-bounded machine](../../space-and-time-complexity/configuration-graph-of-a-space-bounded-machine.md)

## Sources

- Harry Buhrman, Richard Cleve, Michal Koucký, Bruno Loff and Florian Speelman, "Computing with a Full Memory: Catalytic Space", STOC (2014), ECCC TR14-053.
- James Cook, Jiatu Li, Ian Mertz and Edward Pyne, "The Structure of Catalytic Space: Capturing Randomness and Time via Compression", STOC (2025), ECCC TR24-106.
