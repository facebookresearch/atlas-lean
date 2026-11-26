# Valid catalytic machines with nondeterministic or random choices

Recall the catalytic model: a catalytic Turing machine with free space $s=s(n)$ and catalytic space $c=c(n)$ has a read-only input tape holding $x\in\{0,1\}^n$, a read-write work tape of length $s$ initialized to $0^s$, and a read-write catalytic tape of length $c\le 2^{s}$ initialized to an arbitrary string $\tau\in\{0,1\}^c$. Free space counts only work-tape cells.

A machine with choices has, at every step, two (not necessarily distinct) transitions, the $0$-choice and the $1$-choice; equivalently the choices are read one way from a read-only auxiliary tape. The machine is **valid** if for every input $x$, every initial catalytic content $\tau$ and **every** sequence of choices, it halts after finitely many steps with the catalytic tape again equal to $\tau$. Thus restoration is required with certainty on every computation path, not merely with high probability.

A valid machine computes a Boolean function $f$:

- nondeterministically, if for every $x$: $f(x)=1$ iff some choice sequence leads to acceptance (co-nondeterministically: $f(x)=0$ iff some choice sequence rejects);
- with bounded error, if for every $x$ and $\tau$ the output equals $f(x)$ with probability at least $2/3$ over uniformly random choices;
- with unbounded error, if for every $x$ and $\tau$ the output equals $f(x)$ with probability strictly greater than $1/2$;
- with zero error, if for every $x$ and $\tau$ the output is always $f(x)$ or a special symbol $\bot$, and $\bot$ appears with probability at most $1/2$.

## Depends on

- [Configuration graph of a space-bounded machine](../../space-and-time-complexity/configuration-graph-of-a-space-bounded-machine.md)
- [Deterministic logarithmic space](../../time-and-space-complexity-classes/log-space.md)

## Sources

- Michal Koucký, Ian Mertz, Edward Pyne and Sasha Sami, "Collapsing Catalytic Classes", FOCS (2025), arXiv:2504.08444, ECCC TR25-019.
- James Cook, Jiatu Li, Ian Mertz and Edward Pyne, "The Structure of Catalytic Space: Capturing Randomness and Time via Compression", STOC (2025), ECCC TR24-106.
- Harry Buhrman, Michal Koucký, Bruno Loff and Florian Speelman, "Catalytic Space: Non-determinism and Hierarchy", Theory of Computing Systems 62(1) (2018).
- Samir Datta, Chetan Gupta, Rahul Jain, Vimal Raj Sharma and Raghunath Tewari, "Randomized and Symmetric Catalytic Computation", CSR (2020), ECCC TR20-024.
