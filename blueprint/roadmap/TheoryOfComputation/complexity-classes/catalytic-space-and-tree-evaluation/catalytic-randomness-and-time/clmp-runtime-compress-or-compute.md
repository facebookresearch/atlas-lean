# Cook–Li–Mertz–Pyne compress-or-compute: a long-running catalytic computation compresses its own tape

Let $s = s(n) \ge \log n$ be space constructible and let $L \in \mathsf{CSPACE}[s]$ be decided by a deterministic catalytic machine $M$ using workspace $s$ and catalytic tape length $2^s$ (for $\mathsf{CL}$, $s = O(\log n)$). For every compression parameter $B \ge 1$, there exist catalytic subroutines $\mathrm{DetComp}$ and $\mathrm{DetDecomp}$ running in worst-case time $\mathrm{poly}(2^s, B)$ using additional workspace $O(s + \log B)$ on an enlarged catalytic tape $w$ of length $2^s + O(s) + B$ such that for every input $x \in \{0,1\}^n$ (Cook–Li–Mertz–Pyne, Theorem 3.1):

1. $\mathrm{DetComp}_w(1^B, x)$ either returns $L(x)$ and restores the catalytic tape to $w$, or returns $\bot$ and overwrites the catalytic tape with $w' \circ 0^B$ (where $|w'| = 2^s + O(s)$), freeing $B$ catalytic bits.
2. Whenever $\mathrm{DetComp}_w(1^B, x)$ returns $\bot$ with output tape $w' \circ 0^B$, running $\mathrm{DetDecomp}_{w' \circ 0^B}(1^B, x)$ restores the catalytic tape to $w$ in worst-case time $\mathrm{poly}(2^s, B)$.

## Proof sketch

Because $M$'s own configuration graph $G_x$ can have non-reachable predecessor branches whose backward traversal is not time-efficient, Cook–Li–Mertz–Pyne first construct (Theorem 2.7) reversible catalytic subroutines $\mathrm{DetWalk}$ and $\mathrm{DetRev}$ running in worst-case time $\mathrm{poly}(2^s, k)$ via an explicit bijection $\Pi \colon G_x \times \{0,1\} \to G_x \times \{0,1\}$ (implementing an Euler tour of $G_x$) whose orbit from $(\mathrm{start}(m), 0)$ reaches $(\mathrm{halt}(m, L(x)), 0)$ without visiting any other start or halting state. In each of $B$ iterations, $\mathrm{DetComp}$ parses the current non-zero prefix as $m \circ i \circ z$, where $|m| = 2^s$ and $i \in [2^{s+2}]$ is an $(s+2)$-bit counter, and runs $\mathrm{DetWalk}_m(x, i)$: either it reaches $(\mathrm{halt}(m, L(x)), 0)$, outputting $L(x)$ and reversing all prior steps via $\mathrm{DetDecomp}$, or it replaces $(m, i)$ with the reached catalytic tape $m'$, state $v'$ ($s$ bits), and tour bit $a'$ ($1$ bit), saving one bit ($s + 1 < s + 2$) and appending $0$. Because $\Pi$ is a bijection computable in both directions in $\mathrm{poly}(2^s, k)$ time, $\mathrm{DetDecomp}$ undoes all $B$ iterations in reverse order using $\mathrm{DetRev}$ in worst-case time $\mathrm{poly}(2^s, B)$.

## Depends on

- [Polynomial-time catalytic logspace CLP and zero-error polynomial-time catalytic logspace CZPLP](polynomial-time-catalytic-logspace-classes.md)
- [Configuration graph of a space-bounded machine](../../space-and-time-complexity/configuration-graph-of-a-space-bounded-machine.md)

## Sources

- James Cook, Jiatu Li, Ian Mertz and Edward Pyne, "The Structure of Catalytic Space: Capturing Randomness and Time via Compression", STOC (2025), ECCC TR24-106.
