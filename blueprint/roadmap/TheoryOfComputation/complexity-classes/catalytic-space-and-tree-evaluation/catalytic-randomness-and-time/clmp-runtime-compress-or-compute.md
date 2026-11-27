# Cook–Li–Mertz–Pyne compress-or-compute: a long-running catalytic computation compresses its own tape

Let $M$ be a $\mathsf{CL}$ machine with work tape of $s=d\log n$ cells (including state and head information) and catalytic tape of length $c$, and fix an input $x$. Append a block of $s+1$ catalytic bits interpreted as an integer $i\in[2^{s+1}]$. There is a catalytic procedure with $O(\log n)$ work space and running time $\mathrm{poly}(n)$ that, on catalytic content $(\tau,i)$, either

1. observes that $M$ halts from $\langle\tau,0^s\rangle$ within $2^{s+1}$ steps, outputs $M(x)$ and leaves $(\tau,i)$ unchanged; or
2. replaces $(\tau,i)$ by $(\pi,u,0)$, where $\langle\pi,u\rangle$ is the configuration of $M$ after $i$ steps from $\langle\tau,0^s\rangle$; this frees one catalytic bit, and $(\tau,i)$ is recoverable from $(\pi,u)$ by moving backward from $\langle\pi,u\rangle$ until the unique start configuration of the form $\langle\tau',0^s\rangle$ is met, counting the steps.

## Proof sketch

Running $M$ forward with a step counter decides which case applies, and in case 2 the configuration at time $i$ overwrites $(\tau,i)$, which has one more bit than $(\pi,u)$. Validity implies that the start configuration is the only configuration of the form $\langle\tau',0^s\rangle$ whose forward path passes through $\langle\pi,u\rangle$ (two such would have to halt with the same restored content), so a reversible traversal of the predecessor tree of $\langle\pi,u\rangle$ finds it and recovers $i$ as its distance.

## Depends on

- [Polynomial-time catalytic logspace CLP and zero-error polynomial-time catalytic logspace CZPLP](polynomial-time-catalytic-logspace-classes.md)
- [Configuration graph of a space-bounded machine](../../space-and-time-complexity/configuration-graph-of-a-space-bounded-machine.md)

## Sources

- James Cook, Jiatu Li, Ian Mertz and Edward Pyne, "The Structure of Catalytic Space: Capturing Randomness and Time via Compression", STOC (2025), ECCC TR24-106.
