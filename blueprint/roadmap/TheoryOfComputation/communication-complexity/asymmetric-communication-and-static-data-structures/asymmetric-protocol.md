# Asymmetric $[a, b]$-protocols

For $f : X \times Y \to \{0, 1\}$, an *$[a, b]$-protocol* is a (deterministic or public-coin randomized) two-party communication protocol in which, on every input, Alice (holding $x \in X$) sends at most $a$ bits in total and Bob (holding $y \in Y$) sends at most $b$ bits in total. A rectangle $A \times B$ with $A \subseteq X$, $B \subseteq Y$ is a *$1$-rectangle* if $f \equiv 1$ on it.

## Depends on

- [Deterministic two-party protocol](../deterministic-communication-protocols/protocol.md)
- [Public-coin randomized protocol](../randomized-communication-protocols/public-coin-protocol.md)

## Sources

- Peter Bro Miltersen, Noam Nisan, Shmuel Safra, Avi Wigderson, "On Data Structures and Asymmetric Communication Complexity", Journal of Computer and System Sciences 57(1) (1998).
