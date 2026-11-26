# Richness lemma

Call $f : X \times Y \to \{0,1\}$ *$(u, v)$-rich* if at least $v$ columns $y \in Y$ each contain at least $u$ entries $x$ with $f(x, y) = 1$. If $f$ is $(u, v)$-rich and has a deterministic $[a, b]$-protocol, then $f$ contains a $1$-rectangle $A \times B$ with $|A| \ge u / 2^{a}$ and $|B| \ge v / 2^{a + b}$.

## Proof sketch

Induct on the protocol tree. If Alice speaks, she partitions $X$ into two parts, and at least one part keeps $(u/2, v/2)$-richness while costing one bit of $a$; if Bob speaks, he partitions $Y$ and one part keeps $(u, v/2)$-richness at the cost of one bit of $b$. At a leaf the rectangle is monochromatic and rich, hence a $1$-rectangle of the stated dimensions.

## Depends on

- [Asymmetric $[a, b]$-protocols](asymmetric-protocol.md)

## Sources

- Peter Bro Miltersen, Noam Nisan, Shmuel Safra, Avi Wigderson, "On Data Structures and Asymmetric Communication Complexity", Journal of Computer and System Sciences 57(1) (1998).
