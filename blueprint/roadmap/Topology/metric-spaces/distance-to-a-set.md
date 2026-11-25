# The distance to a set is 1-Lipschitz and vanishes exactly on its closure

Let $(E,d)$ be a metric space and $C\subseteq E$ nonempty, and put $d(x,C)=\inf_{c\in C}d(x,c)$. Then

$$\lvert d(x,C)-d(y,C)\rvert\le d(x,y)\qquad\text{for all }x,y\in E,$$

so $x\mapsto d(x,C)$ is continuous, and $d(x,C)=0$ if and only if $x$ lies in the closure of $C$. In particular, for a closed set $C$ the function $d(\cdot,C)$ vanishes exactly on $C$.

## Expansion

A proof page must derive the Lipschitz bound from $d(x,c)\le d(x,y)+d(y,c)$ by taking the infimum over $c\in C$ and exchanging $x$ and $y$, and the characterization of the zero set from the definition of the closure through balls.

## Sources

- W. Rudin, *Principles of Mathematical Analysis*, 3rd ed., McGraw-Hill, 1976, Chapter 4, Exercise 20.
