# Existence of multigraded base-change data

Let $K$ be a field, let
$R = K[x_1, \dots, x_n]$, let $M$ be a multigraded polynomial module over $R$, and let $F$ be a
multigraded free resolution of $M$ whose term $F_i$ has the homogeneous basis
$(e_j)_{j \in \iota_i}$, where every index set $\iota_i$ is finite. Write $K \otimes_R F$ for the
chain complex of $K$-vector spaces obtained from $F$ by extending scalars along the evaluation
$R \to K$ at $x = 0$, and for $\alpha \in \mathbb{Z}^n$ call the $K$-span of the vectors
$1 \otimes e_j$ with $e_j$ of degree $\alpha$ the degree-$\alpha$ piece of $(K \otimes_R F)_i$.
Then multigraded base-change data for $F$ exist: each $(K \otimes_R F)_i$ is the direct sum of
its degree-$\alpha$ pieces over $\alpha \in \mathbb{Z}^n$, the differentials of $K \otimes_R F$
preserve these pieces, and for every $\alpha$ there is a chain complex $C^\alpha$ of $K$-vector
spaces with finite-dimensional homology in every degree, together with a chain map
$C^\alpha \to K \otimes_R F$ that is injective in each homological degree $i$ with image the
degree-$\alpha$ piece of $(K \otimes_R F)_i$.

## Sources

- Benjamin Braun and Brian Davis, "Antichain Simplices," Journal of Integer Sequences 23 (2020), lines 862–867, `https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`.
