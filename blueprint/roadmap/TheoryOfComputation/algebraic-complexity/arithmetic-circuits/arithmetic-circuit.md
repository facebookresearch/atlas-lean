# Arithmetic circuit

An arithmetic circuit over $F$ with inputs indexed by $A$ and
outputs indexed by $B$ consists of a size $s \in \mathbb{N}$, a gate $g_i$ for each $i < s$, and
an output operand for each $b \in B$. Each gate $g_i$ is an addition, subtraction or
multiplication of two operands, each a constant in $F$, an input $a \in A$ or an earlier gate
$g_j$ with $j < i$; an output operand is a constant in $F$, an input or any gate $g_j$ with
$j < s$.

Constants and inputs are free; each gate counts as one scalar operation.
