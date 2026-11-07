# Base change of a homogeneous element along zero evaluation

Let $K$ be a field,
$R = K[x_1, \dots, x_n]$, and let $F$ be a multigraded free $R$-module with basis
$(b_j)_{j \in \iota}$, where each $b_j$ is homogeneous of degree $d_j \in \mathbb{Z}^n$.
Make $K$ an $R$-algebra through the zero evaluation $R \to K$, which sends every
variable to $0$. If $x \in F$ is homogeneous of degree $\alpha \in \mathbb{Z}^n$, then
$1 \otimes x \in K \otimes_R F$ lies in the $K$-linear span of the vectors $1 \otimes b_j$
with $d_j = \alpha$.

## Sources

- Benjamin Braun and Brian Davis, "Antichain Simplices," Journal of Integer Sequences 23 (2020), lines 862–867, `https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`, which split a graded free resolution and take the degree-`α` component after tensoring with `K`.
