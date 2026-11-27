# Rational LP optimization on a strongly polynomial scalar/address RAM

The machine is a fixed finite scalar/address RAM: separate rational data registers and natural index registers, both indexed by naturals, plus program counter and optional output tag. Its finite instructions manipulate rational constants, copies, $+,-,\times,/$ (division by zero stops without a successor), scalar/address indirect loads and stores, natural address constants and copies and $\pm1$ (decrement truncated), conditional less-than branches on either bank, jumps, and tagged halt. No conversion of scalar data to addresses is present. The program and four natural constants precede all inputs. For every number of rows $m>0$ and variables $d>0$, the initial index registers store $m,d$ and the data registers store $A$ by rows followed by $b$ (followed by the objective for optimization), with others zero. The trace has exactly $k$ successful steps including the halt and all $k+1$ states. There are bounds of the form $c(m+d+1)^e$ on $k$ and $c'(B+1)^{e'}$ on the bit length of **each** stored scalar at every state, where $B$ is the sum of the sizes of the input rationals and the size of a reduced rational is $3+\lfloor\log_2|\mathrm{num}|\rfloor+\lfloor\log_2\mathrm{den}\rfloor$ with the $0$ numerator contribution taken as zero. A sparse Farkas certificate is a vector $y\ge0$ with $A^{\mathsf T}y=0$, $b^{\mathsf T}y<0$ and at most $\operatorname{rank}(A)+1$ nonzero entries.

There exists one such program and bounds for every rational $A,b$ and objective $z\in\mathbb Q^d$ for maximizing $z^{\mathsf T}x$ on $Ax\le b$. Tag 0 returns a sparse Farkas certificate $y$ from register 0. Tag 1 returns primal $x$ from register 0, a nonnegative dual $y$ from register $d$ with $A^{\mathsf T}y=z$, and the common value $z^{\mathsf T}x=b^{\mathsf T}y$ in register $d+m$; the primal is feasible and the value bounds every feasible objective. Tag 2 returns a feasible $x$ from register 0 and $v$ from register $d$ with $Av\le0$ and unit gain $z^{\mathsf T}v=1$.

## Depends on

- Exact scalar/address RAM operational semantics, sparse Farkas certificates and matrix rank over $\mathbb Q$.

## Proof depends on

- [Strongly polynomial feasibility](linear-programming-feasibility/strongly-polynomial-feasibility-on-a-scalar-address-ram.md)
- Reduce optimization and certificate production to feasibility without losing either the instruction or scalar-size bound, and certify outputs in all three cases.

## Expansion

Distinguish the fixed program from an input-specific algorithm. Preserve the positively normalized ray and the sparse infeasibility witness, and prove the correspondence of the source cost model to any standard strongly polynomial model before making a broader status claim.

## Sources

- OpenAI Math, [`strongly_polynomial_optimization`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LinearProgramming.lean#L169-L171) (statement and local definitions).
- Related question: [General strongly polynomial linear programming question](strongly-polynomial-linear-programming.md).
