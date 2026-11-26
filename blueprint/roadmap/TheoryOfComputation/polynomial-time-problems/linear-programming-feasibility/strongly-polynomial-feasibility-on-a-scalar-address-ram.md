# Rational LP feasibility on a strongly polynomial scalar/address RAM

The machine is a fixed finite scalar/address RAM: separate rational data registers and natural index registers, both indexed by naturals, plus program counter and optional output tag. Its finite instructions manipulate rational constants, copies, $+,-,\times,/$ (division by zero stops without a successor), scalar/address indirect loads and stores, natural address constants and copies and $\pm1$ (decrement truncated), conditional less-than branches on either bank, jumps, and tagged halt. No conversion of scalar data to addresses is present. The program and four natural constants precede all inputs. For every number of rows $m>0$ and variables $d>0$, the initial index registers store $m,d$ and the data registers store $A$ by rows followed by $b$ (followed by the objective for optimization), with others zero. The trace has exactly $k$ successful steps including the halt and all $k+1$ states. There are bounds of the form $c(m+d+1)^e$ on $k$ and $c'(B+1)^{e'}$ on the bit length of **each** stored scalar at every state, where $B$ is the sum of the sizes of the input rationals and the size of a reduced rational is $3+\lfloor\log_2|\mathrm{num}|\rfloor+\lfloor\log_2\mathrm{den}\rfloor$ with the $0$ numerator contribution taken as zero. A sparse Farkas certificate is a vector $y\ge0$ with $A^{\mathsf T}y=0$, $b^{\mathsf T}y<0$ and at most $\operatorname{rank}(A)+1$ nonzero entries.

There exists one such program and bounds for every $A\in\mathbb Q^{m\times d}$, $b\in\mathbb Q^m$ which finishes either with tag 0 and a feasible $x$ in registers $0,\ldots,d-1$ satisfying $Ax\le b$, or with tag 1 and a sparse Farkas certificate in registers $0,\ldots,m-1$. This is a search/certificate assertion, not merely a language decision problem.

## Depends on

- Exact scalar/address RAM operational semantics, sparse Farkas certificates and matrix rank over $\mathbb Q$.

## Proof depends on

- Correctness and operation count for the exact feasibility algorithm; reduced scalar bit-length bound independent of the chosen input values except through total input length.

## Expansion

Specify the machine and output interface and compare with any existing complexity model before calling this a resolution of the general question. Keep the certificate and both bounds in the same theorem.

## Sources

- OpenAI Math, [`strongly_polynomial_feasibility`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LinearProgramming.lean#L166-L168) (statement and local definitions).
- Related question: [General strongly polynomial linear programming question](../strongly-polynomial-linear-programming.md).
