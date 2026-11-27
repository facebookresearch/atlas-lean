# The threshold theorem from fault-tolerant gadgets

Fix an $[[n, 1, 2t + 1]]$ stabilizer code with $t \ge 1$ and a finite set of location types (preparations, measurements, waits and gates
of a gate set) such that every type has a fault-tolerant gadget for the code ([preparation](fault-tolerant-preparation-gadget.md),
[measurement](fault-tolerant-measurement-gadget.md), [gate](fault-tolerant-gate-gadget.md)), there is a
[fault-tolerant EC gadget](fault-tolerant-error-correction-gadget.md), and all these gadgets use only location types of the
set. Let $A$ be the largest number of sets of $t + 1$ locations in one
[extended rectangle](fault-tolerant-simulation-and-extended-rectangles.md) and $p_T = A^{-1/t}$. Then for
a [local stochastic error model](local-stochastic-error-model.md) with $p_i \le p < p_T$, every circuit $C$ over the
location types and every $\varepsilon > 0$, the $L$-fold concatenated simulation $C' = C^{(L)}$ (each
$C^{(j)}$ the fault-tolerant simulation of $C^{(j-1)}$, $C^{(0)} = C$) with $L = 0$ if $|C| p \le \varepsilon$ (this
includes $p = 0$ and the empty circuit) and otherwise
$L = \lceil \log_{t+1} [\log(\varepsilon / (|C| p_T)) / \log(p / p_T)] \rceil$, which is then at least $1$ since
$\varepsilon < |C| p < |C| p_T$, produces an output within statistical
distance $\varepsilon$ of that of $C$, and its numbers of qubits and time steps are at most $G^L$, a polylogarithmic
function of $|C| / \varepsilon$, times those of $C$, where $G$ bounds the qubits and time steps of a gadget. The proof
applies [level reduction](level-reduction.md) $L$ times: the bounds satisfy $p^{(j)} \le A (p^{(j-1)})^{t+1}$, so
$p^{(L)} / p_T \le (p / p_T)^{(t+1)^L}$, and $L$ is the least nonnegative integer with
$|C| p_T (p / p_T)^{(t+1)^L} \le \varepsilon$ (Gottesman's equation (87)); his closed form (88) alone can be negative, for
instance $t = 1$, $p = p_T/16$ and $\varepsilon = |C| p_T / 2$ give $\lceil \log_2 (1/4) \rceil = -2$.

## Depends on

- [Fault-tolerant simulation of a circuit and extended rectangles](fault-tolerant-simulation-and-extended-rectangles.md)
- [Local stochastic error model](local-stochastic-error-model.md)
- [Concatenated quantum code](concatenated-quantum-code.md)
- [Fault-tolerant preparation gadget](fault-tolerant-preparation-gadget.md)
- [Fault-tolerant measurement gadget](fault-tolerant-measurement-gadget.md)
- [Fault-tolerant gate gadget](fault-tolerant-gate-gadget.md)
- [Fault-tolerant error-correction gadget](fault-tolerant-error-correction-gadget.md)
- [$[[n, k, d]]$ quantum code](../distance-of-a-quantum-code/n-k-d-quantum-code.md)

## Proof depends on

- [Level reduction](level-reduction.md)
- [Error recursion for concatenated fault-tolerant codes](../error-recursion-for-concatenated-fault-tolerant-codes.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 5.2, Theorem 10 and its proof, equations (86)–(89).
- P. Aliferis, D. Gottesman and J. Preskill, *Quantum accuracy threshold for concatenated distance-3 codes*, Quantum Inf. Comput. 6 (2006), 97–165, arXiv:quant-ph/0504218.
