# The threshold theorem

There is a threshold error rate $p_T > 0$ with the following property. Suppose a
[local stochastic error model](local-stochastic-error-model.md) with bounds $p_i \le p < p_T$ acts on circuits. Then for
every ideal quantum circuit $C$ and every $\varepsilon > 0$ there is a fault-tolerant circuit $C'$ which, subject to the
error model, produces an output whose statistical distance from the output of $C$ is at most $\varepsilon$, and whose
numbers of qubits and of time steps are at most $\operatorname{polylog}(|C|/\varepsilon)$ times those of $C$, where $|C|$ is
the number of [locations](locations-of-a-quantum-circuit.md) of $C$.

The proof concatenates an $[[n, 1, 2t + 1]]$ code $L$ times: each level maps a local stochastic model with bound $p$ to one
with bound at most $A p^{t+1}$, so the level-$L$ bound is at most $p_T (p/p_T)^{(t+1)^L}$ with $p_T = A^{-1/t}$, and
$L = O(\log \log (|C|/\varepsilon))$ levels suffice. This $p_T$ is a sufficient threshold coming from the recursion, not
the critical error rate. A numerical value needs a specific noise model and gadgets: for independent stochastic faults
(each location faulty independently with probability at most $\varepsilon$, the faulty operation chosen adversarially),
Aliferis, Gottesman and Preskill's gadgets for Steane's code with a count of malignant sets of faults give
$\varepsilon_0 \ge 2.73 \times 10^{-5}$. Aharonov and Ben-Or, and Knill, Laflamme and Zurek, proved earlier threshold theorems for
probabilistic and quasi-independent noise.

## Expansion

A good expansion adds pages for the remaining definitions and steps of Gottesman's proof: fault-tolerant measurement,
preparation, gate and error-correction gadgets (Definitions 1–5); the fault-tolerant simulation of a circuit and extended
rectangles, good and correct (Definitions 6–10); "good implies correct" (Theorem 6) and the reduction of a circuit of good
extended rectangles to the ideal circuit (Theorems 7–8); level reduction for local stochastic noise (Theorem 9); and
fault-tolerant gadgets for a universal gate set for one distance-3 code, for instance the
[transversal Clifford gates of Steane's code](../fault-tolerant-gates/steane-code-has-transversal-clifford-gates.md) with
[magic-state injection](../fault-tolerant-gates/magic-state-injection.md) of a fault-tolerantly prepared magic state.

## Depends on

- [Local stochastic error model](local-stochastic-error-model.md)
- [Locations of a quantum circuit](locations-of-a-quantum-circuit.md)
- [An event's probabilities differ by at most the total variation](../../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/abs-sub-le-total-variation-dist.md)

## Proof depends on

- [Error recursion for concatenated fault-tolerant codes](../error-recursion-for-concatenated-fault-tolerant-codes.md)
- [Concatenated quantum code](concatenated-quantum-code.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 5, Definitions 6–12 and Theorems 6–10, equations (84)–(89).
- P. Aliferis, D. Gottesman and J. Preskill, *Quantum accuracy threshold for concatenated distance-3 codes*, Quantum Inf. Comput. 6 (2006), 97–165, arXiv:quant-ph/0504218, Theorems 1 and 3 and equation (42) (independent stochastic noise).
- D. Aharonov and M. Ben-Or, *Fault-tolerant quantum computation with constant error rate*, SIAM J. Comput. 38 (2008), 1207–1282, arXiv:quant-ph/9906129, Section 7, Theorem 10, and Section 8.4, Theorem 11.
- E. Knill, R. Laflamme and W. H. Zurek, *Resilient quantum computation: error models and thresholds*, Proc. R. Soc. Lond. A 454 (1998), 365–384, arXiv:quant-ph/9702058, Abstract.
