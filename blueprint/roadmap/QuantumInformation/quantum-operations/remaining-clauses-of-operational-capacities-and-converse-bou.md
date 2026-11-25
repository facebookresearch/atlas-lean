# Capacity comparison: $Q(\Phi) \le C(\Phi) \le \log_2 \dim X$

For a channel $\Phi$ from a finite-dimensional input space $X$ to a finite-dimensional output space, with the unassisted
classical capacity $C(\Phi)$ and quantum capacity $Q(\Phi)$ defined operationally on the capacity-definitions page,
$Q(\Phi) \le C(\Phi) \le \log_2 \dim X$.

## Proof

**$Q(\Phi) \le C(\Phi)$.** Let $R > 0$ be an achievable rate for quantum communication, let $\varepsilon > 0$, and take $n$
large enough that there are channels $\Xi_E$ and $\Xi_D$ with $\lVert \Psi - \mathrm{id} \rVert_\diamond < \varepsilon$ for
$\Psi = \Xi_D \Phi^{\otimes n} \Xi_E$ on $m = \lfloor Rn \rfloor$ qubits. Encode a message $a \in \{0,1\}^m$ as the input state
$\Xi_E(\lvert a \rangle\langle a \rvert)$, and decode by applying $\Xi_D$ and measuring in the computational basis. With
$\rho_a = \Psi(\lvert a \rangle\langle a \rvert)$, the two-outcome measurement $\{\lvert a \rangle\langle a \rvert, I - \lvert a \rangle\langle a \rvert\}$ gives
$2(1 - \langle a \rvert \rho_a \lvert a \rangle) \le \lVert \rho_a - \lvert a \rangle\langle a \rvert \rVert_1 \le \lVert \Psi - \mathrm{id} \rVert_\diamond < \varepsilon$,
so every message is decoded with error probability below $\varepsilon/2$. Hence $R$ is achievable for classical
communication. Rate $0$ is achievable for both, so $Q(\Phi) \le C(\Phi)$.

**$C(\Phi) \le \log_2 \dim X$.** Let $R > 0$ be an achievable rate for classical communication, let $\varepsilon \in (0, 1)$,
and take $n$ large enough that $M = 2^{\lfloor Rn \rfloor}$ messages are encoded as states $\sigma_a$ on $X^{\otimes n}$ and
decoded by a measurement $\{\mu_b\}$ on the output of $\Phi^{\otimes n}$ with every error probability below $\varepsilon$.
The operators $\nu_b = (\Phi^{\otimes n})^*(\mu_b)$ form a measurement on $X^{\otimes n}$, and $\sigma_a \le I$, so

$$M (1 - \varepsilon) < \sum_a \langle \nu_a, \sigma_a \rangle \le \sum_a \operatorname{Tr} \nu_a \le \sum_b \operatorname{Tr} \nu_b = \operatorname{Tr} I_{X^{\otimes n}} = (\dim X)^n .$$

Thus $\lfloor Rn \rfloor < n \log_2 \dim X + \log_2 \tfrac{1}{1 - \varepsilon}$ for all large $n$. Dividing by $n$ and letting
$n \to \infty$ gives $R \le \log_2 \dim X$.

## Depends on

- [Operational classical and quantum capacities](../quantum-shannon-theory/remaining-clauses-of-operational-capacity-definitions.md)

## Related topics

- [Converse bounds for the capacities of a quantum channel](converse-bounds-for-the-capacities-of-a-quantum-channel.md)

## Sources

- J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018 (author copy), Definitions 8.1–8.3
  and 8.42 (the operational definitions; logarithms to base 2), with (8.3)–(8.6) (restriction to classical encodings and
  decodings, and the equivalence of $\varepsilon$-approximation of the dephasing channel with per-message error below
  $\varepsilon/2$). The two inequalities are derived above from these definitions. <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>
