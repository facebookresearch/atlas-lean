# Multi-tape polynomial time equals the canonical class P

The following holds. For every language $L \subseteq \{0, 1\}^*$,

$$L \in \mathsf{P}_{\text{multi-tape}} \iff \chi_L \in \mathsf{P},$$

where $\mathsf{P}_{\text{multi-tape}} = \bigcup_{d \in \mathbb{N}} \mathsf{DTIME}(n^d)$ is the class of languages decided in polynomial time by deterministic multi-tape Turing machines over $\{0, 1\}$; $\chi_L : \{0,1\}^* \to \{\mathrm{true}, \mathrm{false}\}$ is the characteristic function of $L$; and $\mathsf{P}$ is the class of decision problems computable in polynomial time by deterministic multi-stack Turing machines, with the canonical bitstring encodings of inputs and outputs.

## Sources

- M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, Theorem 7.8 and §7.1.
- J. E. Hopcroft, R. Motwani, and J. D. Ullman, *Introduction to Automata Theory, Languages, and Computation*, 3rd ed., Pearson, 2007, §8.4 and §10.1.
