# Chandra–Kozen–Stockmeyer: AP = PSPACE

Alternating polynomial time equals deterministic polynomial space:

$$
\mathsf{AP}=\mathsf{PSPACE}.
$$

Here $\mathsf{AP}$ is decided by alternating multi-tape machines whose every computation path halts within polynomial time, and $\mathsf{PSPACE}$ by deterministic multi-tape machines halting within polynomial work space, for arbitrary injective binary encodings of instances.

## Proof sketch

$\mathsf{AP}\subseteq\mathsf{PSPACE}$: evaluate the game tree of the alternating machine depth-first, storing only the current path of polynomially many configurations. $\mathsf{PSPACE}\subseteq\mathsf{AP}$: play Savitch's midpoint game on the configuration graph of a polynomial-space machine: the existential player names a midpoint configuration, the universal player chooses which half to continue, and after polynomially many rounds a single transition is checked directly.

## Depends on

- [Alternating time and space classes ATIME, ASPACE, AP, APSPACE and AL](alternating-time-and-space-classes.md)
- [Polynomial space for decision problems](../../time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Alternating polynomial time equals polynomial-length game verification](ap-as-polynomial-length-games.md)
- [Savitch's theorem: NPSPACE = PSPACE](../../savitch.md)
- [Configuration graph of a space-bounded machine](../configuration-graph-of-a-space-bounded-machine.md)

## Sources

- Ashok K. Chandra, Dexter C. Kozen and Larry J. Stockmeyer, "Alternation", Journal of the ACM 28(1), 1981.
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
