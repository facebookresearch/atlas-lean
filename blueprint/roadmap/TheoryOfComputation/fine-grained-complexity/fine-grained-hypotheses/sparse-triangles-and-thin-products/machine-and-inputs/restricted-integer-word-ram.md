# Restricted integer word RAM

Memory cells are named by all integers, each holding a $W$-bit word, with unwritten cells initially zero. A deterministic program is a finite list of instructions: write 1, add, subtract, multiply (arithmetic modulo $2^W$), indirectly load or store, branch to a fixed instruction on a negative word, accept, or reject. Addresses stored in words are interpreted as signed; statically named cells can be arbitrary integers. Running off the list rejects. Each instruction, including halt, costs one step; supplying input is not charged. A function problem accepts and writes its answer as signed words immediately following the input.

For one-size problems, cell zero contains $n$ and the input follows. For each fixed natural $\kappa$ one program, slope $b\in\mathbb N$, and time bound must serve all $n\ge0$ and inputs with each word's absolute value at most $n^\kappa$ (except the $n$ header), at **every** $W\ge b(\lfloor\log_2 n\rfloor+1)$, taking $\log_2 0$ in this integer convention to be zero. For a rational exponent $r$, the headline bound means there are $T:\mathbb N\to\mathbb N$ and $K\in\mathbb N$ with $T(n)^{\operatorname{den}(r)}\le K n^{\max(\operatorname{num}(r),0)}$ for $n\ge2$, and all allowed runs halt within $T(n)$. In the paper-item formulation, $O(n^a(\log n)^e)$ means a bound $C(n^a(\log n)^e+1)$ on every allowed run (with Lean's totalized real logarithm and power, and $0^0=1$ for the natural logarithm exponent zero). A tilde allows one natural log exponent chosen after $\kappa$; $n^{a+o(1)}$ similarly uses $C(n^{a+\eta(n)}+1)$ with real $\eta(n)\to0$. For two-size instances $(N,D)$ the minimum word width is $b(\lfloor\log_2 N\rfloor+\lfloor\log_2 D\rfloor+1)$.

## Depends on

- [General word-RAM model](../../the-word-ram-model.md)

## Expansion

Implement the small-step machine and exact input/output convention; verify halting and signed overflow behavior and derive the link between the rational-power and real-bound formulations at $n\ge2$, absorbing the two remaining sizes. Compare to the general word-RAM model to move bounds between models.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [machine and one-size bounds](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/EndStatement.lean#L13-L67) and [real bounds](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L3270-L3364).
