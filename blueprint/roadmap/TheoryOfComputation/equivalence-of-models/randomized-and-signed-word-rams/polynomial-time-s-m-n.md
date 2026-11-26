# The s-m-n theorem in polynomial time

There is a polynomial-time function $\mathrm{hardwire}(d,p)$ which, given the description $d$ of a multi-tape Turing machine and a word $p$, outputs the description of a machine that on every input $x$ behaves exactly as $d$ on $p\,x$ (same output, running time increased by $O(|p|)$). The output description has length $|d|+O(|p|)$.

## Proof sketch

Prefix $d$ with a writing phase of $|p|$ states that prints $p$ before the input (shifting the input or reading $p$ from the states), then jump to the initial state of $d$; the construction is a linear-time rewriting of the transition table.

## Depends on

- [Parametrized s-m-n theorem](../../computability/exists-computable-code.md)
- [Codes for multi-tape machines](../../turing-machines/universal-machines/codes-for-multi-tape-turing-machines/code.md)
- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Sources

- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
