# The s-m-n theorem in polynomial time

Descriptions are codes of multi-tape machines: tables of entries for a machine with a read-only input tape and $k$ work tapes. There is a polynomial-time function $\mathrm{hardwire}(d,p)$ which, given such a code $d$ and a word $p$, outputs a code with the same number of work tapes that on every input $x$ behaves exactly as $d$ on $p\,x$: it halts iff $d$ halts on $p\,x$, with the same output and at most one more step. The output code has $O(|p|+1)$ table entries for each entry of $d$, plus a constant number, so its length is polynomial in $|d|+|p|$.

## Proof sketch

The input tape cannot be rewritten, so the new machine reads $p$ from its states. While $d$'s input head lies on $p$ or on the blank cell before it, the state records the state of $d$ and that head position, the real input head waits on the blank cell before $x$, and the symbol of $p$ is taken from the state; while $d$'s head lies on $x$ or beyond, the state records the state of $d$ and whether the last input-head move was to the left, so that a blank reached by a left move is recognized as the cell before $x$. Moves across the boundary between $p$ and $x$ move the real head; one initial step brings it from the first cell of $x$ to the cell before $x$ when $p$ is nonempty. Each entry of $d$ yields $O(|p|+1)$ entries, in time polynomial in $|d|+|p|$.

## Depends on

- [Parametrized s-m-n theorem](../../computability/exists-computable-code.md)
- [Codes for multi-tape machines](../../turing-machines/universal-machines/codes-for-multi-tape-turing-machines/code.md)
- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Sources

- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
