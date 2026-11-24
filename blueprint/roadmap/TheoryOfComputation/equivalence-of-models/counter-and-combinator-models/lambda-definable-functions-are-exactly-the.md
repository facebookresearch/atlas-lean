# λ-definable functions are exactly the partial recursive functions

Write $\underline{n} = \lambda f x.\, f^n x$ for the Church numerals. A partial function $f : \mathbb{N}^k \rightharpoonup \mathbb{N}$ is *λ-definable* if there is a closed λ-term $F$ such that for all
$(x_1, \dots, x_k) \in \mathbb{N}^k$ and $y \in \mathbb{N}$:

- if $f(x_1, \dots, x_k) = y$, then $F\, \underline{x_1} \cdots \underline{x_k} =_\beta \underline{y}$;
- if $f(x_1, \dots, x_k)$ is undefined, then $F\, \underline{x_1} \cdots \underline{x_k}$ has no $\beta$-normal form.

**Theorem.** A partial function on natural numbers is partial recursive if and only if it is λ-definable.

Every partial recursive $f$ can be written as $g \circ (\mu_n h)$ with $g$ and $h$ primitive recursive, and every primitive recursive function and every total
recursive function is λ-definable; matching undefinedness with the absence of a normal form needs additional care. Conversely, λ-terms can be
coded as numbers and normal-order $\beta$-reduction, which reaches the normal form whenever one exists, can be simulated by a register machine, so
every λ-definable function is register-machine computable, hence partial recursive.

## Depends on

- [Turing computable equals recursive](../equivalence-of-turing-machines-and-recursive-fun/computable-iff-nonempty-tm2-computable.md)

## Sources

- A. M. Pitts, *Computation Theory*, lecture notes, University of Cambridge, 2019–20, <https://www.cl.cam.ac.uk/teaching/1920/CompTheory/comt-notes.pdf>: the definition of λ-definable partial functions, the theorem "computable = λ-definable" and the slides "Recursive implies λ-definable" and "Computable = λ-definable" (notes pages 118–140), with the normal-order reduction fact.
- J. R. Hindley and J. P. Seldin, *Lambda-Calculus and Combinators: An Introduction*, Cambridge University Press, 2008, Chapter 4 (not opened; cited by Pitts for the partial case).
- H. P. Barendregt, *The Lambda Calculus: Its Syntax and Semantics*, revised ed., North-Holland, 1984 (not opened).
