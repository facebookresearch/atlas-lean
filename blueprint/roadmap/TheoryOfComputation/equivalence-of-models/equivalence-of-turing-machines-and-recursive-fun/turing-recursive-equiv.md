# Recursive functions are the Turing-computable functions

A function
$f : \mathbb{N} \to \mathbb{N}$ is computable, that is, total recursive, if and only if some finite
multi-stack Turing machine computes it on binary representations: there are a machine with
finitely many stacks, internal states and program labels and bijections from its input and output
stack alphabets to $\{0, 1\}$ such that, for every $n \in \mathbb{N}$, the machine started in its
initial state with the binary representation of $n$ (least significant bit first, with $0$
written as the empty word) on its input stack and all other stacks empty halts with the binary
representation of $f(n)$ on its output stack, all other stacks empty and its internal state back
at the initial state.

## Sources

- A. M. Turing, *On Computable Numbers* (1936); S. C. Kleene, *General recursive functions of natural numbers* (1936). Knill, *Some fundamental theorems in mathematics*, §23. Via leanprover/lean-eval@38361be, problem `turing_recursive_equiv`.
