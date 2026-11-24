# Correctness of the assembled formula

Let $M$ be a finite multi-stack Turing machine with
encoding data $E$, let $x$ and $Y$ be lists of input symbols of $M$, let $\mathit{acc}$ be an
output symbol of $M$, and let $m, T \in \mathbb{N}$. Suppose that $|x| \le m$ and that
$\mathit{acc}$ is one of the effective symbols of the output stack under $E$. Then the formula
$\Phi(x, Y, \mathit{acc}, m, T)$ emitted by the host is satisfiable if and only if there is a list
$y$ of input symbols, all belonging to $Y$, such that the concatenation $xy$ has length at most
$m$ and the idle-extended run of $M$ from the initial configuration on input $xy$ is, after $T$
steps, an accepting configuration for $\mathit{acc}$: halted, in the initial internal state, with
$\mathit{acc}$ on top of the output stack.

The proof carries the soundness and completeness of the five families through the
concatenation.
