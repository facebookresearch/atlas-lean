# Polynomial-time computability under given encodings

Let $e_\alpha$ encode $\alpha$ as
words over an alphabet $\Gamma_\alpha$ and $e_\beta$ encode $\beta$ as words over $\Gamma_\beta$. A
function $f : \alpha \to \beta$ is polynomial-time computable with respect to $e_\alpha$ and
$e_\beta$ when there are a multi-stack Turing machine with finitely many stacks, function labels
and internal states and a finite input stack alphabet, identifications of its input and output
stack alphabets with $\Gamma_\alpha$ and $\Gamma_\beta$, and a polynomial $p$ with natural-number
coefficients, such that for every $a \in \alpha$ the machine, started at its main function in its
initial state with $e_\alpha(a)$ on its input stack and every other stack empty, halts within
$p(n)$ steps, where $n$ is the length of $e_\alpha(a)$, with $e_\beta(f(a))$ on its output stack,
every other stack empty and its internal state equal to its initial state.

## Sources

- inlined from FormalConjectures (absent from Mathlib).
