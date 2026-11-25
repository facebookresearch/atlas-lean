# Functions computable in polynomial time by multi-stack machines are closed under composition

Let $\alpha$, $\beta$, $\gamma$ be types encoded as words over alphabets by $e_\alpha$,
$e_\beta$, $e_\gamma$. If $f : \alpha \to \beta$ is computable in polynomial time by a finite
multi-stack Turing machine with respect to $e_\alpha$ and $e_\beta$, and $g : \beta \to \gamma$
is computable in polynomial time by a finite multi-stack Turing machine with respect to $e_\beta$
and $e_\gamma$, then some finite multi-stack Turing machine computes $g \circ f$ in polynomial
time with respect to $e_\alpha$ and $e_\gamma$ (each computation coming with bijections between
the input and output stack alphabets and the encoding alphabets, and a polynomial time bound).

## Sources

- Mathlib pull request #44441, https://github.com/leanprover-community/mathlib4/pull/44441, which states the same result as `TM2ComputableInPolyTime.comp`; its description says that the code, the testing and the description were prepared with the help of an AI coding assistant (Codex).
