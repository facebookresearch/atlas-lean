# Completeness of the Boolean certificate verifier

Let $c$ be a circuit over the Boolean
signature with $n$ inputs, $s$ gates and one output, and let $x = (x_0, \dots, x_{n-1})$ be truth
values on which the output of $c$ under the Boolean interpretation is true. Let $b$ be the array
$(x_0, \dots, x_{n-1}, v_0, \dots, v_{s-1})$, where $v_j$ is the value of gate $j$ of $c$ on input
$x$. Then $b$ has length $n + s$ and the Boolean certificate verifier accepts $b$.
