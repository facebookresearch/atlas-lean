# Harvey–van der Hoeven: integer multiplication in time $O(n \log n)$

There is a
multi-stack Turing machine with finite alphabets and a function $t : \mathbb{N} \to \mathbb{N}$
such that, for all natural numbers $x$ and $y$, the machine started on the encoding of the pair
$(x, y)$ (the binary encodings of $x$ and $y$, zipped) halts within $t(\ell)$ steps with the
binary encoding of $xy$, where $\ell$ is the length of the input, and $t(n) = O(n \log n)$ as
$n \to \infty$.

## Sources

- D. Harvey and J. van der Hoeven, `Integer multiplication in time O(n log n)`, Annals of Math, 193 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-193-2-IntegerMultiplication.lean Via leanprover/lean-eval@38361be, problem `annals_integer_multiplication`.
