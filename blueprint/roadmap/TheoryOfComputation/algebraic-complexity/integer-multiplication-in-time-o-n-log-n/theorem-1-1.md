# Harvey–van der Hoeven: integer multiplication in time $O(n \log n)$

There is a
multi-stack Turing machine with finite alphabets and a function $t : \mathbb{N} \to \mathbb{N}$
such that, for all natural numbers $x$ and $y$, the machine started on the encoding of the pair
$(x, y)$ (the binary encodings of $x$ and $y$, zipped) halts within $t(\ell)$ steps with the
binary encoding of $xy$, where $\ell$ is the length of the input, and $t(n) = O(n \log n)$ as
$n \to \infty$.

## Sources

- D. Harvey and J. van der Hoeven, "Integer multiplication in time $O(n \log n)$", *Annals of Mathematics* 193 (2021), 563–617. Statement adapted from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, commit e32eb14), with the binary encoding of natural numbers in place of the upstream unary encoding. Problem `annals_integer_multiplication` of the lean-eval benchmark.
