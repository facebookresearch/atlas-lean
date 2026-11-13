# The Horner step count is polynomial

Let $cs$ be a list of natural numbers and let
$A : \mathbb{N} \to \mathbb{N}$ be a polynomial function, that is, there is a polynomial $q$ with
natural-number coefficients such that $A(n) = q(n)$ for all $n$. Then $n \mapsto h(n, A(n))$ is a
polynomial function in the same sense, where $h(b, a)$ is the step count of the Horner rounds over
$cs$ with base $b$ from accumulator $a$.
