# Acceptance probability of the BLR test

For $f : \{-1, 1\}^n \to \mathbb{R}$, the acceptance probability of the
Blum–Luby–Rubinfeld test is

$$\Pr_{x, y}\big[f(x)\, f(y) = f(x y)\big],$$

with $x, y$ uniform and independent and $x y$ the coordinatewise product. For a function
$F : \mathbb{F}_2^n \to \mathbb{F}_2$ encoded by $f = (-1)^F$, this is the probability that the
test "query $F$ at $x$, $y$ and $x + y$ and accept if $F(x) + F(y) = F(x + y)$" accepts.

## Sources

- Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Section 1.6.
