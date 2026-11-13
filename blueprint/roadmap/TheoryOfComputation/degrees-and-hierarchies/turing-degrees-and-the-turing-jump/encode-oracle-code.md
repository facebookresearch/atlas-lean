# The Gödel numbering of oracle codes

Write $\langle a, b \rangle$ for the pairing of
natural numbers equal to $b^2 + a$ if $a < b$ and to $a^2 + a + b$ otherwise. The code number
$\ulcorner c \urcorner$ of an oracle code $c$ is defined by recursion on $c$: $\mathsf{zero}$,
$\mathsf{succ}$, $\mathsf{left}$, $\mathsf{right}$ and $\mathsf{oracle}$ have code numbers
$\langle 0, 0 \rangle$, $\langle 1, 0 \rangle$, $\langle 2, 0 \rangle$, $\langle 3, 0 \rangle$ and
$\langle 8, 0 \rangle$; $\mathsf{pair}(a, b)$, $\mathsf{comp}(a, b)$ and $\mathsf{prec}(a, b)$
have code numbers $\langle 4, \langle \ulcorner a \urcorner, \ulcorner b \urcorner \rangle \rangle$,
$\langle 5, \langle \ulcorner a \urcorner, \ulcorner b \urcorner \rangle \rangle$ and
$\langle 6, \langle \ulcorner a \urcorner, \ulcorner b \urcorner \rangle \rangle$; and
$\mathsf{rfind}(a)$ has code number $\langle 7, \ulcorner a \urcorner \rangle$.

This numbering is an injection into $\mathbb{N}$.

## Sources

- Rogers, *Theory of Recursive Functions and Effective Computability*, §1.6 (Gödel numberings).
