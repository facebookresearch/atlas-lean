# Gödel numbers of arithmetic terms

The language of arithmetic has the function symbols $0$ (arity $0$), $S$ (arity $1$), $+$ and $\times$ (arity $2$), no relation symbols other than equality, and no free variables; a term or formula with $n$ bound variables in scope uses the variables $x_0, \dots, x_{n-1}$.

Terms with $n$ bound variables in scope are numbered recursively by

$$\ulcorner x_i \urcorner = \langle 1, i \rangle \quad (i < n), \qquad \ulcorner f(t_1, \dots, t_l) \urcorner = \bigl\langle 2, \langle \ulcorner f \urcorner, \mathrm{code}(\ulcorner t_1 \urcorner, \dots, \ulcorner t_l \urcorner) \rangle \bigr\rangle,$$

where $\ulcorner f \urcorner \in \{0, 1, 2, 3\}$ is the number of the function symbol $f$ (for $0, S, +, \times$) and $\mathrm{code}$ is the tuple coding $\mathrm{code}() = 0$, $\mathrm{code}(y_0, \dots, y_l) = \langle \mathrm{code}(y_0, \dots, y_{l-1}), y_l \rangle$.

Here $\langle a, b \rangle$ is the pairing function on $\mathbb{N}$ given by $\langle a, b \rangle = b^2 + a$ if $a < b$ and $\langle a, b \rangle = a^2 + a + b$ otherwise; it is a bijection $\mathbb{N}^2 \to \mathbb{N}$.
