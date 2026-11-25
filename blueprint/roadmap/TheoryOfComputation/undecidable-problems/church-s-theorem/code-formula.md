# Gödel numbers of arithmetic formulas

The language of arithmetic has the function symbols $0$ (arity $0$), $S$ (arity $1$), $+$ and $\times$ (arity $2$), no relation symbols other than equality, and no free variables; a term or formula with $n$ bound variables in scope uses the variables $x_0, \dots, x_{n-1}$.

Formulas built from $\bot$, equations $t_1 = t_2$, implication and universal quantification, with $n$ bound variables in scope, are numbered recursively by

$$\ulcorner \bot \urcorner = 0, \qquad \ulcorner t_1 = t_2 \urcorner = \bigl\langle 1, \langle \ulcorner t_1 \urcorner, \ulcorner t_2 \urcorner \rangle \bigr\rangle,$$

$$\ulcorner \varphi \to \psi \urcorner = \bigl\langle 2, \langle \ulcorner \varphi \urcorner, \ulcorner \psi \urcorner \rangle \bigr\rangle, \qquad \ulcorner \forall x_n\, \varphi \urcorner = \langle 3, \ulcorner \varphi \urcorner \rangle,$$

where in the last case $\varphi$ has $n + 1$ bound variables in scope, and terms are numbered by $\ulcorner x_i \urcorner = \langle 1, i \rangle$ and $\ulcorner f(t_1, \dots, t_l) \urcorner = \langle 2, \langle \ulcorner f \urcorner, \mathrm{code}(\ulcorner t_1 \urcorner, \dots, \ulcorner t_l \urcorner) \rangle \rangle$.

Here $\langle a, b \rangle$ is the pairing function on $\mathbb{N}$ given by $\langle a, b \rangle = b^2 + a$ if $a < b$ and $\langle a, b \rangle = a^2 + a + b$ otherwise; it is a bijection $\mathbb{N}^2 \to \mathbb{N}$.
