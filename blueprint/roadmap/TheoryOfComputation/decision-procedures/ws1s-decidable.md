# Decidability of WS1S

Formulas of WS1S (weak monadic second-order logic of one successor) are built from terms $x_i$ (first-order variables, $i \in \mathbb{N}$), $0$ and $t + 1$, atoms $t_1 = t_2$, $t_1 < t_2$ and $t \in X_i$ (second-order variables, $i \in \mathbb{N}$), $\bot$, $\to$, first-order quantification $\forall x$ over $\mathbb{N}$ and second-order quantification $\forall X$ over finite subsets of $\mathbb{N}$, with variables in de Bruijn style. A formula $\varphi$ is valid if it holds under every assignment $v : \mathbb{N} \to \mathbb{N}$ of first-order variables and every assignment $V$ of finite subsets of $\mathbb{N}$ to second-order variables. Formulas are coded by natural numbers $\ulcorner \varphi \urcorner$ through the pairing function $\pi(a, b) = b^2 + a$ if $a < b$ and $\pi(a, b) = a^2 + a + b$ otherwise, applied to a distinct tag for each constructor and the codes of its arguments; for instance $\bot$ has code $\pi(3, 0) = 12$.

Statement: the set

$$\{\, n \in \mathbb{N} : n = \ulcorner \varphi \urcorner \text{ for some valid WS1S formula } \varphi \,\}$$

is computable.

## Sources

- J. R. Büchi, "Weak second-order arithmetic and finite automata", Zeitschrift für mathematische Logik und Grundlagen der Mathematik 6 (1960), 66-92; see also W. Thomas, "Languages, Automata, and Logic", in Handbook of Formal Languages, Vol. 3, Springer, 1997, §7.
