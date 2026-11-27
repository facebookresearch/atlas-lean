# Whether a polynomial bounds the state complexity of a composed operation is undecidable

There is an effective sequence of compositions of intersection and marked concatenation such that no algorithm decides, given an index and a polynomial, whether the polynomial is an upper bound on the deterministic state complexity of that composition.

The *state complexity* $\mathrm{sc}(L)$ of a regular language $L$ is the number of states of its minimal deterministic finite automaton. For an $m$-ary regularity-preserving operation $f$, a function $g:\mathbb N^m\to\mathbb N$ is a *state complexity upper bound* for $f$ if for all regular $L_1,\dots,L_m$ the language $f(L_1,\dots,L_m)$ has a deterministic automaton with at most $g(\mathrm{sc}(L_1),\dots,\mathrm{sc}(L_m))$ states.

The *marked concatenation* of $L_1,\dots,L_n$ is $L_1\sharp L_2\sharp\cdots\sharp L_n$ for a new symbol $\sharp$. A $(\cap,\sharp)$-*composition* over language variables $L_1,\dots,L_n$, $n\ge2$, is an expression $\beta_1\sharp\beta_2\sharp\cdots\sharp\beta_r$, $r\ge2$, where each $\beta_i=K_1\cap\cdots\cap K_{t_i}$ is an intersection of distinct variables. A sequence $(C_i)$ of such compositions is *effectively constructible* if some algorithm outputs $C_i$ on input $i$.

**Theorem (Salomaa, Salomaa and Yu).** A sequence $(C_i)_{i\in\mathbb N}$ of $(\cap,\sharp)$-compositions can be effectively constructed such that it is undecidable, given $i\in\mathbb N$ and a polynomial $P$ with positive integer coefficients in as many variables as $C_i$ has, whether $P$ is a state complexity upper bound for $C_i$.

## Depends on

None.

## Proof depends on

None.

## Expansion

Tight worst-case state complexities are known for every combination of two basic operations, so the undecidability concerns an infinite family of compositions mixing intersection and marked concatenation, with the composition index part of the input.

## Sources

- Arto Salomaa, Kai Salomaa and Taylor J. Smith, "Descriptional Complexity of Finite Automata – Selected Highlights", *Fundamenta Informaticae* 191(3–4), 2024, paper 10876, doi:[10.46298/fi.10876](https://doi.org/10.46298/fi.10876); read in arXiv:2301.03708v4 ([arXiv](https://arxiv.org/abs/2301.03708v4)): the definition of state complexity upper bounds and the undecidability theorem in the section on operational state complexity.
- The theorem is due to Arto Salomaa, Kai Salomaa and Sheng Yu, "Undecidability of state complexity", *International Journal of Computer Mathematics* 90(6), 2013, pp. 1310–1320, doi:[10.1080/00207160.2012.704994](https://doi.org/10.1080/00207160.2012.704994) (cited as recalled in the survey above; not read).
