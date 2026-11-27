# Clique emitter: one clause

Let $C$ be a clause, $\varphi$ a CNF formula, $R$ a token list
that is empty or starts with a clause marker, $o$ a list of bits, $c, n, B \in \mathbb{N}$ and $v$
a Boolean. Write $T_C$ for the tokens of $C$ as they lie on the token stack (a clause marker,
then the literals last-first) and $D_\psi$ for the tokens of the items of a formula $\psi$. If
$|T_C| + |D_\varphi| \le B$, then for some flag $v'$ the emitter machine goes in at most
$|T_C| \cdot (7B + 7)$ steps from label start with flag $v$ and the state with token stack $T_C$
followed by $R$, output $o$, walked stack $D_\varphi$, clause count $c$, occurrence count $n$ and
all other stacks empty, to label start with flag $v'$ and the state with token stack $R$, output
the rows pushed for the literals of $C$ walked above a clause marker and the items of $\varphi$,
followed by $o$, walked stack $D_{C \varphi}$ for the formula $C\varphi$ with first clause $C$,
clause count $c + 1$, occurrence count $n + |C|$ and all other stacks empty.
