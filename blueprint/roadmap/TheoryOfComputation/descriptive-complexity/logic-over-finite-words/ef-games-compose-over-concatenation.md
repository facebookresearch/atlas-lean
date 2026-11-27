# EF games compose over concatenations of words

If Duplicator wins the $n$-round Ehrenfeucht–Fraïssé game on words $u_1, v_1$ and on $u_2, v_2$ (from given pebbled positions), then she wins it on $u_1 u_2$ and $v_1 v_2$ from the combined positions. Consequently the rank-$n$ type of a concatenation is determined by the rank-$n$ types of its factors; since there are finitely many rank-$n$ types, $\equiv_n$ is a congruence of finite index on $\Sigma^*$.

## Proof sketch

Duplicator answers each Spoiler move inside the factor where it was made using that factor's strategy; since every position of the first factor precedes every position of the second, order relations across factors are preserved automatically.

## Depends on

- [Words as finite structures; FO[<] and MSO definability](words-as-finite-structures.md)
- [Duplicator wins the EF game iff there is a back-and-forth system](../ehrenfeucht-fraisse-games/ef-game-back-and-forth.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
- H. Straubing, Finite Automata, Formal Logic, and Circuit Complexity, Birkhäuser, 1994.
