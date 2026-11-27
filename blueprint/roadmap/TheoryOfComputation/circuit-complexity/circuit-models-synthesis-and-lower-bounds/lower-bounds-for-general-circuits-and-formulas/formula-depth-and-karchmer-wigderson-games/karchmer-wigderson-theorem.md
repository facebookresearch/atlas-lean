# Karchmer–Wigderson: formula depth equals communication complexity

For every Boolean function $f$, the least depth of a De Morgan formula computing $f$ (with negations at the leaves and free) equals $\mathrm{CC}(\mathrm{KW}_f)$. For every monotone $f$, the least depth of a monotone formula computing $f$ equals $\mathrm{CC}(\mathrm{KW}^+_f)$. Consequently the fan-in-two circuit depth of $f$ equals $\mathrm{CC}(\mathrm{KW}_f)$.

## Proof sketch

A formula gives a protocol by walking down from the root: at an AND gate Bob (whose input falsifies it) names a false child, at an OR gate Alice names a true child, and at a leaf the literal separates the inputs. Conversely a protocol tree is converted into a formula by labelling Alice's nodes OR and Bob's nodes AND, by induction on rectangles $X\times Y$ with $X\subseteq f^{-1}(1)$, $Y\subseteq f^{-1}(0)$.

## Depends on

- [The Karchmer–Wigderson game of a Boolean function](karchmer-wigderson-game.md)
- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [Unfolding a circuit into a formula of the same depth](../../circuit-models-and-classes/circuit-models-and-complexity-measures/unfolding-a-circuit-into-a-formula.md)

## Sources

- Mauricio Karchmer, Avi Wigderson, "Monotone circuits for connectivity require super-logarithmic depth", SIAM Journal on Discrete Mathematics 3(2), 255–265, 1990.
- Eyal Kushilevitz, Noam Nisan, "Communication Complexity", Cambridge University Press, 1997.
