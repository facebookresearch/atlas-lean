# Lasso characterization of Büchi nonemptiness

For finitely many states, the language of a nondeterministic Büchi automaton is nonempty iff
some accepting state is reachable from a start state and lies on a nonempty cycle.

The cycle must have positive length. In the proof of his Proposition 13, Vardi states the
criterion as "$t$ is connected to $s_0$ and $t$ is connected to itself", with a definition of
connectedness that also admits the path of length $0$; read literally, the second condition is
then always true. His argument uses a genuine cycle (an accepting state occurring twice in an
accepting run), and his linear-time algorithm asks for a nontrivial strongly connected
component, which is the condition of this statement. The finiteness of the state set is used only in the direction from an accepted
word to a lasso.

## Informally uses

- [An accepted word yields a lasso](has-lasso-of-mem.md): some accepting state recurs.
- [Lassos give accepted ultimately periodic words](lasso-mem-language.md): the converse.

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 2.4, Proposition 13 (and the definition of connectedness in the proof
  of Proposition 11).
- W. Thomas, "Automata on infinite objects", in *Handbook of Theoretical Computer Science*,
  Vol. B, Elsevier 1990.
