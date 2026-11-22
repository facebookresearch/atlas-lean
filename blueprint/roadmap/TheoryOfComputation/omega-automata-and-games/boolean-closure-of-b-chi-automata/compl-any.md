# Complement of an ω-regular language, over any alphabet

If an ω-language $L$ over an alphabet $\Sigma$ is recognized by a finite-state nondeterministic
Büchi automaton, so is its complement $\Sigma^\omega \setminus L$. No assumption is made on
$\Sigma$; Büchi's theorem and Vardi's Proposition 7 are stated for a finite nonempty alphabet.

For a nonempty alphabet, the complement is recognized through Büchi's congruence of finite index,
an argument that does not use the finiteness of the alphabet. Over the empty alphabet there are no
infinite words, so the complement is the empty language, which is recognized by an automaton with
no initial state. No bound on the number of states is claimed.

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 2.2, Proposition 7.
- J. R. Büchi, "On a decision method in restricted second order arithmetic", in *Proc.
  International Congress on Logic, Methodology and Philosophy of Science 1960*, Stanford
  University Press 1962, 1-11.
