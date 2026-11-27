# Rational relations and transducers

Let $A$ and $B$ be finite alphabets. A *rational relation* over $A$ and $B$ is a rational subset of the monoid $A^* \times B^*$ with
componentwise concatenation: a member of the least family of subsets that contains the finite subsets and is closed under union,
product and the generated submonoid. A *transduction* $\tau : A^* \to B^*$ is a map from $A^*$ to the subsets of $B^*$, identified with its
graph $\{(x, y) : y \in \tau(x)\}$; it is *rational* if its graph is a rational relation, and a *rational function* if moreover
$\tau(x)$ has at most one element for every $x$.

A *transducer* $T = \langle A, B, Q, q_-, Q_+, E\rangle$ has a finite set $Q$ of states, an initial state $q_-$, a set $Q_+$ of final states and a
finite set $E \subseteq Q \times A^* \times B^* \times Q$ of transitions; a path $(p_1, u_1, v_1, q_1) \cdots (p_n, u_n, v_n, q_n)$ with
$q_i = p_{i+1}$ has label $(u_1 \cdots u_n, v_1 \cdots v_n)$, and the transduction $|T|$ *realized* by $T$ maps $x$ to the set of $y$ such that
some path from $q_-$ to a state of $Q_+$ has label $(x, y)$.

## Sources

- J. Berstel, *Transductions and Context-Free Languages*, Teubner, 1979; electronic edition of Chapters I–IV, 2007, <http://www-igm.univ-mlv.fr/~berstel/LivreTransductions/LivreTransductions.pdf>: Section III.2 (rational subsets of a monoid), Section III.3 (definition of rational relations), Section III.4 (transductions and rational transductions), Section III.6 (definition of transducers and of $|T|$) and Section IV.1 (rational functions).
