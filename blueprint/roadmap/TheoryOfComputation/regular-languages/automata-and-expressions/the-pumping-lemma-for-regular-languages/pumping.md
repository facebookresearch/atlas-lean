# The pumping lemma for regular languages

Words are finite lists over an alphabet, and a language is regular when it is recognized by a deterministic finite automaton. For every regular language $L$ there is a natural number $n$ such that every word $w \in L$ with $|w| \ge n$ can be written as $w = xyz$ with $|x| + |y| \le n$ and $y$ nonempty, such that $x y^i z \in L$ for every $i \ge 0$.

Equivalently, every regular language has a [pumping length](is-pumping-length.md): a number $n$ with the property above.
