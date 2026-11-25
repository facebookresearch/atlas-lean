# A long accepted word makes the language of an encoded DFA infinite

Let $D$ be an
encoded DFA and let $N$ be the length of the list of states of $D$. If $D$ accepts a word of
length at least $N$, then the language of $D$ is infinite.

The proof pumps the word, using the pumping lemma for DFAs.

## Sources

- M. O. Rabin and D. Scott, *Finite automata and their decision problems*, IBM Journal of Research and Development 3(2) (April 1959), 114–125, Lemma 8 and the converse direction of Theorem 9 (p. 119).
