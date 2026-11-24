# Accepted words of length between the number of listed states and twice it

Let $D$ be an
encoded DFA over an alphabet $\alpha$ with decidable equality, and let $N$ be the length of its
list of states. For every natural number $n$ and every word $w$ of length $n$ in the language of
$D$ with $N \le n$, the language of $D$ contains a word $v$ whose length $|v|$ satisfies
$N \le |v| < 2N$.

## Sources

- M. O. Rabin and D. Scott, *Finite automata and their decision problems*, IBM Journal of Research and Development 3(2) (April 1959), 114–125, Theorem 9 (p. 119), the direction from an infinite language to an accepted tape of length
  $n$ with $r \le n < 2r$, $r$ the number of states. Here $N$ is the length of the list of states,
  which is $r$ when the list has no repetitions.
