# Infiniteness test for encoded DFAs

Let $D$ be an encoded DFA over a finite alphabet and
let $N$ be the length of its list of states. The infiniteness test is the Boolean that is true
exactly when the language of $D$ contains a word $w$ with $N \le |w| < 2N$; it checks every word
of each length $N + i$ with $0 \le i < N$.
