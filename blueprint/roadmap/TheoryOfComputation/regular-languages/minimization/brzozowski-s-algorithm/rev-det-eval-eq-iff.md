# Brzozowski's lemma

Let $M$ be a DFA with finitely many states in which every state is
reached from the start state by some word, and let $L$ be its language. Write $u^R$ for the word
$u$ read backwards, $L^R = \{u \mid u^R \in L\}$ for the reversed language, and
$w^{-1}K = \{v \mid wv \in K\}$ for the left quotient of a language $K$ by a word $w$. Then two
words $w$ and $w'$ lead the determinized reversal of $M$ from its start state to the same set of
states if and only if $w^{-1}L^R = w'^{-1}L^R$.
