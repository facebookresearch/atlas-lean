# Ogden's lemma

Let $L$ be a context-free language over an alphabet $T$. A marked word is a
word whose letters are pairs $(a, b)$ with $a \in T$ and $b$ a Boolean, the letter being marked
when $b$ is true; its underlying word is the word of first components. Then there is a natural
number $n > 0$ such that every marked word $w$ whose underlying word lies in $L$ and which has at
least $n$ marked letters can be written as $w = uvxyz$ with marked words $u, v, x, y, z$ such that
$vy$ has at least one marked letter, $vxy$ has at most $n$ marked letters, and for every natural
number $i$ the underlying word of $u v^i x y^i z$ lies in $L$, where $v^i$ is the concatenation
of $i$ copies of $v$.
