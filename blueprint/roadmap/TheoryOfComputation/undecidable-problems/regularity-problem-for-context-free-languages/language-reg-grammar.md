# The language of the regularity grammar

Let $g$ be an encoded context-free grammar over a
finite alphabet $T$ with decidable equality, with language $L(g)$. Over the letters of $T$, a
separator $\#$ and two bits $0$ and $1$, the regularity grammar of $g$ generates exactly
$L(g) \# \{0,1\}^* \cup T^* \# \{0^n 1^n : n \ge 0\}$, the set of words $u \# v$ with $u$ a word
over $T$, $v$ a word over the bits, and $u \in L(g)$ or $v = 0^n 1^n$ for some $n$.
