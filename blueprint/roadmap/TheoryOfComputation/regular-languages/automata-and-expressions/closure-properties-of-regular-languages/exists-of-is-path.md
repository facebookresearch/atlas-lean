# Soundness of the homomorphic-image ε-NFA

Let $M$ be a DFA over a finite alphabet $T$ with
start state $q_0$, and let $\varphi$ map letters of $T$ to words over $T'$; for a word $w$ over $T$,
write $\varphi(w)$ for the concatenation of the images of its letters. Suppose the ε-NFA of $M$ and
$\varphi$ has a path from the state $q_0$ of $M$ to a state $u$, with label sequence $x$, and let
$\bar x$ be the word formed by the non-ε labels of $x$. If $u$ is a state $q$ of $M$, then there is
a word $w$ over $T$ on which $M$ reaches $q$ from $q_0$ and $\varphi(w) = \bar x$. If $u$ is the
intermediate state $(q, a, i)$, then there is a word $w$ over $T$ on which $M$ reaches $q$ from
$q_0$ and $\varphi(w)$ followed by the first $i$ letters of $\varphi(a)$ (all of $\varphi(a)$ if it
is shorter) equals $\bar x$.
