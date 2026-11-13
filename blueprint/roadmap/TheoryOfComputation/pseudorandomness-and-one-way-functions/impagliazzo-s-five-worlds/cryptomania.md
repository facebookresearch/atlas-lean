# Cryptomania

Cryptomania is the statement that public-key cryptography exists: there
are a polynomial $\ell$ with natural-number coefficients and polynomial-time computable maps
$G$ (key generation), $E$ (encryption) and $D$ (decryption) from bitstrings to bitstrings with
the following two properties. First, decryption is correct: for every natural number $n$, all
key coins $r$ and encryption coins $s$ that are bitstrings of length $\ell(n)$, and every bit
$b$, if $(pk, sk)$ is the key pair of $G$ on $r$ and the ciphertext $e$ is $E$ applied to the
bitstring encoding of the triple $(pk, (b), s)$, where $(b)$ is the one-bit list, then $D$
applied to the bitstring encoding of the pair $(sk, e)$ is $(b)$. Second, the scheme is secure:
for every family $(C_n)$ of encoded flat Boolean circuits and every polynomial $q$ with
natural-number coefficients such that each $C_n$ has at most $q(n)$ gates, and for every natural
number $c$, there is $N$ such that for all $n \ge N$ the eavesdropping advantage of $C_n$
against $(G, E)$ with polynomial $\ell$ at length $n$ is at most $1/n^c$.
