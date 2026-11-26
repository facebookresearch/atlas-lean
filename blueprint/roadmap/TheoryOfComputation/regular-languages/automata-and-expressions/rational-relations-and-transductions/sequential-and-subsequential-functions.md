# Sequential and subsequential functions

A *(left) sequential transducer* $L = \langle A, B, Q, q_-\rangle$ has a finite set $Q$ of states, an initial state $q_-$, and partial functions
$\delta : Q \times A \to Q$ (next state, written $q \cdot a$) and $\lambda : Q \times A \to B^*$ (output, written $q * a$) with the same domain, extended to
words by $q \cdot 1 = q$, $q \cdot wa = (q \cdot w) \cdot a$, $q * 1 = 1$ and $q * wa = (q * w)((q \cdot w) * a)$. It realizes the partial function
$w \mapsto q_- * w$, and a partial function $A^* \to B^*$ is *sequential* if it is realized by a sequential transducer. A *subsequential
transducer* adds a partial final output $\rho : Q \to B^*$ and realizes $x \mapsto (q_- * x)\,\rho(q_- \cdot x)$; its functions are the *subsequential*
functions. A *right sequential* function is one whose reversal $x \mapsto \alpha(\tilde x)^\sim$ is sequential.

The *distance* of words $u, v$ is $\|u, v\| = |u| + |v| - 2|u \wedge v|$, where $u \wedge v$ is their longest common prefix. A partial function
$\alpha : A^* \to B^*$ has *bounded variation* if for every $k \ge 0$ there is $K \ge 0$ such that $u, v \in \mathrm{dom}(\alpha)$ and $\|u, v\| \le k$
imply $\|\alpha(u), \alpha(v)\| \le K$. Every subsequential function, hence every sequential function, is a rational function.

## Depends on

- [Rational relations and transducers](rational-relations-and-transducers.md)

## Sources

- J. Berstel, *Transductions and Context-Free Languages*, Teubner, 1979; electronic edition of Chapters I–IV, 2007, <http://www-igm.univ-mlv.fr/~berstel/LivreTransductions/LivreTransductions.pdf>: Section IV.2, the definitions of sequential and subsequential transducers and functions, right sequential functions, distance and bounded variation, and Propositions IV.2.1, IV.2.4 and Corollary IV.2.3.
