# NP membership from the CLIQUE, INDEPENDENT-SET and VERTEX-COVER verifier

Let $L$ be a
decision problem, let $m$ be a mode (clique, independent set or vertex cover), and let $V_m$ be
the verifier of mode $m$. If for every bit string $x$, $L$ accepts $x$ exactly when there is a
bit string $w$ with $|w| \le |x|$ such that $V_m$ accepts $(x, w)$, then $L$ is in NP.
