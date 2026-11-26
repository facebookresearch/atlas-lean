# Cocycle condition for descent data

Let $A$ and $B$ be commutative rings with $B$ an $A$-algebra, let $N$ be a $B$-module, and let $\varphi : (i_1)_! N \xrightarrow{\sim} (i_2)_! N$ be an isomorphism of $(B \otimes_A B)$-modules, where $i_1, i_2 : B \to B \otimes_A B$ are $b \mapsto b \otimes 1$ and $b \mapsto 1 \otimes b$ and $f_!$ denotes extension of scalars along $f$. Write $\varphi_{12}, \varphi_{23}, \varphi_{13}$ for the transports of $\varphi$ along the coface maps

$$c_{12}(b \otimes b') = b \otimes (b' \otimes 1),\quad c_{23}(b \otimes b') = 1 \otimes (b \otimes b'),\quad c_{13}(b \otimes b') = b \otimes (1 \otimes b'),$$

each obtained by extending $\varphi$ along the coface map and composing with the canonical identifications of extension of scalars along composites. The pair $(N, \varphi)$ satisfies the cocycle condition when

$$\varphi_{13} = \varphi_{23} \circ \varphi_{12}.$$

The isomorphism requirement on $\varphi$ is part of the data: the zero morphism would satisfy the same equation without being descent data.
