# Determinant of a scaled dual pairing

Let $R$ be a commutative ring, $A$ a
commutative $R$-algebra with a basis $(b_i)_{i \in \iota}$ indexed by a finite type $\iota$,
$\tau \colon A \to R$ an $R$-linear form, and $c \in A$. Then

$$\det\bigl(\tau(c\, b_i b_j)\bigr)_{i,j} = N_{A/R}(c)\,\det\bigl(\tau(b_i b_j)\bigr)_{i,j},$$

where $N_{A/R}(c)$, the norm of $c$, is the determinant of multiplication by $c$. Column $i$
of the matrix $L_c$ of that multiplication in the basis $b$ holds the coordinates of
$c\, b_i$, so the left-hand matrix is $L_c^{\top}$ times $\bigl(\tau(b_i b_j)\bigr)_{i,j}$,
and $\det L_c^{\top} = \det L_c = N_{A/R}(c)$.
