# Stable submonoids of a free monoid are free

A submonoid of a free monoid is free exactly when it is stable: whenever $U$, $VW$, $UV$ and $W$ lie in it, so does $V$.

Let $M$ be a submonoid of a free monoid $\Sigma^*$. Call $M$ free if there is a set $B \subseteq M \setminus \{\varepsilon\}$, a basis, such that every element of $M$ is a product $b_1 \cdots b_s$ ($s \ge 0$) of elements of $B$ and this sequence $(b_1, \dots, b_s)$ is unique. Then $M$ is free if and only if there are no words $U, V, W \in \Sigma^*$ with $U, VW, UV, W \in M$ but $V \notin M$.


## Depends on

None.

## Proof depends on

None.

## Expansion

Suppose $M$ is free with basis $B$ and $U, VW, UV, W \in M$. Factorise $U = u_1 \cdots u_a$, $VW = x_1 \cdots x_b$, $UV = y_1 \cdots y_c$ and $W = w_1 \cdots w_d$ over $B$. The word $UVW$ equals both $u_1 \cdots u_a x_1 \cdots x_b$ and $y_1 \cdots y_c w_1 \cdots w_d$, so by uniqueness these sequences coincide. All factors are nonempty, so the partial products of the common sequence have strictly increasing lengths; the prefix of length $|U|$ is $u_1 \cdots u_a$ and the prefix of length $|UV| \ge |U|$ is $y_1 \cdots y_c$, so $a \le c$, $y_i = u_i$ for $i \le a$, and $V = y_{a+1} \cdots y_c \in M$.

Conversely, suppose $M$ is stable and let $B = (M \setminus \{\varepsilon\}) \setminus (M \setminus \{\varepsilon\})^2$. Every element of $M$ is a product of elements of $B$, by induction on length. If $b_1 \cdots b_s = c_1 \cdots c_t$ with all $b_i, c_j \in B$ and the sequences differ, both sequences are nonempty, as only the empty sequence of nonempty factors has product $\varepsilon$; cancel a common first factor and induct; if $b_1 \neq c_1$, then $|b_1| \neq |c_1|$ as both are prefixes of the same word, say $|b_1| < |c_1|$, and then $c_1 = b_1 V$ with $V$ nonempty. With $U = b_1$ and $W = c_2 \cdots c_t$ we have $U \in M$, $UV = c_1 \in M$, $W \in M$, and $VW = b_2 \cdots b_s \in M$, so $V \in M$ by stability, and $c_1 = b_1 V$ is a product of two nonempty elements of $M$, contradicting $c_1 \in B$. The same arguments give the basis explicitly. In a free $M$, a basis element $b$ is not a product $xy$ of two nonempty elements of $M$, since factorising $x$ and $y$ would give a second factorisation of $b$; and a nonempty element that is not such a product has a factorisation of length one, so it lies in the basis; the empty word, whose factorisation has length zero, lies in no basis. Hence a free submonoid has exactly one basis, the set $(M \setminus \{\varepsilon\}) \setminus (M \setminus \{\varepsilon\})^2$ of its nonempty elements that are not products of two nonempty elements; this elementary remark is used, without being stated, in the proof of Saarela's Lemma 15.

## Sources

- Aleksi Saarela, "Hardness Results for Constant-Free Pattern Languages and Word Equations", ICALP 2020, LIPIcs 168, Article 140 (2020), https://doi.org/10.4230/LIPIcs.ICALP.2020.140, Theorem 2 (Section 2), quoted there as a well-known characterisation of free monoids, and the definitions of free monoid and basis before it
