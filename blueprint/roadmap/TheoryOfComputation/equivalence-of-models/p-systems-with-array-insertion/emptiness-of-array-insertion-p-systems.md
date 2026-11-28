# Emptiness of one-dimensional array insertion P systems is undecidable

No algorithm decides whether a sequential P system that rewrites one-dimensional arrays only by array insertion rules generates any terminal array, already for membrane structures of height one.

A *one-dimensional array* over an alphabet $V$ is a finite map from a subset of $\mathbb Z$ to $V$, considered up to translation, with all other positions blank ($\#$). An *array insertion rule* $I(\mathcal A_1,\mathcal A_2)$, given by two finite arrays with disjoint shapes, inserts $\mathcal A_2$ next to an occurrence of the context $\mathcal A_1$ into blank positions; an *array deletion rule* removes $\mathcal A_2$ in the context $\mathcal A_1$.

A *sequential P system* $\Pi=(G,\mu,R,i_0)$ consists of an array grammar $G$ with an axiom array, a membrane structure $\mu$ (a tree of labeled membranes), rules $(h,r,tar)$ that apply the grammar rule $r$ to the single current array inside membrane $h$ and then send it here, out, or into a (named) inner membrane, and an initial membrane $i_0$. A computation starts with the axiom in $i_0$; it *halts* when no rule of the current membrane applies, and its result counts if it is terminal. $L_t(\Pi)$ is the set of terminal results of halting computations, A one-dimensional *array insertion P system* uses only array insertion rules.

**Theorem (Freund, Ivanov, Oswald and Subramanian).** For every $k\ge1$, it is undecidable, given a one-dimensional array insertion P system $\Pi$ with membrane tree of height at most $k$, whether $L_t(\Pi)$ is empty. The abstract states this for insertion rules, and Lemma 3 builds, from an instance of the Post correspondence problem, an array insertion P system with a membrane tree of height one whose language is empty exactly when the instance has no solution. In the source's notation, Corollary 4 states the same undecidability for the family $\mathcal L_t(DI\text{-}LP^{\langle k\rangle})$, where $DI$ allows deletion and insertion rules.

With array deletion as well, the systems are computationally complete; in dimension $d\ge2$, emptiness is undecidable already for contextual array grammars without membranes.

## Depends on

- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

From an instance $((u_1,\dots,u_n),(v_1,\dots,v_n))$ of Post's correspondence problem over $T$, Lemma 3 builds a system with a skin membrane $0$ and inner membranes $1,\dots,n+1$ whose results are exactly the arrays $LL'h_T(w)RR'$, where $w$ ranges over the results $u_{i_1}\cdots u_{i_k}$ of solutions and $h_T(a)=aa'$ interleaves each letter with a primed copy. The skin appends a copy of some $u_i$ and sends the array into membrane $i$, which must then append the primed copy of $v_i$ and send it back; insertion contexts keep the unprimed and primed sequences interleaved, so the two concatenations stay aligned, and a final rule placing $RR'$ applies only when both have the same length. Hence $L_t(\Pi)$ is nonempty iff the instance has a solution.

## Sources

- Rudolf Freund, Sergiu Ivanov, Marion Oswald and K. G. Subramanian, "One-dimensional Array Grammars and P Systems with Array Insertion and Deletion Rules", in *Proceedings Machines, Computations and Universality 2013*, Electronic Proceedings in Theoretical Computer Science 128, 2013, pp. 62–75, doi:[10.4204/EPTCS.128.14](https://doi.org/10.4204/EPTCS.128.14); read in arXiv:1309.1268v1 ([arXiv](https://arxiv.org/abs/1309.1268v1)), whose numbering is used (one counter for theorems, lemmas and corollaries): Section 2 (array insertion and deletion rules), Section 3 (sequential P systems and the families $\mathcal L_t(X\text{-}LP^{\langle n\rangle})$), Lemma 3 and Corollary 4 in the subsection encoding the Post correspondence problem.
