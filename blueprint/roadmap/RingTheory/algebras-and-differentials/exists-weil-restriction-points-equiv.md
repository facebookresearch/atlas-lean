# Weil restriction along a finite free extension

Let $A$ and $B$ be commutative rings with $B$ an $A$-algebra that is finite and free as an $A$-module, and let $H$ be a commutative $B$-algebra (all in one universe). Then there exist a commutative ring $W$ with an $A$-algebra structure and, for every commutative $A$-algebra $T$, a bijection

$$e_T : \operatorname{Hom}_{A\text{-alg}}(W, T) \;\cong\; \operatorname{Hom}_{B\text{-alg}}(H,\, B \otimes_A T),$$

natural in $T$: for every $A$-algebra homomorphism $u : T \to T'$ between commutative $A$-algebras and every $f : W \to T$,

$$e_{T'}(u \circ f) = (\mathrm{id}_B \otimes u) \circ e_T(f).$$

So $W$ represents the functor $T \mapsto \operatorname{Hom}_{B\text{-alg}}(H, B \otimes_A T)$ on commutative $A$-algebras.
