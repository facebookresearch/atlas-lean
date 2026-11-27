# Nielsen transformations of quadratic word equations

Nielsen transformations rewrite a quadratic word equation by guessing which of the two leading symbols is a prefix of the other and cancelling it. They never lengthen the equation and keep it quadratic, so only finitely many equations are reachable; the reachability graph describes all solutions.

Let $A$ be an alphabet of constants and $X$ a set of variables. For a quadratic equation $E$ given by $\alpha = \beta$ let $|E| = |\alpha\beta|$ and let $\mathrm{qv}(E)$ be the set of variables occurring exactly twice in $\alpha\beta$. For $z \in A \cup X$ and $y \in X$ let $\psi_{z<y}$ be the morphism of $(A \cup X)^*$ with $\psi_{z<y}(y) = zy$ that fixes every other symbol. For $Y \subseteq X$ let $\pi_{X \setminus Y}$ be the morphism that erases the variables in $Y$ and fixes every other symbol. If $E$ has the form $z\alpha' = y\beta'$ with $z, y \in A \cup X$, the following rewriting steps are defined:

1. if $z \in \mathrm{qv}(E)$ and $z \ne y$: $\; z\alpha' = y\beta' \;\Rightarrow_L\; z\,\psi_{y<z}(\alpha') = \psi_{y<z}(\beta')$;
2. if $y \in \mathrm{qv}(E)$ and $z \ne y$: $\; z\alpha' = y\beta' \;\Rightarrow_R\; \psi_{z<y}(\alpha') = y\,\psi_{z<y}(\beta')$;
3. if $z \in X \setminus \mathrm{qv}(E)$: $\; z\alpha' = y\beta' \;\Rightarrow_>\; z\alpha' = \beta'$;
4. if $y \in X \setminus \mathrm{qv}(E)$: $\; z\alpha' = y\beta' \;\Rightarrow_>\; \alpha' = y\beta'$;
5. if $z = y$: $\; z\alpha' = y\beta' \;\Rightarrow_>\; \alpha' = \beta'$.

In addition, for every quadratic equation $\alpha = \beta$ (with $\alpha$ or $\beta$ possibly empty) and every set $Y \subseteq \mathrm{var}(E)$ of variables occurring in it, $\alpha = \beta \Rightarrow_> \pi_{X \setminus Y}(\alpha) = \pi_{X \setminus Y}(\beta)$. For $Y = \varnothing$ this step is the identity, a loop at every equation; every other step of $\Rightarrow_>$ shortens the equation (the source's Remark 3.1 states the shortening for all of $\Rightarrow_>$, which taken literally fails for the identity loop). The **Nielsen transformation relation** is $\Rightarrow_{NT} = \Rightarrow_L \cup \Rightarrow_R \cup \Rightarrow_>$, and $\Rightarrow\, = \Rightarrow_L \cup \Rightarrow_R$ is its length-preserving part. The **Nielsen graph** $G_E$ of $E$ has as vertices the equations $E'$ with $E \Rightarrow_{NT}^* E'$ and as edges the pairs $(E_1, E_2)$ of distinct such equations with $E_1 \Rightarrow_{NT} E_2$; that is, it is the source's graph with the identity loops suppressed, which changes neither reachability nor shortest directed distances. When two distinct constants lead the two sides no step of the forms 1–5 applies.

Every step maps quadratic equations to quadratic equations and regular equations to regular equations, introduces no new variables or constants, and satisfies $|E'| = |E|$ for $\Rightarrow$ and $|E'| < |E|$ for every non-identity step of $\Rightarrow_>$; in particular $G_E$ is finite.

## Depends on

- [Quadratic, regular and regular-ordered word equations](restricted-classes-of-word-equations.md)

## Proof depends on

None.

## Expansion

This is a definition; the closing paragraph records the observations that make it useful. A step $\Rightarrow_L$ corresponds to the guess that, in a solution $h$, the image $h(y)$ of the other leading symbol is a prefix of $h(z)$, possibly equal to it: substituting $yz$ for $z$ everywhere and cancelling the common leading $y$ keeps $z$ occurring at most twice, and the new value of $z$ is the remaining suffix, which may be empty. Steps $\Rightarrow_>$ either let a once-occurring variable absorb the other leading symbol, cancel equal leading symbols, or erase a nonempty set of variables guessed to be empty; each strictly shortens the equation, the empty erasure being the identity. Since lengths never increase and the symbols are drawn from those of $E$, the reachable set is finite. Other textbook variants of the rules, such as Levi's method used by Lin and Majumdar, differ in the length-reducing steps and are separate relations; results stated for one variant are not transferred to another without proof.

## Sources

- Joel D. Day and Florin Manea, "On the structure of solution-sets to regular word equations", *Theory of Computing Systems* 68:662–739, 2024, <https://doi.org/10.1007/s00224-021-10058-5>, Section 3.1 (the morphisms $\psi_{z<y}$ and the relations $\Rightarrow_L, \Rightarrow_R, \Rightarrow_>$), Remark 3.1 (preservation of quadraticity and regularity, lengths, finiteness) and Section 3.2 (the graph).
- Anthony W. Lin and Rupak Majumdar, "Quadratic Word Equations with Length Constraints, Counter Systems, and Presburger Arithmetic with Divisibility", *Logical Methods in Computer Science* 17(4:4), 2021, <https://doi.org/10.46298/lmcs-17(4:4)2021>; arXiv:2007.15478v6, Section 3.1 (the variant called Levi's method).
