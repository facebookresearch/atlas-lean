# Minimal arithmetic theories capture their complexity classes

A theory of bounded arithmetic whose comprehension is limited to formulas describing a class $C$ between $\mathsf{AC}^0$ and $\mathsf{P}$ proves total exactly the functions computable in $C$, provided it proves its own closure under first-order operations and its theorems have $C$-computable witnesses.

A system of arithmetic captures a function class if it proves the totality of all and only the functions in that class. If a logic $\Phi$ captures a complexity class $C$ in the sense of descriptive complexity, the function class $FC$ consists of the number functions $f$ and string functions $F$ whose graphs and bit graphs are $\Phi$-definable: $z=f(\bar x,\bar Y)\leftrightarrow\varphi(z,\bar x,\bar Y)$ and $F(\bar x,\bar Y)(i)\leftrightarrow i<t\wedge\varphi(i,\bar x,\bar Y)$ with $\varphi\in\Phi$. For a class $\Phi_C$ of existential second-order formulas capturing $C$, the theory $V\text{-}\Phi_C$ is $V^0$ together with comprehension over bounded $\Phi_C$ formulas.

Claim. Let $\mathsf{AC}^0\subseteq C\subseteq\mathsf{P}$. Suppose $\Phi_C$ is closed under first-order operations provably in $V\text{-}\Phi_C$, and for every $\varphi(\bar x,\bar Y)\in\Phi_C$ with $V\text{-}\Phi_C\vdash\varphi$ there is a function on the free variables of $\varphi$, computable in $C$, that witnesses the existential quantifiers of $\varphi$. Then the provably total functions of $V\text{-}\Phi_C$ are exactly the functions computable in $C$.

The source states this as an informal summary of the general result. Instances: $V^0$ captures $\mathsf{AC}^0$; $V\text{-}\mathrm{Horn}$ and $V\text{-}\mathrm{Krom}$, with comprehension over second-order existential Horn and Krom formulas, capture $\mathsf{P}$ and $\mathsf{NL}$; and $V^1$ also captures $\mathsf{P}$, though it likely proves more $\Sigma_2^B$ statements than $V\text{-}\mathrm{Horn}$.

## Expansion

The systems reason only with objects of their class, and provable closure under $\mathsf{AC}^0$ operations (conjunction, disjunction, complementation) lets them prove totality of every function definable by an object in their comprehension scheme; the witnessing hypothesis gives the converse. $V\text{-}\mathrm{Horn}$ formalizes the Horn-satisfiability algorithm and is finitely axiomatizable, while $V\text{-}\mathrm{Krom}$ formalizes Immerman's inductive counting, which proves that $\mathsf{NL}$, and with it second-order existential Krom logic, is closed under complementation inside $\mathsf{NL}$ reasoning.

## Depends on

None.

## Proof depends on

- [Immerman–Szelepcsényi theorem](../../../complexity-classes/immerman-szelepcsenyi.md)

## Sources

- Antonina Kolokolova, "Expressing versus Proving: Relating Forms of Complexity in Logic", *Journal of Logic and Computation*, 2012, https://doi.org/10.1093/logcom/exq013 (Definitions 4, 5 and 6, Section 5, and the Claim in Section 6).
