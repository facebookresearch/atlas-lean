# Checked-answer branch weights equal conditional checked-answer probabilities

Let $G$ be an $\alpha$-anchored game with $0 < \alpha < 1$, question sets $\mathcal{X}$ and $\mathcal{Y}$ (both containing the anchor $\perp$), answer sets $\mathcal{A}$ and $\mathcal{B}$ and question law $\mu$, and let $\eta = \alpha/2$. Fix $n \ge 1$ and a finite-dimensional tensor strategy for the $n$-fold repetition: a unit vector $|\psi\rangle \in \mathbb{C}^d \otimes \mathbb{C}^d$ and POVMs $\{A_{\mathbf{x}}(\mathbf{a})\}_{\mathbf{a} \in \mathcal{A}^n}$ on the first factor and $\{B_{\mathbf{y}}(\mathbf{b})\}_{\mathbf{b} \in \mathcal{B}^n}$ on the second, for $\mathbf{x} \in \mathcal{X}^n$ and $\mathbf{y} \in \mathcal{Y}^n$. Draw $n$ independent copies $(D_j, M_j, X_j, Y_j)$ of the noisy-reveal variables of the linked page with $\eta = \alpha/2$, and answers $(\mathbf{A}, \mathbf{B})$ that, given the questions $(\mathbf{X}, \mathbf{Y}) = (\mathbf{x}, \mathbf{y})$, are independent of $(\mathbf{D}, \mathbf{M})$ and equal $(\mathbf{a}, \mathbf{b})$ with probability $\langle\psi| A_{\mathbf{x}}(\mathbf{a}) \otimes B_{\mathbf{y}}(\mathbf{b}) |\psi\rangle$. Fix a set $C \subseteq [n]$ of checked coordinates and an unchecked coordinate $i \notin C$, and call $\Omega_{-i} = \bigl((D_j, M_j)_{j \notin C \cup \{i\}}, \mathbf{X}_C, \mathbf{Y}_C\bigr)$ the *retained question information*. For checked answers $(a_C, b_C)$ let $A_{\mathbf{x}}(a_C)$ be the sum of the $A_{\mathbf{x}}(\mathbf{a})$ over the $\mathbf{a}$ that agree with $a_C$ on $C$, define $B_{\mathbf{y}}(b_C)$ likewise, and for a value $\omega_{-i}$ of $\Omega_{-i}$ of positive probability, $x \in \mathcal{X}$ and $y \in \mathcal{Y}$ let $A_{\omega_{-i}, x}(a_C) = \mathbb{E}[A_{\mathbf{X}}(a_C) \mid \Omega_{-i} = \omega_{-i}, X_i = x]$ and $B_{\omega_{-i}, y}(b_C) = \mathbb{E}[B_{\mathbf{Y}}(b_C) \mid \Omega_{-i} = \omega_{-i}, Y_i = y]$. For a *left message* $x$, that is, the event $(D_i, M_i) = (A, x)$, let $A_{\omega_{-i}, \perp/x}(a_C) = \eta\, A_{\omega_{-i}, \perp}(a_C) + (1 - \eta)\, A_{\omega_{-i}, x}(a_C)$, which mixes the *anchor branch* $X_i = \perp$ with weight equal to the erasure rate $\eta = \alpha/2$ and the *ordinary branch* $X_i = x$ with weight $1 - \eta$. With $r_{-i} = (\omega_{-i}, a_C, b_C)$, the *branch vector* of $s \in \mathcal{X} \cup \{\perp/x : x \in \mathcal{X}\}$ and $y$ is

$$
|\Phi_{r_{-i}, s, y}\rangle = A_{\omega_{-i}, s}(a_C)^{1/2} \otimes B_{\omega_{-i}, y}(b_C)^{1/2}\, |\psi\rangle .
$$

Then for $s \in \mathcal{X}$ and $y$ with $\mu(s, y) > 0$,

$$
\bigl\| |\Phi_{r_{-i}, s, y}\rangle \bigr\|^2 = \Pr\bigl[(\mathbf{A}_C, \mathbf{B}_C) = (a_C, b_C) \bigm| \Omega_{-i} = \omega_{-i}, X_i = s, Y_i = y\bigr],
$$

and for a left message $x$ and $y$ with $\mu(x, y) > 0$ the squared norm of $|\Phi_{r_{-i}, \perp/x, y}\rangle$ is $\eta$ times this probability for $s = \perp$ plus $1 - \eta$ times it for $s = x$, which equals $\Pr[(\mathbf{A}_C, \mathbf{B}_C) = (a_C, b_C) \mid \Omega_{-i} = \omega_{-i}, (D_i, M_i) = (A, x), Y_i = y]$ (Bavarian, Vidick and Yuen, Section 4.4, eqs. (12)–(19) and Proposition 4.9, eqs. (20)–(22)).

## Proof sketch

By definition $\| |\Phi_{r_{-i}, s, y}\rangle \|^2 = \langle\psi| A_{\omega_{-i}, s}(a_C) \otimes B_{\omega_{-i}, y}(b_C) |\psi\rangle$, which for $s \in \mathcal{X}$ is the average of $\langle\psi| A_{\mathbf{x}}(a_C) \otimes B_{\mathbf{y}}(b_C) |\psi\rangle = \Pr[(\mathbf{A}_C, \mathbf{B}_C) = (a_C, b_C) \mid \mathbf{X} = \mathbf{x}, \mathbf{Y} = \mathbf{y}]$ over $\mathbf{X}$ given $(\omega_{-i}, X_i = s)$ and $\mathbf{Y}$ given $(\omega_{-i}, Y_i = y)$. The coordinates are independent and, within each coordinate $j \notin C \cup \{i\}$, $X_j$ and $Y_j$ are independent given $(D_j, M_j)$, so $\mathbf{X}$ and $\mathbf{Y}$ are independent given $(\Omega_{-i}, X_i, Y_i)$ and the average is the stated conditional probability. For a left message use linearity, and that given $(D_i, M_i) = (A, x)$ the question $X_i$ equals $\perp$ with probability $\eta$ (for $x \ne \perp$; always, for $x = \perp$) independently of $Y_i$.

## Depends on

- [Anchoring a two-prover game](anchoring-a-two-prover-game.md)
- [Entangled strategies and the entangled value of a game](../entangled-strategies-and-entangled-value.md)
- [Conditional independence of the noisy reveal in anchored repetition](noisy-reveal-conditional-independence.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2), 2022.
