# Postfix regular expression reader step (bounded languages)

One postfix token is read onto a stack of regular expressions: $(0, 0)$ pushes $\emptyset$, $(1, 0)$ pushes $\varepsilon$, $(2, a)$ pushes the letter $a$; $(3, 0)$ and $(4, 0)$ replace the top two expressions $\alpha, \beta$ ($\beta$ on top) by $\alpha + \beta$ and $\alpha\beta$; $(5, 0)$ replaces the top expression $\alpha$ by $\alpha^*$; any other token, or too short a stack, fails.
