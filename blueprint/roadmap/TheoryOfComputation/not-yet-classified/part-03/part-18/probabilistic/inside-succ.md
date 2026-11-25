# Inside recurrence at successor depth

For a context-free grammar with rule weights $q$, a nonterminal $A$ and a word $w$, the depth-$(d+1)$ inside weight is $\beta_{d+1}(A, w) = \ell(A, w) + \sum_{A \to B C} \sum_{k=0}^{|w|} q(A \to BC)\, \beta_d(B, w_{<k})\, \beta_d(C, w_{\ge k})$, where the $k$ terms with $w_{<k}$ or $w_{\ge k}$ empty are $0$, and the leaf weight $\ell(A, w)$ is $q(A \to a)$ when $w$ is a single terminal $a$ with that rule in the grammar, and $0$ otherwise.
