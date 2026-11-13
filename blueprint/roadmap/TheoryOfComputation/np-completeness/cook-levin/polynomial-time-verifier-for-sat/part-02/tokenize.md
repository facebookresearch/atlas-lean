# Tokenizer of the SAT verifier

Given bit strings $x$ and $w$, the tokenizer rejects
(returns no result) if $x$ does not decode to a CNF formula. If $x$ decodes to a formula
$\varphi$, it returns the pair consisting of the token stack, the reverse of the tokens of
$\varphi$ in reading order, and the table stack of the occurrence table of $\varphi$ and $w$.
