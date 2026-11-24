# Language of a sentential form

For an encoded regular expression $e$, the language of a
sentential form $X_1 \cdots X_n$ (terminals in $\alpha$, nonterminals in $\mathbb{N}$) is the
product $L_1 \cdots L_n$, where $L_i$ is $\{a\}$, the language of the one-letter word $a$, when
$X_i$ is the terminal $a$, and the language of the regular expression at node $k$ of $e$ when
$X_i$ is the nonterminal $k$. The empty form has language $\{\varepsilon\}$.
