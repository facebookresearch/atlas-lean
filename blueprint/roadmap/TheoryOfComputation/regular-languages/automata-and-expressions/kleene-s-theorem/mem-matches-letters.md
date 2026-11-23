# Letters of matched words occur in the regular expression

Let $\alpha$ be an alphabet and $r$ a regular expression over $\alpha$. The set of letters of $r$ is defined
recursively: empty for $0$ and $1$, $\{a\}$ for a letter $a$, and the union of the letter sets of the parts for a
sum or a concatenation, and that of the argument for a Kleene star. If a word $w$ is matched by $r$ and $a$ is a
letter occurring in $w$, then $a$ is a letter of $r$.
