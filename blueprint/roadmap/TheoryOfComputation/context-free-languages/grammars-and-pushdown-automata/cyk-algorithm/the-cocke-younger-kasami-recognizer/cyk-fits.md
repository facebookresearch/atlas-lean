# When a production output fits a word

Let $f$ assign a cell (a finite set of nonterminals)
to every word. A production output fits a word $w$ with respect to $f$ exactly in two cases: the
output is a single terminal $a$ and $w$ is the one-letter word $a$; or the output is a pair of
nonterminals $B C$ and there is some $i$ with $0 < i < |w|$ such that $B$ lies in the cell of the
first $i$ letters of $w$ and $C$ lies in the cell of the remaining letters. No other output fits
any word.
