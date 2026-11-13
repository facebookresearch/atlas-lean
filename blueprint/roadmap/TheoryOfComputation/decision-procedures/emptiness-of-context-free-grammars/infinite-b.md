# The infiniteness test

Let $g$ be an encoded grammar and $N$ its pumping bound. The test
returns true exactly when some word $w$ whose letters all occur as terminals in the productions
of $g$, with $N \le |w| < 2N$, is accepted by the membership test for $g$.
