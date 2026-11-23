# Embedding of ordinary words into string terms

Let $\alpha$ be an alphabet and $V$ a set of variables. String terms are built from constant words and variables by concatenation (and by applying letter-to-word substitutions), and the embedding of a pattern $c_1 \cdots c_k$ is the term $c_1 \cdot (c_2 \cdot (\cdots (c_k \cdot \varepsilon)))$ in which each constant letter $a$ becomes the constant word $a$, each variable stays a variable, and the empty pattern becomes the constant empty word $\varepsilon$. Formally, the embedding of the empty pattern
is the constant empty word, the embedding of $a w$ with $a \in \alpha$ is the concatenation of the constant
word $a$ with the embedding of $w$, and the embedding of $x w$ with $x \in V$ is the concatenation of the
variable $x$ with the embedding of $w$.
