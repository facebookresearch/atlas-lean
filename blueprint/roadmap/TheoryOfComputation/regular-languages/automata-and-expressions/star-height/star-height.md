# Generalized star height

The generalized star height of a generalized regular expression
is the nesting depth of the Kleene star in it, counting the stars inside its ordinary regular
subexpressions: for generalized regular expressions $e$, $e_1$, $e_2$, an ordinary regular
expression has its usual star height; the complement $\neg e$ has the star height of $e$; the
union $e_1 + e_2$ and the concatenation $e_1 e_2$ have the larger of the star heights of $e_1$
and $e_2$; and the star $e^*$ has star height one more than $e$.
