# Evaluation of a QBF matrix gate

Given a list $s$ of truth values (the values of the earlier
gates) and an assignment $\alpha$ of a truth value to every natural number, the value of a gate
$(t, r)$ is computed as follows, where $s_a$ is the $a$-th entry of $s$ if $a$ is less than the
length of $s$ and false otherwise: if $t = 0$ and $r = [v]$, it is $\alpha(v)$; if $t = 1$ and
$r = [b]$, it is true exactly when $b = 1$; if $t = 2$ and $r = [a]$, it is the negation of $s_a$;
if $t = 3$, it is true exactly when $s_a$ is true for every $a$ in $r$; if $t = 4$, it is true
exactly when $s_a$ is true for some $a$ in $r$; for every other gate it is false.
