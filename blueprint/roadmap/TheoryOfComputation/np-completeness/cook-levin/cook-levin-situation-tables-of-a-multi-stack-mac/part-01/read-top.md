# Top of a stack as read from the windows

Let $W$ assign to each stack $k$ a window, a list
of entries that are symbols of $k$ or the empty cell $\bot$; let $P$ assign to each stack $k$ a
list of symbols of $k$; and let $c$ assign a natural number to each stack. The top of stack $k$ is
the first element of $P(k)$ when $P(k)$ is nonempty. Otherwise it is the entry of $W(k)$ at
position $c(k)$, counting from $0$, or $\bot$ when $W(k)$ has fewer than $c(k) + 1$ entries.

Here $P(k)$ lists the symbols pushed in this step and still on top, and $c(k)$ counts the original
symbols already consumed.
