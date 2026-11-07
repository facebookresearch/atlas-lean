# Step bound of the host

Let $M$ be a finite multi-stack Turing machine with encoding data
$E$, let $Y$ be a list of input symbols, and let $m, T \in \mathbb{N}$. Let $H = m + (T + 1) d + 1$,
where $d$ is the window depth of $M$, and let $R = T + H + 1$. Let $L$ be the layout of $E$ and $N$
its number of situations. Let $c_I$ be the init generator's constant for $L$, the number of
distinct codes of symbols of $Y$, and the number of the input stack; let $c_F$ be the family
generator's constant for $L$ and $N$; let $c_S$ be the shift generator's constant for $L$ and $N$;
and let $c_A$ be the accept generator's constant for $L$, the number of (label, state) codes, and
the number of the output stack. The step bound is

$$c_I R^5 + c_F R^5 + c_F R^5 + c_S R^6 + c_A R^4 + 5,$$

the bounds of the init, update, situation-definition, shift and accept generators plus five
chaining steps.
