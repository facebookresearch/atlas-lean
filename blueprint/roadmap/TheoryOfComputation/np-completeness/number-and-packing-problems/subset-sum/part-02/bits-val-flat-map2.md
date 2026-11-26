# Value of a list of two-bit digits

Write $\mathrm{val}(l)$ for the value of a bit list $l$
read as a binary number least significant bit first. Let $f$ assign to each bit a list of exactly
two bits. Then for every bit list $b_0, b_1, \dots, b_{m-1}$, the concatenation
$f(b_0) f(b_1) \cdots f(b_{m-1})$ has value $\sum_{q < m} 4^q \, \mathrm{val}(f(b_q))$.
