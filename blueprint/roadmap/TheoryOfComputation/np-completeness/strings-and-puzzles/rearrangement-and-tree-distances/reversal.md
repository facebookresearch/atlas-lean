# Signed reversal

The reversal $\rho(a, b)$ reverses the segment at ($0$-based) positions $a, \dots, b$ and flips the orientation of each of its genes, for $a \le b$; positions past the end are ignored. For $b < a$ the segment is empty, by truncated subtraction, and the result is the first $a$ genes followed by the genes from position $b + 1$ on.
