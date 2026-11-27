# Fooling-set bound on rectangle covers

Let $S$ be a finite [fooling set](../deterministic-communication-protocols/is-fooling-set.md) for $f$ with value true, and let $(A_1, B_1), \dots, (A_r, B_r)$ be a list of [monochromatic-1 rectangles](rect-mono.md) with finite sides such that every element of $S$ lies in one of them (the rectangles need only cover $S$, for example when they cover every input on which $f$ is true). Then $|S| \le r$, since two distinct elements of $S$ never share a rectangle.
