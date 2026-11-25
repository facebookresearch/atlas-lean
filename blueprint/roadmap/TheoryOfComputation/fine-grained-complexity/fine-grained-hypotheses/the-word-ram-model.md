# The word-RAM model

In the word-RAM with word size $w$, memory is an array of $S$ cells of $w$ bits each. Words serve as addresses, so any cell can be read or written given its address, and $w \ge \log_2 S$; for a problem of input size $n$ this gives $w \ge \log_2 n$. In one step the machine reads or writes one memory cell, or applies one of a fixed set of operations on words, namely addition, subtraction, multiplication, integer division and remainder, bitwise operations, shifts and comparisons, the primitives of a language such as C. Each step costs one unit, and the running time of an algorithm is the number of steps it takes. In fine-grained complexity the word size is $w = O(\log n)$.

## Sources

- E. Demaine, *6.851: Advanced Data Structures*, Lecture 11 (scribe notes), Massachusetts Institute of Technology, Spring 2012, <https://courses.csail.mit.edu/6.851/spring12/scribe/L11.pdf>, Sections 2.1 and 2.2
- V. Vassilevska Williams, "On some fine-grained questions in algorithms and complexity", *Proceedings of the ICM 2018*, <http://people.csail.mit.edu/virgi/eccentri.pdf>, Section 1 (the word-RAM with $O(\log n)$-bit words)
