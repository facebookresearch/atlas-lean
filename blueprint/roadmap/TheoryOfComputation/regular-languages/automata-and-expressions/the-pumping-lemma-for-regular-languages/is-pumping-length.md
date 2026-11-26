# Pumping lengths of a language

Words are finite lists over an alphabet, and a language is a set of words. A natural number $n$ is a pumping length for a language $L$ when every word $w \in L$ of length at least $n$ can be written as $w = xyz$ with $|x| + |y| \le n$ and $y$ nonempty, such that $x y^i z \in L$ for every $i \ge 0$, where $y^i$ is $y$ repeated $i$ times. In particular the nonempty middle part $y$ lies within the first $n$ letters of $w$.
