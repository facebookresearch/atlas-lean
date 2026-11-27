# Locally testable languages

A language $L \subseteq A^+$ is *locally testable* if it is a Boolean combination of languages of the form $\{x\}$, $xA^*$, $A^*x$ and $A^*xA^*$ with $x \in A^+$, and
*positively locally testable* if it is a positive Boolean combination of them. Intuitively, membership in a locally testable language depends only
on the prefixes and suffixes of length less than $n$ and the factors of length $n$ of a word, for some $n$, as read by a scanner with a window of
size $n$.

## Sources

- J.-É. Pin, "Syntactic semigroups", in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 1, Springer, 1997, pp. 679–746, author's copy <https://www.irif.fr/~jep/PDF/HandBook.pdf>: Section 5.3, the description of scanners and the definitions of positively locally testable and locally testable languages.
