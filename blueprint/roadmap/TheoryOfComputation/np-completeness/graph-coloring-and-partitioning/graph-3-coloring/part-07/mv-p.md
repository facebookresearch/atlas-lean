# Moving one color code in the 3-COLOR verifier

Given a map $f$ from pairs of bits to
labels: if the color stack $P$ is empty, reject (an endpoint lies past the last vertex);
otherwise pop two bits $a$, $b$ off $P$, push them onto the scratch stack $T$ in that order (so
$b$ ends on top), and go to the label $f(a, b)$. A missing or non-bit symbol is read as $0$.
