# The cleanup phase erases the marked tape

For a finite, nonempty alphabet $\Gamma$, starting the canonical one-cell computer in its cleanup state on a contiguous marked tape with head cell $a$, marked cells $l$ to the left and $r$ to the right (which may include marked source blanks), it reaches, in exactly $2|l| + 2|r| + 5$ steps, the halting configuration whose tape holds the single cell $a$ under the head and nothing else. The count includes the passes outward and back on both sides.
