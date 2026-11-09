----------------------- MODULE trailing_identifier_stest -----------------------

\* A trailing identifier is not part of the expression before it.  tlapm
\* discards C, so Left is TRUE and the back-end proves the theorem.

Left == TRUE C

THEOREM Left = TRUE
BY DEF Left

=============================================================================
known: the parser drops a trailing identifier.
SANY rejects this module. Always parse specs with SANY before tlapm.
