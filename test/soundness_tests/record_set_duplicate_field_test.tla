------------- MODULE record_set_duplicate_field_test --------------

\* Reject duplicate fields in a set of records (the Rect parser branch),
\* independently of the check for record constructors using |->.

Records == [a: {1}, a: {2}]

============================================================
result: 3
stderr: a field occurs more than once in a record
