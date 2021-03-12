------------------------- MODULE parse_function_comma_args ---------------------

(* only for parsing, backends cannot yet handle this function *)
p1 == [m, n \in {1}, r \in {2} |-> m]

(* only for parsing, backends cannot yet handle this function *)
p2 == [<<m, n>> \in {1} \X {2}, r \in {3} |-> m]

(* only for parsing, backends cannot yet handle this function *)
f == [1 EXCEPT ![1, 2] = 1]


k == [<<m, n>> \in {1} \X {2} |-> m]


THEOREM k[1, 2] = 1
BY DEF k

================================================================================
