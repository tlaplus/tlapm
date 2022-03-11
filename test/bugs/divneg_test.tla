---- MODULE divneg_test ----

EXTENDS TLAPS, Integers

----

(* Division in TLA+ expects second argument to be positive *)
THEOREM ASSUME NEW m \in Int,
               NEW n \in Int,
               n # 0
        PROVE  (m \div n) \in Int
    OBVIOUS

====
stderr: status:failed
