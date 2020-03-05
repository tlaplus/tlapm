(*  Copyright 2004 INRIA  *)

Require Import zenon.

Lemma zenon_equiv_init_0 : forall A : Prop,
  ((True <-> (A <-> True)) -> False) -> A -> False.
  Proof. tauto. Qed.

Lemma zenon_equiv_init_1 : forall K A B : Prop,
  (((K <-> (True <-> A)) <-> B) -> False) -> (K <-> (A <-> B)) -> False.
  Proof. tauto. Qed.

Lemma zenon_equiv_init_2 : forall K A B C : Prop,
  ((K <-> (A <-> (B <-> C))) -> False) -> (K <-> ((A <-> B) <-> C)) -> False.
  Proof. tauto. Qed.

Lemma zenon_equiv_init_3 : forall K A B : Prop,
  ((K <-> (A <-> ~B)) -> False) -> (K <-> ~(A <-> B)) -> False.
  Proof. tauto. Qed.

Lemma zenon_equiv_init_4 : forall K A : Prop,
  ((K <-> A) -> False) -> (K <-> ~~A) -> False.
  Proof. tauto. Qed.

Lemma zenon_equiv_init_5 : forall K A B : Prop,
  ((K <-> (A <-> ~B)) -> False) -> (K <-> (~A <-> B)) -> False.
  Proof. tauto. Qed.

Lemma zenon_equiv_init_6 : forall K : Prop,
  (((K <-> True) <-> (True <-> True)) -> False) -> (K <-> True) -> False.
  Proof. tauto. Qed.

Lemma zenon_equiv_init_7 : forall K : Prop,
  (((K <-> True) <-> (False <-> True)) -> False) -> (K <-> ~True) -> False.
  Proof. tauto. Qed.

Lemma zenon_equiv_init_8 : forall K B : Prop,
  ((K <-> B) -> False) -> (K <-> (True <-> B)) -> False.
  Proof. tauto. Qed.

Lemma zenon_equiv_init_9 : forall K B : Prop,
  ((K <-> ~B) -> False) -> (K <-> (False <-> B)) -> False.
  Proof. tauto. Qed.

Lemma zenon_equiv_merge_right : forall X D E F G : Prop,
  (((X <-> D) <-> (F <-> (G <-> E))) -> False)
  -> ((X <-> (D <-> E)) <-> (F <-> G))
  -> False.
  Proof. tauto. Qed.

Let L'1_zenon_equiv_merge_left:(forall T'0:(Prop),(forall T'1:(Prop),((~
(T'1<->T'0))->((~T'1)->((~T'0)->(False)))))).
Proof (fun(T'0:(Prop))(T'1:(Prop))(H'7:(~(T'1<->T'0)))(H'8:(~T'1))(H'9:(
~T'0))=>(zenon_notequiv T'1 T'0 (fun(H'8:(~T'1))(H'b:T'0)=>(H'9 H'b)) (
fun(H'a:T'1)(H'9:(~T'0))=>(H'8 H'a)) H'7)).
Let L'2_zenon_equiv_merge_left:(forall T'4:(Prop),(forall T'3:(Prop),((~
(T'3<->T'4))->(T'4->(T'3->(False)))))).
Proof (fun(T'4:(Prop))(T'3:(Prop))(H'c:(~(T'3<->T'4)))(H'd:T'4)(H'e:T'3)
=>(zenon_notequiv T'3 T'4 (fun(H'10:(~T'3))(H'd:T'4)=>(H'10 H'e)) (fun(
H'e:T'3)(H'f:(~T'4))=>(H'f H'd)) H'c)).
Let L'3_zenon_equiv_merge_left:(forall T'4:(Prop),(forall T'3:(Prop),(
forall T'5:(Prop),((T'5<->(T'3<->T'4))->((~T'5)->(T'4->(T'3->(False)))))
))).
Proof (fun(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'11:(T'5<->(T'3<->T'4)))
(H'12:(~T'5))(H'd:T'4)(H'e:T'3)=>(zenon_equiv T'5 (T'3<->T'4) (fun(H'12
:(~T'5))(H'c:(~(T'3<->T'4)))=>(L'2_zenon_equiv_merge_left T'4 T'3 H'c
H'd H'e)) (fun(H'13:T'5)(H'14:(T'3<->T'4))=>(H'12 H'13)) H'11)).
Let L'4_zenon_equiv_merge_left:(forall T'2:(Prop),(forall T'4:(Prop),(
forall T'3:(Prop),(forall T'5:(Prop),((~T'5)->(((T'5<->(T'3<->T'4))<->
T'2)->(T'2->(T'4->(T'3->(False)))))))))).
Proof (fun(T'2:(Prop))(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'12:(~T'5))(
H'15:((T'5<->(T'3<->T'4))<->T'2))(H'16:T'2)(H'd:T'4)(H'e:T'3)=>(
zenon_equiv (T'5<->(T'3<->T'4)) T'2 (fun(H'18:(~(T'5<->(T'3<->T'4))))(
H'17:(~T'2))=>(H'17 H'16)) (fun(H'11:(T'5<->(T'3<->T'4)))(H'16:T'2)=>(
L'3_zenon_equiv_merge_left T'4 T'3 T'5 H'11 H'12 H'd H'e)) H'15)).
Let L'5_zenon_equiv_merge_left:(forall T'4:(Prop),(forall T'3:(Prop),((
T'3<->T'4)->(T'3->((~T'4)->(False)))))).
Proof (fun(T'4:(Prop))(T'3:(Prop))(H'14:(T'3<->T'4))(H'e:T'3)(H'f:(~T'4)
)=>(zenon_equiv T'3 T'4 (fun(H'10:(~T'3))(H'f:(~T'4))=>(H'10 H'e)) (fun(
H'e:T'3)(H'd:T'4)=>(H'f H'd)) H'14)).
Let L'6_zenon_equiv_merge_left:(forall T'4:(Prop),(forall T'3:(Prop),(
forall T'5:(Prop),((~T'5)->((~(T'5<->(T'3<->T'4)))->(T'3->((~T'4)->(
False)))))))).
Proof (fun(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'12:(~T'5))(H'18:(~(T'5
<->(T'3<->T'4))))(H'e:T'3)(H'f:(~T'4))=>(zenon_notequiv T'5 (T'3<->T'4)
(fun(H'12:(~T'5))(H'14:(T'3<->T'4))=>(L'5_zenon_equiv_merge_left T'4
T'3 H'14 H'e H'f)) (fun(H'13:T'5)(H'c:(~(T'3<->T'4)))=>(H'12 H'13))
H'18)).
Let L'7_zenon_equiv_merge_left:(forall T'2:(Prop),(forall T'4:(Prop),(
forall T'3:(Prop),(forall T'5:(Prop),((~T'5)->(T'2->((~((T'5<->(T'3<->
T'4))<->T'2))->(T'3->((~T'4)->(False)))))))))).
Proof (fun(T'2:(Prop))(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'12:(~T'5))(
H'16:T'2)(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'e:T'3)(H'f:(~T'4))=>(
zenon_notequiv (T'5<->(T'3<->T'4)) T'2 (fun(H'18:(~(T'5<->(T'3<->T'4))))
(H'16:T'2)=>(L'6_zenon_equiv_merge_left T'4 T'3 T'5 H'12 H'18 H'e H'f))
(fun(H'11:(T'5<->(T'3<->T'4)))(H'17:(~T'2))=>(H'17 H'16)) H'19)).
Let L'8_zenon_equiv_merge_left:(forall T'0:(Prop),(forall T'1:(Prop),((
T'1<->T'0)->((~T'1)->(T'0->(False)))))).
Proof (fun(T'0:(Prop))(T'1:(Prop))(H'1a:(T'1<->T'0))(H'8:(~T'1))(H'b
:T'0)=>(zenon_equiv T'1 T'0 (fun(H'8:(~T'1))(H'9:(~T'0))=>(H'9 H'b)) (
fun(H'a:T'1)(H'b:T'0)=>(H'8 H'a)) H'1a)).
Let L'9_zenon_equiv_merge_left:(forall T'0:(Prop),(forall T'1:(Prop),((
T'1<->T'0)->((~T'0)->(T'1->(False)))))).
Proof (fun(T'0:(Prop))(T'1:(Prop))(H'1a:(T'1<->T'0))(H'9:(~T'0))(H'a
:T'1)=>(zenon_equiv T'1 T'0 (fun(H'8:(~T'1))(H'9:(~T'0))=>(H'8 H'a)) (
fun(H'a:T'1)(H'b:T'0)=>(H'9 H'b)) H'1a)).
Let L'10_zenon_equiv_merge_left:(forall T'0:(Prop),(forall T'1:(Prop),((
~(T'1<->T'0))->(T'1->(T'0->(False)))))).
Proof (fun(T'0:(Prop))(T'1:(Prop))(H'7:(~(T'1<->T'0)))(H'a:T'1)(H'b:T'0)
=>(zenon_notequiv T'1 T'0 (fun(H'8:(~T'1))(H'b:T'0)=>(H'8 H'a)) (fun(
H'a:T'1)(H'9:(~T'0))=>(H'9 H'b)) H'7)).
Let L'11_zenon_equiv_merge_left:(forall T'4:(Prop),(forall T'3:(Prop),((
~T'3)->((T'3<->T'4)->(T'4->(False)))))).
Proof (fun(T'4:(Prop))(T'3:(Prop))(H'10:(~T'3))(H'14:(T'3<->T'4))(H'd
:T'4)=>(zenon_equiv T'3 T'4 (fun(H'10:(~T'3))(H'f:(~T'4))=>(H'f H'd)) (
fun(H'e:T'3)(H'd:T'4)=>(H'10 H'e)) H'14)).
Let L'12_zenon_equiv_merge_left:(forall T'4:(Prop),(forall T'3:(Prop),(
forall T'5:(Prop),((~T'3)->((T'5<->(T'3<->T'4))->(T'5->(T'4->(False)))))
))).
Proof (fun(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'10:(~T'3))(H'11:(T'5<->
(T'3<->T'4)))(H'13:T'5)(H'd:T'4)=>(zenon_equiv T'5 (T'3<->T'4) (fun(
H'12:(~T'5))(H'c:(~(T'3<->T'4)))=>(H'12 H'13)) (fun(H'13:T'5)(H'14:(T'3
<->T'4))=>(L'11_zenon_equiv_merge_left T'4 T'3 H'10 H'14 H'd)) H'11)).
Let L'13_zenon_equiv_merge_left:(forall T'2:(Prop),(forall T'4:(Prop),(
forall T'3:(Prop),(forall T'5:(Prop),((~T'3)->(T'5->(((T'5<->(T'3<->T'4)
)<->T'2)->(T'2->(T'4->(False)))))))))).
Proof (fun(T'2:(Prop))(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'10:(~T'3))(
H'13:T'5)(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'16:T'2)(H'd:T'4)=>(
zenon_equiv (T'5<->(T'3<->T'4)) T'2 (fun(H'18:(~(T'5<->(T'3<->T'4))))(
H'17:(~T'2))=>(H'17 H'16)) (fun(H'11:(T'5<->(T'3<->T'4)))(H'16:T'2)=>(
L'12_zenon_equiv_merge_left T'4 T'3 T'5 H'10 H'11 H'13 H'd)) H'15)).
Let L'14_zenon_equiv_merge_left:(forall T'4:(Prop),(forall T'3:(Prop),((
~T'3)->((~(T'3<->T'4))->((~T'4)->(False)))))).
Proof (fun(T'4:(Prop))(T'3:(Prop))(H'10:(~T'3))(H'c:(~(T'3<->T'4)))(H'f
:(~T'4))=>(zenon_notequiv T'3 T'4 (fun(H'10:(~T'3))(H'd:T'4)=>(H'f H'd))
 (fun(H'e:T'3)(H'f:(~T'4))=>(H'10 H'e)) H'c)).
Let L'15_zenon_equiv_merge_left:(forall T'4:(Prop),(forall T'3:(Prop),(
forall T'5:(Prop),((~T'3)->(T'5->((~(T'5<->(T'3<->T'4)))->((~T'4)->(
False)))))))).
Proof (fun(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'10:(~T'3))(H'13:T'5)(
H'18:(~(T'5<->(T'3<->T'4))))(H'f:(~T'4))=>(zenon_notequiv T'5 (T'3<->
T'4) (fun(H'12:(~T'5))(H'14:(T'3<->T'4))=>(H'12 H'13)) (fun(H'13:T'5)(
H'c:(~(T'3<->T'4)))=>(L'14_zenon_equiv_merge_left T'4 T'3 H'10 H'c H'f))
 H'18)).
Let L'16_zenon_equiv_merge_left:(forall T'2:(Prop),(forall T'4:(Prop),(
forall T'3:(Prop),(forall T'5:(Prop),((~T'3)->(T'5->(T'2->((~((T'5<->(
T'3<->T'4))<->T'2))->((~T'4)->(False)))))))))).
Proof (fun(T'2:(Prop))(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'10:(~T'3))(
H'13:T'5)(H'16:T'2)(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'f:(~T'4))=>(
zenon_notequiv (T'5<->(T'3<->T'4)) T'2 (fun(H'18:(~(T'5<->(T'3<->T'4))))
(H'16:T'2)=>(L'15_zenon_equiv_merge_left T'4 T'3 T'5 H'10 H'13 H'18 H'f)
) (fun(H'11:(T'5<->(T'3<->T'4)))(H'17:(~T'2))=>(H'17 H'16)) H'19)).
Let L'17_zenon_equiv_merge_left:(forall T'4:(Prop),(forall T'3:(Prop),(
forall T'5:(Prop),((~T'3)->((~T'5)->((~(T'5<->(T'3<->T'4)))->(T'4->(
False)))))))).
Proof (fun(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'10:(~T'3))(H'12:(~T'5))
(H'18:(~(T'5<->(T'3<->T'4))))(H'd:T'4)=>(zenon_notequiv T'5 (T'3<->T'4)
(fun(H'12:(~T'5))(H'14:(T'3<->T'4))=>(L'11_zenon_equiv_merge_left T'4
T'3 H'10 H'14 H'd)) (fun(H'13:T'5)(H'c:(~(T'3<->T'4)))=>(H'12 H'13))
H'18)).
Let L'18_zenon_equiv_merge_left:(forall T'2:(Prop),(forall T'4:(Prop),(
forall T'3:(Prop),(forall T'5:(Prop),((~T'3)->((~T'5)->(((T'5<->(T'3<->
T'4))<->T'2)->((~T'2)->(T'4->(False)))))))))).
Proof (fun(T'2:(Prop))(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'10:(~T'3))(
H'12:(~T'5))(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'17:(~T'2))(H'd:T'4)=>(
zenon_equiv (T'5<->(T'3<->T'4)) T'2 (fun(H'18:(~(T'5<->(T'3<->T'4))))(
H'17:(~T'2))=>(L'17_zenon_equiv_merge_left T'4 T'3 T'5 H'10 H'12 H'18
H'd)) (fun(H'11:(T'5<->(T'3<->T'4)))(H'16:T'2)=>(H'17 H'16)) H'15)).
Let L'19_zenon_equiv_merge_left:(forall T'4:(Prop),(forall T'3:(Prop),(
forall T'5:(Prop),((~T'3)->((T'5<->(T'3<->T'4))->((~T'5)->((~T'4)->(
False)))))))).
Proof (fun(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'10:(~T'3))(H'11:(T'5<->
(T'3<->T'4)))(H'12:(~T'5))(H'f:(~T'4))=>(zenon_equiv T'5 (T'3<->T'4) (
fun(H'12:(~T'5))(H'c:(~(T'3<->T'4)))=>(L'14_zenon_equiv_merge_left T'4
T'3 H'10 H'c H'f)) (fun(H'13:T'5)(H'14:(T'3<->T'4))=>(H'12 H'13)) H'11))
.
Let L'20_zenon_equiv_merge_left:(forall T'2:(Prop),(forall T'4:(Prop),(
forall T'3:(Prop),(forall T'5:(Prop),((~T'3)->((~T'5)->((~T'2)->((~((
T'5<->(T'3<->T'4))<->T'2))->((~T'4)->(False)))))))))).
Proof (fun(T'2:(Prop))(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'10:(~T'3))(
H'12:(~T'5))(H'17:(~T'2))(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'f:(~
T'4))=>(zenon_notequiv (T'5<->(T'3<->T'4)) T'2 (fun(H'18:(~(T'5<->(T'3
<->T'4))))(H'16:T'2)=>(H'17 H'16)) (fun(H'11:(T'5<->(T'3<->T'4)))(H'17:(
~T'2))=>(L'19_zenon_equiv_merge_left T'4 T'3 T'5 H'10 H'11 H'12 H'f))
H'19)).
Let L'21_zenon_equiv_merge_left:(forall T'4:(Prop),(forall T'3:(Prop),(
forall T'5:(Prop),(T'5->((~(T'5<->(T'3<->T'4)))->(T'4->(T'3->(False)))))
))).
Proof (fun(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'13:T'5)(H'18:(~(T'5<->(
T'3<->T'4))))(H'd:T'4)(H'e:T'3)=>(zenon_notequiv T'5 (T'3<->T'4) (fun(
H'12:(~T'5))(H'14:(T'3<->T'4))=>(H'12 H'13)) (fun(H'13:T'5)(H'c:(~(T'3
<->T'4)))=>(L'2_zenon_equiv_merge_left T'4 T'3 H'c H'd H'e)) H'18)).
Let L'22_zenon_equiv_merge_left:(forall T'2:(Prop),(forall T'4:(Prop),(
forall T'3:(Prop),(forall T'5:(Prop),(T'5->(((T'5<->(T'3<->T'4))<->T'2)
->((~T'2)->(T'4->(T'3->(False)))))))))).
Proof (fun(T'2:(Prop))(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'13:T'5)(
H'15:((T'5<->(T'3<->T'4))<->T'2))(H'17:(~T'2))(H'd:T'4)(H'e:T'3)=>(
zenon_equiv (T'5<->(T'3<->T'4)) T'2 (fun(H'18:(~(T'5<->(T'3<->T'4))))(
H'17:(~T'2))=>(L'21_zenon_equiv_merge_left T'4 T'3 T'5 H'13 H'18 H'd
H'e)) (fun(H'11:(T'5<->(T'3<->T'4)))(H'16:T'2)=>(H'17 H'16)) H'15)).
Let L'23_zenon_equiv_merge_left:(forall T'4:(Prop),(forall T'3:(Prop),(
forall T'5:(Prop),((T'5<->(T'3<->T'4))->(T'5->(T'3->((~T'4)->(False)))))
))).
Proof (fun(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'11:(T'5<->(T'3<->T'4)))
(H'13:T'5)(H'e:T'3)(H'f:(~T'4))=>(zenon_equiv T'5 (T'3<->T'4) (fun(H'12
:(~T'5))(H'c:(~(T'3<->T'4)))=>(H'12 H'13)) (fun(H'13:T'5)(H'14:(T'3<->
T'4))=>(L'5_zenon_equiv_merge_left T'4 T'3 H'14 H'e H'f)) H'11)).
Let L'24_zenon_equiv_merge_left:(forall T'2:(Prop),(forall T'4:(Prop),(
forall T'3:(Prop),(forall T'5:(Prop),(T'5->((~T'2)->((~((T'5<->(T'3<->
T'4))<->T'2))->(T'3->((~T'4)->(False)))))))))).
Proof (fun(T'2:(Prop))(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'13:T'5)(
H'17:(~T'2))(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'e:T'3)(H'f:(~T'4))=>
(zenon_notequiv (T'5<->(T'3<->T'4)) T'2 (fun(H'18:(~(T'5<->(T'3<->T'4)))
)(H'16:T'2)=>(H'17 H'16)) (fun(H'11:(T'5<->(T'3<->T'4)))(H'17:(~T'2))=>(
L'23_zenon_equiv_merge_left T'4 T'3 T'5 H'11 H'13 H'e H'f)) H'19)).
Let L'25_zenon_equiv_merge_left:(forall T'2:(Prop),(forall T'4:(Prop),(
forall T'3:(Prop),(forall T'5:(Prop),((~T'5)->(((T'5<->(T'3<->T'4))<->
T'2)->((~T'2)->(T'3->((~T'4)->(False)))))))))).
Proof (fun(T'2:(Prop))(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'12:(~T'5))(
H'15:((T'5<->(T'3<->T'4))<->T'2))(H'17:(~T'2))(H'e:T'3)(H'f:(~T'4))=>(
zenon_equiv (T'5<->(T'3<->T'4)) T'2 (fun(H'18:(~(T'5<->(T'3<->T'4))))(
H'17:(~T'2))=>(L'6_zenon_equiv_merge_left T'4 T'3 T'5 H'12 H'18 H'e H'f)
) (fun(H'11:(T'5<->(T'3<->T'4)))(H'16:T'2)=>(H'17 H'16)) H'15)).
Let L'26_zenon_equiv_merge_left:(forall T'2:(Prop),(forall T'4:(Prop),(
forall T'3:(Prop),(forall T'5:(Prop),((~T'5)->((~T'2)->((~((T'5<->(T'3
<->T'4))<->T'2))->(T'4->(T'3->(False)))))))))).
Proof (fun(T'2:(Prop))(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'12:(~T'5))(
H'17:(~T'2))(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'd:T'4)(H'e:T'3)=>(
zenon_notequiv (T'5<->(T'3<->T'4)) T'2 (fun(H'18:(~(T'5<->(T'3<->T'4))))
(H'16:T'2)=>(H'17 H'16)) (fun(H'11:(T'5<->(T'3<->T'4)))(H'17:(~T'2))=>(
L'3_zenon_equiv_merge_left T'4 T'3 T'5 H'11 H'12 H'd H'e)) H'19)).
Let L'27_zenon_equiv_merge_left:(forall T'2:(Prop),(forall T'4:(Prop),(
forall T'3:(Prop),(forall T'5:(Prop),((~T'3)->(T'5->(((T'5<->(T'3<->T'4)
)<->T'2)->((~T'2)->((~T'4)->(False)))))))))).
Proof (fun(T'2:(Prop))(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'10:(~T'3))(
H'13:T'5)(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'17:(~T'2))(H'f:(~T'4))=>(
zenon_equiv (T'5<->(T'3<->T'4)) T'2 (fun(H'18:(~(T'5<->(T'3<->T'4))))(
H'17:(~T'2))=>(L'15_zenon_equiv_merge_left T'4 T'3 T'5 H'10 H'13 H'18
H'f)) (fun(H'11:(T'5<->(T'3<->T'4)))(H'16:T'2)=>(H'17 H'16)) H'15)).
Let L'28_zenon_equiv_merge_left:(forall T'2:(Prop),(forall T'4:(Prop),(
forall T'3:(Prop),(forall T'5:(Prop),((~T'3)->(T'5->((~T'2)->((~((T'5<->
(T'3<->T'4))<->T'2))->(T'4->(False)))))))))).
Proof (fun(T'2:(Prop))(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'10:(~T'3))(
H'13:T'5)(H'17:(~T'2))(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'd:T'4)=>(
zenon_notequiv (T'5<->(T'3<->T'4)) T'2 (fun(H'18:(~(T'5<->(T'3<->T'4))))
(H'16:T'2)=>(H'17 H'16)) (fun(H'11:(T'5<->(T'3<->T'4)))(H'17:(~T'2))=>(
L'12_zenon_equiv_merge_left T'4 T'3 T'5 H'10 H'11 H'13 H'd)) H'19)).
Let L'29_zenon_equiv_merge_left:(forall T'2:(Prop),(forall T'4:(Prop),(
forall T'3:(Prop),(forall T'5:(Prop),((~T'3)->((~T'5)->(((T'5<->(T'3<->
T'4))<->T'2)->(T'2->((~T'4)->(False)))))))))).
Proof (fun(T'2:(Prop))(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'10:(~T'3))(
H'12:(~T'5))(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'16:T'2)(H'f:(~T'4))=>(
zenon_equiv (T'5<->(T'3<->T'4)) T'2 (fun(H'18:(~(T'5<->(T'3<->T'4))))(
H'17:(~T'2))=>(H'17 H'16)) (fun(H'11:(T'5<->(T'3<->T'4)))(H'16:T'2)=>(
L'19_zenon_equiv_merge_left T'4 T'3 T'5 H'10 H'11 H'12 H'f)) H'15)).
Let L'30_zenon_equiv_merge_left:(forall T'2:(Prop),(forall T'4:(Prop),(
forall T'3:(Prop),(forall T'5:(Prop),((~T'3)->((~T'5)->(T'2->((~((T'5<->
(T'3<->T'4))<->T'2))->(T'4->(False)))))))))).
Proof (fun(T'2:(Prop))(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'10:(~T'3))(
H'12:(~T'5))(H'16:T'2)(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'd:T'4)=>(
zenon_notequiv (T'5<->(T'3<->T'4)) T'2 (fun(H'18:(~(T'5<->(T'3<->T'4))))
(H'16:T'2)=>(L'17_zenon_equiv_merge_left T'4 T'3 T'5 H'10 H'12 H'18 H'd)
) (fun(H'11:(T'5<->(T'3<->T'4)))(H'17:(~T'2))=>(H'17 H'16)) H'19)).
Let L'31_zenon_equiv_merge_left:(forall T'2:(Prop),(forall T'4:(Prop),(
forall T'3:(Prop),(forall T'5:(Prop),(T'5->(((T'5<->(T'3<->T'4))<->T'2)
->(T'2->(T'3->((~T'4)->(False)))))))))).
Proof (fun(T'2:(Prop))(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'13:T'5)(
H'15:((T'5<->(T'3<->T'4))<->T'2))(H'16:T'2)(H'e:T'3)(H'f:(~T'4))=>(
zenon_equiv (T'5<->(T'3<->T'4)) T'2 (fun(H'18:(~(T'5<->(T'3<->T'4))))(
H'17:(~T'2))=>(H'17 H'16)) (fun(H'11:(T'5<->(T'3<->T'4)))(H'16:T'2)=>(
L'23_zenon_equiv_merge_left T'4 T'3 T'5 H'11 H'13 H'e H'f)) H'15)).
Let L'32_zenon_equiv_merge_left:(forall T'2:(Prop),(forall T'4:(Prop),(
forall T'3:(Prop),(forall T'5:(Prop),(T'5->(T'2->((~((T'5<->(T'3<->T'4))
<->T'2))->(T'4->(T'3->(False)))))))))).
Proof (fun(T'2:(Prop))(T'4:(Prop))(T'3:(Prop))(T'5:(Prop))(H'13:T'5)(
H'16:T'2)(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'd:T'4)(H'e:T'3)=>(
zenon_notequiv (T'5<->(T'3<->T'4)) T'2 (fun(H'18:(~(T'5<->(T'3<->T'4))))
(H'16:T'2)=>(L'21_zenon_equiv_merge_left T'4 T'3 T'5 H'13 H'18 H'd H'e))
 (fun(H'11:(T'5<->(T'3<->T'4)))(H'17:(~T'2))=>(H'17 H'16)) H'19)).

Definition zenon_equiv_merge_left:(forall A:(Prop),(forall B:(Prop),(
forall C:(Prop),(forall Y:(Prop),(forall F:(Prop),(forall G:(Prop),
  (((((A<->B)<->Y)<->(F<->(G<->C)))->False)->
  ((((A<->(B<->C))<->Y)<->(F<->G))->False))))))))
:=

(NNPP _ (fun z'g:(~(forall A:(Prop),(forall B:(Prop),(forall C:(Prop),(
forall Y:(Prop),(forall F:(Prop),(forall G:(Prop),(((((A<->B)<->Y)<->(F
<->(G<->C)))->False)->((((A<->(B<->C))<->Y)<->(F<->G))->False)))))))))=>
(zenon_notall (Prop) (fun A:(Prop)=>(forall B:(Prop),(forall C:(Prop),(
forall Y:(Prop),(forall F:(Prop),(forall G:(Prop),(((((A<->B)<->Y)<->(F
<->(G<->C)))->False)->((((A<->(B<->C))<->Y)<->(F<->G))->False)))))))) (
fun(T'5:(Prop))(H'2e:(~(forall B:(Prop),(forall C:(Prop),(forall Y:(
Prop),(forall F:(Prop),(forall G:(Prop),(((((T'5<->B)<->Y)<->(F<->(G<->
C)))->False)->((((T'5<->(B<->C))<->Y)<->(F<->G))->False)))))))))=>(
zenon_notall (Prop) (fun B:(Prop)=>(forall C:(Prop),(forall Y:(Prop),(
forall F:(Prop),(forall G:(Prop),(((((T'5<->B)<->Y)<->(F<->(G<->C)))->
False)->((((T'5<->(B<->C))<->Y)<->(F<->G))->False))))))) (fun(T'3:(Prop)
)(H'2d:(~(forall C:(Prop),(forall Y:(Prop),(forall F:(Prop),(forall G:(
Prop),(((((T'5<->T'3)<->Y)<->(F<->(G<->C)))->False)->((((T'5<->(T'3<->C)
)<->Y)<->(F<->G))->False))))))))=>(zenon_notall (Prop) (fun C:(Prop)=>(
forall Y:(Prop),(forall F:(Prop),(forall G:(Prop),(((((T'5<->T'3)<->Y)
<->(F<->(G<->C)))->False)->((((T'5<->(T'3<->C))<->Y)<->(F<->G))->False))
)))) (fun(T'4:(Prop))(H'2c:(~(forall Y:(Prop),(forall F:(Prop),(forall
G:(Prop),(((((T'5<->T'3)<->Y)<->(F<->(G<->T'4)))->False)->((((T'5<->(
T'3<->T'4))<->Y)<->(F<->G))->False)))))))=>(zenon_notall (Prop) (fun Y:(
Prop)=>(forall F:(Prop),(forall G:(Prop),(((((T'5<->T'3)<->Y)<->(F<->(G
<->T'4)))->False)->((((T'5<->(T'3<->T'4))<->Y)<->(F<->G))->False))))) (
fun(T'2:(Prop))(H'2b:(~(forall F:(Prop),(forall G:(Prop),(((((T'5<->T'3)
<->T'2)<->(F<->(G<->T'4)))->False)->((((T'5<->(T'3<->T'4))<->T'2)<->(F
<->G))->False))))))=>(zenon_notall (Prop) (fun F:(Prop)=>(forall G:(
Prop),(((((T'5<->T'3)<->T'2)<->(F<->(G<->T'4)))->False)->((((T'5<->(T'3
<->T'4))<->T'2)<->(F<->G))->False)))) (fun(T'1:(Prop))(H'2a:(~(forall G
:(Prop),(((((T'5<->T'3)<->T'2)<->(T'1<->(G<->T'4)))->False)->((((T'5<->(
T'3<->T'4))<->T'2)<->(T'1<->G))->False)))))=>(zenon_notall (Prop) (fun
G:(Prop)=>(((((T'5<->T'3)<->T'2)<->(T'1<->(G<->T'4)))->False)->((((T'5
<->(T'3<->T'4))<->T'2)<->(T'1<->G))->False))) (fun(T'0:(Prop))(H'29:(~((
(((T'5<->T'3)<->T'2)<->(T'1<->(T'0<->T'4)))->False)->((((T'5<->(T'3<->
T'4))<->T'2)<->(T'1<->T'0))->False))))=>(zenon_notimply ((((T'5<->T'3)
<->T'2)<->(T'1<->(T'0<->T'4)))->False) ((((T'5<->(T'3<->T'4))<->T'2)<->(
T'1<->T'0))->False) (fun(H'26:((((T'5<->T'3)<->T'2)<->(T'1<->(T'0<->T'4)
))->False))(H'28:(~((((T'5<->(T'3<->T'4))<->T'2)<->(T'1<->T'0))->False))
)=>(zenon_notimply (((T'5<->(T'3<->T'4))<->T'2)<->(T'1<->T'0)) False (
fun(H'1c:(((T'5<->(T'3<->T'4))<->T'2)<->(T'1<->T'0)))(H'27:(~False))=>(
zenon_imply (((T'5<->T'3)<->T'2)<->(T'1<->(T'0<->T'4))) False (fun H'25
:(~(((T'5<->T'3)<->T'2)<->(T'1<->(T'0<->T'4))))=>(zenon_notequiv ((T'5
<->T'3)<->T'2) (T'1<->(T'0<->T'4)) (fun(H'24:(~((T'5<->T'3)<->T'2)))(
H'23:(T'1<->(T'0<->T'4)))=>(zenon_notequiv (T'5<->T'3) T'2 (fun(H'21:(~(
T'5<->T'3)))(H'16:T'2)=>(zenon_notequiv T'5 T'3 (fun(H'12:(~T'5))(H'e
:T'3)=>(zenon_equiv T'1 (T'0<->T'4) (fun(H'8:(~T'1))(H'1d:(~(T'0<->T'4))
)=>(zenon_notequiv T'0 T'4 (fun(H'9:(~T'0))(H'd:T'4)=>(zenon_equiv ((
T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(H'19:(~((T'5<->(T'3<->T'4))
<->T'2)))(H'7:(~(T'1<->T'0)))=>(L'1_zenon_equiv_merge_left T'0 T'1 H'7
H'8 H'9)) (fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(
L'4_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'12 H'15 H'16 H'd H'e))
H'1c)) (fun(H'b:T'0)(H'f:(~T'4))=>(zenon_equiv ((T'5<->(T'3<->T'4))<->
T'2) (T'1<->T'0) (fun(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->
T'0)))=>(L'7_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'12 H'16 H'19 H'e
H'f)) (fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(
L'8_zenon_equiv_merge_left T'0 T'1 H'1a H'8 H'b)) H'1c)) H'1d)) (fun(
H'a:T'1)(H'1e:(T'0<->T'4))=>(zenon_equiv T'0 T'4 (fun(H'9:(~T'0))(H'f:(~
T'4))=>(zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(H'19:(~
((T'5<->(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(
L'7_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'12 H'16 H'19 H'e H'f)) (
fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(
L'9_zenon_equiv_merge_left T'0 T'1 H'1a H'9 H'a)) H'1c)) (fun(H'b:T'0)(
H'd:T'4)=>(zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(
H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(
L'10_zenon_equiv_merge_left T'0 T'1 H'7 H'a H'b)) (fun(H'15:((T'5<->(
T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(L'4_zenon_equiv_merge_left T'2
T'4 T'3 T'5 H'12 H'15 H'16 H'd H'e)) H'1c)) H'1e)) H'23)) (fun(H'13:T'5)
(H'10:(~T'3))=>(zenon_equiv T'1 (T'0<->T'4) (fun(H'8:(~T'1))(H'1d:(~(
T'0<->T'4)))=>(zenon_notequiv T'0 T'4 (fun(H'9:(~T'0))(H'd:T'4)=>(
zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(H'19:(~((T'5<->
(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(L'1_zenon_equiv_merge_left
T'0 T'1 H'7 H'8 H'9)) (fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1
<->T'0))=>(L'13_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'10 H'13 H'15
H'16 H'd)) H'1c)) (fun(H'b:T'0)(H'f:(~T'4))=>(zenon_equiv ((T'5<->(T'3
<->T'4))<->T'2) (T'1<->T'0) (fun(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(
H'7:(~(T'1<->T'0)))=>(L'16_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'10
H'13 H'16 H'19 H'f)) (fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1<->
T'0))=>(L'8_zenon_equiv_merge_left T'0 T'1 H'1a H'8 H'b)) H'1c)) H'1d))
(fun(H'a:T'1)(H'1e:(T'0<->T'4))=>(zenon_equiv T'0 T'4 (fun(H'9:(~T'0))(
H'f:(~T'4))=>(zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(
H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(
L'16_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'10 H'13 H'16 H'19 H'f)) (
fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(
L'9_zenon_equiv_merge_left T'0 T'1 H'1a H'9 H'a)) H'1c)) (fun(H'b:T'0)(
H'd:T'4)=>(zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(
H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(
L'10_zenon_equiv_merge_left T'0 T'1 H'7 H'a H'b)) (fun(H'15:((T'5<->(
T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(L'13_zenon_equiv_merge_left T'2
T'4 T'3 T'5 H'10 H'13 H'15 H'16 H'd)) H'1c)) H'1e)) H'23)) H'21)) (fun(
H'20:(T'5<->T'3))(H'17:(~T'2))=>(zenon_equiv T'5 T'3 (fun(H'12:(~T'5))(
H'10:(~T'3))=>(zenon_equiv T'1 (T'0<->T'4) (fun(H'8:(~T'1))(H'1d:(~(T'0
<->T'4)))=>(zenon_notequiv T'0 T'4 (fun(H'9:(~T'0))(H'd:T'4)=>(
zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(H'19:(~((T'5<->
(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(L'1_zenon_equiv_merge_left
T'0 T'1 H'7 H'8 H'9)) (fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1
<->T'0))=>(L'18_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'10 H'12 H'15
H'17 H'd)) H'1c)) (fun(H'b:T'0)(H'f:(~T'4))=>(zenon_equiv ((T'5<->(T'3
<->T'4))<->T'2) (T'1<->T'0) (fun(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(
H'7:(~(T'1<->T'0)))=>(L'20_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'10
H'12 H'17 H'19 H'f)) (fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1<->
T'0))=>(L'8_zenon_equiv_merge_left T'0 T'1 H'1a H'8 H'b)) H'1c)) H'1d))
(fun(H'a:T'1)(H'1e:(T'0<->T'4))=>(zenon_equiv T'0 T'4 (fun(H'9:(~T'0))(
H'f:(~T'4))=>(zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(
H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(
L'20_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'10 H'12 H'17 H'19 H'f)) (
fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(
L'9_zenon_equiv_merge_left T'0 T'1 H'1a H'9 H'a)) H'1c)) (fun(H'b:T'0)(
H'd:T'4)=>(zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(
H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(
L'10_zenon_equiv_merge_left T'0 T'1 H'7 H'a H'b)) (fun(H'15:((T'5<->(
T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(L'18_zenon_equiv_merge_left T'2
T'4 T'3 T'5 H'10 H'12 H'15 H'17 H'd)) H'1c)) H'1e)) H'23)) (fun(H'13
:T'5)(H'e:T'3)=>(zenon_equiv T'1 (T'0<->T'4) (fun(H'8:(~T'1))(H'1d:(~(
T'0<->T'4)))=>(zenon_notequiv T'0 T'4 (fun(H'9:(~T'0))(H'd:T'4)=>(
zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(H'19:(~((T'5<->
(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(L'1_zenon_equiv_merge_left
T'0 T'1 H'7 H'8 H'9)) (fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1
<->T'0))=>(L'22_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'13 H'15 H'17
H'd H'e)) H'1c)) (fun(H'b:T'0)(H'f:(~T'4))=>(zenon_equiv ((T'5<->(T'3<->
T'4))<->T'2) (T'1<->T'0) (fun(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(
~(T'1<->T'0)))=>(L'24_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'13 H'17
H'19 H'e H'f)) (fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))
=>(L'8_zenon_equiv_merge_left T'0 T'1 H'1a H'8 H'b)) H'1c)) H'1d)) (fun(
H'a:T'1)(H'1e:(T'0<->T'4))=>(zenon_equiv T'0 T'4 (fun(H'9:(~T'0))(H'f:(~
T'4))=>(zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(H'19:(~
((T'5<->(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(
L'24_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'13 H'17 H'19 H'e H'f)) (
fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(
L'9_zenon_equiv_merge_left T'0 T'1 H'1a H'9 H'a)) H'1c)) (fun(H'b:T'0)(
H'd:T'4)=>(zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(
H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(
L'10_zenon_equiv_merge_left T'0 T'1 H'7 H'a H'b)) (fun(H'15:((T'5<->(
T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(L'22_zenon_equiv_merge_left T'2
T'4 T'3 T'5 H'13 H'15 H'17 H'd H'e)) H'1c)) H'1e)) H'23)) H'20)) H'24))
(fun(H'22:((T'5<->T'3)<->T'2))(H'1f:(~(T'1<->(T'0<->T'4))))=>(
zenon_equiv (T'5<->T'3) T'2 (fun(H'21:(~(T'5<->T'3)))(H'17:(~T'2))=>(
zenon_notequiv T'5 T'3 (fun(H'12:(~T'5))(H'e:T'3)=>(zenon_notequiv T'1 (
T'0<->T'4) (fun(H'8:(~T'1))(H'1e:(T'0<->T'4))=>(zenon_equiv T'0 T'4 (
fun(H'9:(~T'0))(H'f:(~T'4))=>(zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (
T'1<->T'0) (fun(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))
=>(L'1_zenon_equiv_merge_left T'0 T'1 H'7 H'8 H'9)) (fun(H'15:((T'5<->(
T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(L'25_zenon_equiv_merge_left T'2
T'4 T'3 T'5 H'12 H'15 H'17 H'e H'f)) H'1c)) (fun(H'b:T'0)(H'd:T'4)=>(
zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(H'19:(~((T'5<->
(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(L'26_zenon_equiv_merge_left
T'2 T'4 T'3 T'5 H'12 H'17 H'19 H'd H'e)) (fun(H'15:((T'5<->(T'3<->T'4))
<->T'2))(H'1a:(T'1<->T'0))=>(L'8_zenon_equiv_merge_left T'0 T'1 H'1a
H'8 H'b)) H'1c)) H'1e)) (fun(H'a:T'1)(H'1d:(~(T'0<->T'4)))=>(
zenon_notequiv T'0 T'4 (fun(H'9:(~T'0))(H'd:T'4)=>(zenon_equiv ((T'5<->(
T'3<->T'4))<->T'2) (T'1<->T'0) (fun(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))
(H'7:(~(T'1<->T'0)))=>(L'26_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'12
H'17 H'19 H'd H'e)) (fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1<->
T'0))=>(L'9_zenon_equiv_merge_left T'0 T'1 H'1a H'9 H'a)) H'1c)) (fun(
H'b:T'0)(H'f:(~T'4))=>(zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->
T'0) (fun(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(
L'10_zenon_equiv_merge_left T'0 T'1 H'7 H'a H'b)) (fun(H'15:((T'5<->(
T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(L'25_zenon_equiv_merge_left T'2
T'4 T'3 T'5 H'12 H'15 H'17 H'e H'f)) H'1c)) H'1d)) H'1f)) (fun(H'13:T'5)
(H'10:(~T'3))=>(zenon_notequiv T'1 (T'0<->T'4) (fun(H'8:(~T'1))(H'1e:(
T'0<->T'4))=>(zenon_equiv T'0 T'4 (fun(H'9:(~T'0))(H'f:(~T'4))=>(
zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(H'19:(~((T'5<->
(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(L'1_zenon_equiv_merge_left
T'0 T'1 H'7 H'8 H'9)) (fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1
<->T'0))=>(L'27_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'10 H'13 H'15
H'17 H'f)) H'1c)) (fun(H'b:T'0)(H'd:T'4)=>(zenon_equiv ((T'5<->(T'3<->
T'4))<->T'2) (T'1<->T'0) (fun(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(
~(T'1<->T'0)))=>(L'28_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'10 H'13
H'17 H'19 H'd)) (fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))
=>(L'8_zenon_equiv_merge_left T'0 T'1 H'1a H'8 H'b)) H'1c)) H'1e)) (fun(
H'a:T'1)(H'1d:(~(T'0<->T'4)))=>(zenon_notequiv T'0 T'4 (fun(H'9:(~T'0))(
H'd:T'4)=>(zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(
H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(
L'28_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'10 H'13 H'17 H'19 H'd)) (
fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(
L'9_zenon_equiv_merge_left T'0 T'1 H'1a H'9 H'a)) H'1c)) (fun(H'b:T'0)(
H'f:(~T'4))=>(zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(
H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(
L'10_zenon_equiv_merge_left T'0 T'1 H'7 H'a H'b)) (fun(H'15:((T'5<->(
T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(L'27_zenon_equiv_merge_left T'2
T'4 T'3 T'5 H'10 H'13 H'15 H'17 H'f)) H'1c)) H'1d)) H'1f)) H'21)) (fun(
H'20:(T'5<->T'3))(H'16:T'2)=>(zenon_equiv T'5 T'3 (fun(H'12:(~T'5))(
H'10:(~T'3))=>(zenon_notequiv T'1 (T'0<->T'4) (fun(H'8:(~T'1))(H'1e:(
T'0<->T'4))=>(zenon_equiv T'0 T'4 (fun(H'9:(~T'0))(H'f:(~T'4))=>(
zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(H'19:(~((T'5<->
(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(L'1_zenon_equiv_merge_left
T'0 T'1 H'7 H'8 H'9)) (fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1
<->T'0))=>(L'29_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'10 H'12 H'15
H'16 H'f)) H'1c)) (fun(H'b:T'0)(H'd:T'4)=>(zenon_equiv ((T'5<->(T'3<->
T'4))<->T'2) (T'1<->T'0) (fun(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(
~(T'1<->T'0)))=>(L'30_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'10 H'12
H'16 H'19 H'd)) (fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))
=>(L'8_zenon_equiv_merge_left T'0 T'1 H'1a H'8 H'b)) H'1c)) H'1e)) (fun(
H'a:T'1)(H'1d:(~(T'0<->T'4)))=>(zenon_notequiv T'0 T'4 (fun(H'9:(~T'0))(
H'd:T'4)=>(zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(
H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(
L'30_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'10 H'12 H'16 H'19 H'd)) (
fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(
L'9_zenon_equiv_merge_left T'0 T'1 H'1a H'9 H'a)) H'1c)) (fun(H'b:T'0)(
H'f:(~T'4))=>(zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(
H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(
L'10_zenon_equiv_merge_left T'0 T'1 H'7 H'a H'b)) (fun(H'15:((T'5<->(
T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(L'29_zenon_equiv_merge_left T'2
T'4 T'3 T'5 H'10 H'12 H'15 H'16 H'f)) H'1c)) H'1d)) H'1f)) (fun(H'13
:T'5)(H'e:T'3)=>(zenon_notequiv T'1 (T'0<->T'4) (fun(H'8:(~T'1))(H'1e:(
T'0<->T'4))=>(zenon_equiv T'0 T'4 (fun(H'9:(~T'0))(H'f:(~T'4))=>(
zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(H'19:(~((T'5<->
(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(L'1_zenon_equiv_merge_left
T'0 T'1 H'7 H'8 H'9)) (fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1
<->T'0))=>(L'31_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'13 H'15 H'16
H'e H'f)) H'1c)) (fun(H'b:T'0)(H'd:T'4)=>(zenon_equiv ((T'5<->(T'3<->
T'4))<->T'2) (T'1<->T'0) (fun(H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(
~(T'1<->T'0)))=>(L'32_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'13 H'16
H'19 H'd H'e)) (fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))
=>(L'8_zenon_equiv_merge_left T'0 T'1 H'1a H'8 H'b)) H'1c)) H'1e)) (fun(
H'a:T'1)(H'1d:(~(T'0<->T'4)))=>(zenon_notequiv T'0 T'4 (fun(H'9:(~T'0))(
H'd:T'4)=>(zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(
H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(
L'32_zenon_equiv_merge_left T'2 T'4 T'3 T'5 H'13 H'16 H'19 H'd H'e)) (
fun(H'15:((T'5<->(T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(
L'9_zenon_equiv_merge_left T'0 T'1 H'1a H'9 H'a)) H'1c)) (fun(H'b:T'0)(
H'f:(~T'4))=>(zenon_equiv ((T'5<->(T'3<->T'4))<->T'2) (T'1<->T'0) (fun(
H'19:(~((T'5<->(T'3<->T'4))<->T'2)))(H'7:(~(T'1<->T'0)))=>(
L'10_zenon_equiv_merge_left T'0 T'1 H'7 H'a H'b)) (fun(H'15:((T'5<->(
T'3<->T'4))<->T'2))(H'1a:(T'1<->T'0))=>(L'31_zenon_equiv_merge_left T'2
T'4 T'3 T'5 H'13 H'15 H'16 H'e H'f)) H'1c)) H'1d)) H'1f)) H'20)) H'22))
H'25)) (fun H'1b:False=>H'1b) H'26)) H'28)) H'29)) H'2a)) H'2b)) H'2c))
H'2d)) H'2e)) z'g))).

Lemma zenon_equiv_merge_1 : forall A L Q : Prop,
  ((A <-> ((Q <-> L) <-> True)) -> False)
  -> ((A <-> L) <-> (Q <-> True))
  -> False.
  Proof. tauto. Qed.

Lemma zenon_equiv_simplify : forall A L M N : Prop,
  ((L <-> (M <-> N)) -> False) -> (L <-> (M <-> ((N <-> A) <-> A))) -> False.
  Proof. tauto. Qed.

Lemma zenon_equiv_merge_simplify : forall A B C D Z : Prop,
  ((((A <-> B) <-> D) <-> Z) -> False)
  -> (((A <-> (B <-> C)) <-> (D <-> C)) <-> Z)
  -> False.
  Proof. tauto. Qed.

Lemma zenon_equiv_inner_loop : forall L A B : Prop,
  ((L <-> ((A <-> True) <-> B)) -> False)
  -> (((L <-> True) <-> True) <-> (A <-> B))
  -> False.
  Proof. tauto. Qed.

Let L'1_zenon_equiv_reverse:(forall T'0:(Prop),(forall T'1:(Prop),((~(
T'1<->T'0))->((~T'1)->((~T'0)->(False)))))).
Proof (fun(T'0:(Prop))(T'1:(Prop))(H'6:(~(T'1<->T'0)))(H'7:(~T'1))(H'8:(
~T'0))=>(zenon_notequiv T'1 T'0 (fun(H'7:(~T'1))(H'a:T'0)=>(H'8 H'a)) (
fun(H'9:T'1)(H'8:(~T'0))=>(H'7 H'9)) H'6)).
Let L'2_zenon_equiv_reverse:(forall T'2:(Prop),(forall T'3:(Prop),((~(
T'3<->T'2))->((~T'3)->((~T'2)->(False)))))).
Proof (fun(T'2:(Prop))(T'3:(Prop))(H'b:(~(T'3<->T'2)))(H'c:(~T'3))(H'd:(
~T'2))=>(zenon_notequiv T'3 T'2 (fun(H'c:(~T'3))(H'f:T'2)=>(H'd H'f)) (
fun(H'e:T'3)(H'd:(~T'2))=>(H'c H'e)) H'b)).
Let L'3_zenon_equiv_reverse:(forall T'2:(Prop),(forall T'3:(Prop),((T'3
<->T'2)->((~T'3)->(T'2->(False)))))).
Proof (fun(T'2:(Prop))(T'3:(Prop))(H'10:(T'3<->T'2))(H'c:(~T'3))(H'f
:T'2)=>(zenon_equiv T'3 T'2 (fun(H'c:(~T'3))(H'd:(~T'2))=>(H'd H'f)) (
fun(H'e:T'3)(H'f:T'2)=>(H'c H'e)) H'10)).
Let L'4_zenon_equiv_reverse:(forall T'0:(Prop),(forall T'1:(Prop),((T'1
<->T'0)->((~T'1)->(T'0->(False)))))).
Proof (fun(T'0:(Prop))(T'1:(Prop))(H'11:(T'1<->T'0))(H'7:(~T'1))(H'a
:T'0)=>(zenon_equiv T'1 T'0 (fun(H'7:(~T'1))(H'8:(~T'0))=>(H'8 H'a)) (
fun(H'9:T'1)(H'a:T'0)=>(H'7 H'9)) H'11)).
Let L'5_zenon_equiv_reverse:(forall T'0:(Prop),(forall T'1:(Prop),((T'1
<->T'0)->((~T'0)->(T'1->(False)))))).
Proof (fun(T'0:(Prop))(T'1:(Prop))(H'11:(T'1<->T'0))(H'8:(~T'0))(H'9
:T'1)=>(zenon_equiv T'1 T'0 (fun(H'7:(~T'1))(H'8:(~T'0))=>(H'7 H'9)) (
fun(H'9:T'1)(H'a:T'0)=>(H'8 H'a)) H'11)).
Let L'6_zenon_equiv_reverse:(forall T'0:(Prop),(forall T'1:(Prop),((~(
T'1<->T'0))->(T'1->(T'0->(False)))))).
Proof (fun(T'0:(Prop))(T'1:(Prop))(H'6:(~(T'1<->T'0)))(H'9:T'1)(H'a:T'0)
=>(zenon_notequiv T'1 T'0 (fun(H'7:(~T'1))(H'a:T'0)=>(H'7 H'9)) (fun(
H'9:T'1)(H'8:(~T'0))=>(H'8 H'a)) H'6)).
Let L'7_zenon_equiv_reverse:(forall T'2:(Prop),(forall T'3:(Prop),((~(
T'3<->T'2))->(T'3->(T'2->(False)))))).
Proof (fun(T'2:(Prop))(T'3:(Prop))(H'b:(~(T'3<->T'2)))(H'e:T'3)(H'f:T'2)
=>(zenon_notequiv T'3 T'2 (fun(H'c:(~T'3))(H'f:T'2)=>(H'c H'e)) (fun(
H'e:T'3)(H'd:(~T'2))=>(H'd H'f)) H'b)).
Let L'8_zenon_equiv_reverse:(forall T'2:(Prop),(forall T'3:(Prop),((T'3
<->T'2)->((~T'2)->(T'3->(False)))))).
Proof (fun(T'2:(Prop))(T'3:(Prop))(H'10:(T'3<->T'2))(H'd:(~T'2))(H'e
:T'3)=>(zenon_equiv T'3 T'2 (fun(H'c:(~T'3))(H'd:(~T'2))=>(H'c H'e)) (
fun(H'e:T'3)(H'f:T'2)=>(H'd H'f)) H'10)).

Definition zenon_equiv_reverse:(forall L:(Prop),(forall A:(Prop),(
forall B:(Prop),(forall C:(Prop),(forall D:(Prop),
  (((L<->((A<->(B<->D))<->C))->False)->
  ((L<->((A<->B)<->(C<->D)))->False)))))))
:=

(NNPP _ (fun z'g:(~(forall L:(Prop),(forall A:(Prop),(forall B:(Prop),(
forall C:(Prop),(forall D:(Prop),(((L<->((A<->(B<->D))<->C))->False)->((
L<->((A<->B)<->(C<->D)))->False))))))))=>(zenon_notall (Prop) (fun L:(
Prop)=>(forall A:(Prop),(forall B:(Prop),(forall C:(Prop),(forall D:(
Prop),(((L<->((A<->(B<->D))<->C))->False)->((L<->((A<->B)<->(C<->D)))->
False))))))) (fun(T'4:(Prop))(H'26:(~(forall A:(Prop),(forall B:(Prop),(
forall C:(Prop),(forall D:(Prop),(((T'4<->((A<->(B<->D))<->C))->False)->
((T'4<->((A<->B)<->(C<->D)))->False))))))))=>(zenon_notall (Prop) (fun
A:(Prop)=>(forall B:(Prop),(forall C:(Prop),(forall D:(Prop),(((T'4<->((
A<->(B<->D))<->C))->False)->((T'4<->((A<->B)<->(C<->D)))->False)))))) (
fun(T'1:(Prop))(H'25:(~(forall B:(Prop),(forall C:(Prop),(forall D:(
Prop),(((T'4<->((T'1<->(B<->D))<->C))->False)->((T'4<->((T'1<->B)<->(C
<->D)))->False)))))))=>(zenon_notall (Prop) (fun B:(Prop)=>(forall C:(
Prop),(forall D:(Prop),(((T'4<->((T'1<->(B<->D))<->C))->False)->((T'4<->
((T'1<->B)<->(C<->D)))->False))))) (fun(T'0:(Prop))(H'24:(~(forall C:(
Prop),(forall D:(Prop),(((T'4<->((T'1<->(T'0<->D))<->C))->False)->((T'4
<->((T'1<->T'0)<->(C<->D)))->False))))))=>(zenon_notall (Prop) (fun C:(
Prop)=>(forall D:(Prop),(((T'4<->((T'1<->(T'0<->D))<->C))->False)->((
T'4<->((T'1<->T'0)<->(C<->D)))->False)))) (fun(T'3:(Prop))(H'23:(~(
forall D:(Prop),(((T'4<->((T'1<->(T'0<->D))<->T'3))->False)->((T'4<->((
T'1<->T'0)<->(T'3<->D)))->False)))))=>(zenon_notall (Prop) (fun D:(Prop)
=>(((T'4<->((T'1<->(T'0<->D))<->T'3))->False)->((T'4<->((T'1<->T'0)<->(
T'3<->D)))->False))) (fun(T'2:(Prop))(H'22:(~(((T'4<->((T'1<->(T'0<->
T'2))<->T'3))->False)->((T'4<->((T'1<->T'0)<->(T'3<->T'2)))->False))))=>
(zenon_notimply ((T'4<->((T'1<->(T'0<->T'2))<->T'3))->False) ((T'4<->((
T'1<->T'0)<->(T'3<->T'2)))->False) (fun(H'1f:((T'4<->((T'1<->(T'0<->T'2)
)<->T'3))->False))(H'21:(~((T'4<->((T'1<->T'0)<->(T'3<->T'2)))->False)))
=>(zenon_notimply (T'4<->((T'1<->T'0)<->(T'3<->T'2))) False (fun(H'17:(
T'4<->((T'1<->T'0)<->(T'3<->T'2))))(H'20:(~False))=>(zenon_imply (T'4<->
((T'1<->(T'0<->T'2))<->T'3)) False (fun H'1e:(~(T'4<->((T'1<->(T'0<->
T'2))<->T'3)))=>(zenon_notequiv T'4 ((T'1<->(T'0<->T'2))<->T'3) (fun(
H'15:(~T'4))(H'1d:((T'1<->(T'0<->T'2))<->T'3))=>(zenon_equiv (T'1<->(
T'0<->T'2)) T'3 (fun(H'1b:(~(T'1<->(T'0<->T'2))))(H'c:(~T'3))=>(
zenon_notequiv T'1 (T'0<->T'2) (fun(H'7:(~T'1))(H'18:(T'0<->T'2))=>(
zenon_equiv T'0 T'2 (fun(H'8:(~T'0))(H'd:(~T'2))=>(zenon_equiv T'4 ((
T'1<->T'0)<->(T'3<->T'2)) (fun(H'15:(~T'4))(H'16:(~((T'1<->T'0)<->(T'3
<->T'2))))=>(zenon_notequiv (T'1<->T'0) (T'3<->T'2) (fun(H'6:(~(T'1<->
T'0)))(H'10:(T'3<->T'2))=>(L'1_zenon_equiv_reverse T'0 T'1 H'6 H'7 H'8))
 (fun(H'11:(T'1<->T'0))(H'b:(~(T'3<->T'2)))=>(L'2_zenon_equiv_reverse
T'2 T'3 H'b H'c H'd)) H'16)) (fun(H'14:T'4)(H'13:((T'1<->T'0)<->(T'3<->
T'2)))=>(H'15 H'14)) H'17)) (fun(H'a:T'0)(H'f:T'2)=>(zenon_equiv T'4 ((
T'1<->T'0)<->(T'3<->T'2)) (fun(H'15:(~T'4))(H'16:(~((T'1<->T'0)<->(T'3
<->T'2))))=>(zenon_notequiv (T'1<->T'0) (T'3<->T'2) (fun(H'6:(~(T'1<->
T'0)))(H'10:(T'3<->T'2))=>(L'3_zenon_equiv_reverse T'2 T'3 H'10 H'c H'f)
) (fun(H'11:(T'1<->T'0))(H'b:(~(T'3<->T'2)))=>(L'4_zenon_equiv_reverse
T'0 T'1 H'11 H'7 H'a)) H'16)) (fun(H'14:T'4)(H'13:((T'1<->T'0)<->(T'3<->
T'2)))=>(H'15 H'14)) H'17)) H'18)) (fun(H'9:T'1)(H'19:(~(T'0<->T'2)))=>(
zenon_notequiv T'0 T'2 (fun(H'8:(~T'0))(H'f:T'2)=>(zenon_equiv T'4 ((
T'1<->T'0)<->(T'3<->T'2)) (fun(H'15:(~T'4))(H'16:(~((T'1<->T'0)<->(T'3
<->T'2))))=>(zenon_notequiv (T'1<->T'0) (T'3<->T'2) (fun(H'6:(~(T'1<->
T'0)))(H'10:(T'3<->T'2))=>(L'3_zenon_equiv_reverse T'2 T'3 H'10 H'c H'f)
) (fun(H'11:(T'1<->T'0))(H'b:(~(T'3<->T'2)))=>(L'5_zenon_equiv_reverse
T'0 T'1 H'11 H'8 H'9)) H'16)) (fun(H'14:T'4)(H'13:((T'1<->T'0)<->(T'3<->
T'2)))=>(H'15 H'14)) H'17)) (fun(H'a:T'0)(H'd:(~T'2))=>(zenon_equiv T'4
((T'1<->T'0)<->(T'3<->T'2)) (fun(H'15:(~T'4))(H'16:(~((T'1<->T'0)<->(
T'3<->T'2))))=>(zenon_notequiv (T'1<->T'0) (T'3<->T'2) (fun(H'6:(~(T'1
<->T'0)))(H'10:(T'3<->T'2))=>(L'6_zenon_equiv_reverse T'0 T'1 H'6 H'9
H'a)) (fun(H'11:(T'1<->T'0))(H'b:(~(T'3<->T'2)))=>(
L'2_zenon_equiv_reverse T'2 T'3 H'b H'c H'd)) H'16)) (fun(H'14:T'4)(
H'13:((T'1<->T'0)<->(T'3<->T'2)))=>(H'15 H'14)) H'17)) H'19)) H'1b)) (
fun(H'1a:(T'1<->(T'0<->T'2)))(H'e:T'3)=>(zenon_equiv T'1 (T'0<->T'2) (
fun(H'7:(~T'1))(H'19:(~(T'0<->T'2)))=>(zenon_notequiv T'0 T'2 (fun(H'8:(
~T'0))(H'f:T'2)=>(zenon_equiv T'4 ((T'1<->T'0)<->(T'3<->T'2)) (fun(H'15
:(~T'4))(H'16:(~((T'1<->T'0)<->(T'3<->T'2))))=>(zenon_notequiv (T'1<->
T'0) (T'3<->T'2) (fun(H'6:(~(T'1<->T'0)))(H'10:(T'3<->T'2))=>(
L'1_zenon_equiv_reverse T'0 T'1 H'6 H'7 H'8)) (fun(H'11:(T'1<->T'0))(
H'b:(~(T'3<->T'2)))=>(L'7_zenon_equiv_reverse T'2 T'3 H'b H'e H'f))
H'16)) (fun(H'14:T'4)(H'13:((T'1<->T'0)<->(T'3<->T'2)))=>(H'15 H'14))
H'17)) (fun(H'a:T'0)(H'd:(~T'2))=>(zenon_equiv T'4 ((T'1<->T'0)<->(T'3
<->T'2)) (fun(H'15:(~T'4))(H'16:(~((T'1<->T'0)<->(T'3<->T'2))))=>(
zenon_notequiv (T'1<->T'0) (T'3<->T'2) (fun(H'6:(~(T'1<->T'0)))(H'10:(
T'3<->T'2))=>(L'8_zenon_equiv_reverse T'2 T'3 H'10 H'd H'e)) (fun(H'11:(
T'1<->T'0))(H'b:(~(T'3<->T'2)))=>(L'4_zenon_equiv_reverse T'0 T'1 H'11
H'7 H'a)) H'16)) (fun(H'14:T'4)(H'13:((T'1<->T'0)<->(T'3<->T'2)))=>(
H'15 H'14)) H'17)) H'19)) (fun(H'9:T'1)(H'18:(T'0<->T'2))=>(zenon_equiv
T'0 T'2 (fun(H'8:(~T'0))(H'd:(~T'2))=>(zenon_equiv T'4 ((T'1<->T'0)<->(
T'3<->T'2)) (fun(H'15:(~T'4))(H'16:(~((T'1<->T'0)<->(T'3<->T'2))))=>(
zenon_notequiv (T'1<->T'0) (T'3<->T'2) (fun(H'6:(~(T'1<->T'0)))(H'10:(
T'3<->T'2))=>(L'8_zenon_equiv_reverse T'2 T'3 H'10 H'd H'e)) (fun(H'11:(
T'1<->T'0))(H'b:(~(T'3<->T'2)))=>(L'5_zenon_equiv_reverse T'0 T'1 H'11
H'8 H'9)) H'16)) (fun(H'14:T'4)(H'13:((T'1<->T'0)<->(T'3<->T'2)))=>(
H'15 H'14)) H'17)) (fun(H'a:T'0)(H'f:T'2)=>(zenon_equiv T'4 ((T'1<->T'0)
<->(T'3<->T'2)) (fun(H'15:(~T'4))(H'16:(~((T'1<->T'0)<->(T'3<->T'2))))=>
(zenon_notequiv (T'1<->T'0) (T'3<->T'2) (fun(H'6:(~(T'1<->T'0)))(H'10:(
T'3<->T'2))=>(L'6_zenon_equiv_reverse T'0 T'1 H'6 H'9 H'a)) (fun(H'11:(
T'1<->T'0))(H'b:(~(T'3<->T'2)))=>(L'7_zenon_equiv_reverse T'2 T'3 H'b
H'e H'f)) H'16)) (fun(H'14:T'4)(H'13:((T'1<->T'0)<->(T'3<->T'2)))=>(
H'15 H'14)) H'17)) H'18)) H'1a)) H'1d)) (fun(H'14:T'4)(H'1c:(~((T'1<->(
T'0<->T'2))<->T'3)))=>(zenon_notequiv (T'1<->(T'0<->T'2)) T'3 (fun(H'1b
:(~(T'1<->(T'0<->T'2))))(H'e:T'3)=>(zenon_notequiv T'1 (T'0<->T'2) (fun(
H'7:(~T'1))(H'18:(T'0<->T'2))=>(zenon_equiv T'0 T'2 (fun(H'8:(~T'0))(
H'd:(~T'2))=>(zenon_equiv T'4 ((T'1<->T'0)<->(T'3<->T'2)) (fun(H'15:(~
T'4))(H'16:(~((T'1<->T'0)<->(T'3<->T'2))))=>(H'15 H'14)) (fun(H'14:T'4)(
H'13:((T'1<->T'0)<->(T'3<->T'2)))=>(zenon_equiv (T'1<->T'0) (T'3<->T'2)
(fun(H'6:(~(T'1<->T'0)))(H'b:(~(T'3<->T'2)))=>(L'1_zenon_equiv_reverse
T'0 T'1 H'6 H'7 H'8)) (fun(H'11:(T'1<->T'0))(H'10:(T'3<->T'2))=>(
L'8_zenon_equiv_reverse T'2 T'3 H'10 H'd H'e)) H'13)) H'17)) (fun(H'a
:T'0)(H'f:T'2)=>(zenon_equiv T'4 ((T'1<->T'0)<->(T'3<->T'2)) (fun(H'15:(
~T'4))(H'16:(~((T'1<->T'0)<->(T'3<->T'2))))=>(H'15 H'14)) (fun(H'14:T'4)
(H'13:((T'1<->T'0)<->(T'3<->T'2)))=>(zenon_equiv (T'1<->T'0) (T'3<->T'2)
 (fun(H'6:(~(T'1<->T'0)))(H'b:(~(T'3<->T'2)))=>(L'7_zenon_equiv_reverse
T'2 T'3 H'b H'e H'f)) (fun(H'11:(T'1<->T'0))(H'10:(T'3<->T'2))=>(
L'4_zenon_equiv_reverse T'0 T'1 H'11 H'7 H'a)) H'13)) H'17)) H'18)) (
fun(H'9:T'1)(H'19:(~(T'0<->T'2)))=>(zenon_notequiv T'0 T'2 (fun(H'8:(~
T'0))(H'f:T'2)=>(zenon_equiv T'4 ((T'1<->T'0)<->(T'3<->T'2)) (fun(H'15:(
~T'4))(H'16:(~((T'1<->T'0)<->(T'3<->T'2))))=>(H'15 H'14)) (fun(H'14:T'4)
(H'13:((T'1<->T'0)<->(T'3<->T'2)))=>(zenon_equiv (T'1<->T'0) (T'3<->T'2)
 (fun(H'6:(~(T'1<->T'0)))(H'b:(~(T'3<->T'2)))=>(L'7_zenon_equiv_reverse
T'2 T'3 H'b H'e H'f)) (fun(H'11:(T'1<->T'0))(H'10:(T'3<->T'2))=>(
L'5_zenon_equiv_reverse T'0 T'1 H'11 H'8 H'9)) H'13)) H'17)) (fun(H'a
:T'0)(H'd:(~T'2))=>(zenon_equiv T'4 ((T'1<->T'0)<->(T'3<->T'2)) (fun(
H'15:(~T'4))(H'16:(~((T'1<->T'0)<->(T'3<->T'2))))=>(H'15 H'14)) (fun(
H'14:T'4)(H'13:((T'1<->T'0)<->(T'3<->T'2)))=>(zenon_equiv (T'1<->T'0) (
T'3<->T'2) (fun(H'6:(~(T'1<->T'0)))(H'b:(~(T'3<->T'2)))=>(
L'6_zenon_equiv_reverse T'0 T'1 H'6 H'9 H'a)) (fun(H'11:(T'1<->T'0))(
H'10:(T'3<->T'2))=>(L'8_zenon_equiv_reverse T'2 T'3 H'10 H'd H'e)) H'13)
) H'17)) H'19)) H'1b)) (fun(H'1a:(T'1<->(T'0<->T'2)))(H'c:(~T'3))=>(
zenon_equiv T'1 (T'0<->T'2) (fun(H'7:(~T'1))(H'19:(~(T'0<->T'2)))=>(
zenon_notequiv T'0 T'2 (fun(H'8:(~T'0))(H'f:T'2)=>(zenon_equiv T'4 ((
T'1<->T'0)<->(T'3<->T'2)) (fun(H'15:(~T'4))(H'16:(~((T'1<->T'0)<->(T'3
<->T'2))))=>(H'15 H'14)) (fun(H'14:T'4)(H'13:((T'1<->T'0)<->(T'3<->T'2))
)=>(zenon_equiv (T'1<->T'0) (T'3<->T'2) (fun(H'6:(~(T'1<->T'0)))(H'b:(~(
T'3<->T'2)))=>(L'1_zenon_equiv_reverse T'0 T'1 H'6 H'7 H'8)) (fun(H'11:(
T'1<->T'0))(H'10:(T'3<->T'2))=>(L'3_zenon_equiv_reverse T'2 T'3 H'10
H'c H'f)) H'13)) H'17)) (fun(H'a:T'0)(H'd:(~T'2))=>(zenon_equiv T'4 ((
T'1<->T'0)<->(T'3<->T'2)) (fun(H'15:(~T'4))(H'16:(~((T'1<->T'0)<->(T'3
<->T'2))))=>(H'15 H'14)) (fun(H'14:T'4)(H'13:((T'1<->T'0)<->(T'3<->T'2))
)=>(zenon_equiv (T'1<->T'0) (T'3<->T'2) (fun(H'6:(~(T'1<->T'0)))(H'b:(~(
T'3<->T'2)))=>(L'2_zenon_equiv_reverse T'2 T'3 H'b H'c H'd)) (fun(H'11:(
T'1<->T'0))(H'10:(T'3<->T'2))=>(L'4_zenon_equiv_reverse T'0 T'1 H'11
H'7 H'a)) H'13)) H'17)) H'19)) (fun(H'9:T'1)(H'18:(T'0<->T'2))=>(
zenon_equiv T'0 T'2 (fun(H'8:(~T'0))(H'd:(~T'2))=>(zenon_equiv T'4 ((
T'1<->T'0)<->(T'3<->T'2)) (fun(H'15:(~T'4))(H'16:(~((T'1<->T'0)<->(T'3
<->T'2))))=>(H'15 H'14)) (fun(H'14:T'4)(H'13:((T'1<->T'0)<->(T'3<->T'2))
)=>(zenon_equiv (T'1<->T'0) (T'3<->T'2) (fun(H'6:(~(T'1<->T'0)))(H'b:(~(
T'3<->T'2)))=>(L'2_zenon_equiv_reverse T'2 T'3 H'b H'c H'd)) (fun(H'11:(
T'1<->T'0))(H'10:(T'3<->T'2))=>(L'5_zenon_equiv_reverse T'0 T'1 H'11
H'8 H'9)) H'13)) H'17)) (fun(H'a:T'0)(H'f:T'2)=>(zenon_equiv T'4 ((T'1
<->T'0)<->(T'3<->T'2)) (fun(H'15:(~T'4))(H'16:(~((T'1<->T'0)<->(T'3<->
T'2))))=>(H'15 H'14)) (fun(H'14:T'4)(H'13:((T'1<->T'0)<->(T'3<->T'2)))=>
(zenon_equiv (T'1<->T'0) (T'3<->T'2) (fun(H'6:(~(T'1<->T'0)))(H'b:(~(
T'3<->T'2)))=>(L'6_zenon_equiv_reverse T'0 T'1 H'6 H'9 H'a)) (fun(H'11:(
T'1<->T'0))(H'10:(T'3<->T'2))=>(L'3_zenon_equiv_reverse T'2 T'3 H'10
H'c H'f)) H'13)) H'17)) H'18)) H'1a)) H'1c)) H'1e)) (fun H'12:False=>
H'12) H'1f)) H'21)) H'22)) H'23)) H'24)) H'25)) H'26)) z'g))).

Lemma zenon_equiv_outer_loop : forall A Q : Prop,
  ((Q <-> (A <-> True)) -> False) -> (A <-> (Q <-> True)) -> False.
  Proof. tauto. Qed.

Lemma zenon_equiv_finish_0 : forall Q : Prop,
  (Q -> False) -> (True <-> ((True <-> Q) <-> True)) -> False.
  Proof. tauto. Qed.

Lemma zenon_equiv_finish_1 : forall Q : Prop,
  (~Q -> False) -> (True <-> ((False <-> Q) <-> True)) -> False.
  Proof. tauto. Qed.

Lemma zenon_equiv_finish_2 : forall Q : Prop,
  (~Q -> False) -> (False <-> ((True <-> Q) <-> True)) -> False.
  Proof. tauto. Qed.


Definition zenon_equiv_init_0_s :=
  fun A c h => zenon_equiv_init_0 A h c
.
Definition zenon_equiv_init_1_s :=
  fun A B C c h => zenon_equiv_init_1 A B C h c
.
Definition zenon_equiv_init_2_s :=
  fun A B C D c h => zenon_equiv_init_2 A B C D h c
.
Definition zenon_equiv_init_3_s :=
  fun A B C c h => zenon_equiv_init_3 A B C h c
.
Definition zenon_equiv_init_4_s :=
  fun A B c h => zenon_equiv_init_4 A B h c
.
Definition zenon_equiv_init_5_s :=
  fun A B C c h => zenon_equiv_init_5 A B C h c
.
Definition zenon_equiv_init_6_s :=
  fun A c h => zenon_equiv_init_6 A h c
.
Definition zenon_equiv_init_7_s :=
  fun A c h => zenon_equiv_init_7 A h c
.
Definition zenon_equiv_init_8_s :=
  fun A B c h => zenon_equiv_init_8 A B h c
.
Definition zenon_equiv_init_9_s :=
  fun A B c h => zenon_equiv_init_9 A B h c
.
Definition zenon_equiv_merge_right_s :=
  fun A B C D E c h => zenon_equiv_merge_right A B C D E h c
.
Definition zenon_equiv_merge_left_s :=
  fun A B C D E F c h => zenon_equiv_merge_left A B C D E F h c
.
Definition zenon_equiv_merge_1_s :=
  fun A B C c h => zenon_equiv_merge_1 A B C h c
.
Definition zenon_equiv_simplify_s :=
  fun A B C D c h => zenon_equiv_simplify A B C D h c
.
Definition zenon_equiv_merge_simplify_s :=
  fun A B C D E c h => zenon_equiv_merge_simplify A B C D E h c
.
Definition zenon_equiv_inner_loop_s :=
  fun A B C c h => zenon_equiv_inner_loop A B C h c
.
Definition zenon_equiv_reverse_s :=
  fun A B C D E c h => zenon_equiv_reverse A B C D E h c
.
Definition zenon_equiv_outer_loop_s :=
  fun A B c h => zenon_equiv_outer_loop A B h c
.
Definition zenon_equiv_finish_0_s :=
  fun A c h => zenon_equiv_finish_0 A h c
.
Definition zenon_equiv_finish_1_s :=
  fun A c h => zenon_equiv_finish_1 A h c
.
Definition zenon_equiv_finish_2_s :=
  fun A c h => zenon_equiv_finish_2 A h c
.
