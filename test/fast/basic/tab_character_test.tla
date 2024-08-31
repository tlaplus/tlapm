---- MODULE tab_character_test ----

	(* This line contains a tab character,
in order to test that `tlapm` will exit
with a message that informs about the
presence of the tab character. *)

===================================
result: 3
stderr: Unexpected TAB character.
stderr: TLAPS does not handle TAB characters in source files.
