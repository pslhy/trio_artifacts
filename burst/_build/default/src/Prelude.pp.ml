Caml1999M027����            .src/Prelude.ml����  �   �  �  蠠���1ocaml.ppx.context��&_none_@@ �A����������)tool_name���-ppxlib_driver@@@����,include_dirs����"[]@@@����)load_path!����
%@%@@����,open_modules*����.@.@@����+for_package3����$None8@8@@����%debug=����%falseB@B@@����+use_threadsG����
K@K@@����-use_vmthreadsP����T@T@@����/recursive_typesY����]@]@@����)principalb����%f@f@@����3transparent_modulesk����.o@o@@����-unboxed_typest����7x@x@@����-unsafe_string}����@�@�@@����'cookies�����"::�����������/ppx_optcomp.env@�@@�������#env��&_none_A@ ��A@ �A��A@ ��A@ �A@@���-ocaml_version����'Defined��A@ ��A@ �A�������!4@��A@ ��A@ �A@@����"10@��#A@ ��$A@ �A@@����!0@��+A@ ��,A@ �A@@@��.A@ ��/A@ �A@@��1A@ ��2A@ �A@@@��4A@ ��5A@ �A@@@�@@�������@�@@@�@@�@@@@�@@@�@�ڠ��@�����.prelude_string��.src/Prelude.mlA@D�A@R@��A@D�A@R@@@���
  ;
(* PRELUDE *)

(*type bool =
  | False
  | True

let not =
  fun (v : bool) ->
    match v binding i with
    | False -> True
    | True -> False
;;

let and =
  fun (b1 : bool) ->
    fun (b2 : bool) ->
      match b1 binding b1 with
      | False -> False
      | True -> b2
;;

let or =
  fun (b1 : bool) ->
    fun (b2 : bool) ->
      match b1 binding b1 with
      | False -> b2
      | True -> True
;;

let implies =
  fun (b1 : bool) ->
    fun (b2 : bool) ->
      (or (not b1) b2)
;;

type nat = mu nat .
  | O
  | S of nat

(*let add =
  fix (add : nat -> nat -> nat) =
    fun (x1 : nat) ->
      fun (x2 : nat) ->
        match x1 binding x1 with
        | O -> x2
        | S -> add x1 (S x2)
;;*)

let nat_lte =
  fix (nat_lte : nat -> nat -> bool) =
    fun (x1 : nat) ->
      fun (x2 : nat) ->
        match x1 binding x1 with
        | O -> True
        | S -> (match x2 binding x2 with
                | O -> False
                | S -> nat_lte x1 x2)
;;

let nat_eq =
  fix (nat_eq : nat -> nat -> bool) =
    fun (x1 : nat) ->
      fun (x2 : nat) ->
        match x1 binding x1 with
        | O -> (match x2 binding x2 with
                | O -> True
                | S -> False)
        | S -> (match x2 binding x2 with
                | O -> False
                | S -> nat_eq x1 x2)
;;*)

(* END_PRELUDE *)

@��A@U� LQR@@@@��A@@� LQR@@��A@@� LQR@@