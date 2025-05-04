open Core
open Sk
open Types
open Data_types
open Infer

let%expect_test "infer" =
  let infer sk =
    let fuel = ref 1000000 in
    match infer fuel [] sk with
    | None -> if !fuel = 0 then print_endline "out of fuel"
    | Some t -> print_s [%sexp (t : t)]
  in
  (* terms with type *)
  infer iop;
  [%expect {| (S2ty Kty Kty) |}];
  infer (id * Tag.dummy_value Sop);
  [%expect {| (fun Sty Sty) |}];
  infer (id * Tag.dummy_value zero);
  [%expect {| (fun nat nat) |}];
  infer (id * Tag.sk_of nat);
  [%expect {| (fun nat nat) |}];
  infer (id * Tag.sk_of nat * one);
  [%expect {| nat |}];
  infer ff;
  [%expect {| bool |}];
  infer tt;
  [%expect {| bool |}];
  infer zero;
  [%expect {| nat |}];
  infer (iop * zero);
  [%expect {| nat |}];
  infer (succ * zero);
  [%expect {| nat |}];
  infer (pair * zero * tt);
  [%expect {| (product nat bool) |}];
  infer (inl * zero * Tag.dummy_value tt);
  [%expect {| (sum nat bool) |}];
  infer (inr * Tag.dummy_value zero * tt);
  [%expect {| (sum nat bool) |}];
  infer (inr * Tag.sk_of nat * tt);
  [%expect {| (sum nat bool) |}];
  infer (case_c * (pair * isZero * iop) * (inl * zero * Tag.dummy_value tt));
  [%expect {| bool |}];
  infer (case_c * (pair * isZero * iop) * (inr * Tag.dummy_value zero * tt));
  [%expect {| bool |}];
  infer (lam "x" (isZero * Ref "x") ~arg:(Tag.dummy_value zero));
  [%expect {| (fun nat bool) |}];
  infer (lam "x" (isZero * Ref "x") ~arg:(Tag.sk_of nat));
  [%expect {| (fun nat bool) |}];
  infer (z * Kop);
  [%expect {| (z Kty) |}];
  infer (nil * Tag.dummy_value zero);
  [%expect {| (list nat) |}];
  infer (nil * Tag.sk_of nat);
  [%expect {| (list nat) |}];
  infer (of_list zero [ zero; one ]);
  [%expect {| (list nat) |}];
  infer (prim_plus * zero * zero);
  [%expect {| nat |}];
  infer
    (to_fun
    * ("p" ^ (prim_plus * (fst * Ref "p") * (snd * Ref "p")))
    * Tag.sk_of ~args:[ Some (Tag.sk_of nat); Some (Tag.sk_of nat) ] product);
  [%expect {| (fun (product nat nat) nat) |}];
  let list = of_list zero [ num 4; num 2 ] in
  infer list;
  [%expect {| (list nat) |}];
  infer (empty_of * list);
  [%expect {| (list nat) |}];
  infer (reverse * list);
  [%expect {| (list nat) |}];
  infer (fold_left prim_plus * (pair * zero * list));
  [%expect {| nat |}];
  infer (fold_right prim_plus * (pair * zero * list));
  [%expect {| nat |}];
  infer (map (Tag.sk_of nat) * succ * list);
  [%expect {| (list nat) |}];
  infer (list_module (Tag.sk_of nat));
  [%expect
    {|
    (product (product (list nat) (fun (product nat (list nat)) (list nat)))
     (fun (list nat) (list nat)))
    |}];
  infer (list_module (Tag.dummy_value tt));
  [%expect
    {|
    (product (product (list bool) (fun (product bool (list bool)) (list bool)))
     (fun (list bool) (list bool)))
    |}];
  (* terms without type *)
  infer (id * Tag.sk_of nat * tt);
  [%expect {| |}];
  infer (zero * zero);
  [%expect {| |}];
  infer (isZero * tt);
  [%expect {| |}];
  infer (lam "x" (isZero * Ref "x") ~arg:(Tag.dummy_value zero) * tt);
  [%expect {| |}];
  infer (lam "x" (isZero * Ref "x") ~arg:(Tag.sk_of bool));
  [%expect {| |}];
  infer (of_list zero [ zero; tt ]);
  [%expect {| |}];
  let omega = Sop * iop * iop in
  infer (omega * omega);
  [%expect {| out of fuel |}]

let%expect_test "fuel requirements" =
  let dump t = print_s [%sexp (infer_measure t : int * int * float)] in
  List.iter [ num 0; num 1; num 2; num 3; num 4; num 1000 ] ~f:dump;
  [%expect
    {|
    (24 23 0.96)
    (66 83 1.26)
    (108 143 1.32)
    (150 203 1.35)
    (192 263 1.37)
    (42024 60023 1.43)
    |}];
  dump (lam "x" (isZero * Ref "x") ~arg:(Tag.dummy_value zero) * tt);
  [%expect {| (220 365 1.66) |}];
  dump (lam "x" (isZero * Ref "x") ~arg:(Tag.sk_of bool));
  [%expect {| (179 321 1.79) |}];
  dump (prim_plus * zero * zero);
  [%expect {| (856 1292 1.51) |}];
  dump (prim_plus * num 1000 * num 1000);
  [%expect {| (84856 121292 1.43) |}];
  ()
