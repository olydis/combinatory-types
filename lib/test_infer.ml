open Core
open Sk
open Types
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
  infer (iop * zero);
  [%expect {| nat |}];
  infer (pairL * zero * tt);
  [%expect {| (product nat bool) |}];
  infer (inl_c * (pairL * zero * tt));
  [%expect {| (sum nat bool) |}];
  infer (inr_c * (pairL * zero * tt));
  [%expect {| (sum nat bool) |}];
  infer (lam "x" (isZero * Ref "x") zero);
  [%expect {| (fun nat bool) |}];
  infer (z Kop);
  [%expect {| (z Kty) |}];
  infer (of_list zero [ zero; one ]);
  [%expect {| (list nat) |}];
  (* terms without type *)
  infer (zero * zero);
  [%expect {| |}];
  infer (isZero * tt);
  [%expect {| |}];
  infer (lam "x" (isZero * Ref "x") zero * tt);
  [%expect {| |}];
  let omega = Sop * iop * iop in
  infer (omega * omega);
  [%expect {| out of fuel |}]

let%expect_test "fuel requirements" =
  let example_terms =
    [
      iop;
      tag;
      pairL;
      pairL * Kop * Sop;
      fstL;
      sndL;
      fstL * (pairL * Kop * Sop);
      sndL * (pairL * Kop * Sop);
      tt;
      ff;
      cond;
      cond * tt * Kop * Sop;
      cond * ff * Kop * Sop;
      zero;
      succ;
      one;
      num 42;
      num 1000;
      isZero;
      isZero * zero;
      isZero * num 1000;
      predN;
      predN * zero;
      predN * num 1000;
      inl_c * (pairL * zero * tt);
      inr_c * (pairL * zero * tt);
      case_c;
      case_c * (pairL * Kop * Sop) * (inl_c * (pairL * zero * tt));
      case_c * (pairL * Kop * Sop) * (inr_c * (pairL * zero * tt));
      wop * iop * iop * iop;
      lam "x" (isZero * Ref "x") zero;
      prim_plus;
      prim_plus * zero * zero;
      prim_plus * num 1000 * num 1000;
      fold_left_c prim_plus;
      fold_left_c prim_plus
      * (pairL * zero * of_list zero [ num 1000; num 1000 ]);
    ]
  in
  (* maximum fuel to size ratio among example terms *)
  List.map example_terms ~f:infer_measure
  |> List.max_elt ~compare:Float.compare
  |> Option.value_exn |> [%sexp_of: float] |> print_s;
  [%expect {| 4.2 |}];
  print_s [%sexp (infer_measure (wop * iop * iop * iop) : float)];
  [%expect {| 4.2 |}];
  (* asymptotic behavior of specific kinds of terms *)
  List.map [ num 0; num 1; num 2; num 3; num 4; num 1000 ] ~f:infer_measure
  |> [%sexp_of: float list] |> print_s;
  [%expect {| (2.9 3.28 3.35 3.39 3.41 3.47) |}];
  let rec self_apply_l n sk =
    if n = 0 then sk else self_apply_l (n - 1) sk * sk
  in
  let rec self_apply_r n sk =
    if n = 0 then sk else sk * self_apply_r (n - 1) sk
  in
  List.map
    [
      self_apply_l 10 iop;
      self_apply_l 100 iop;
      self_apply_l 1000 iop;
      self_apply_r 10 iop;
      self_apply_r 100 iop;
      self_apply_r 1000 iop;
    ]
    ~f:infer_measure
  |> [%sexp_of: float list] |> print_s;
  [%expect {| (3.85 3.98 4 3.85 3.98 4) |}];
  List.map
    [
      self_apply_l 10 Sop;
      self_apply_l 100 Sop;
      self_apply_l 1000 Sop;
      self_apply_r 10 Sop;
      self_apply_r 100 Sop;
      self_apply_r 1000 Sop;
    ]
    ~f:infer_measure
  |> [%sexp_of: float list] |> print_s;
  [%expect {| (8.27 75.75 750.75 2.82 2.98 3) |}];
  List.map
    [
      self_apply_l 10 wop;
      self_apply_l 100 wop;
      self_apply_l 1000 wop;
      self_apply_r 10 wop;
      self_apply_r 100 wop;
      self_apply_r 1000 wop;
    ]
    ~f:infer_measure
  |> [%sexp_of: float list] |> print_s;
  [%expect {| (4.1 4.35 4.38 3.66 3.72 3.73) |}];
  (* compiler for a toy language (does not leverage tagging) *)
  let defs =
    let lines = In_channel.read_lines "./iota.dag" in
    let defs = Hashtbl.create (module String) in
    let named = ref [] in
    (* define iota operator *)
    Hashtbl.set defs ~key:"u" ~data:("f" ^ (Ref "f" * Sop * Kop));
    List.iter lines ~f:(fun line ->
        match String.split line ~on:' ' with
        | [ dst; src ] ->
            named := dst :: !named;
            Hashtbl.set defs ~key:dst ~data:(Hashtbl.find_exn defs src)
        | dst :: a :: b :: _ ->
            Hashtbl.set defs ~key:dst
              ~data:(App (Hashtbl.find_exn defs a, Hashtbl.find_exn defs b))
        | _ -> ());
    List.map !named ~f:(fun name -> (name, Hashtbl.find_exn defs name))
    |> Map.of_alist_exn (module String)
  in
  let get_def name = Map.find_exn defs name in
  print_s [%sexp (infer_measure (get_def "compile") : float)];
  [%expect {| 4.5 |}];
  print_s [%sexp (infer_measure (get_def "finalizeNativeExpr") : float)];
  [%expect {| 4.39 |}];
  (* List.map (Map.data defs) ~f:infer_measure
  |> List.max_elt ~compare:Float.compare
  |> Option.value_exn |> [%sexp_of: float] |> print_s;
  [%expect {| 4.52 |}]; *)
  ()
