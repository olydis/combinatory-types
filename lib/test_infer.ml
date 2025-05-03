open Core
open Sk
open Types
open Infer

let rec self_apply_l n sk = if n = 0 then sk else self_apply_l (n - 1) sk * sk
let rec self_apply_r n sk = if n = 0 then sk else sk * self_apply_r (n - 1) sk

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
  |> List.max_elt ~compare:(fun (_, _, ratio1) (_, _, ratio2) ->
         Float.compare ratio1 ratio2)
  |> Option.value_exn |> [%sexp_of: int * int * float] |> print_s;
  [%expect {| (46 102 2.22) |}];
  print_s [%sexp (size (Sop * iop * iop * (Sop * iop * iop)) : int)];
  [%expect {| 14 |}];
  let latex_row ?assert_fails name term =
    let assert_fails = Option.is_some assert_fails in
    let size, calls, ratio = infer_measure ~assert_fails term in
    print_endline
      (Printf.sprintf "%s & %s & %d & %d & %.2f \\\\" name
         (if assert_fails then "no" else "yes")
         size calls ratio)
  in
  latex_row "{\\bf ff}" ff;
  latex_row "{\\bf tt}" tt;
  latex_row "{\\bf cond}" cond;
  latex_row "{\\bf cond tt ff tt}" (cond * tt * ff * tt);
  latex_row ~assert_fails:() "{\\bf cond tt tt zero}" (cond * tt * tt * zero);
  latex_row "{\\bf cond} ({\\bf cond tt ff tt}) {\\bf ff tt}"
    (cond * (cond * tt * ff * tt) * ff * tt);
  latex_row "{\\bf isZero}" isZero;
  latex_row ~assert_fails:() "{\\bf isZero tt} " (isZero * tt);
  latex_row "{\\bf lam} $x$ ({\\bf isZero} $x$) {\\bf zero}"
    (lam "x" (isZero * Ref "x") zero);
  latex_row "{\\bf lam $x$ $x$ zero zero}" (lam "x" (Ref "x") zero * zero);
  latex_row ~assert_fails:() "{\\bf lam $x$ $x$ zero tt}"
    (lam "x" (Ref "x") zero * tt);
  latex_row ~assert_fails:() "{\\bf successor tt}" (succ * tt);
  latex_row "{\\bf successor zero}" (succ * zero);
  latex_row "{\\bf successor$^3$ zero}" (num 3);
  latex_row "{\\bf successor$^{1000}$ zero}" (num 1000);
  latex_row ~assert_fails:() "cons (pair ff (nil zero))"
    (cons_c * (pairL * ff * (nil_c * zero)));
  latex_row "{\\bf plus}" prim_plus;
  latex_row "{\\bf plus} ({\\bf successor zero})" (prim_plus * (succ * zero));
  latex_row "{\\bf plus} ({\\bf successor zero}) {\\bf zero}"
    (prim_plus * (succ * zero) * zero);
  latex_row ~assert_fails:() "{\\bf plus} ({\\bf successor zero}) {\\bf tt}"
    (prim_plus * (succ * zero) * tt);
  latex_row "{\\bf fold\\_left plus}" (fold_left_c prim_plus);
  latex_row "{\\bf cons} ({\\bf pair ff} ({\\bf nil tt}))"
    (cons_c * (pairL * ff * (nil_c * tt)));
  latex_row ~assert_fails:() "{\\bf cons} ({\\bf pair ff} ({\\bf nil zero}))"
    (cons_c * (pairL * ff * (nil_c * zero)));
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
  latex_row "compiler of a toy language" (get_def "compile");
  latex_row "$S^4$ (= $S~S~S~S$)" (self_apply_l 4 Sop);
  latex_row "$S^{10}$" (self_apply_l 10 Sop);
  latex_row "$S^{100}$" (self_apply_l 100 Sop);
  (* for table in paper *)
  [%expect {|
    {\bf ff} & yes & 22 & 21 & 0.95 \\
    {\bf tt} & yes & 19 & 18 & 0.95 \\
    {\bf cond} & yes & 89 & 88 & 0.99 \\
    {\bf cond tt ff tt} & yes & 149 & 244 & 1.64 \\
    {\bf cond tt tt zero} & no & 147 & 242 & 1.65 \\
    {\bf cond} ({\bf cond tt ff tt}) {\bf ff tt} & yes & 279 & 470 & 1.68 \\
    {\bf isZero} & yes & 103 & 153 & 1.49 \\
    {\bf isZero tt}  & no & 122 & 178 & 1.46 \\
    {\bf lam} $x$ ({\bf isZero} $x$) {\bf zero} & yes & 140 & 204 & 1.46 \\
    {\bf lam $x$ $x$ zero zero} & yes & 55 & 58 & 1.05 \\
    {\bf lam $x$ $x$ zero tt} & no & 54 & 57 & 1.06 \\
    {\bf successor tt} & no & 57 & 74 & 1.30 \\
    {\bf successor zero} & yes & 58 & 75 & 1.29 \\
    {\bf successor$^3$ zero} & yes & 134 & 187 & 1.40 \\
    {\bf successor$^{1000}$ zero} & yes & 38020 & 56019 & 1.47 \\
    cons (pair ff (nil zero)) & no & 188 & 294 & 1.56 \\
    {\bf plus} & yes & 680 & 712 & 1.05 \\
    {\bf plus} ({\bf successor zero}) & yes & 738 & 914 & 1.24 \\
    {\bf plus} ({\bf successor zero}) {\bf zero} & yes & 758 & 1151 & 1.52 \\
    {\bf plus} ({\bf successor zero}) {\bf tt} & no & 757 & 1095 & 1.45 \\
    {\bf fold\_left plus} & yes & 1206 & 1238 & 1.03 \\
    {\bf cons} ({\bf pair ff} ({\bf nil tt})) & yes & 187 & 293 & 1.57 \\
    {\bf cons} ({\bf pair ff} ({\bf nil zero})) & no & 188 & 294 & 1.56 \\
    compiler of a toy language & yes & 48016989 & 119811071 & 2.50 \\
    $S^4$ (= $S~S~S~S$) & yes & 5 & 10 & 2.00 \\
    $S^{10}$ & yes & 11 & 70 & 6.36 \\
    $S^{100}$ & yes & 101 & 7450 & 73.76 \\
    |}];
  (* asymptotic behavior of specific kinds of terms *)
  List.iter
    [ num 0; num 1; num 2; num 3; num 4; num 1000 ]
    ~f:(fun t -> print_s [%sexp (infer_measure t : int * int * float)]);
  [%expect {|
    (20 19 0.95)
    (58 75 1.29)
    (96 131 1.36)
    (134 187 1.4)
    (172 243 1.41)
    (38020 56019 1.47)
    |}];
  List.iter
    [
      self_apply_l 10 iop;
      self_apply_l 100 iop;
      self_apply_l 1000 iop;
      self_apply_r 10 iop;
      self_apply_r 100 iop;
      self_apply_r 1000 iop;
    ]
    ~f:(fun t -> print_s [%sexp (infer_measure t : int * int * float)]);
  [%expect {|
    (33 62 1.88)
    (303 602 1.99)
    (3003 6002 2)
    (33 62 1.88)
    (303 602 1.99)
    (3003 6002 2)
    |}];
  List.iter
    [
      self_apply_l 1 Sop;
      self_apply_l 2 Sop;
      self_apply_l 3 Sop;
      self_apply_l 4 Sop;
      self_apply_l 5 Sop;
      self_apply_l 6 Sop;
      self_apply_l 10 Sop;
      self_apply_l 100 Sop;
      self_apply_l 1000 Sop;
      self_apply_r 10 Sop;
      self_apply_r 100 Sop;
      self_apply_r 1000 Sop;
    ]
    ~f:(fun t -> print_s [%sexp (infer_measure t : int * int * float)]);
  [%expect {|
    (2 1 0.5)
    (3 2 0.67)
    (4 6 1.5)
    (5 10 2)
    (6 17 2.83)
    (7 24 3.43)
    (11 70 6.36)
    (101 7450 73.76)
    (1001 749500 748.75)
    (11 10 0.91)
    (101 100 0.99)
    (1001 1000 1)
    |}];
  List.iter
    [
      self_apply_l 10 wop;
      self_apply_l 100 wop;
      self_apply_l 1000 wop;
      self_apply_r 10 wop;
      self_apply_r 100 wop;
      self_apply_r 1000 wop;
    ]
    ~f:(fun t -> print_s [%sexp (infer_measure t : int * int * float)]);
  [%expect {|
    (407 856 2.1)
    (3737 8776 2.35)
    (37037 87976 2.38)
    (407 676 1.66)
    (3737 6436 1.72)
    (37037 64036 1.73)
    |}];
  (* compiler *)
  print_s [%sexp (infer_measure (get_def "compile") : int * int * float)];
  [%expect {| (48016989 119811071 2.5) |}];
  print_s
    [%sexp (infer_measure (get_def "finalizeNativeExpr") : int * int * float)];
  [%expect {| (735525 1757351 2.39) |}];
  Map.to_alist defs
  |> List.map ~f:(fun (name, def) -> (name, def, infer_measure def))
  |> List.max_elt ~compare:(fun (_, _, (_, _, a)) (_, _, (_, _, b)) ->
         Float.compare a b)
  |> Option.value_exn
  |> fun (name, def, _) ->
  latex_row name def;
  [%expect {| _48 & yes & 22563 & 56888 & 2.52 \\ |}];
  ()
