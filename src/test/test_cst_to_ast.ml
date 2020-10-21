(* these tests should not raise an exception and make Cervino fail *)

let%test_module _ =
  ( module struct
    let check src =
      let cst = Parsing.parse_string src in
      let ast = Cst_to_ast.convert cst "prop" in
      Fmt.(pf stdout) "%a@.-->@.%a" Cst.pp cst Ast.pp ast


    let%expect_test "sorts, relations and constants" =
      check
        {|
constant a in T 
sort S
relation p in S * S
relation q in T
sort T
constant b in T
check prop {} using TEA
|};
      [%expect
        {|
        ((sorts (S T))
         (relations (((r_name p) (r_profile (S S))) ((r_name q) (r_profile (T)))))
         (constants (((c_name a) (c_domain T)) ((c_name b) (c_domain T))))
         (events ())
         (checks (((check_name prop) (check_body ()) (check_using TEA)))))
        -->
        ((model
          ((sorts (S T))
           (relations
            (((rel_name p) (rel_profile (S S))) ((rel_name q) (rel_profile (T)))))
           (constants (((cst_name a) (cst_sort T)) ((cst_name b) (cst_sort T))))
           (events ())))
         (check
          ((chk_name prop) (chk_body True) (chk_assuming True) (chk_using TEA)))) |}]

    let%expect_test "not not not" =
      check
        {|
sort S
relation p in S
axiom { all x: S { 
  !!p(x)
  !p(x)
  !!!p(x) } }
check prop {} using TEA
          |};
      [%expect
        {|
              ((sorts (S)) (relations (((r_name p) (r_profile (S)))))
               (axioms
                (((a_body
                   ((Quant All (((x) S))
                     ((Unary Not (Unary Not (Pred ((pred p) (args (x))))))
                      (Unary Not (Pred ((pred p) (args (x)))))
                      (Unary Not (Unary Not (Unary Not (Pred ((pred p) (args (x))))))))))))))
               (events ())
               (checks (((check_name prop) (check_body ()) (check_using TEA)))))
              -->
              ((model
                ((sorts (S)) (relations (((rel_name p) (rel_profile (S)))))
                 (axioms
                  ((All ((var_name x) (var_sort S))
                    (And
                     (Lit
                      (Pos_app 0 ((rel_name p) (rel_profile (S)))
                       ((Var ((var_name x) (var_sort S))))))
                     (And
                      (Lit
                       (Neg_app 0 ((rel_name p) (rel_profile (S)))
                        ((Var ((var_name x) (var_sort S))))))
                      (Lit
                       (Neg_app 0 ((rel_name p) (rel_profile (S)))
                        ((Var ((var_name x) (var_sort S)))))))))))
                 (events ())))
               (check
                ((chk_name prop) (chk_body True) (chk_assuming True) (chk_using TEA)))) |}]

    let%expect_test "implies, iff" =
      check
        {|
sort S
relation p in S * S
relation q in S * S
axiom { all x, y, z, t : S { 
  !!!p(x,y)
  p(x, y) => q(z, t)
  p(x, y) <=> q(z, t) } }
check prop {} using TEA
    |};
      [%expect
        {|
        ((sorts (S))
         (relations (((r_name p) (r_profile (S S))) ((r_name q) (r_profile (S S)))))
         (axioms
          (((a_body
             ((Quant All (((x y z t) S))
               ((Unary Not (Unary Not (Unary Not (Pred ((pred p) (args (x y)))))))
                (Binary Implies (Pred ((pred p) (args (x y))))
                 (Pred ((pred q) (args (z t)))))
                (Binary Iff (Pred ((pred p) (args (x y))))
                 (Pred ((pred q) (args (z t))))))))))))
         (events ())
         (checks (((check_name prop) (check_body ()) (check_using TEA)))))
        -->
        ((model
          ((sorts (S))
           (relations
            (((rel_name p) (rel_profile (S S))) ((rel_name q) (rel_profile (S S)))))
           (axioms
            ((All ((var_name x) (var_sort S))
              (All ((var_name y) (var_sort S))
               (All ((var_name z) (var_sort S))
                (All ((var_name t) (var_sort S))
                 (And
                  (Lit
                   (Neg_app 0 ((rel_name p) (rel_profile (S S)))
                    ((Var ((var_name x) (var_sort S)))
                     (Var ((var_name y) (var_sort S))))))
                  (And
                   (Or
                    (Lit
                     (Neg_app 0 ((rel_name p) (rel_profile (S S)))
                      ((Var ((var_name x) (var_sort S)))
                       (Var ((var_name y) (var_sort S))))))
                    (Lit
                     (Pos_app 0 ((rel_name q) (rel_profile (S S)))
                      ((Var ((var_name z) (var_sort S)))
                       (Var ((var_name t) (var_sort S)))))))
                   (And
                    (Or
                     (Lit
                      (Neg_app 0 ((rel_name p) (rel_profile (S S)))
                       ((Var ((var_name x) (var_sort S)))
                        (Var ((var_name y) (var_sort S))))))
                     (Lit
                      (Pos_app 0 ((rel_name q) (rel_profile (S S)))
                       ((Var ((var_name z) (var_sort S)))
                        (Var ((var_name t) (var_sort S)))))))
                    (Or
                     (Lit
                      (Neg_app 0 ((rel_name q) (rel_profile (S S)))
                       ((Var ((var_name z) (var_sort S)))
                        (Var ((var_name t) (var_sort S))))))
                     (Lit
                      (Pos_app 0 ((rel_name p) (rel_profile (S S)))
                       ((Var ((var_name x) (var_sort S)))
                        (Var ((var_name y) (var_sort S))))))))))))))))
           (events ())))
         (check
          ((chk_name prop) (chk_body True) (chk_assuming True) (chk_using TEA)))) |}]

    let%expect_test "next" =
      check
        {|
sort S
relation p in S
axiom { all x: S { 
  ! X ! X p(x) 
  X G X p(x)
  X F X p(x)
}}
check prop {} using TEA
          |};
      [%expect
        {|
        ((sorts (S)) (relations (((r_name p) (r_profile (S)))))
         (axioms
          (((a_body
             ((Quant All (((x) S))
               ((Unary Not
                 (Unary X (Unary Not (Unary X (Pred ((pred p) (args (x))))))))
                (Unary X (Unary G (Unary X (Pred ((pred p) (args (x)))))))
                (Unary X (Unary F (Unary X (Pred ((pred p) (args (x))))))))))))))
         (events ())
         (checks (((check_name prop) (check_body ()) (check_using TEA)))))
        -->
        ((model
          ((sorts (S)) (relations (((rel_name p) (rel_profile (S)))))
           (axioms
            ((All ((var_name x) (var_sort S))
              (And
               (Lit
                (Pos_app 2 ((rel_name p) (rel_profile (S)))
                 ((Var ((var_name x) (var_sort S))))))
               (And
                (G
                 (Lit
                  (Pos_app 2 ((rel_name p) (rel_profile (S)))
                   ((Var ((var_name x) (var_sort S)))))))
                (F
                 (Lit
                  (Pos_app 2 ((rel_name p) (rel_profile (S)))
                   ((Var ((var_name x) (var_sort S))))))))))))
           (events ())))
         (check
          ((chk_name prop) (chk_body True) (chk_assuming True) (chk_using TEA)))) |}]

    (*  *)
  end )
