let%test_module _ =
  ( module struct
    let base =
      {|
sort S
sort T
relation p in S * S
relation q in T
axiom { all x, y : S, z : T | p(x,y) => q(z)}
axiom { all x, y : S, z : T | p(x,y) <=> q(z)}
axiom { all x : T | ! (! q'(x)) }
check prop {} using TEA
|}


    let%expect_test _ =
      let cst = Parsing.parse_string base in
      let ast = Cst_to_ast.convert cst "prop" in
      Fmt.(pf stdout) "%a@.-->@.%a" Cst.pp cst Ast.pp ast;
      [%expect
        {|
        ((sorts (S T))
         (relations (((r_name p) (r_profile (S S))) ((r_name q) (r_profile (T)))))
         (axioms
          (((a_body
             ((Quant All (((x y) S) ((z) T))
               ((Binary Implies (Pred ((pred p) (args (x y))))
                 (Pred ((pred q) (args (z))))))))))
           ((a_body
             ((Quant All (((x y) S) ((z) T))
               ((Binary Iff (Pred ((pred p) (args (x y))))
                 (Pred ((pred q) (args (z))))))))))
           ((a_body
             ((Quant All (((x) T))
               ((Unary Not (Unary Not (Pred ((pred q) (primed) (args (x)))))))))))))
         (events ())
         (checks (((check_name prop) (check_body ()) (check_using TEA)))))
        -->
        ((model
          ((sorts (S T))
           (relations
            (((rel_name p) (rel_profile (S S))) ((rel_name q) (rel_profile (T)))))
           (axioms
            ((All ((var_name x) (var_sort S))
              (All ((var_name y) (var_sort S))
               (All ((var_name z) (var_sort T))
                (Or
                 (Lit
                  (Neg_app 0 ((rel_name p) (rel_profile (S S)))
                   ((Var ((var_name x) (var_sort S)))
                    (Var ((var_name y) (var_sort S))))))
                 (Lit
                  (Pos_app 0 ((rel_name q) (rel_profile (T)))
                   ((Var ((var_name z) (var_sort T))))))))))
             (All ((var_name x) (var_sort S))
              (All ((var_name y) (var_sort S))
               (All ((var_name z) (var_sort T))
                (And
                 (Or
                  (Lit
                   (Neg_app 0 ((rel_name p) (rel_profile (S S)))
                    ((Var ((var_name x) (var_sort S)))
                     (Var ((var_name y) (var_sort S))))))
                  (Lit
                   (Pos_app 0 ((rel_name q) (rel_profile (T)))
                    ((Var ((var_name z) (var_sort T)))))))
                 (Or
                  (Lit
                   (Neg_app 0 ((rel_name q) (rel_profile (T)))
                    ((Var ((var_name z) (var_sort T))))))
                  (Lit
                   (Pos_app 0 ((rel_name p) (rel_profile (S S)))
                    ((Var ((var_name x) (var_sort S)))
                     (Var ((var_name y) (var_sort S)))))))))))
             (All ((var_name x) (var_sort T))
              (Lit
               (Pos_app 1 ((rel_name q) (rel_profile (T)))
                ((Var ((var_name x) (var_sort T)))))))))
           (events ())))
         (check
          ((chk_name prop) (chk_body True) (chk_assuming True) (chk_using TEA)))) |}]

    (*  *)
  end )
