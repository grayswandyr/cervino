(* these tests should not raise an exception and make Cervino fail *)

let%test_module _ =
  ( module struct
    let check src =
      let cst = Parsing.parse_string src in
      let ast = Cst_to_ast.convert cst "prop" in
      let ast' = Remove_equalities.convert ast in
      Fmt.pr "%s@.-->@.%a" src Ast.Electrum.pp ast'


    let%expect_test "sorts, relations and constants" =
      check
        {|
constant a in T 
sort S
relation p in S * S
relation q in S
relation r in S * S * S
relation u in S * S * T
sort T
relation v in T
constant b in T
axiom { some x, y : S | x = y && q(x) }
axiom { some x, y : S | x = y && q(x) }
axiom { some x, y : T | x = y && v(x) }
check prop {} using TEA
|};
      [%expect
        {|
        constant a in T
        sort S
        relation p in S * S
        relation q in S
        relation r in S * S * S
        relation u in S * S * T
        sort T
        relation v in T
        constant b in T
        axiom { some x, y : S | x = y && q(x) }
        axiom { some x, y : S | x = y && q(x) }
        axiom { some x, y : T | x = y && v(x) }
        check prop {} using TEA

        -->
        sig S {}
        sig T {}
        one sig a in T {}
        one sig b in T {}
        one sig _M {
          var p : S -> S,
          var q : S,
          var r : S -> S -> S,
          var u : S -> S -> T,
          var v : T,
          var _eq_T : T -> T,
          var _eq_S : S -> S,
        }
        fact {
          always (all _x: T | (all _y: T | (all _z: T |
           (_x->_y in _M._eq_T &&
            ((_x->_y !in _M._eq_T || _y->_x in _M._eq_T) &&
             ((_x->_y !in _M._eq_T || _y->_z !in _M._eq_T) || _x->_z in _M._eq_T))))))
          }
        fact {
          always (all _x: S | (all _y: S | (all _z: S |
           (_x->_y in _M._eq_S &&
            ((_x->_y !in _M._eq_S || _y->_x in _M._eq_S) &&
             ((_x->_y !in _M._eq_S || _y->_z !in _M._eq_S) || _x->_z in _M._eq_S))))))
          }
        fact {
          always (all _x: T | (all _y: T |
           (_x->_y !in _M._eq_T ||
            ((all _e0: S | (all _e1: S |
             ((_e0->_e1->_x !in _M.u || _e0->_e1->_y in _M.u) &&
              (_e0->_e1->_y !in _M.u || _e0->_e1->_x in _M.u))))
             && ((_x !in _M.v || _y in _M.v) && (_y !in _M.v || _x in _M.v)))))) }
        fact {
          always (all _x: S | (all _y: S |
           (_x->_y !in _M._eq_S ||
            ((all _e0: S |
             ((_e0->_x !in _M.p || _e0->_y in _M.p) &&
              (_e0->_y !in _M.p || _e0->_x in _M.p)))
             &&
             ((all _e0: S |
              ((_x->_e0 !in _M.p || _y->_e0 in _M.p) &&
               (_y->_e0 !in _M.p || _x->_e0 in _M.p)))
              &&
              (((_x !in _M.q || _y in _M.q) && (_y !in _M.q || _x in _M.q)) &&
               ((all _e0: S | (all _e1: S |
                ((_e0->_e1->_x !in _M.r || _e0->_e1->_y in _M.r) &&
                 (_e0->_e1->_y !in _M.r || _e0->_e1->_x in _M.r))))
                &&
                ((all _e0: S | (all _e1: S |
                 ((_e0->_x->_e1 !in _M.r || _e0->_y->_e1 in _M.r) &&
                  (_e0->_y->_e1 !in _M.r || _e0->_x->_e1 in _M.r))))
                 &&
                 ((all _e0: S | (all _e1: S |
                  ((_x->_e0->_e1 !in _M.r || _y->_e0->_e1 in _M.r) &&
                   (_y->_e0->_e1 !in _M.r || _x->_e0->_e1 in _M.r))))
                  &&
                  ((all _e0: S | (all _e1: T |
                   ((_e0->_x->_e1 !in _M.u || _e0->_y->_e1 in _M.u) &&
                    (_e0->_y->_e1 !in _M.u || _e0->_x->_e1 in _M.u))))
                   && (all _e0: S | (all _e1: T |
                   ((_x->_e0->_e1 !in _M.u || _y->_e0->_e1 in _M.u) &&
                    (_y->_e0->_e1 !in _M.u || _x->_e0->_e1 in _M.u)))))))))))))) }
        fact { (some x: T | (some y: T | (x->y in _M._eq_T && x in _M.v))) }
        fact { (some x: S | (some y: S | (x->y in _M._eq_S && x in _M.q))) }
        fact { (some x: S | (some y: S | (x->y in _M._eq_S && x in _M.q))) }
        fact /* assuming */ { {} }
        check prop { {} } |}]

    (*  *)
  end )
