(* these tests should not raise an exception and make Cervino fail *)

let%test_module _ =
  ( module struct
    let check src =
      let cst = Parsing.parse_string src in
      let ast = Cst_to_ast.convert cst "prop" in
      Fmt.pr "%a@." Ast.Electrum.pp ast


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
        sig S {}
        sig T {}
        one sig a in T {}
        one sig b in T {}
        one sig _M {
          var p : S -> S,
          var q : set T,
        }

        fact /* assuming */ { ({}) }
        check prop { ({}) } |}]

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
              sig S {}

              one sig _M {
                var p : set S,
              }
              fact { (all x: S | (x in _M.p && (x !in _M.p && x !in _M.p))) }
              fact /* assuming */ { ({}) }
              check prop { ({}) } |}]

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
        sig S {}

        one sig _M {
          var p : S -> S,
          var q : S -> S,
        }
        fact { (all x: S | (all y: S | (all z: S | (all t: S |
          (x->y !in _M.p &&
           ((x->y !in _M.p || z->t in _M.q) &&
            ((x->y !in _M.p || z->t in _M.q) && (z->t !in _M.q || x->y in _M.p))))))))
          }
        fact /* assuming */ { ({}) }
        check prop { ({}) } |}]

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
        sig S {}

        one sig _M {
          var p : set S,
        }
        fact { (all x: S |
          (x in _M.p'' && (always x in _M.p'' && eventually x in _M.p''))) }
        fact /* assuming */ { ({}) }
        check prop { ({}) } |}]

    (*  *)
  end )
