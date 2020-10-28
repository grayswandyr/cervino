(* these tests should not raise an exception and make Cervino fail *)

let%test_module _ =
  ( module struct
    let check src =
      let cst = Parsing.parse_string src in
      let ast = Cst_to_ast.convert cst "Safety" in
      let ast' = Expand_modifies.convert ast |> Transfo_TEA.convert in
      Fmt.pr "%a@." Ast.Electrum.pp ast'


    let%expect_test _ =
      check
        {|
        sort Process
        sort Node

        relation List in Process
        relation Lock in Node * Process
        
        
        event join[p: Process] modifies List at {p}{	
          List'(p)
          }
        
        
        check Safety {} using TEA           
|};
      [%expect
        {|
        sig Process {}
        sig Node {}

        one sig _M {
          var _E_s_Process1 : set Process,
          var List : set Process,
          var Lock : Node -> Process,
        }
        fact {
          always (all _s_Process1: Process |
           ((_s_Process1 in _M.List' || _s_Process1 !in _M._E_s_Process1) &&
            ((all _m0: Process |
             (_m0 in _M._E_s_Process1 ||
              ((_m0 !in _M.List || _m0 in _M.List') &&
               (_m0 !in _M.List' || _m0 in _M.List))))
             && (all _m0: Node | (all _m1: Process |
             ((_m0->_m1 !in _M.Lock || _m0->_m1 in _M.Lock') &&
              (_m0->_m1 !in _M.Lock' || _m0->_m1 in _M.Lock))))))) }
        fact {
          always (all _x: Process | (all _y: Process |
           ((_x !in _M._E_s_Process1 || _y !in _M._E_s_Process1) || _x = _y))) }
        fact /* assuming */ { no none }
        check Safety { no none } |}]
  end )
