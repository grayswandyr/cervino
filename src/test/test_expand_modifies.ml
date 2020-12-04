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
          always (all _eax: Process | (all _eay: Process |
           ((_eax !in _M._E_s_Process1 || _eay !in _M._E_s_Process1) || _eax = _eay)))
          }
        fact {
          always (all _s_Process1: Process |
           ((_s_Process1 in _M.List' || _s_Process1 !in _M._E_s_Process1) &&
            ((all _em0: Process |
             (_em0 in _M._E_s_Process1 ||
              ((_em0 !in _M.List || _em0 in _M.List') &&
               (_em0 !in _M.List' || _em0 in _M.List))))
             && (all _em0: Node | (all _em1: Process |
             ((_em0->_em1 !in _M.Lock || _em0->_em1 in _M.Lock') &&
              (_em0->_em1 !in _M.Lock' || _em0->_em1 in _M.Lock))))))) }
        fact { (!{}) }
        fact { ({}) }
        fact /* assuming */ { ({}) }
        check Safety { (!{}) } |}]
  end )
