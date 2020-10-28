(* these tests should not raise an exception and make Cervino fail *)

let%test_module _ =
  ( module struct
    let check src =
      let cst = Parsing.parse_string src in
      let ast = Cst_to_ast.convert cst "prop" in
      let ast' = Transfo_TEA.convert ast in
      Fmt.pr "%a@." Ast.Electrum.pp ast'


    let%expect_test _ =
      check
        {|
        sort Process
        sort index
        
        constant zero in index
        relation prev_index in index*index
        relation prev_tc in index*index
        
        relation list in index*Process
        relation is_in_list in Process
        relation last_list in index
        
        paths[prev_index, prev_tc]
        
        event enter_list[p:Process, last:index] modifies last_list, list at {(last,p)}, is_in_list at {p}{
          last_list(last)
          !is_in_list(p)
          
          list'(last, p)
          {all i:index | last_list'(i) <=> prev_index(i,last)}
        }
        
        event exit_list[p,p2,p3:Process] modifies last_list, list, is_in_list at {p}{
          list(zero,p)
          
          !is_in_list'(p)
          {all i,last:index | last_list(last) => (last_list'(i) <=> prev_index(last,i))}
          {all i,i2:index, p:Process | prev_index(i,i2) => (list(i,p) <=> list'(i2,p))}
        }
        
        check prop {all p : Process | G (is_in_list(p) => F !is_in_list(p))} 
using TEA        
|};
      [%expect
        {|
        sig Process {}
        sig index {}
        one sig zero in index {}
        one sig _M {
          var _E_s_index1 : set index,
          var _E_s_Process1 : set Process,
          var _E_s_Process2 : set Process,
          var _E_s_Process3 : set Process,
          var prev_index : index -> index,
          var prev_tc : index -> index,
          var list : index -> Process,
          var is_in_list : set Process,
          var last_list : set index,
        }
        fact {
          always (all _s_index1: index | (all _s_Process1: Process |
           (all _s_Process2: Process | (all _s_Process3: Process |
           (((_s_index1 in _M.last_list || _s_index1 !in _M._E_s_index1) &&
             ((_s_Process1 !in _M.is_in_list || _s_Process1 !in _M._E_s_Process1) &&
              ((_s_index1->_s_Process1 in _M.list' ||
                (_s_index1 !in _M._E_s_index1 || _s_Process1 !in _M._E_s_Process1))
               && (all i: index |
               ((i !in _M.last_list' ||
                 (i->_s_index1 in _M.prev_index || _s_index1 !in _M._E_s_index1))
                &&
                ((i->_s_index1 !in _M.prev_index || _s_index1 !in _M._E_s_index1) ||
                 i in _M.last_list'))))))
            ||
            ((zero->_s_Process1 in _M.list || _s_Process1 !in _M._E_s_Process1) &&
             ((_s_Process1 !in _M.is_in_list' || _s_Process1 !in _M._E_s_Process1) &&
              ((all i: index | (all last: index |
               (last !in _M.last_list ||
                ((i !in _M.last_list' || last->i in _M.prev_index) &&
                 (last->i !in _M.prev_index || i in _M.last_list')))))
               && (all i: index | (all i2: index | (all p: Process |
               (i->i2 !in _M.prev_index ||
                (((i->_s_Process1 !in _M.list || _s_Process1 !in _M._E_s_Process1) ||
                  (i2->_s_Process1 in _M.list' || _s_Process1 !in _M._E_s_Process1))
                 &&
                 ((i2->_s_Process1 !in _M.list' || _s_Process1 !in _M._E_s_Process1)
                  || (i->_s_Process1 in _M.list || _s_Process1 !in _M._E_s_Process1)))))))))))))))
          }
        fact {
          always
           ((all _x: index | (all _y: index |
            ((_x !in _M._E_s_index1 || _y !in _M._E_s_index1) || _x = _y))) &&
            (all _x: Process | (all _y: Process |
            (((_x !in _M._E_s_Process3 || _y !in _M._E_s_Process3) || _x = _y) &&
             (((_x !in _M._E_s_Process2 || _y !in _M._E_s_Process2) || _x = _y) &&
              ((_x !in _M._E_s_Process1 || _y !in _M._E_s_Process1) || _x = _y))))))
          }
        fact /* assuming */ { no none }
        check prop { (all p: Process |
          always (p !in _M.is_in_list || eventually p !in _M.is_in_list)) } |}]

    (*  *)
  end )
