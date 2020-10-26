(* these tests should not raise an exception and make Cervino fail *)

let%test_module _ =
  ( module struct
    let check src =
      let cst = Parsing.parse_string src in
      let ast = Cst_to_ast.convert cst "prop" in
      let ast' = Cervino_semantics.convert ast in
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
        
        axiom DefIndex {
        G{all i1,i2,i3:index | {
          !prev_index(zero,i1)
          (prev_index(i1,i3) && prev_index(i1,i2)) => i2 = i3
          (prev_index(i1,i3) && prev_index(i2,i3)) => i2 = i1
          prev_tc(zero,i1) && prev_tc(i1,zero)
          }
        }
        }
        
        axiom init {
          {all i:index, p:Process | !list(i,p)}
          {all i:index | last_list(i) <=> i = zero}
        }
        
        event enter_list[p:Process, last:index] modifies last_list, list at {(last,p)}, is_in_list at {p}{
          last_list(last)
          !is_in_list(p)
          
          list'(last, p)
          {all i:index | last_list'(i) <=> prev_index(i,last)}
        }
        
        event exit_list[p:Process] modifies last_list, list, is_in_list at {p}{
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
          var prev_index : index -> index,
          var prev_tc : index -> index,
          var list : index -> Process,
          var is_in_list : Process,
          var last_list : index,
        }
        fact {
          always (some _s_index1: index | (some _s_Process1: Process |
           ((last in _M.last_list &&
             (p !in _M.is_in_list &&
              (last->p in _M.list' && (all i: index |
               ((i !in _M.last_list' || i->last in _M.prev_index) &&
                (i->last !in _M.prev_index || i in _M.last_list'))))))
            ||
            (zero->p in _M.list &&
             (p !in _M.is_in_list' &&
              ((all i: index | (all last: index |
               (last !in _M.last_list ||
                ((i !in _M.last_list' || last->i in _M.prev_index) &&
                 (last->i !in _M.prev_index || i in _M.last_list')))))
               && (all i: index | (all i2: index | (all p: Process |
               (i->i2 !in _M.prev_index ||
                ((i->p !in _M.list || i2->p in _M.list') &&
                 (i2->p !in _M.list' || i->p in _M.list)))))))))))) }
        fact {
          always (all i1: index | (all i2: index | (all i3: index |
           (zero->i1 !in _M.prev_index &&
            (((i1->i3 !in _M.prev_index || i1->i2 !in _M.prev_index) || i2 = i3) &&
             (((i1->i3 !in _M.prev_index || i2->i3 !in _M.prev_index) || i2 = i1) &&
              (zero->i1 in _M.prev_tc && i1->zero in _M.prev_tc))))))) }
        fact {
          ((all i: index | (all p: Process | i->p !in _M.list)) && (all i: index |
           ((i !in _M.last_list || i = zero) && (i != zero || i in _M.last_list)))) }
        fact /* assuming */ { {} }
        check prop { (all p: Process |
          always (p !in _M.is_in_list || eventually p !in _M.is_in_list)) } |}]

    (*  *)
  end )
