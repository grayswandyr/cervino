(* these tests should not raise an exception and make Cervino fail *)

let%test_module _ =
  ( module struct
    let check src =
      let cst = Parsing.parse_string src in
      let ast = Cst_to_ast.convert cst "prop" in
      let ast' = Cervino_semantics.convert ast in
      Fmt.pr "%s@.-->@.%a" src Ast.Electrum.pp ast'


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
      [%expect {| |}]

    (*  *)
  end )
