open Ast

let find_transitive_closure m rel =
    match List.find_pred (fun cur_path -> equal_relation cur_path.base rel) m.closures with
    | None -> None
    | Some p -> Some p.tc

 let closure_axiom rel var vars fml =
   (* let propagate rel fml_from_x = (true) in *)
    (rel, var, vars, fml)

