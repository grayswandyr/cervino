module type S = sig
  val convert : Ast.t -> Ast.t
end

module Name = struct
  let tea = "TEA"

  let ttc = "TTC"

  let tfc = "TFC"

  let of_using (using : Ast.transfo) =
    match using with TEA -> tea | TTC _ -> ttc | TFC _ -> tfc
end

module Id = struct
  let convert ast = ast
end

(* apply ast->ast transformations from left to right *)
let compose (transfos : (module S) list) ast =
  List.fold_left (fun ast (module T : S) -> T.convert ast) ast transfos


let apply_transformation (using : Ast.transfo) : Ast.t -> Ast.t =
  let steps : (module S) list =
    match using with
    | TEA ->
        [ (module Expand_modifies); (module Transfo_TEA) ]
    | TTC _ ->
        [ (module Transfo_TTC) ]
    | TFC _ ->
        [ (module Transfo_TFC) ]
  in
  compose steps


let convert Ast.({ check = { chk_using; _ }; _ } as ast) =
  apply_transformation chk_using ast
