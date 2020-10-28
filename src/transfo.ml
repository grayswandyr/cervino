type t = Ast.t -> Ast.t

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
let compose (transfos : t list) ast =
  List.fold_left (fun ast convert -> convert ast) ast transfos


let apply_transformation (using : Ast.transfo option) : t =
  (* applied from left to right *)
  let steps : t list =
    match using with
    | Some TEA ->
        [ Transfo_TEA.convert]
    | Some (TTC _) ->
        [ Transfo_TTC.convert ]
    | Some (TFC _) ->
        [ Transfo_TFC.convert ]
    | None ->
        [ Cervino_semantics.convert ]
  in
  compose steps


let convert Ast.({ check = { chk_using; _ }; _ } as ast) =
  apply_transformation chk_using ast
