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

let if_ cond t1 t2 =
  if cond then t1 else t2

(* apply ast->ast transformations from left to right *)
let compose (transfos : t list) : t =
 fun ast -> List.fold_left (fun ast convert -> convert ast) ast transfos


let apply_transformation preinstantiate (using : Ast.transfo option) : t =
  (* applied from left to right *)
  let steps : t list =
    match using with
    | Some TEA ->
        [ Instantiation.convert_ae;
          Expand_modifies.convert;
          (* NEVER CALL Cervino_semantics.convert AS THE SEMANTICS
             IS ENSURED BY TEA IN THIS CASE! *)
          Transfo_TEA.convert
        ]
    | Some (TTC _) ->
        [ Instantiation.convert_ae;
          Transfo_TTC.convert_instantiated_TC_axiom;
          Remove_equalities.add_eq_relations;
          Expand_modifies.convert;
          Remove_equalities.convert;
          Cervino_semantics.convert;
          Skolemize.convert;
          if_ preinstantiate Id.convert Instantiation.convert 
        ]
    | Some (TFC _) ->
        [ Instantiation.convert_ae;
          Transfo_TFC.convert;
          Remove_equalities.add_eq_relations;
          Expand_modifies.convert;
          Remove_equalities.convert;
          Cervino_semantics.convert;
          Skolemize.convert;
          if_ preinstantiate Id.convert Instantiation.convert 
          ]
    | None ->
        [ Expand_modifies.convert; Cervino_semantics.convert ]
  in
  compose steps


let convert preinstantiate instantiate Ast.({ check = { chk_using; _ }; _ } as ast) =
  if instantiate
  then 
    Instantiation.convert ast
  else
    apply_transformation preinstantiate chk_using ast
