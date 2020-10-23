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

let get_transformation (using : Ast.transfo) : (module S) =
  match using with
  | TEA ->
      (module Transfo_tea)
  | TTC _ ->
      (module Transfo_TTC)
  | _ ->
      Msg.warn (fun m ->
          m "Unimplemented transformation: %s" (Name.of_using using));
      (module Id)


let process Ast.({ check = { chk_using; _ }; _ } as ast) =
  let module T = (val get_transformation chk_using) in
  T.convert ast
