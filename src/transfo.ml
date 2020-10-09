module type S = sig
  type t

  val convert : t -> Ast.t -> Ast.t
end
