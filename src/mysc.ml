module List = struct
  (* checks that a list has no duplicates *)
  let rec all_different ~eq = function
    | [] ->
        true
    | hd :: tl ->
        (not @@ List.mem ~eq hd tl) && all_different ~eq tl


  (* a guard function for monads *)
  let guard c = if c then [ () ] else []

  (* like combine but doesn't fail for different lengths, cut at the shortest rather *)
  let rec zip xs ys =
    match (xs, ys) with
    | [], _ | _, [] ->
        []
    | x :: xs, y :: ys ->
        (x, y) :: zip xs ys


  module Infix = struct
    include List.Infix

    (* provides a lock-step product for use with the applicative (let+) (while (and+) yields a Cartesian product) *)
    let ( and& ) = zip

    let ( let& ) = ( let+ )
  end
end
