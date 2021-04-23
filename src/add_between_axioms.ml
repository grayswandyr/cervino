open Ast

let fresh_var s var_sort = make_variable ~var_name:(Name.make_unloc s) ~var_sort

(* from strict to lesser precedence: function application > **... > *... > +... > @... *)

let ( **= ) t1 t2 = lit @@ eq 0 t1 t2

let ( **!= ) t1 t2 = lit @@ neq 0 t1 t2

let ( *&& ) = and_

let ( +|| ) = or_

let ( @=> ) = implies

let between_axioms base_rel ({ rel_profile; _ } as btw) =
  assert (not @@ List.is_empty rel_profile);
  let sort = List.hd rel_profile in
  let p1 = fresh_var "p1" sort in
  let p2 = fresh_var "p2" sort in
  let p3 = fresh_var "p3" sort in
  let p4 = fresh_var "p4" sort in
  let v1 = var p1 in
  let v2 = var p2 in
  let v3 = var p3 in
  let v4 = var p4 in
  let app terms = lit @@ pos_app 0 btw terms in
  let rotate = app [ v1; v2; v3 ] @=> app [ v2; v3; v1 ] in
  let transitivity =
    (app [ v4; v1; v2 ] *&& app [ v4; v2; v3 ]) @=> app [ v4; v1; v3 ]
  in
  let antisymmetry =
    (app [ v4; v1; v2 ] *&& app [ v4; v2; v1 ]) @=> (v1 **= v2)
  in
  let partial_totality =
    (app [ v4; v1; v1 ] *&& app [ v4; v2; v2 ])
    @=> (app [ v4; v1; v2 ] +|| app [ v4; v2; v1 ])
  in
  let partial_reflexivity =
    app [ v4; v1; v2 ] @=> (app [ v4; v1; v1 ] *&& app [ v4; v2; v2 ])
  in
  let cycle_maximality = app [ v1; v1; v2 ] @=> (v1 **= v2) in
  let transitivity_of_reachability =
    (app [ v1; v2; v2 ] *&& app [ v2; v3; v3 ]) @=> app [ v1; v3; v3 ]
  in
  let path_consistency =
    (app [ v1; v2; v3 ] *&& app [ v1; v3; v4 ] *&& (v2 **!= v3))
    @=> app [ v2; v3; v4 ]
  in
  let axioms =
    always
    @@ all_many [ p1; p2; p3; p4 ]
    @@ conj
         [ rotate;
           transitivity;
           antisymmetry;
           partial_totality;
           partial_reflexivity;
           cycle_maximality;
           transitivity_of_reachability;
           path_consistency
         ]
  in
  let relation_to_base =
    always
    @@ all_many [ p1; p2 ]
    @@ (lit @@ pos_app 0 base_rel [ v1; v2 ])
    @=> app [ v1; v2; v2 ]
        *&& (all p3 @@ app [ v1; v3; v3 ] @=> app [ v1; v2; v3 ])
  in
  and_ axioms relation_to_base


let make_between_axioms (closures : path list) =
  let make_between_axiom { base; between; _ } =
    match between with None -> [] | Some btw -> [ between_axioms base btw ]
  in
  List.flat_map make_between_axiom closures


let convert { model; check } =
  let between_axioms = make_between_axioms model.closures in
  let updated_model =
    make_model
      ~sorts:model.sorts
      ~relations:model.relations
      ~constants:model.constants
      ~closures:model.closures
      ~axioms:(model.axioms @ between_axioms)
      ~events:model.events
      ()
  in
  Ast.make ~model:updated_model ~check
