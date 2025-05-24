Require Import OpSem.
Require Import Utf8.

Definition pre_arc(o: op) :=
    match o with
    | Ormw (Ofetch_add 1) false Xpln Orlx Orlx => Some (1, 0)
    | Ormw (Ocas v0 v1) false Xpln Orlx Orel =>
      if Nat.eqb v0 (S v1) then Some (1, 0) else None
    | Ofence Oacq => Some (0, 1)
    | _ => None
    end.

Definition post_arc o v :=
    match o with
    | Ormw (Ofetch_add 1) false Xpln Orlx Orlx =>
      match v with
      | Some 0 => None
      | Some _ => Some (2, 0)
      | None => None
      end
    | Ormw (Ocas v0 v1) false Xpln Orlx Orel =>
      if Nat.eqb v0 (S v1) then
        match v with
        | Some 0 => None
        | Some 1 => Some (0, 1)
        | Some _ => Some (0, 0)
        | None => None
        end
      else
        None
    | Ofence Oacq => Some (0, 1)
    | _ => None
    end.

Definition Σ_arc: atomic_spec := {|
    v0 := 1;
    ρ0 := 1;
    pre := pre_arc;
    post := post_arc;
|}.