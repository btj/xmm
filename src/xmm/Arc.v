Require Import OpSem.
Require Import Utf8.

(* The IMM programming language does not have fetch_and_sub, so we use a CAS to decrement the counter. *)

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
        | Some v =>
          if Nat.eqb v v0 then if Nat.eqb v0 1 then Some (0, 1) else Some (0, 0)
          else Some (1, 0) (* A failed CAS simply returns the unit of global tied resource *)
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

Lemma arc_dec_reading_1_unique l ρ Θ:
  hb_consistent Σ_arc l (Some 1) (Ormw (Ocas 1 0) false Xpln Orlx Orel) (ρ, Θ) →
  Θ = O_RB.
Proof.
Admitted.

Lemma arc_fence_no_global_resources l ρ Θ:
  hb_consistent Σ_arc l None (Ofence Oacq) (ρ, Θ) →
  ρ = 0.
Proof.
Admitted.
