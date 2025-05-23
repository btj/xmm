(*

Work-in-progress mechanisation of

Bart Jacobs and Justus Fasse. An approach for modularly verifying the core of Rust's atomic reference counting algorithm against the (X)C20 memory consistency model. 2025. https://arxiv.org/abs/2505.00449

*)

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Core.
Require Import Utf8.
Require Import xmm_s_hb.

Inductive op :=
| Oload (ord:mode)
| Ostore (ord:mode) (val: value)
| Ormw (f: value → option value) (rexmod:bool) (xmod:x_mode) (ordr ordw:mode)
| Ofence (ord:mode)
.

(* For now, we fix the resource algebras for global and local tied resource to [nat]. *)
Definition RG := nat.
Definition RL := nat.
Definition RB := thread_id → RL.
Definition RT: Type := RG * RB.

Record atomic_spec := {
    v0: value;
    ρ0: RG;
    pre: op → option (RG * RL);
    post: op * option value → option (RG * RL);
}.

Inductive event_origin :=
| orig_simple (o: op)
| orig_rmw_read (o: op) (w: option actid)
| orig_rmw_write (o: op) (r: actid)
.

Inductive label_matches_origin: label → event_origin → Prop :=
| load_matches_orig_simple o l v:
    label_matches_origin (Aload false o l v) (orig_simple (Oload o))
| store_matches_orig_simple o l v:
    label_matches_origin (Astore Xpln o l v) (orig_simple (Ostore o v))
| fence_matches_orig_simple o:
    label_matches_origin (Afence o) (orig_simple (Ofence o))
| load_matches_orig_rmw_read f rexmod xmod ordr ordw l v w:
    label_matches_origin (Aload rexmod ordr l v) (orig_rmw_read (Ormw f rexmod xmod ordr ordw) w)
| store_matches_orig_rmw_write f rexmod xmod ordr ordw l v r:
    label_matches_origin (Astore xmod ordw l v) (orig_rmw_write (Ormw f rexmod xmod ordr ordw) r)
.

Definition ops_of_event(t: thread_id)(orig: event_origin)(v: option value): list (thread_id * (op * option value)) :=
    match orig with
    | orig_simple o | orig_rmw_read o _ => [(t, (o, v))]
    | orig_rmw_write _ _ => []
    end.

Fixpoint run(S: atomic_spec)(ω0: RT)(es: list (thread_id * (op * option value))): option RT :=
    match es with
    | [] => Some ω0
    | (t, (o, v)) :: es' =>
        match S.(pre) o with
        | None => None
        | Some (ρ, θ) =>
            let (ρ0, Θ0) := ω0 in
            if negb (Nat.leb ρ ρ0 && Nat.leb θ (Θ0 t)) then
                None
            else
            match S.(post) (o, v) with
            | None => None
            | Some (ρ', θ') =>
                let ρ' := ρ0 - ρ + ρ' in
                let Θ' := upd Θ0 t (Θ0 t - θ + θ') in
                run S (ρ', Θ') es'
            end
        end
    end.

Record hb_consistent(S: atomic_spec)(l: location)(v: option value)(o: op)(ω: RT) :=
{
    G: execution;
    HGWf: Wf G;
    HGcons: WCore.is_cons G;

    init: actid;
    Hinit_acts: G.(acts_set) init;
    Hinit_loc: loc G.(lab) init = Some l;
    Hinit_is_w: is_w G.(lab) init;
    Hinit_mod: mod G.(lab) init = Opln;
    Hint_val: val G.(lab) init = Some S.(v0);

    E: actid → Prop;
    HE_acts: E ⊆₁ G.(acts_set);
    HE_loc: ∀ a, E a → loc G.(lab) a = None ∨ loc G.(lab) a = Some l;
    HE_sb_init: ∀ a, E a → hb G init a;
    HE_rf_complete: ∀ a b, E b → rf G a b → a = init ∨ E a;

    orig: actid → event_origin;
    Hlab_matches_orig: ∀ a, E a → label_matches_origin (G.(lab) a) (orig a);
    Horig_simple: ∀ a o,
        E a → orig a = orig_simple o →
        S.(post) (o, val G.(lab) a) <> None;
    Horig_rmw_read_None: ∀ a f rexmod xmod ordr ordw v,
        E a → orig a = orig_rmw_read (Ormw f rexmod xmod ordr ordw) None →
        val G.(lab) a = Some v →
        f v = None ∧ S.(post) (o, Some v) <> None;
    Horig_rmw_read_Some: ∀ a f rexmod xmod ordr ordw v0 v1 w,
        E a → orig a = orig_rmw_read (Ormw f rexmod xmod ordr ordw) (Some w) →
        E w →
        val G.(lab) a = Some v0 →
        val G.(lab) w = Some v1 →
        orig w = orig_rmw_write (Ormw f rexmod xmod ordr ordw) a ∧
        f v0 = Some v1 ∧
        rmw G a w ∧
        S.(post) (o, Some v0) <> None;
    Horig_rmw_write: ∀ a f rexmod xmod ordr ordw r,
        E a → orig a = orig_rmw_write (Ormw f rexmod xmod ordr ordw) r →
        E r ∧
        orig r = orig_rmw_read (Ormw f rexmod xmod ordr ordw) (Some a) ∧
        rmw G r a;

    e: actid;
    HE_e: E e;
    He_val: val G.(lab) e = v;
    He_orig: orig e = orig_simple o ∨ ∃ w, orig e = orig_rmw_read o w;

    E': actid → Prop;
    HE'_acts: E' ⊆₁ E;
    HE'_hb1: ∀a, E a → hb G a e → E' a;
    HE'_e: ¬ E' e;
    HE'_hb2: ∀ a, E a → hb G e a → ¬ E' a;
    Homega: ∀ es f,
        (* es contains each element of E' exactly once *)
        (∀ a, E' a → nth_error es (f a) = Some a) →
        (∀ k a, nth_error es k = Some a → E' a /\ f a = k) →
        (* the order is consistent with hb *)
        (∀ a b, E' a → E' b → hb G a b → f a < f b) →
        run S (S.(ρ0), λ _, 0) (flat_map (λ a, ops_of_event (tid a) (orig a) (val G.(lab) a)) es) = Some ω;
}.

From imm Require Import ProgToExecution.

(* There is no allocation or deallocation; all locations have a value from the start.
   But a location l is temporarily removed from the regular heap during a nonatomic write
   and between a begin_atomic l and an end_atomic l. *)
Definition heap := location → option value.
Definition atomic_heap := location → option (atomic_spec * RT).

Inductive opsem_pc :=
| AboutToExecute (pc:nat)
| Executing (pc:nat) (* Executing a nonatomic write. *)
.

Record thread_cfg := {
    regf: RegFile.t;
    pc: opsem_pc;
}.

Record cfg := {
    h : heap;
    A : atomic_heap;
    T : thread_id → thread_cfg;
}.
