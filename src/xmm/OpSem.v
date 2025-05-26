(*

Work-in-progress mechanisation of

Bart Jacobs and Justus Fasse. An approach for modularly verifying the core of Rust's atomic reference counting algorithm against the (X)C20 memory consistency model. 2025. https://arxiv.org/abs/2505.00449

*)

From hahn Require Export Hahn.
From hahnExt Require Export HahnExt.
From imm Require Export Events Execution.
Require Export Core.
Require Export Utf8.
Require Export xmm_s_hb.

Inductive f_rmw :=
| Ofetch_add (addendum: value)
| Ocas (old: value) (new: value)
| Oexchange (new: value)
.

Definition eval_f_rmw (f: f_rmw) (v: value): option value :=
    match f with
    | Ofetch_add addendum => Some (v + addendum)
    | Ocas old new =>
        if Nat.eqb v old then Some new else None
    | Oexchange new => Some new
    end.

Inductive op :=
| Oload (ord:mode)
| Ostore (ord:mode) (val: value)
| Ormw (f: f_rmw) (rexmod:bool) (xmod:x_mode) (ordr ordw:mode)
| Ofence (ord:mode)
.

(* For now, we fix the resource algebras for global and local tied resource to [nat]. *)
Definition RG := nat.
Definition RL := nat.
Definition RB := thread_id → RL.
Definition RT: Type := RG * RB.

Definition O_RB: RB := λ _, 0.

Definition compose (ω1 ω2: RT): RT :=
    let (ρ1, Θ1) := ω1 in
    let (ρ2, Θ2) := ω2 in
    (ρ1 + ρ2, λ t, Θ1 t + Θ2 t).

Record atomic_spec := {
    v0: value;
    ρ0: RG;
    pre: op → option (RG * RL);
    post: op → option value → option (RG * RL);
}.

Inductive event_origin :=
| orig_simple (o: op)
| orig_rmw_read (o: op) (w: option actid)
| orig_rmw_write (o: op) (r: actid) (vr: value)
.

Inductive label_matches_origin: label → event_origin → Prop :=
| load_matches_orig_simple o l v:
    label_matches_origin (Aload false o l v) (orig_simple (Oload o))
| store_matches_orig_simple o l v:
    label_matches_origin (Astore Xpln o l v) (orig_simple (Ostore o v))
| fence_matches_orig_simple o:
    label_matches_origin (Afence o) (orig_simple (Ofence o))
| load_matches_orig_rmw_read f rexmod xmod ordr ordw l v w
    (Hrmw_read_None: w = None ↔ eval_f_rmw f v = None):
    label_matches_origin (Aload rexmod ordr l v) (orig_rmw_read (Ormw f rexmod xmod ordr ordw) w)
| store_matches_orig_rmw_write f rexmod xmod ordr ordw l v r vr:
    label_matches_origin (Astore xmod ordw l v) (orig_rmw_write (Ormw f rexmod xmod ordr ordw) r vr)
.

Definition ops_of_event(t: thread_id)(orig: event_origin)(v: option value): list (thread_id * (op * option value)) :=
    match orig with
    | orig_simple o => [(t, (o, v))]
    | orig_rmw_read o None => [(t, (o, v))]
    | orig_rmw_read _ _ => []
    | orig_rmw_write o _ vr => [(t, (o, Some vr))]
    end.

Fixpoint run(Σ: atomic_spec)(ω0: RT)(es: list (thread_id * (op * option value))): option RT :=
    match es with
    | [] => Some ω0
    | (t, (o, v)) :: es' =>
        match Σ.(pre) o with
        | None => None
        | Some (ρ, θ) =>
            let (ρ0, Θ0) := ω0 in
            if negb (Nat.leb ρ ρ0 && Nat.leb θ (Θ0 t)) then
                None
            else
            match Σ.(post) o v with
            | None => None
            | Some (ρ', θ') =>
                let ρ' := ρ0 - ρ + ρ' in
                let Θ' := upd Θ0 t (Θ0 t - θ + θ') in
                run Σ (ρ', Θ') es'
            end
        end
    end.

Record hb_consistent(Σ: atomic_spec)(t: thread_id)(l: location)(v: option value)(o: op)(ω: RT) :=
{
    G: execution;
    HG_Wf: Wf G;
    HG_cons: WCore.is_cons G;
    HG_rf_complete: complete G;

    init: actid;
    Hinit_acts: G.(acts_set) init;
    Hinit_loc: loc G.(lab) init = Some l;
    Hinit_is_w: is_w G.(lab) init;
    Hinit_mod: mod G.(lab) init = Opln;
    Hinit_val: val G.(lab) init = Some Σ.(v0);

    E: actid → Prop;
    HE_acts: E ⊆₁ G.(acts_set);
    HE_loc: ∀ a, E a → loc G.(lab) a = None ∨ loc G.(lab) a = Some l;
    HE_hb_init: ∀ a, E a → hb G init a;
    HE_rf_complete: ∀ a b, E b → rf G a b → a = init ∨ E a;

    (* Expresses well-foundedness of co within E *)
    co_rank: actid -> nat;
    Hco_rank_co: ∀ a1 a2, E a1 → E a2 → co G a1 a2 → co_rank a1 < co_rank a2;

    orig: actid → event_origin;
    Hlab_matches_orig: ∀ a, E a → label_matches_origin (G.(lab) a) (orig a);
    Horig_simple: ∀ a o,
        E a → orig a = orig_simple o →
        Σ.(post) o (val G.(lab) a) <> None;
    Horig_rmw_read_None: ∀ a f rexmod xmod ordr ordw v,
        orig a = orig_rmw_read (Ormw f rexmod xmod ordr ordw) None →
        E a →
        val G.(lab) a = Some v →
        eval_f_rmw f v = None ∧
        Σ.(post) (Ormw f rexmod xmod ordr ordw) (Some v) <> None;
    Horig_rmw_read_Some: ∀ a f rexmod xmod ordr ordw v0 v1 w,
        orig a = orig_rmw_read (Ormw f rexmod xmod ordr ordw) (Some w) →
        E a →
        E w →
        val G.(lab) a = Some v0 →
        val G.(lab) w = Some v1 →
        orig w = orig_rmw_write (Ormw f rexmod xmod ordr ordw) a v0 ∧
        eval_f_rmw f v0 = Some v1 ∧
        rmw G a w;
    Horig_rmw_write: ∀ a f rexmod xmod ordr ordw r vr,
        orig a = orig_rmw_write (Ormw f rexmod xmod ordr ordw) r vr →
        E a →
        E r ∧
        orig r = orig_rmw_read (Ormw f rexmod xmod ordr ordw) (Some a) ∧
        rmw G r a ∧
        Σ.(post) (Ormw f rexmod xmod ordr ordw) (Some vr) <> None;

    e: actid;
    HE_e: E e;
    He_tid: tid e = t;
    He_orig:
        (orig e = orig_simple o ∨ orig e = orig_rmw_read o None) ∧ v = val G.(lab) e ∨
        ∃ r vr, orig e = orig_rmw_write o r vr ∧ v = Some vr;

    E': actid → Prop;
    HE'_acts: E' ⊆₁ E;
    HE'_hb1: ∀a, E a → hb G a e → E' a;
    HE'_e: ¬ E' e;
    HE'_hb2: ∀ a, E a → hb G e a → ¬ E' a;

    (* Expresses finiteness of E' *)
    es'0: list actid;
    f_es'0: actid → nat;
    Hf_es'0: ∀ a, E' a → nth_error es'0 (f_es'0 a) = Some a;
    Hes'0: ∀ k a, nth_error es'0 k = Some a → E' a ∧ f_es'0 a = k;
    Hhb_es'0: ∀ a b, E' a → E' b → hb G a b → f_es'0 a < f_es'0 b;
    Hco_es'0: ∀ a b, E' a → E' b → co G a b → f_es'0 a < f_es'0 b; (* For convenience, we pick as the canonical order one that is consistent with co. *)

    (* Expresses the order of es'0 is consistent with rf *)

    (* Expresses the order of es'0 is consistent with hb *)

    Homega: ∀ es f,
        (* es contains each element of E' exactly once *)
        (∀ a, E' a → nth_error es (f a) = Some a) →
        (∀ k a, nth_error es k = Some a → E' a ∧ f a = k) →
        (* the order is consistent with hb *)
        (∀ a b, E' a → E' b → hb G a b → f a < f b) →
        run Σ (Σ.(ρ0), O_RB) (flat_map (λ a, ops_of_event (tid a) (orig a) (val G.(lab) a)) es) = Some ω;
}.

Definition atomic_spec_pre_sufficient (Σ: atomic_spec)(o: op): Prop :=
  False. (* TODO: Weaken. For now, we consider programs with plain accesses only. *)

Definition is_valid_atomic_spec (Σ: atomic_spec): Prop :=
  (∀ mod, Σ.(pre) (Ofence mod) = Some (0, 0)) ∧
  (∀ mod, Σ.(post) (Ofence mod) None = Some (0, 0)) ∧
  ∀ o, atomic_spec_pre_sufficient Σ o.

From imm Require Import ProgToExecution.

(* There is no allocation or deallocation; all locations have a value from the start.
   But a location l is temporarily removed from the regular heap during a nonatomic write
   and between a begin_atomic l and an end_atomic l. *)
Definition heap := location → option value.
Definition atomic_heap := location → option (atomic_spec * RT).
Record state := {
    h: heap;
    A: atomic_heap
}.

Definition with_heap (σ: state)(h': heap): state :=
  {| h := h'; A := σ.(A) |}.
Definition with_atomic_heap (σ: state)(A': atomic_heap): state :=
  {| h := σ.(h); A := A' |}.

Inductive opsem_pc :=
| AboutToExecute (pc:nat)
| Executing (pc:nat) (* Executing a nonatomic write. *)
.

Record thread_cfg := {
    regf: RegFile.t;
    pc: opsem_pc;
}.

Definition tcfg_init := 
  {| regf := RegFile.init; pc := AboutToExecute 0 |}.

Record cfg := {
    σ : state;
    T : thread_id → thread_cfg;
}.

Section Prog.

Variable prog: Prog.Prog.t.

Definition instr t pc :=
  match Basic.IdentMap.find t prog with
  | Some instrs => nth_error instrs pc
  | None => None
  end.

Inductive annotation :=
| NoAnnotation
| BeginAtomic(Σ: atomic_spec)
| EndAtomic
.

Variable init_annot: location → annotation.
Variable instr_annot: thread_id → nat → annotation.

Hypothesis init_annot_valid:
  ∀ l, match init_annot l with
    BeginAtomic Σ => is_valid_atomic_spec Σ ∧ Σ.(v0) = 0
  | _ => True
  end.
Hypothesis instr_annot_valid:
  ∀ t pc, match instr_annot t pc with
    NoAnnotation => True
  | BeginAtomic Σ => is_valid_atomic_spec Σ
  | EndAtomic => True
  end.

(* The initial state of the program. *)

Definition h_init: heap := λ l, match init_annot l with BeginAtomic Σ => None | _ => Some 0 end.
Definition A_init: atomic_heap := λ l, match init_annot l with BeginAtomic Σ => Some (Σ, (Σ.(ρ0), O_RB)) | _ => None end.
Definition σ_init := {| h:=h_init; A:=A_init |}.

Definition γ_init := 
  {| σ := σ_init; T := fun t => tcfg_init |}.

Definition eval_rmw(regf: RegFile.t)(rmw: Prog.Instr.rmw): f_rmw :=
  match rmw with
  | Prog.Instr.fetch_add addendum => Ofetch_add (RegFile.eval_expr regf addendum)
  | Prog.Instr.cas old new => Ocas (RegFile.eval_expr regf old) (RegFile.eval_expr regf new)
  | Prog.Instr.exchange new => Oexchange (RegFile.eval_expr regf new)
  end.

Inductive tstep: state → thread_cfg → thread_id → state → thread_cfg → Prop :=
  tstep_assign σ regf pc t reg expr:
    instr t pc = Some (Prog.Instr.assign reg expr) →
    tstep
      σ
      {|
        regf:=regf;
        pc:=(AboutToExecute pc)
      |}
      t
      σ
      {|
        regf:= Prog.RegFun.add reg (RegFile.eval_expr regf expr) regf;
        pc:=AboutToExecute (S pc)
      |}
| tstep_if σ regf pc t cond pc':
    instr t pc = Some (Prog.Instr.ifgoto cond pc') →
    tstep
      σ
      {|
        regf:=regf;
        pc:=AboutToExecute pc
      |}
      t
      σ
      {|
        regf:=regf;
        pc:=AboutToExecute (if Prog.Const.eq_dec (RegFile.eval_expr regf cond) 0 then S pc else pc')
      |}
| tstep_load_pln σ regf pc t lhs l v:
    instr t pc = Some (Prog.Instr.load Opln lhs l) →
    σ.(h) (RegFile.eval_lexpr regf l) = Some v →
    tstep
      σ
      {|
        regf:=regf;
        pc:=AboutToExecute pc
      |}
      t
      σ
      {|
        regf:=Prog.RegFun.add lhs v regf;
        pc:=AboutToExecute (S pc)
      |}
| tstep_store_pln σ regf pc t l rhs v0:
    instr_annot t pc = NoAnnotation →
    instr t pc = Some (Prog.Instr.store Opln l rhs) →
    σ.(h) (RegFile.eval_lexpr regf l) = Some v0 →
    tstep
      σ
      {|
        regf:=regf;
        pc:=AboutToExecute pc
      |}
      t
      (with_heap σ (upd σ.(h) (RegFile.eval_lexpr regf l) None))
      {|
        regf:=regf;
        pc:=Executing pc
      |}
| tstep_store_pln' σ regf pc t l rhs:
    instr t pc = Some (Prog.Instr.store Opln l rhs) →
    tstep
      σ
      {|
        regf:=regf;
        pc:=Executing pc
      |}
      t
      (with_heap σ (upd σ.(h) (RegFile.eval_lexpr regf l) (Some (RegFile.eval_expr regf rhs))))
      {|
        regf:=regf;
        pc:=AboutToExecute (S pc)
      |}
| tstep_begin_atomic σ regf pc t Σ l rhs v_0:
    instr_annot t pc = BeginAtomic Σ →
    instr t pc = Some (Prog.Instr.store Opln l rhs) →
    σ.(h) (RegFile.eval_lexpr regf l) = Some v_0 →
    Σ.(v0) = RegFile.eval_expr regf rhs →
    tstep
      σ
      {|
        regf:=regf;
        pc:=AboutToExecute pc
      |}
      t
      {|
        h:=upd σ.(h) (RegFile.eval_lexpr regf l) None;
        A:=upd σ.(A) (RegFile.eval_lexpr regf l) (Some (Σ, (Σ.(ρ0), O_RB)))
      |}
      {|
        regf:=regf;
        pc:=AboutToExecute (S pc)
      |}
| tstep_end_atomic σ regf pc t l rhs Σ ω:
    instr_annot t pc = EndAtomic →
    instr t pc = Some (Prog.Instr.store Opln l rhs) →
    σ.(A) (RegFile.eval_lexpr regf l) = Some (Σ, ω) →
    tstep
      σ
      {|
        regf:=regf;
        pc:=AboutToExecute pc
      |}
      t
      {|
        h:=upd σ.(h) (RegFile.eval_lexpr regf l) (Some (RegFile.eval_expr regf rhs));
        A:=upd σ.(A) (RegFile.eval_lexpr regf l) None
      |}
      {|
        regf:=regf;
        pc:=AboutToExecute (S pc)
      |}
| tstep_rmw_stutter σ regf pc t rmw rexmod xmod ordr ordw lhs l Σ ω ρ_pre θ_pre ω_frame:
    instr t pc = Some (Prog.Instr.update rmw rexmod xmod ordr ordw lhs l) →
    σ.(A) (RegFile.eval_lexpr regf l) = Some (Σ, ω) →
    Σ.(pre) (Ormw (eval_rmw regf rmw) rexmod xmod ordr ordw) = Some (ρ_pre, θ_pre) →
    ω = compose ω_frame (ρ_pre, upd O_RB t θ_pre) →
    tstep
      σ
      {|
        regf:=regf;
        pc:=AboutToExecute pc
      |}
      t
      σ
      {|
        regf:=regf;
        pc:=AboutToExecute pc
      |}
| tstep_rmw σ regf pc t rmw rexmod xmod ordr ordw lhs l Σ ω ρ_pre θ_pre ω_frame v ρ_post θ_post:
    instr t pc = Some (Prog.Instr.update rmw rexmod xmod ordr ordw lhs l) →
    σ.(A) (RegFile.eval_lexpr regf l) = Some (Σ, ω) →
    Σ.(pre) (Ormw (eval_rmw regf rmw) rexmod xmod ordr ordw) = Some (ρ_pre, θ_pre) →
    ω = compose ω_frame (ρ_pre, upd O_RB t θ_pre) →
    Σ.(post) (Ormw (eval_rmw regf rmw) rexmod xmod ordr ordw) (Some v) = Some (ρ_post, θ_post) →
    hb_consistent Σ t (RegFile.eval_lexpr regf l) (Some v) (Ormw (eval_rmw regf rmw) rexmod xmod ordr ordw) ω →
    tstep
      σ
      {|
        regf:=regf;
        pc:=AboutToExecute pc
      |}
      t
      (with_atomic_heap σ (upd σ.(A) (RegFile.eval_lexpr regf l) (Some (Σ, compose ω_frame (ρ_post, upd O_RB t θ_post)))))
      {|
        regf:=Prog.RegFun.add lhs v regf;
        pc:=AboutToExecute (S pc)
      |}
| tstep_fence_stutter σ regf pc t ord:
    instr t pc = Some (Prog.Instr.fence ord) →
    tstep
      σ
      {|
        regf:=regf;
        pc:=AboutToExecute pc
      |}
      t
      σ
      {|
        regf:=regf;
        pc:=AboutToExecute pc
      |}
| tstep_fence σ regf pc t ord:
    instr t pc = Some (Prog.Instr.fence ord) →
    (∀ l Σ ω, σ.(A) l = Some (Σ, ω) → hb_consistent Σ t l None (Ofence ord) ω) →
    tstep
      σ
      {|
        regf:=regf;
        pc:=AboutToExecute pc
      |}
      t
      σ
      {|
        regf:=regf;
        pc:=AboutToExecute (S pc)
      |}
.

Inductive step: cfg → cfg → Prop :=
  step_intro σ T t σ' tcfg':
    tstep σ (T t) t σ' tcfg' →
    step (Build_cfg σ T) (Build_cfg σ' (upd T t tcfg'))
.

Definition thread_finished (γ: cfg) (t: thread_id): bool :=
  match Basic.IdentMap.find t prog with
    None => true
  | Some instrs =>
    match (γ.(T) t).(pc) with
    | AboutToExecute pc =>
      match nth_error instrs pc with
      | None => true
      | Some _ => false
      end
    | Executing _ => false
    end
  end.

Definition thread_ok (γ: cfg) (t: thread_id): Prop :=
  thread_finished γ t ∨
  ∃ σ' tcfg', tstep γ.(σ) (γ.(T) t) t σ' tcfg'.

Definition cfg_safe (γ: cfg): Prop :=
  ∀ γ', step^* γ γ' → ∀ t, thread_ok γ t.

Definition prog_safe := cfg_safe γ_init.

(*

[is_thread_state_trace t s trace] says that [trace] is a *finite* prefix of a trace for thread state [s].

Turning this into a coinductive definition naively does not work, because a thread that goes into an infinite loop without
performing any memory operations would have any trace.

The absence of infinite traces does not matter for XMM because under XMM all executions are finite.

*)

Inductive is_thread_state_trace (t: thread_id): ProgToExecution.state → trace label → Prop :=
| is_thread_trace_nil s: is_thread_state_trace t s (trace_fin [])
| is_thread_trace_nonnil lbls s s' trace:
  istep t lbls s s' →
  is_thread_state_trace t s' trace →
  is_thread_state_trace t s (trace_app (trace_fin (List.rev lbls)) trace).

(* The given trace is a finite prefix of a trace for the given thread. *)
Definition is_thread_trace t trace :=
  match Basic.IdentMap.find t prog with
    None => trace = trace_fin []
  | Some instrs =>
    is_thread_state_trace t (init instrs) trace
  end.

(*

The program has the given execution.

Note: the execution is not necessarily complete, in the sense that some threads may not yet have finished.

*)

Definition prog_has_xc20_execution (G: execution): Prop :=
  ∃ threads sc0 sc',
    (xmm_step_trace is_thread_trace)^* {| WCore.G:=WCore.init_exec threads; WCore.sc:=sc0 |} {| WCore.G:=G; WCore.sc:=sc' |}.

Definition is_race G a1 a2 := race_mod G Opln a1 a2.

Theorem safe_programs_have_no_races:
  ∀ G,
  prog_safe →
  prog_has_xc20_execution G →
  ∀ a1 a2, ~ is_race G a1 a2.
Proof.
Admitted.

End Prog.