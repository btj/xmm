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
    | Ofence Oacq => match v with None => Some (0, 1) | Some _ => None end
    | _ => None
    end.

Inductive post_arc_: op -> option value -> RG * RL -> Prop :=
| post_arc_fetch_add_1 n:
    post_arc_ (Ormw (Ofetch_add 1) false Xpln Orlx Orlx) (Some (S n)) (2, 0)
| post_arc_cas_1:
    post_arc_ (Ormw (Ocas 1 0) false Xpln Orlx Orel) (Some 1) (0, 1)
| post_arc_cas n:
    post_arc_ (Ormw (Ocas (S (S n)) (S n)) false Xpln Orlx Orel) (Some (S (S n))) (0, 0)
| post_arc_cas_fail n m:
    m <> n →
    post_arc_ (Ormw (Ocas (S n) n) false Xpln Orlx Orel) (Some (S m)) (1, 0)
| post_arc_fence:
    post_arc_ (Ofence Oacq) None (0, 1)
.

Lemma post_arc__sound o v ρ:
  post_arc_ o v ρ →
  post_arc o v = Some ρ.
Proof.
  intros.
  inversion H; subst; try reflexivity; simpl; rewrite PeanoNat.Nat.eqb_refl; simpl; try reflexivity.
  rewrite <- PeanoNat.Nat.eqb_neq in H0.
  rewrite H0.
  reflexivity.
Qed.

Lemma post_arc__complete o v ρ:
  post_arc o v = Some ρ →
  post_arc_ o v ρ.
Proof.
  destruct o; simpl in *; intros; try discriminate.
  - destruct f; try discriminate.
    + destruct addendum; try discriminate.
      destruct addendum; try discriminate.
      destruct rexmod; try discriminate.
      destruct xmod; try discriminate.
      destruct ordr; try discriminate.
      destruct ordw; try discriminate.
      destruct v; try discriminate.
      destruct n; try discriminate.
      injection H; clear H; intros; subst.
      constructor.
    + destruct rexmod; try discriminate.
      destruct xmod; try discriminate.
      destruct ordr; try discriminate.
      destruct ordw; try discriminate.
      case_eq (Nat.eqb old (S new)); intros; rewrite H0 in H; try discriminate.
      apply PeanoNat.Nat.eqb_eq in H0. subst.
      destruct v; try discriminate.
      destruct n; try discriminate.
      case_eq (Nat.eqb (S n) (S new)); intros; rewrite H0 in H; try discriminate.
      * apply PeanoNat.Nat.eqb_eq in H0.
        injection H0; clear H0; intros; subst.
        case_eq (Nat.eqb (S new) 1); intros; rewrite H0 in H; try discriminate.
        -- injection H; clear H; intros; subst.
           apply PeanoNat.Nat.eqb_eq in H0.
           injection H0; clear H0; intros; subst.
           apply post_arc_cas_1.
        -- destruct new; try discriminate.
           injection H; clear H; intros; subst.
           apply post_arc_cas.
      * injection H; clear H; intros; subst.
        apply post_arc_cas_fail.
        apply PeanoNat.Nat.eqb_neq in H0.
        congruence.
  - destruct ord; try discriminate.
    destruct v; try discriminate.
    injection H; clear H; intros; subst.
    apply post_arc_fence.
Qed.

Lemma post_arc_rmw_reading_0 f modw:
  post_arc (Ormw f false Xpln Orlx modw) (Some 0) = None.
Proof.
  destruct f.
  + destruct addendum.
    * reflexivity.
    * destruct addendum.
      -- destruct modw; simpl; try reflexivity.
      -- reflexivity.
  + destruct modw; try reflexivity.
    simpl.
    destruct (Nat.eqb old (S new)); reflexivity.
  + reflexivity.
Qed.

Definition Σ_arc: atomic_spec := {|
    v0 := 1;
    ρ0 := 1;
    pre := pre_arc;
    post := post_arc;
|}.

Lemma upd_O_RB_0 (t: thread_id): upd O_RB t 0 = O_RB.
Proof.
  unfold upd, O_RB.
  apply functional_extensionality.
  intro t'.
  destruct (excluded_middle_informative (t' = t)); reflexivity.
Qed.

Lemma arc_run_produces_local_resource (tid: actid → thread_id) orig lab ρ Θ:
  ∀ es ρ0,
  Forall (λ a, label_matches_origin (lab a) (orig a) ∧ ¬ ∃ r, orig a = orig_rmw_write (Ormw (Ocas 1 0) false Xpln Orlx Orel) r 1) es →
  run Σ_arc (ρ0, O_RB) (flat_map (λ a, ops_of_event (tid a) (orig a) (val lab a)) es) = Some (ρ, Θ) →
  Θ = O_RB.
Proof.
  induction es; intros ρ0 Hfor Hrun. {
    simpl in Hrun.
    inversion Hrun; subst.
    reflexivity.
  }
  simpl in Hrun.
  inversion Hfor; subst.
  clear Hfor; rename H1 into Ha; rename H2 into Hfor.
  destruct Ha as [Hlab Horig].
  inversion Hlab; subst; rewrite <- H in Hrun; try discriminate; simpl in Hrun.
  - (* fence *)
    destruct o; try discriminate.
  - (* rmw read *)
    destruct w; try discriminate.
    + (* successful rmw *)
      apply IHes with (ρ0 := ρ0); assumption.
    + (* failed rmw *)
      simpl in Hrun.
      destruct f; try discriminate.
      * destruct addendum; try discriminate.
        destruct addendum; try discriminate.
        destruct rexmod; try discriminate.
        destruct xmod; try discriminate.
        destruct ordr; try discriminate.
        destruct ordw; try discriminate.
        case_eq (Nat.leb 1 ρ0); intros; rewrite H1 in Hrun; try discriminate.
        simpl in Hrun.
        unfold val in Hrun.
        rewrite <- H0 in Hrun.
        destruct v; try discriminate.
        rewrite upd_O_RB_0 in Hrun.
        apply IHes with (1:=Hfor) (2:=Hrun).
      * destruct Hrmw_read_None as [Hrmw_read_None _].
        lapply Hrmw_read_None. 2:reflexivity. clear Hrmw_read_None. intro Hrmw_read_None.
        simpl in Hrmw_read_None.
        destruct rexmod; try discriminate.
        destruct xmod; try discriminate.
        destruct ordr; try discriminate.
        destruct ordw; try discriminate.
        case_eq (Nat.eqb old (S new)); intros; rewrite H1 in Hrun; try discriminate.
        apply PeanoNat.Nat.eqb_eq in H1; subst.
        case_eq (Nat.leb 1 ρ0); intros; rewrite H1 in Hrun; try discriminate.
        simpl in Hrun.
        unfold val in Hrun.
        rewrite <- H0 in Hrun.
        destruct v; try discriminate.
        case_eq (Nat.eqb (S v) (S new)); intros. {
          rewrite H2 in Hrmw_read_None; discriminate.
        }
        rewrite H2 in Hrun; try discriminate.
        rewrite upd_O_RB_0 in Hrun.
        apply IHes with (1:=Hfor) (2:=Hrun).
  - (* rmw write *)
      destruct f; try discriminate.
      * destruct addendum; try discriminate.
        destruct addendum; try discriminate.
        destruct rexmod; try discriminate.
        destruct xmod; try discriminate.
        destruct ordr; try discriminate.
        destruct ordw; try discriminate.
        case_eq (Nat.leb 1 ρ0); intros; rewrite H1 in Hrun; try discriminate.
        simpl in Hrun.
        destruct vr; try discriminate.
        rewrite upd_O_RB_0 in Hrun.
        apply IHes with (1:=Hfor) (2:=Hrun).
      * destruct rexmod; try discriminate.
        destruct xmod; try discriminate.
        destruct ordr; try discriminate.
        destruct ordw; try discriminate.
        case_eq (Nat.eqb old (S new)); intros; rewrite H1 in Hrun; try discriminate.
        apply PeanoNat.Nat.eqb_eq in H1; subst.
        case_eq (Nat.leb 1 ρ0); intros; rewrite H1 in Hrun; try discriminate.
        simpl in Hrun.
        destruct vr; try discriminate.
        case_eq (Nat.eqb (S vr) (S new)); intros; rewrite H2 in Hrun; try discriminate.
        -- case_eq (Nat.eqb new 0); intros; rewrite H3 in Hrun; try discriminate.
           ++ elim Horig.
              exists r.
              apply PeanoNat.Nat.eqb_eq in H2.
              injection H2; clear H2; intros; subst.
              apply PeanoNat.Nat.eqb_eq in H3. subst.
              congruence.
           ++ rewrite upd_O_RB_0 in Hrun.
              apply IHes with (1:=Hfor) (2:=Hrun).
        -- rewrite upd_O_RB_0 in Hrun.
           apply IHes with (1:=Hfor) (2:=Hrun).
Qed.

Lemma arc_dec_reading_1_unique l ρ Θ:
  hb_consistent Σ_arc l (Some 1) (Ormw (Ocas 1 0) false Xpln Orlx Orel) (ρ, Θ) →
  Θ = O_RB.
Proof.
  intro Hhb_consistent.
  destruct Hhb_consistent.
  assert
      (Hlem:
       ∀ n a1 a2 r1 f2 modw2 r2 v2,
       E a1 → E a2 →
       co_rank a2 = n →
       orig a1 = orig_rmw_write (Ormw (Ocas 1 0) false Xpln Orlx Orel) r1 1 →
       orig a2 = orig_rmw_write (Ormw f2 false Xpln Orlx modw2) r2 v2 →
       co G a1 a2 →
       False). {
    intro n.
    apply (well_founded_induction Wf_nat.lt_wf) with (a:=n).
    clear n.
    intros n IH a1 a2 r1 f2 modw2 r2 v2 Ha1 Ha2 Hco_rank Horig1 Horig2 Hco.

    assert (Ha1_lab: ∃ v, lab G a1 = Astore Xpln Orel l v). {
      pose proof (Hlab_matches_orig a1 Ha1).
      rewrite Horig1 in H.
      inversion H.
      subst.
      pose proof (HE_loc a1 Ha1).
      unfold loc in H0.
      rewrite <- H1 in H0.
      destruct H0; try discriminate.
      exists v.
      congruence.
    }
    destruct Ha1_lab as [v_a1 Ha1_lab].

    assert (Hval_a1: val G.(lab) a1 = Some v_a1). {
      unfold val.
      rewrite Ha1_lab.
      reflexivity.
    }

    pose proof (Horig1' := Horig1).
    apply Horig_rmw_write in Horig1'. 2: assumption.
    destruct Horig1' as [Hr1 [Horig_r1 [Hrmw1 Hpost1]]].

    assert (Hr1_lab: ∃ v_r1, lab G r1 = Aload false Orlx l v_r1). {
      pose proof (Hr1' := Hr1).
      apply Hlab_matches_orig in Hr1'.
      rewrite Horig_r1 in Hr1'.
      inversion Hr1'.
      subst.
      pose proof (HE_loc r1 Hr1).
      unfold loc in H.
      rewrite <- H0 in H.
      destruct H; try discriminate.
      exists v.
      congruence.
    }
    destruct Hr1_lab as [v_r1 Hr1_lab].

    assert (Hval_r1: val G.(lab) r1 = Some v_r1). {
      unfold val.
      rewrite Hr1_lab.
      reflexivity.
    }

    pose proof (Horig_r1' := Horig_r1).
    apply Horig_rmw_read_Some with (v0:=v_r1) (v1:=v_a1) in Horig_r1'; try assumption.
    destruct Horig_r1' as [Horig_a1' [Heval1 _]].
    assert (v_r1 = 1). congruence. subst v_r1.
    clear Horig_a1'.
    simpl in Heval1.
    assert (v_a1 = 0). congruence. subst v_a1.
    clear Heval1.

    assert (Ha2_lab: ∃ v, lab G a2 = Astore Xpln modw2 l v). {
      pose proof (Hlab_matches_orig a2 Ha2).
      rewrite Horig2 in H.
      inversion H.
      subst.
      pose proof (HE_loc a2 Ha2).
      unfold loc in H0.
      rewrite <- H1 in H0.
      destruct H0; try discriminate.
      exists v.
      congruence.
    }
    destruct Ha2_lab as [v_a2 Ha2_lab].
    assert (Hval_a2: val G.(lab) a2 = Some v_a2). {
      unfold val.
      rewrite Ha2_lab.
      reflexivity.
    }

    pose proof (Horig2' := Horig2).
    apply Horig_rmw_write in Horig2'. 2: assumption.
    destruct Horig2' as [Hr2 [Horig_r2 [Hrmw2 Hpost2]]].

    assert (Hr2_lab: ∃ v_r2, lab G r2 = Aload false Orlx l v_r2). {
      pose proof (Hr2' := Hr2).
      apply Hlab_matches_orig in Hr2'.
      rewrite Horig_r2 in Hr2'.
      inversion Hr2'.
      subst.
      pose proof (HE_loc r2 Hr2).
      unfold loc in H.
      rewrite <- H0 in H.
      destruct H; try discriminate.
      exists v.
      congruence.
    }
    destruct Hr2_lab as [v_r2 Hr2_lab].

    assert (Hval_r2: val G.(lab) r2 = Some v_r2). {
      unfold val.
      rewrite Hr2_lab.
      reflexivity.
    }

    pose proof (Horig_r2' := Horig_r2).
    eapply Horig_rmw_read_Some in Horig_r2'; try eassumption.
    destruct Horig_r2' as [Horig_a2' [Heval2 _]].
    assert (v_r2 = v2). congruence. subst v_r2.
    clear Horig_a2'.

    destruct (HG_rf_complete r2) as [w_r2 Hw_r2]. {
      split.
      - apply HE_acts.
        assumption.
      - unfold is_r.
        rewrite Hr2_lab.
        reflexivity.
    }

    assert (Hw_r2_acts: G.(acts_set) w_r2). {
      pose proof (HG_Wf.(wf_rfE)).
      destruct H.
      apply H in Hw_r2.
      destruct Hw_r2.
      destruct H1.
      apply H1.
    }

    assert (Hw_r2_is_w: is_w G.(lab) w_r2). {
      pose proof (HG_Wf.(wf_rfD)).
      destruct H.
      apply H in Hw_r2.
      destruct Hw_r2.
      destruct H1.
      apply H1.
    }

    assert (Hw_r2_loc: loc G.(lab) w_r2 = Some l). {
      pose proof (HG_Wf.(wf_rfl) w_r2 r2 Hw_r2).
      unfold same_loc in H.
      unfold loc in H.
      rewrite Hr2_lab in H.
      apply H.
    }

    assert (Hw_r2_val: val G.(lab) w_r2 = Some v2). {
      pose proof (HG_Wf.(wf_rfv) w_r2 r2 Hw_r2).
      congruence.
    }

    assert (Hw_r2_co: co G a1 w_r2). {
      pose proof (HG_Wf.(wf_co_total)).
      pose proof (H (Some l) w_r2).
      lapply H0. 2:{
        split.
        - split; assumption.
        - assumption.
      }
      intros.
      lapply (H1 a1). 2:{
        split.
        - split.
          + apply HE_acts.
            assumption.
          + unfold is_w.
            rewrite Ha1_lab.
            reflexivity.
        - unfold loc.
          rewrite Ha1_lab.
          reflexivity.
      }
      destruct (classic (w_r2 = a1)). {
        assert (v2 = 0). congruence. subst v2.
        rewrite post_arc_rmw_reading_0 in Hpost2.
        elim Hpost2; reflexivity.
      }
      intro.
      apply H3 in H2.
      destruct H2. {
        pose proof (HG_cons.(WCore.cons_atomicity)).
        destruct H4.
        pose proof (H4 r2 a2).
        elim H6.
        split; try assumption.
        exists a1.
        split.
        * exists w_r2.
          split.
          -- apply Hw_r2.
          -- assumption.
        * assumption.
      }
      assumption.
    }
    
    assert (HE_w_r2: E w_r2). {
      pose proof (HE_rf_complete w_r2 r2 Hr2 Hw_r2).
      destruct H. {
        subst w_r2.
        pose proof (HG_cons.(WCore.cons_coherence)).
        pose proof (H init).
        elim H0.
        exists a1.
        split.
        - apply HE_hb_init.
          assumption.
        - right.
          left.
          right.
          exists init.
          split.
          + assumption.
          + left.
            reflexivity.
      }
      assumption.
    }

    assert (Horig_w_r2: ∃ f_w_r2 modw_w_r2 r_w_r2 vr_w_r2, orig w_r2 = orig_rmw_write (Ormw f_w_r2 false Xpln Orlx modw_w_r2) r_w_r2 vr_w_r2). {
      pose proof (Hlab_matches_orig w_r2 HE_w_r2).
      unfold is_w in Hw_r2_is_w.
      case_eq (orig w_r2); intros. {
          rewrite H0 in H;
          inversion H; subst;
          rewrite <- H2 in Hw_r2_is_w; try discriminate.
          apply Horig_simple in H0; try assumption.
          elim H0; reflexivity.
      } {
          rewrite H0 in H;
          inversion H; subst;
          rewrite <- H2 in Hw_r2_is_w; try discriminate.
      }
      rewrite H0 in H;
      inversion H; subst.
      apply Horig_rmw_write in H0; try assumption.
      destruct H0 as [? [? [? Hpost_w_r2]]].
      simpl in Hpost_w_r2.
      destruct f; try discriminate.
      - destruct addendum; try (elim Hpost_w_r2; reflexivity).
        destruct addendum; try (elim Hpost_w_r2; reflexivity).
        destruct rexmod; try (elim Hpost_w_r2; reflexivity).
        destruct xmod; try (elim Hpost_w_r2; reflexivity).
        destruct ordr; try (elim Hpost_w_r2; reflexivity).
        destruct ordw; try (elim Hpost_w_r2; reflexivity).
        destruct vr; try (elim Hpost_w_r2; reflexivity).
        exists (Ofetch_add 1), Orlx, r, (S vr).
        reflexivity.
      - destruct rexmod; try (elim Hpost_w_r2; reflexivity).
        destruct xmod; try (elim Hpost_w_r2; reflexivity).
        destruct ordr; try (elim Hpost_w_r2; reflexivity).
        destruct ordw; try (elim Hpost_w_r2; reflexivity).
        case_eq (Nat.eqb old (S new)); intros. {
          rewrite H4 in Hpost_w_r2.
          destruct vr; try (elim Hpost_w_r2; reflexivity).
          exists (Ocas (S new) new), Orel, r, (S vr).
          apply PeanoNat.Nat.eqb_eq in H4.
          subst.
          reflexivity.
        }
        rewrite H4 in Hpost_w_r2.
        elim Hpost_w_r2; reflexivity.
      - elim Hpost_w_r2; reflexivity.
    }
    destruct Horig_w_r2 as [f_w_r2 [modw_w_r2 [r_w_r2 [vr_w_r2 Horig_w_r2]]]].

    eapply IH with (y:=co_rank w_r2) (a1:=a1) (a2:=w_r2); try eassumption. 2:reflexivity.
    rewrite <- Hco_rank. apply Hco_rank_co; try assumption.
    pose proof (HG_Wf.(wf_co_total)).
    pose proof (H (Some l) w_r2).
    lapply H0. 2:{
      split.
      - split; assumption.
      - assumption.
    }
    intros.
    lapply (H1 a2). 2:{
      split.
      - split.
        + apply HE_acts.
          assumption.
        + unfold is_w.
          rewrite Ha2_lab.
          reflexivity.
      - unfold loc.
        rewrite Ha2_lab.
        reflexivity.
    }
    intros.
    destruct (classic (w_r2 = a2)). {
      subst w_r2.
      apply (rmw_in_sb HG_Wf) in Hrmw2.
      apply sb_in_hb in Hrmw2.
      pose proof (HG_cons.(WCore.cons_coherence)).
      elim (H3 r2).
      exists a2.
      split. assumption.
      right.
      apply Execution_eco.rf_in_eco.
      assumption.
    }
    apply H2 in H3.
    destruct H3. assumption.
    apply (rmw_in_sb HG_Wf) in Hrmw2.
    apply sb_in_hb in Hrmw2.
    pose proof (HG_cons.(WCore.cons_coherence)).
    elim (H4 r2).
    exists a2.
    split. assumption.
    right.
    left.
    right.
    exists w_r2.
    split. assumption.
    right.
    assumption.
  }

  assert
      (Hlem1:
       ∀ a1 a2 r1 r2,
       E a1 → E a2 →
       orig a1 = orig_rmw_write (Ormw (Ocas 1 0) false Xpln Orlx Orel) r1 1 →
       orig a2 = orig_rmw_write (Ormw (Ocas 1 0) false Xpln Orlx Orel) r2 1 →
       co G a1 a2 →
       False). {
    intros a1 a2 r1 r2 Ha1 Ha2 Horig1 Horig2 Hco.
    eapply Hlem with (n:=co_rank a2) (1:=Ha1) (2:=Ha2); try eassumption.
    reflexivity.
  }

  assert (He_orig': ∃ re, orig e = orig_rmw_write (Ormw (Ocas 1 0) false Xpln Orlx Orel) re 1). {
    pose proof (Hlab_matches_orig e HE_e).
    destruct He_orig.
    * destruct H0.
      destruct H0;
      rewrite H0 in H;
      inversion H; subst.
      eapply Horig_rmw_read_None in H0; try eassumption. 2:{
          rewrite <- H1.
          reflexivity.
      }
      destruct H0.
      discriminate.
    * destruct H0 as [re [vre [Horig_re Heval]]].
      rewrite Horig_re in H.
      inversion H; subst.
      exists re. congruence.
  }
  destruct He_orig' as [re Horig'].

  assert (Hlab_e: ∃ ve, lab G e = Astore Xpln Orel l ve). {
    pose proof (Hlab_matches_orig e HE_e).
    rewrite Horig' in H.
    inversion H.
    subst.
    pose proof (HE_loc e HE_e).
    unfold loc in H0.
    rewrite <- H1 in H0.
    destruct H0; try discriminate.
    exists v.
    congruence.
  }
  destruct Hlab_e as [ve Hlab_e].

  assert (He_is_w: is_w G.(lab) e). {
    unfold is_w.
    rewrite Hlab_e.
    reflexivity.
  }

  assert (Hlem2: ∀ a r, E' a → orig a ≠ orig_rmw_write (Ormw (Ocas 1 0) false Xpln Orlx Orel) r 1). {
    intros a r Ha Horig.
    (* We now have two decrements that read 1. They are totally ordered by mo. *)
    pose proof (HG_Wf.(wf_co_total)).
    pose proof (H (Some l) a).
    lapply H0. 2:{
      split.
      - split.
        + apply HE_acts.
          apply HE'_acts.
          assumption.
        + pose proof (Hlab_matches_orig a (HE'_acts a Ha)).
          rewrite Horig in H1.
          inversion H1; subst.
          unfold is_w.
          rewrite <- H3.
          reflexivity.
      - pose proof (Hlab_matches_orig a (HE'_acts a Ha)).
        rewrite Horig in H1.
        inversion H1; subst.
        unfold loc.
        rewrite <- H3.
        pose proof (HE_loc a (HE'_acts a Ha)).
        unfold loc in H2.
        rewrite <- H3 in H2.
        destruct H2; try discriminate.
        congruence.
    }
    intros.
    lapply (H1 e). 2:{
      split.
      - split.
        + apply HE_acts.
          assumption.
        + assumption.
      - pose proof (HE_loc e HE_e).
        (*unfold loc in H2.
        rewrite Hlab_e in H2.*)
        unfold loc.
        rewrite Hlab_e.
        reflexivity.
    }
    intros.
    lapply H2. 2:{
      intro.
      subst.
      tauto.
    }
    intro.
    destruct H3.
    - eapply Hlem1 with (5:=H3); try eassumption.
      apply HE'_acts.
      assumption.
    - eapply Hlem1 with (5:=H3); try eassumption.
      apply HE'_acts.
      assumption.
  }

  assert (∀ es ρ0, Forall E' es → run Σ_arc (ρ0, O_RB) (flat_map (λ a, ops_of_event (tid a) (orig a) (val G.(lab) a)) es) = Some (ρ, Θ) → Θ = O_RB). {
    intros es ρ0 Hfor Hrun.
    apply arc_run_produces_local_resource with (tid:=tid) (orig:=orig) (lab:=lab G) (ρ0:=ρ0) (ρ:=ρ) (es:=es); try assumption.
    apply Forall_forall. intros a Ha.
    pose proof (Forall_in _ Hfor Ha).
    split.
    - apply Hlab_matches_orig.
      apply HE'_acts.
      assumption.
    - intro.
      destruct H0 as [r H0].
      apply Hlem2 with (1:=H) (2:=H0).
  }

  apply H with (es:=es'0) (ρ0 := Σ_arc.(ρ0)).
  - apply Forall_forall. intros.
    apply In_nth_error in H0.
    destruct H0 as [k H0].
    apply Hes'0 in H0.
    tauto.
  - apply Homega with (f:=f_es'0); assumption.
Qed.

Lemma arc_fence_no_global_resources l ρ Θ:
  hb_consistent Σ_arc l None (Ofence Oacq) (ρ, Θ) →
  ρ = 0.
Proof.
Admitted.
