import Model.Canon.ArgConv
import Model.Canon.Kan

/-!
# Canonicity: the eliminator of an inductive type is computable

By induction on the computability relation of the scrutinee (`DR`): on a constructor, the
eliminator computes to its branch applied to the arguments and the eliminations of the
recursive arguments (`elimCon`); on a formal composition, to a composition in the motive
(`elimHcomp`).
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

variable (hW : WfSig S)
include hW

/-- Application through a Π-telescope. -/
theorem RE_apps : ∀ (as : List Tm) {Δ prev : List Tm} {f base : Tm}, as.length = Δ.length →
    RE S k ((Δ.foldr Tm.pi base).substList prev) f →
    (∀ j (hj : j < as.length) (hj' : j < Δ.length), RE S k (Δ[j].substList ((as.take j).reverse ++ prev)) as[j]) →
    RE S k (base.substList (as.reverse ++ prev)) (Tm.apps f as)
  | [], [], prev, f, base, _, hf, _ => by simpa [Tm.apps] using hf
  | a :: as, A :: Δ, prev, f, base, hl, hf, ha => by
    rw [List.foldr_cons, pi_substList] at hf
    have h1 := RE_pi_elim hW hf (by simpa using ha 0 (by simp) (by simp))
    rw [up_slS_inst] at h1
    have := RE_apps as (by simpa using hl) h1 (fun j hj hj' => by
      have := ha (j + 1) (by simp; omega) (by simp; omega)
      simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using this)
    simpa [Tm.apps, List.foldl, List.reverse_cons, List.append_assoc] using this
  | [], _ :: _, _, _, _, hl, _, _ | _ :: _, [], _, _, _, hl, _, _ => by simp at hl

/-- Interval application through iterated `(i : I) → _`. -/
theorem RE_papps {B : Tm} {σ : ℕ → Tm} : ∀ (rs : List I) {g : Tm} {τ : ℕ → I}, (∀ r ∈ rs, r.Scoped k) →
    RE S k ((ipis rs.length B).subst σ τ) g → RE S k (B.subst σ (consIs rs τ)) (Tm.papps g rs)
  | [], g, τ, _, hg => by simpa [Tm.papps, ipis, consIs] using hg
  | r :: rs, g, τ, hrs, hg => by
    rw [List.length_cons, ipis_succ] at hg
    have h1 := RE_ipi_elim hW hg r (hrs r (List.mem_cons_self ..))
    rw [dup_dinst] at h1
    exact RE_papps rs (fun r' h => hrs r' (List.mem_cons_of_mem _ h)) h1

omit hW in
theorem dataMem_restr {d : ℕ} {D : DataDecl} {k0 : ℕ} (ps : Tm) (σ : ISub k k0) :
    dataMem S (ΘK S D d k0 ps) ((Hom.id k0).comp σ.hom) = dataMem S (ΘK S D d k (ps.isub σ)) (Hom.id k) := by
  funext k1 g t
  simp only [dataMem, Hom.id_comp, ← SData.restr_restr, ΘK_restr]

omit hW in
theorem dataP_restr {d : ℕ} {D : DataDecl} {k0 : ℕ} (ps : Tm) (σ : ISub k k0) :
    dataP S (ΘK S D d k0 ps) ((Hom.id k0).comp σ.hom) = dataP S (ΘK S D d k (ps.isub σ)) (Hom.id k) := by
  funext k1 g c j pre A t
  simp only [dataP, Hom.id_comp, ← SData.restr_restr, ΘK_restr]

theorem tyEq_data_eq {d : ℕ} {qs ps : Tm} {l : ℕ} (h : TyEq S k (.data d qs) (.data d ps))
    (hp : HasTy S k .one [] (.data d ps) (.univ l)) : ∃ l', EqTm S k .one [] (.data d qs) (.data d ps) (.univ l') := by
  rcases h with h | h
  · rw [h]; exact ⟨l, EqTm.refl hp⟩
  · exact h

/-- The eliminator is computable on computable elements (by induction on the relation). -/
theorem RE_elim_DR {d : ℕ} {D : DataDecl} (hd : S[d]? = some (.data D)) {k0 : ℕ} {ps P bs : Tm} {m : ℕ}
    (hE : ∀ k (σ : ISub k k0), ElimPrem S k .one [] d D (ps.isub σ) (P.isub σ) (bs.isub σ) m)
    (hPc : ∀ k (σ : ISub k k0) t, RE S k (.data d (ps.isub σ)) t → RE S k (.univ m) ((P.isub σ).inst t))
    (hbr : ∀ k (σ : ISub k k0) (c : ℕ) (C : Ctor) (b : Tm), D.ctors[c]? = some C → (bs.isub σ).toList[c]? = some b →
      RE S k (D.branchTy d c C (ps.isub σ) (P.isub σ)) b) :
    ∀ {k : ℕ} {g : Hom k k0} {A t : Tm},
      DR S d D (dataMem S (ΘK S D d k0 ps) (Hom.id k0)) (dataP S (ΘK S D d k0 ps) (Hom.id k0)) k g A t →
      ∀ σ : ISub k k0, g = σ.hom → TyEq S k A (.data d (ps.isub σ)) →
      RE S k ((P.isub σ).inst t) (.elim d (ps.isub σ) (P.isub σ) (bs.isub σ) t) := by
  have hS := sigClosed_of_wfSig hW
  intro k g A t h
  induction h with
  | @con k g A t qs c C args rs hm hC hrs hsc hqs hAeq he hlen hrec hpt ihrec =>
    intro σ hg hA
    subst hg
    have hEk := hE k σ
    have hpsT' : HasTy S k .one [] (.data d (ps.isub σ)) (.univ D.level) := minimal_to_spec hEk.hdata
    have hpl' := hEk.hps
    have hpsl' : (ps.isub σ).toList.length = D.params.length := by simpa using tele_length hEk.hpt
    have hqp : TyEq S k (.data d qs) (.data d (ps.isub σ)) := hAeq.symm.trans hW hA
    obtain ⟨lq, eq⟩ := tyEq_data_eq hW hqp hpsT'
    have eq0 := spec_to_minimal_eq hW eq
    obtain ⟨D', hD', hqt⟩ := gen_data_tele (spec_to_minimal hW (HasTy.eqL eq)) rfl
    rw [hd] at hD'; cases hD'
    have hqsl : qs.toList.length = D.params.length := by simpa using tele_length hqt
    have hΛ : (ΘK S D d k0 ps).restr ((Hom.id k0).comp σ.hom) = ΘK S D d k (ps.isub σ) := by
      rw [Hom.id_comp]; exact ΘK_restr ps σ
    obtain ⟨hc', hCeq⟩ := List.getElem?_eq_some_iff.1 hC
    -- the arguments are typed
    have hargT : ∀ j (hj : j < args.length), HasTy S k .one [] args[j]
        ((C.argTy d D.params.length j).substList ((args.take j).reverse ++ qs.toList.reverse)) := by
      intro j hj
      cases hr : C.isRec j
      · have := hpt j hj hr; unfold dataP at this; exact (Comp_el_typed this).1
      · have := (hrec j hj hr).typed
        have hsl : ∀ L, (Tm.data d (Ctor.paramVars D.params.length j)).substList L =
            Tm.data d ((Ctor.paramVars D.params.length j).substList L) := fun L => rfl
        rw [argTy_rec hr, hsl, Meta.paramVars_substList hqs hqsl (by simp; omega)]
        exact this
    have hnat : ∀ t ∈ args, Natural S t k (idEnv k) (γ0 k) := by
      intro t ht
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
      exact natural_of_ty hW (hargT i hi)
    have htq : HasTele0 S k .one [] (Tm.ofList args) (C.argTys d D.params.length) qs.toList.reverse :=
      HasTele0.ofList_of (wf_of_tele hqt) _ _ _ (by rw [argTys_length]; exact hlen) fun j a B haj hB => by
        have hj : j < C.args.length := by
          rw [← argTys_length C d D.params.length]; exact (List.getElem?_eq_some_iff.1 hB).1
        rw [argTys_get hj] at hB
        obtain rfl := Option.some.inj hB
        obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 haj
        exact spec_to_minimal hW (hargT j hj')
    obtain ⟨htp, hteq⟩ := args_retype hW hd hC hqs hpl' hqt hEk.hpt eq0 htq
    rw [toList_ofList] at hteq
    -- the arguments are computable
    have hargC : ∀ j (hj : j < args.length),
        RE S k ((C.argTy d D.params.length j).substList ((args.take j).reverse ++ (ps.isub σ).toList.reverse)) args[j] := by
      intro j hj
      obtain ⟨lj, ej⟩ := hteq j hj
      have ej' : TyEq S k ((C.argTy d D.params.length j).substList ((args.take j).reverse ++ qs.toList.reverse))
          ((C.argTy d D.params.length j).substList ((args.take j).reverse ++ (ps.isub σ).toList.reverse)) :=
        .inr ⟨lj, minimal_to_spec_eq ej⟩
      cases hr : C.isRec j
      · have h := hpt j hj hr
        unfold dataP at h
        rw [hΛ] at h
        have hv := validPre_of_el h
        obtain ⟨Aj, hAj⟩ := argTy_point (C := C) (by omega) hr
        rw [tyLook_eq hv, ΘK_ty_id hW hd hpsT' hpl' hC hAj (by simp; omega)
          (fun t ht => hnat t (List.mem_of_mem_take ht)) (ptValid_of_validPre hv)] at h
        have h' : RE S k ((C.argTy d D.params.length j).substList ((args.take j).reverse ++ qs.toList.reverse)) args[j] := by
          unfold RE; rw [semK_tyEq hW ej']; exact h
        exact h'.conv_ty hW ej'
      · have hsl : ∀ L, (Tm.data d (Ctor.paramVars D.params.length j)).substList L =
            Tm.data d ((Ctor.paramVars D.params.length j).substList L) := fun L => rfl
        rw [argTy_rec hr, hsl, Meta.paramVars_substList hpl' hpsl' (by simp; omega)]
        have hr1 := DR.rebase (Hom.id k0) (hrec j hj hr) σ.hom (Hom.id k) (Hom.comp_id _).symm
        rw [dataMem_restr, dataP_restr] at hr1
        have hr2 := hr1.conv hW (fun k1 f t1 t1' A1 e1 hm1 => by unfold dataMem at hm1 ⊢; rwa [← semK_eq hW e1])
          hqp (EqTm.refl ((hr1.typed).tyConv hqp))
        exact (RE_data_iff hW hd hpsT').2 ⟨hr2.typed, hr2⟩
    -- the constructor at the eliminator's parameters
    have hDl := (hW.2 d D hd).1
    have hcp := HasTy0.con hd hC hpl' hEk.hdata hEk.hpt htp hrs hsc
    have hcq := HasTy0.con hd hC hqs (HasTy0.data hd hDl hqt) hqt htq hrs hsc
    have eps := EqTele0.dataInj hd hqt hEk.hpt eq0
    have ec := EqTm0.con hd hC hcq (HasTy0.conv hcp (EqTm0.symm eq0)) eps (EqTele0.refl htq) rfl
      (fun k r r' h1 h2 => by rw [h1] at h2; cases h2; exact I_eq_refl _)
    have htc : EqTm S k .one [] t (.con d c (ps.isub σ) (Tm.ofList args) rs) (.data d (ps.isub σ)) :=
      EqTm.trans (he.tyConv hA) (minimal_to_spec_eq (EqTm0.conv ec eq0))
    have htc0 := spec_to_minimal_eq hW htc
    have ht0 := spec_to_minimal hW (HasTy.eqL htc)
    -- `elim t ≡ elim (con …) ≡ branch`
    have e1 := hEk.elim_congr hS ht0 hcp htc0
    have hbl : (bs.isub σ).toList.length = D.ctors.length := hEk.hlen
    obtain ⟨b, hb⟩ : ∃ b, (bs.isub σ).toList[c]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by rw [hbl]; exact hc')⟩
    have e2 := EqTm.elimCon (T := (P.isub σ).inst (.con d c (ps.isub σ) (Tm.ofList args) rs)) hd hC hb hpl'
      (by rw [toList_ofList]) hEk.hbs (toFull_tele htp) (minimal_to_spec (hEk.elim_ty hcp))
    rw [toList_ofList] at e2
    -- the branch applied is computable
    have hbr' : RE S k ((((List.range C.args.length).map
        (DataDecl.branchArgTy d D.params.length C (ps.isub σ))).foldr Tm.pi
          (((List.range C.recPos.length).map (DataDecl.branchIhTy C (P.isub σ))).foldr Tm.pi
            (ipis C.dims (DataDecl.branchBody d c C (ps.isub σ) (P.isub σ))))).substList []) b := by
      rw [substList_nil]; have := hbr k σ c C b hC hb; rw [Meta.branchTy_eq] at this; exact this
    have h1 := RE_apps hW args (by simp [hlen]) hbr' (fun j hj hj' => by
      simp only [List.getElem_map, List.getElem_range, List.append_nil]
      rw [branchArgTy_substList hS hd hC hpsl' (by simp; omega)]
      exact hargC j hj)
    rw [List.append_nil] at h1
    let ihs := C.recPos.map fun j => Tm.elim d (ps.isub σ) (P.isub σ) (bs.isub σ) (args.getD j .abort)
    have hihs : ihs.length = C.recPos.length := by simp [ihs]
    have h2 := RE_apps hW ihs (Δ := (List.range C.recPos.length).map (DataDecl.branchIhTy C (P.isub σ)))
      (by simp [hihs]) h1 (fun s hs hs' => by
        simp only [List.length_map, List.length_range] at hs'
        simp only [List.getElem_map, List.getElem_range]
        rw [branchIhTy_substList (P.isub σ) hs' (by simp; omega) hlen]
        obtain ⟨hjn, hjr⟩ := mem_recPos (List.getElem_mem (l := C.recPos) hs')
        have hgd : C.recPos.getD s 0 = C.recPos[s] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs']; rfl
        have hag : args.getD C.recPos[s] .abort = args[C.recPos[s]]'(by omega) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
        simp only [ihs, List.getElem_map, hgd, hag]
        exact ihrec _ (by omega) hjr σ rfl hqp)
    rw [substList_eq, ← hrs] at h2
    have h3 := RE_papps hW rs hsc h2
    rw [branchBody_inst hihs hlen hrs] at h3
    have happ : Tm.apps (Tm.apps b args) ihs = Tm.apps b (args ++ ihs) := by
      rw [Tm.apps, Tm.apps, Tm.apps, List.foldl_append]
    rw [happ] at h3
    -- conclude
    have eP := HasTy0.inst_congr hS hEk.hP hcp ht0 (EqTm0.symm htc0)
    have eP' : TyEq S k ((P.isub σ).inst (.con d c (ps.isub σ) (Tm.ofList args) rs)) ((P.isub σ).inst t) :=
      .inr ⟨m, minimal_to_spec_eq eP⟩
    exact h3.conv hW eP' (EqTm.trans ((EqTm.symm e2).tyConv eP') (EqTm.symm (minimal_to_spec_eq e1)))
  | @hcomp k g A t qs u a φ hm hH hsc hn hqs hAeq he ha hu iha ihu =>
    sorry

end

end Model.Canon
