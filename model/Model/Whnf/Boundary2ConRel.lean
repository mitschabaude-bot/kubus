import Model.Whnf.Boundary2Overlap

/-! # Constructor relatedness from per-face overlap agreement -/
set_option autoImplicit false
namespace Model.Whnf.Boundary2
open KubusCore KubusCore.Meta Model.Canon Model.Whnf
noncomputable section
attribute [local instance] Classical.propDecidable
variable {S : Sig} {d K : ℕ} {D : DataDecl} {P : Tm}
section
variable (hW : WfSig S) (hD : S[d]? = some (.data D))
  (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (hPP : RT2 S K (.data d P) (.data d P))
  (hH : D.isHIT = true) (hBT : BndTyping S d)
include hW hD hP hPP hH hBT

/-- Constructors with related arguments are related at each stage, given the relation of the earlier
constructors. -/
theorem con_at {c : ℕ} (ih : ∀ c' < c, CRSt S d D K P c') {k3 : ℕ} (ρ' : ISub k3 K) {C : Ctor} {q q' : Tm}
    {X X' : List Tm} {rs rs' : List I} (hC : D.ctors[c]? = some C)
    (ht : HasTy S k3 .one [] (.con d c q (Tm.ofList X) rs) (.data d (P.isub ρ')))
    (ht' : HasTy S k3 .one [] (.con d c q' (Tm.ofList X') rs') (.data d (P.isub ρ')))
    (hrs : List.Forall₂ I.Eq rs rs')
    (hargs : ∀ i (_hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ (P.isub ρ').toList.reverse)) (X.getD i .abort) (X'.getD i .abort)) :
    DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k3 ρ'.hom
      (.data d (P.isub ρ')) (.con d c q (Tm.ofList X) rs) (.con d c q' (Tm.ofList X') rs') := by
  have hPρ : HasTy S k3 .one [] (.data d (P.isub ρ')) (.univ D.level) := HasTy.isubS hW hP ρ'
  have hPPρ : RT2 S k3 (.data d (P.isub ρ')) (.data d (P.isub ρ')) := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ'
  have hPl := (dataLit_rel hW hD hP hPP ρ').2.2.2.2.2.1
  have hplen : (P.isub ρ').toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl hPρ⟩ : IsTyK S k3 (.data d (P.isub ρ'))); rwa [dataD_eq hW hD] at this
  have CI := con_inv hW hD hC ht hPρ
  have CI' := con_inv hW hD hC ht' hPρ
  have hrsl := CI.2.2.2.1
  have hsc := CI.2.2.2.2.1
  have hXl := CI.2.2.2.2.2.1
  have hcP := CI.2.2.2.2.2.2.1
  have hqL := CI.2.2.2.2.2.2.2.2.1
  have hql := CI.2.2.2.2.2.2.2.2.2
  have hrsl' := CI'.2.2.2.1
  have hsc' := CI'.2.2.2.2.1
  have hX'l := CI'.2.2.2.2.2.1
  have hqL' := CI'.2.2.2.2.2.2.2.2.1
  have hql' := CI'.2.2.2.2.2.2.2.2.2
  have he : EqTm S k3 .one [] (.con d c q (Tm.ofList X) rs) (.con d c q' (Tm.ofList X') rs') (.data d (P.isub ρ')) :=
    con_eqTm hW hD hC hPρ ht ht' hrs fun i hi => (RE2.typed (hargs i hi)).2.2
  have hself := args_self hW hD hP hPP ρ' hC hXl hX'l hargs
  cases hf : firstBnd C.bnd rs with
  | none =>
    have hf' : firstBnd C.bnd rs' = none := by rw [← firstBnd_eq hrs]; exact hf
    refine DR2At_conH_of hW hD hP hPP ρ' hC hXl hX'l ht hf ⟨redW_self (step_con_none hD hC _ _ hf'), EqTm.refl ht'⟩
      he hrsl hrsl' (ieq_of_forall2 hrs).2 hsc hsc' fun i hi hi' => ⟨fun hri => ?_, fun hri _ => ?_⟩
    · have h := hargs i (by omega)
      rw [argTy_rec_inst hri hPl hplen (by simp; omega), getD_eq_get' hi, getD_eq_get' hi'] at h
      exact h
    · have h := hargs i (by omega)
      rwa [getD_eq_get' hi, getD_eq_get' hi'] at h
  | some b =>
    have hf' : firstBnd C.bnd rs' = some b := by rw [← firstBnd_eq hrs]; exact hf
    obtain ⟨kb, ψ, hb, hent⟩ := firstBnd_spec hf
    obtain ⟨-, -, hsimple, -⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 kb ψ b hb
    obtain ⟨kb', ψ', hb', hent'⟩ := firstBnd_spec hf'
    have e1 : EqTm S k3 .one [] (.con d c q (Tm.ofList X) rs) (Ctor.bndAt b q.toList X rs) (.data d (P.isub ρ')) := by
      have := EqTm.conBnd hD hC hb hent hqL (by rw [toList_ofList]) ht
      rwa [toList_ofList] at this
    have e1' : EqTm S k3 .one [] (.con d c q' (Tm.ofList X') rs') (Ctor.bndAt b q'.toList X' rs')
        (.data d (P.isub ρ')) := by
      have := EqTm.conBnd hD hC hb' hent' hqL' (by rw [toList_ofList]) ht'
      rwa [toList_ofList] at this
    have hrel := hBT hD hH hC hb hent hPρ hPPρ hXl hcP (fun i hi => (hself i hi).2.1)
    have R := bnd_rel hW hD hP hPP ih hC (sizeOf b + 1) b (by omega) hsimple ρ' hql hql' hXl hX'l hrs hargs hrel
      (HasTy.eqR e1) (HasTy.eqR e1')
    have at0 := DR2.at_id hW (Θ := ΘK S D d K P) ((RE2_dataLit_iff hW hD hP ρ').1 R).2
    have s1 : step S (.con d c q (Tm.ofList X) rs) = some (Ctor.bndAt b q.toList X rs) := by
      rw [step_con_some hD hC _ _ hf, toList_ofList]
    have s1' : step S (.con d c q' (Tm.ofList X') rs') = some (Ctor.bndAt b q'.toList X' rs') := by
      rw [step_con_some hD hC _ _ hf', toList_ofList]
    exact DR2At.expandL hW (DR2At.expandR hW at0 (.step s1' (.refl _)) e1') (.step s1 (.refl _)) e1

/-- The coherence of a constructor: its normal form, restricted, is related to its restriction. -/
theorem con_coh0 {c : ℕ} (ih : ∀ c' < c, CRSt S d D K P c') (hCB : ∀ c' < c, CBRSt S d D c') {k3 : ℕ} (ρ' : ISub k3 K) {C : Ctor} {q : Tm}
    {X : List Tm} {rs : List I} (hC : D.ctors[c]? = some C)
    (ht : HasTy S k3 .one [] (.con d c q (Tm.ofList X) rs) (.data d (P.isub ρ')))
    (hargs : ∀ i (_hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ (P.isub ρ').toList.reverse)) (X.getD i .abort) (X.getD i .abort))
    {w : Tm} (hw : RedW S (.con d c q (Tm.ofList X) rs) w) {k5 : ℕ} (κ : ISub k5 k3) :
    DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k5
      (ρ'.comp κ).hom (.data d (P.isub (ρ'.comp κ))) (w.isub κ) ((Tm.con d c q (Tm.ofList X) rs).isub κ) := by
  have eP : ∀ {k4 : ℕ} (σ : ISub k4 k3), (Tm.data d (P.isub ρ')).isub σ = .data d (P.isub (ρ'.comp σ)) := by
    intro k4 σ; show Tm.data d ((P.isub ρ').isub σ) = _; rw [Tm.isub_isub]
  have hPρ : HasTy S k3 .one [] (.data d (P.isub ρ')) (.univ D.level) := HasTy.isubS hW hP ρ'
  have hPPρ : RT2 S k3 (.data d (P.isub ρ')) (.data d (P.isub ρ')) := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ'
  have hPκT : HasTy S k5 .one [] (.data d (P.isub (ρ'.comp κ))) (.univ D.level) := HasTy.isubS hW hP (ρ'.comp κ)
  have hPPκ : RT2 S k5 (.data d (P.isub (ρ'.comp κ))) (.data d (P.isub (ρ'.comp κ))) :=
    RT2.isub hW (tyCode_of_univ hW hP) hPP (ρ'.comp κ)
  have hPlκ := (dataLit_rel hW hD hP hPP (ρ'.comp κ)).2.2.2.2.2.1
  have hplenκ : (P.isub (ρ'.comp κ)).toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl hPκT⟩ : IsTyK S k5 (.data d (P.isub (ρ'.comp κ)))); rwa [dataD_eq hW hD] at this
  have CI := con_inv hW hD hC ht hPρ
  have hrsl := CI.2.2.2.1
  have hXl := CI.2.2.2.2.2.1
  have hqL := CI.2.2.2.2.2.2.2.2.1
  have hql := CI.2.2.2.2.2.2.2.2.2
  have htκ := HasTy.isubS hW ht κ
  rw [isub_conT, eP] at htκ
  have CIκ := con_inv hW hD hC htκ hPκT
  have hXκl := CIκ.2.2.2.2.2.1
  have hcPκ := CIκ.2.2.2.2.2.2.1
  have hqLκ := CIκ.2.2.2.2.2.2.2.2.1
  have hqlκ := CIκ.2.2.2.2.2.2.2.2.2
  have argsκ := args_restr hW hD hP hPP ρ' hC hXl hXl hargs κ
  cases hf : firstBnd C.bnd rs with
  | none =>
    obtain rfl := RedW.unique hw (redW_self (step_con_none hD hC _ _ hf))
    rw [isub_conT]
    exact con_at hW hD hP hPP hH hBT ih (ρ'.comp κ) hC htκ htκ (forall2_ieq_refl _) argsκ
  | some b =>
    obtain ⟨kb, ψ, hb, hent⟩ := firstBnd_spec hf
    obtain ⟨hψs, hbc, hsimple, -⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 kb ψ b hb
    have e1 : EqTm S k3 .one [] (.con d c q (Tm.ofList X) rs) (Ctor.bndAt b q.toList X rs) (.data d (P.isub ρ')) := by
      have := EqTm.conBnd hD hC hb hent hqL (by rw [toList_ofList]) ht
      rwa [toList_ofList] at this
    have s1 : step S (.con d c q (Tm.ofList X) rs) = some (Ctor.bndAt b q.toList X rs) := by
      rw [step_con_some hD hC _ _ hf, toList_ofList]
    have hwB := red_redW (.step s1 (.refl _)) hw
    have hrel := hBT hD hH hC hb hent hPρ hPPρ hXl CI.2.2.2.2.2.2.1 hargs
    have RBB := bnd_rel hW hD hP hPP ih hC (sizeOf b + 1) b (by omega) hsimple ρ' hql hql hXl hXl
      (forall2_ieq_refl _) hargs hrel (HasTy.eqR e1) (HasTy.eqR e1)
    have hBc := closed_of_ty hW (HasTy.eqR e1)
    obtain ⟨-, hdB⟩ := (RE2_dataLit_iff hW hD hP ρ').1 RBB
    have h2 : DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k5
        (ρ'.comp κ).hom (.data d (P.isub (ρ'.comp κ))) (w.isub κ) ((Ctor.bndAt b q.toList X rs).isub κ) := by
      cases hdB with
      | intro _ _ hc _ =>
        have := hc k3 (ISub.id k3) w (by rw [isub_id_of_closed hBc]; exact hwB) k5 κ
        rwa [ISub.id_comp, eP, ← ISub.hom_comp] at this
    have hbc' : b.closedB (q.toList.length + X.length) rs.length = true := by rw [hql, hXl, hrsl]; exact hbc
    rw [bndAt_isubL hqL hbc' κ] at h2
    -- the boundaries at the restriction
    have hsc : ∀ p ∈ C.bnd, p.1.Scoped rs.length := by
      intro p hp
      obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
      obtain ⟨h0, -⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 i p.1 p.2 (by rw [List.getElem?_eq_getElem hi, hpi])
      rw [hrsl]; exact h0
    obtain ⟨b'', hf''⟩ := firstBnd_isSome_subst hf hsc κ.τ
    obtain ⟨kb'', ψ'', hb'', hent''⟩ := firstBnd_spec hf''
    obtain ⟨-, -, hsimple'', -⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 kb'' ψ'' b'' hb''
    have hentκ : I.Entails .one (Ctor.cofAt ψ (rs.map (·.subst κ.τ))) := by
      rw [← cofAt_subst κ.τ (by rw [hrsl]; exact hψs)]; exact ent_one_subst hent κ.τ
    have eqb : ∀ {kb0 : ℕ} {ψ0 : I} {b0 : Tm}, C.bnd[kb0]? = some (ψ0, b0) →
        I.Entails .one (Ctor.cofAt ψ0 (rs.map (·.subst κ.τ))) → ∀ {q0 : Tm}, q0 = Tm.ofList q0.toList →
        HasTy S k5 .one [] (.con d c q0 (Tm.ofList (X.map (·.isub κ))) (rs.map (·.subst κ.τ)))
          (.data d (P.isub (ρ'.comp κ))) →
        EqTm S k5 .one [] (.con d c q0 (Tm.ofList (X.map (·.isub κ))) (rs.map (·.subst κ.τ)))
          (Ctor.bndAt b0 q0.toList (X.map (·.isub κ)) (rs.map (·.subst κ.τ))) (.data d (P.isub (ρ'.comp κ))) := by
      intro kb0 ψ0 b0 hb0 hent0 q0 hq0 h0
      have := EqTm.conBnd hD hC hb0 hent0 hq0 (by rw [toList_ofList]) h0
      rwa [toList_ofList] at this
    have e_qb := eqb hb hentκ hqLκ htκ
    have e_qb'' := eqb hb'' hent'' hqLκ htκ
    have e_Pb := eqb hb hentκ hPlκ hcPκ
    have e_Pb'' := eqb hb'' hent'' hPlκ hcPκ
    have hrelκ := hBT hD hH hC hb hentκ hPκT hPPκ hXκl hcPκ argsκ
    have hrelκ'' := hBT hD hH hC hb'' hent'' hPκT hPPκ hXκl hcPκ argsκ
    have R1 := bnd_rel hW hD hP hPP ih hC (sizeOf b + 1) b (by omega) hsimple (ρ'.comp κ) hqlκ hplenκ hXκl hXκl
      (forall2_ieq_refl _) argsκ hrelκ (HasTy.eqR e_qb) (HasTy.eqR e_Pb)
    have RB := overlap_rel hW hD hH hBT hPκT hPPκ (fun c' hc' => crst_restr (ih c' hc') (ρ'.comp κ)) hCB
      hC hb hb'' hentκ hent'' hXκl hcPκ argsκ
    have R4 := bnd_rel hW hD hP hPP ih hC (sizeOf b'' + 1) b'' (by omega) hsimple'' (ρ'.comp κ) hplenκ hqlκ hXκl hXκl
      (forall2_ieq_refl _) argsκ hrelκ'' (HasTy.eqR e_Pb'') (HasTy.eqR e_qb'')
    have R := RE2.trans hW hPPκ R1 (RE2.trans hW hPPκ RB R4)
    have at1 := DR2.at_id hW (Θ := ΘK S D d K P) ((RE2_dataLit_iff hW hD hP (ρ'.comp κ)).1 R).2
    have tr := DR2At_trans hW (Hom.id K) (perP_ΘK hW hD hP) h2 at1 (argRelH_litH hW hD hP hPP (ρ'.comp κ))
    have s'' : step S (.con d c (q.isub κ) (Tm.ofList (X.map (·.isub κ))) (rs.map (·.subst κ.τ))) =
        some (Ctor.bndAt b'' (q.isub κ).toList (X.map (·.isub κ)) (rs.map (·.subst κ.τ))) := by
      rw [step_con_some hD hC _ _ hf'', toList_ofList]
    rw [isub_conT]
    exact DR2At.expandR hW tr (.step s'' (.refl _)) e_qb''

/-- Constructors of a literal higher inductive type with related arguments and `I.Eq`-equal interval
arguments are related (with any parameter annotations). -/
theorem con_rel_step {c : ℕ} (ih : ∀ c' < c, CRSt S d D K P c') (hCB : ∀ c' < c, CBRSt S d D c') :
    CRSt S d D K P c := by
  intro k3 ρ' C q q' X X' rs rs' hC ht ht' hrs hargs
  have eP : ∀ {k4 : ℕ} (σ : ISub k4 k3), (Tm.data d (P.isub ρ')).isub σ = .data d (P.isub (ρ'.comp σ)) := by
    intro k4 σ; show Tm.data d ((P.isub ρ').isub σ) = _; rw [Tm.isub_isub]
  have hPρ : HasTy S k3 .one [] (.data d (P.isub ρ')) (.univ D.level) := HasTy.isubS hW hP ρ'
  have hXl := (con_inv hW hD hC ht hPρ).2.2.2.2.2.1
  have hX'l := (con_inv hW hD hC ht' hPρ).2.2.2.2.2.1
  have he : EqTm S k3 .one [] (.con d c q (Tm.ofList X) rs) (.con d c q' (Tm.ofList X') rs') (.data d (P.isub ρ')) :=
    con_eqTm hW hD hC hPρ ht ht' hrs fun i hi => (RE2.typed (hargs i hi)).2.2
  have hself := args_self hW hD hP hPP ρ' hC hXl hX'l hargs
  have coh : ∀ {q0 : Tm} {X0 : List Tm} {rs0 : List I},
      HasTy S k3 .one [] (.con d c q0 (Tm.ofList X0) rs0) (.data d (P.isub ρ')) →
      (∀ i (_hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
        ((X0.take i).reverse ++ (P.isub ρ').toList.reverse)) (X0.getD i .abort) (X0.getD i .abort)) →
      ∀ k4 (σ : ISub k4 k3) w, RedW S ((Tm.con d c q0 (Tm.ofList X0) rs0).isub σ) w → ∀ k5 (κ : ISub k5 k4),
      DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k5
        (ρ'.hom.comp (σ.comp κ).hom) ((Tm.data d (P.isub ρ')).isub (σ.comp κ)) (w.isub κ)
        ((Tm.con d c q0 (Tm.ofList X0) rs0).isub (σ.comp κ)) := by
    intro q0 X0 rs0 h0 hX0 k4 σ w hw k5 κ
    have hX0l := (con_inv hW hD hC h0 hPρ).2.2.2.2.2.1
    have h0σ := HasTy.isubS hW h0 σ
    rw [isub_conT, eP] at h0σ
    rw [isub_conT] at hw
    have := con_coh0 hW hD hP hPP hH hBT ih hCB (ρ'.comp σ) hC h0σ (args_restr hW hD hP hPP ρ' hC hX0l hX0l hX0 σ) hw κ
    have e1 : (Tm.con d c q0 (Tm.ofList X0) rs0).isub (σ.comp κ) =
        (Tm.con d c (q0.isub σ) (Tm.ofList (X0.map (·.isub σ))) (rs0.map (·.subst σ.τ))).isub κ := by
      rw [← isub_conT, Tm.isub_isub]
    have e2 : (Tm.data d (P.isub ρ')).isub (σ.comp κ) = Tm.data d (P.isub ((ρ'.comp σ).comp κ)) := by
      rw [eP, ISub.comp_assoc]
    rw [e1, e2, ← ISub.hom_comp, ← ISub.comp_assoc]
    exact this
  refine (RE2_dataLit_iff hW hD hP ρ').2 ⟨⟨ht, ht', he⟩, .intro he (fun k4 κ => ?_)
    (coh ht fun i hi => (hself i hi).2.1) (coh ht' fun i hi => ?_)⟩
  · have htκ := HasTy.isubS hW ht κ
    have ht'κ := HasTy.isubS hW ht' κ
    rw [isub_conT, eP] at htκ ht'κ
    rw [eP, isub_conT, isub_conT, ← ISub.hom_comp]
    exact con_at hW hD hP hPP hH hBT ih (ρ'.comp κ) hC htκ ht'κ (forall2_ieq_map hrs κ.τ)
      (args_restr hW hD hP hPP ρ' hC hXl hX'l hargs κ)
  · exact (hself i hi).2.2



end
end
end Model.Whnf.Boundary2
