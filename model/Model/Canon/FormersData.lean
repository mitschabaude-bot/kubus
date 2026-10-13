import Model.Canon.Formers

/-!
# Canonicity: computability at inductive types, for closed types
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

/-- The semantic inductive type of a closed data type at stage `k`. -/
abbrev ΘK (S : Sig) (D : DataDecl) (d k : ℕ) (ps : Tm) : SData k :=
  dataSD (sigUpTo S d) D d k (psRV S ps k (idEnv k) (γ0 k))

variable (hW : WfSig S)
include hW

theorem tyCode_of_univ {A : Tm} {l : ℕ} (h : HasTy S k .one [] A (.univ l)) : TyCode k (semK S k A) := by
  have := mem_of_ty hW h
  rw [show semK S k (.univ l) = univC k l from rfl, El_univC, ZFSet.mem_sep] at this
  exact ⟨l, lvl_of_ty hW h, .inl ⟨this.2, this.1⟩⟩

variable {d : ℕ} {D : DataDecl} (hd : S[d]? = some (.data D))
include hd

theorem paramsOK_K {ps : Tm} {l : ℕ} (h : HasTy S k .one [] (.data d ps) (.univ l)) :
    ParamsOK (sigUpTo S d) D k (psRV S ps k (idEnv k) (γ0 k)) :=
  paramsOK_of_code hd (tyCode_of_univ hW h)

theorem semK_dataT {ps : Tm} {l : ℕ} (h : HasTy S k .one [] (.data d ps) (.univ l)) :
    semK S k (.data d ps) = dataC (ΘK S D d k ps) :=
  sem_data_of hd (paramsOK_K hW hd h)

theorem ΘK_good {ps : Tm} {l : ℕ} (h : HasTy S k .one [] (.data d ps) (.univ l)) : (ΘK S D d k ps).Good :=
  (((sigOK_of_wfSig _ S rfl hW).2 d D hd).2 _ _ (paramsOK_K hW hd h)).1

theorem dataD_eq : dataD S d = D := by unfold dataD; rw [hd]

/-- Computable elements of a closed data type. -/
theorem RE_data_iff {ps t : Tm} {l : ℕ} (h : HasTy S k .one [] (.data d ps) (.univ l)) :
    RE S k (.data d ps) t ↔ HasTy S k .one [] t (.data d ps) ∧
      DR S d D (dataMem S (ΘK S D d k ps) (Hom.id k)) (dataP S (ΘK S D d k ps) (Hom.id k)) k (Hom.id k)
        (.data d ps) t := by
  unfold RE
  rw [semK_dataT hW hd h, Comp_dataC]
  simp only [show (ΘK S D d k ps).idx = d from rfl, dataD_eq hW hd]
  constructor
  · rintro ⟨ht, -, -, hdr⟩; exact ⟨ht, hdr⟩
  · rintro ⟨ht, hdr⟩
    refine ⟨ht, ?_, ht, hdr⟩
    rw [← semK_dataT hW hd h, res_id (kv_semK_of_univ hW h)]; exact mem_of_ty hW ht

omit hW hd in
theorem ΘK_restr (ps : Tm) (σ : ISub k' k) : (ΘK S D d k ps).restr σ.hom = ΘK S D d k' (ps.isub σ) := by
  rw [← dataSD_restr']
  congr 1
  funext n g
  simp only [psRV, show ps.isub σ = ps.dsubst σ.τ from rfl, sem_dsubst, γ0_restr]
  congr 1
  funext i; rw [ival.restr, ← IEnv.restr_restr, ← env_isub]; rfl

/-- The argument types of a closed data type, at valid earlier arguments. -/
theorem ΘK_ty_id {ps : Tm} {l : ℕ} (hpsT : HasTy S k .one [] (.data d ps) (.univ l)) (hpl : ps = Tm.ofList ps.toList)
    {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {j : ℕ} {A : Tm} (hA : C.args[j]? = some (.point A))
    {args : List Tm} (hlen : args.length = j) (hnat : ∀ t ∈ args, Natural S t k (idEnv k) (γ0 k))
    (hv : (ΘK S D d k ps).PtValid c k (Hom.id k) (args.map (semK S k))) :
    (ΘK S D d k ps).ty c j k (Hom.id k) (args.map (semK S k)) =
      semK S k ((C.argTy d D.params.length j).substList (args.reverse ++ ps.toList.reverse)) := by
  have hok := (sigOK_of_wfSig _ S rfl hW).2 d D hd
  have hpok := paramsOK_K hW hd hpsT
  have hjC : j < C.args.length := (List.getElem?_eq_some_iff.1 hA).1
  have hpsl : ps.toList.length = D.params.length := by
    have h1 := (hpok k (Hom.id k)).1
    simp only [psRV, IEnv.restr_id, γ0_restr] at h1
    rw [hpl] at h1
    exact listLen_unique (listLen_sem_ofList _ _ _) h1
  have hpsnat := psnat_of_paramsOK hpl hpsl (fun _ => isKV_mkKV (fun _ _ => emptyDatum)) hpok
  rw [show C.argTy d D.params.length j = A by simp [Ctor.argTy, hA]]
  unfold semK
  rw [sem_argTy_subst hd hok.1 hC hA args.reverse ps.toList (by simp [hlen]) hpsl (fun t ht => by
    rcases List.mem_append.1 ht with ht | ht
    · exact hnat t (List.mem_reverse.1 ht)
    · exact hpsnat t (List.mem_reverse.1 ht)), ← hpl, List.reverse_reverse]
  show argTySem _ _ _ _ _ _ _ _ = _
  rw [argTySem_eq, if_pos ⟨by rw [getD_ctors hC]; omega, by rw [getD_ctors hC]; simp [Ctor.isRec, hA],
    ptValid_argPreValid hv (by simp [hlen])⟩]
  simp only [psRV, IEnv.restr_id, γ0_restr]

/-- Valid earlier arguments of computable constructor arguments. -/
theorem ptValid_args {ps : Tm} {l : ℕ} (hpsT : HasTy S k .one [] (.data d ps) (.univ l))
    (hpl : ps = Tm.ofList ps.toList) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {args : List Tm}
    (hlen : args.length = C.args.length)
    (hrec : ∀ j (hj : j < args.length), C.isRec j = true → RE S k (.data d ps) args[j])
    (hpt : ∀ j (hj : j < args.length), C.isRec j = false →
      RE S k ((C.argTy d D.params.length j).substList ((args.take j).reverse ++ ps.toList.reverse)) args[j]) :
    ∀ j, j ≤ args.length → (ΘK S D d k ps).PtValid c k (Hom.id k) ((args.take j).map (semK S k)) := by
  have hnat : ∀ t ∈ args, Natural S t k (idEnv k) (γ0 k) := by
    intro t ht
    obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem ht
    cases hri : C.isRec i'
    · exact natural_of_ty hW (Comp_el_typed (hpt i' hi' hri)).1
    · exact natural_of_ty hW (Comp_el_typed (hrec i' hi' hri)).1
  intro j
  induction j with
  | zero => intro _ i hi; simp at hi
  | succ j ih =>
    intro hj
    have hv := ih (by omega)
    intro i hi hr
    simp only [List.length_map, List.length_take] at hi
    by_cases hij : i < j
    · have := hv i (by simp; omega) hr
      simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hij), Nat.min_eq_left (by omega : i ≤ j + 1)] using this
    obtain rfl : i = j := by omega
    have hr' : C.isRec i = false := by rw [← getD_ctors hC]; exact hr
    obtain ⟨A, hA⟩ := argTy_point (by omega) hr'
    have hRE := hpt i (by omega) hr'
    have hty := ΘK_ty_id hW hd hpsT hpl hC hA (args := args.take i) (by simp; omega)
      (fun t ht => hnat t (List.mem_of_mem_take ht)) hv
    have hmem := (Comp_el_typed hRE).2
    rw [El_res, Hom.comp_id] at hmem
    simp only [List.getElem_map, List.getElem_take, List.take_take, Nat.min_eq_left (Nat.le_succ i),
      List.map_take]
    rw [← List.map_take, hty]
    exact hmem

/-- Constructors of computable arguments are computable. -/
theorem RE_con {ps : Tm} {l : ℕ} (hpsT : HasTy S k .one [] (.data d ps) (.univ l))
    (hpl : ps = Tm.ofList ps.toList) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {args : List Tm}
    (hlen : args.length = C.args.length) {rs : List I} (hrs : rs.length = C.dims) (hsc : ∀ r ∈ rs, r.Scoped k)
    (hty : HasTy S k .one [] (.con d c ps (Tm.ofList args) rs) (.data d ps))
    (hrec : ∀ j (hj : j < args.length), C.isRec j = true → RE S k (.data d ps) args[j])
    (hpt : ∀ j (hj : j < args.length), C.isRec j = false →
      RE S k ((C.argTy d D.params.length j).substList ((args.take j).reverse ++ ps.toList.reverse)) args[j]) :
    RE S k (.data d ps) (.con d c ps (Tm.ofList args) rs) := by
  have hv := ptValid_args hW hd hpsT hpl hC hlen hrec hpt
  refine (RE_data_iff hW hd hpsT).2 ⟨hty, DR.con ?_ hC hrs hsc hpl (TyEq.refl _) (EqTm.refl hty) hlen
    (fun j hj hr => ((RE_data_iff hW hd hpsT).1 (hrec j hj hr)).2) (fun j hj hr => ?_)⟩
  · unfold dataMem
    have := mem_of_ty hW hty
    rw [semK_dataT hW hd hpsT, El_dataC] at this
    simp only [Hom.comp_id, SData.restr_id]
    exact this
  · unfold dataP
    simp only [Hom.comp_id, SData.restr_id]
    obtain ⟨A, hA⟩ := argTy_point (by omega) hr
    have hnat : ∀ t ∈ args, Natural S t k (idEnv k) (γ0 k) := by
      intro t ht
      obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem ht
      cases hri : C.isRec i'
      · exact natural_of_ty hW (Comp_el_typed (hpt i' hi' hri)).1
      · exact natural_of_ty hW (Comp_el_typed (hrec i' hi' hri)).1
    obtain ⟨hc', hCeq⟩ := List.getElem?_eq_some_iff.1 hC
    have hvj : ValidPre (ΘK S D d k ps) c j ((args.take j).map (semK S k)) := by
      refine ⟨hc', by simp only [show (ΘK S D d k ps).ctors = D.ctors from rfl, hCeq]; omega,
        by simp; omega, fun i hi => ?_⟩
      simp only [List.length_map, List.length_take] at hi
      simp only [argSet, show (ΘK S D d k ps).ctors = D.ctors from rfl, hCeq]
      split
      · rename_i hri
        have := (Comp_el_typed (hrec i (by omega) hri)).2
        rw [El_res, Hom.comp_id, semK_dataT hW hd hpsT, El_dataC] at this
        simpa using this
      · rename_i hri
        have := hv j (by omega) i (by simp; omega)
          (by show (D.ctors.getD c default).isRec i = false; rw [getD_ctors hC]; simpa using hri)
        simpa using this
    rw [tyLook_eq hvj, ΘK_ty_id hW hd hpsT hpl hC hA (by simp; omega)
      (fun t ht => hnat t (List.mem_of_mem_take ht)) (hv j (by omega))]
    exact hpt j hj hr

omit hW hd in
/-- Valid prefixes have their point arguments in their types. -/
theorem ptValid_of_validPre {Λ : SData m} {c j : ℕ} {pre : List V} (h : ValidPre Λ c j pre) :
    Λ.PtValid c m (Hom.id m) pre := by
  obtain ⟨hc, -, -, hp⟩ := h
  intro i hi hr
  have := hp i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some] at hr
  simp only [argSet, hr] at this
  simpa using this

/-- A closed data type is computable when the argument types of its constructors are, at all
restrictions and computable earlier point arguments. -/
theorem RT_data_of {ps : Tm} {l : ℕ} (hpsT : HasTy S k .one [] (.data d ps) (.univ l))
    (hpl : ps = Tm.ofList ps.toList)
    (hpt : ∀ k' (σ : ISub k' k) (c : ℕ) (C : Ctor), D.ctors[c]? = some C → ∀ args : List Tm,
      args.length < C.args.length → C.isRec args.length = false →
      (∀ i (hi : i < args.length), C.isRec i = false →
        RE S k' ((C.argTy d D.params.length i).substList ((args.take i).reverse ++ (ps.isub σ).toList.reverse))
          args[i]) →
      RT S k' ((C.argTy d D.params.length args.length).substList (args.reverse ++ (ps.isub σ).toList.reverse))) :
    RT S k (.data d ps) := by
  unfold RT
  rw [semK_dataT hW hd hpsT, Comp_dataC]
  simp only [show (ΘK S D d k ps).idx = d from rfl, dataD_eq hW hd]
  refine ⟨⟨⟨l, .inl hpsT⟩, by rw [← semK_dataT hW hd hpsT, res_id (kv_semK_of_univ hW hpsT)]⟩, ps, TyEq.refl _, hpl,
    fun k' σ c C args hC hlt hnr hrec hptd => ?_⟩
  have hΛ : (ΘK S D d k ps).restr ((Hom.id k).comp σ.hom) = ΘK S D d k' (ps.isub σ) := by
    rw [Hom.id_comp]; exact ΘK_restr ps σ
  simp only [dataP, dataMem, hΛ] at hrec hptd
  rw [hΛ]
  have hpsT' : HasTy S k' .one [] (.data d (ps.isub σ)) (.univ l) := HasTy.isubS hW hpsT σ
  have hpl' : ps.isub σ = Tm.ofList (ps.isub σ).toList := isList_subst hpl _ _
  obtain ⟨hc', hCeq⟩ := List.getElem?_eq_some_iff.1 hC
  have hnat : ∀ t ∈ args, Natural S t k' (idEnv k') (γ0 k') := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    cases hri : C.isRec i
    · exact natural_of_ty hW (Comp_el_typed (hptd i hi hri)).1
    · exact natural_of_ty hW (hrec i hi hri).typed
  -- the point arguments, at their types
  have hpoint : ∀ i (hi : i < args.length), C.isRec i = false →
      ValidPre (ΘK S D d k' (ps.isub σ)) c i ((args.take i).map (semK S k')) ∧
      RE S k' ((C.argTy d D.params.length i).substList ((args.take i).reverse ++ (ps.isub σ).toList.reverse))
        args[i] := by
    intro i hi hri
    have h := hptd i hi hri
    have hv := validPre_of_el h
    refine ⟨hv, ?_⟩
    obtain ⟨Ai, hAi⟩ := argTy_point (C := C) (by omega) hri
    rw [tyLook_eq hv, ΘK_ty_id hW hd hpsT' hpl' hC hAi (by simp; omega) (fun t ht => hnat t (List.mem_of_mem_take ht))
      (ptValid_of_validPre hv)] at h
    exact h
  have hv : ValidPre (ΘK S D d k' (ps.isub σ)) c args.length (args.map (semK S k')) := by
    refine ⟨hc', by simp only [show (ΘK S D d k' (ps.isub σ)).ctors = D.ctors from rfl, hCeq]; omega,
      by simp, fun i hi => ?_⟩
    simp only [List.length_map] at hi
    simp only [argSet, show (ΘK S D d k' (ps.isub σ)).ctors = D.ctors from rfl, hCeq]
    split
    · rename_i hri
      have := (hrec i hi hri).mem
      unfold dataMem at this; rw [hΛ] at this
      simpa using this
    · rename_i hri
      have hri' : C.isRec i = false := by simpa using hri
      have hp := hpoint i hi hri'
      have := (Comp_el_typed hp.2).2
      obtain ⟨Ai, hAi⟩ := argTy_point (C := C) (by omega) hri'
      rw [El_res, Hom.comp_id, ← ΘK_ty_id hW hd hpsT' hpl' hC hAi
        (by simp; omega) (fun t ht => hnat t (List.mem_of_mem_take ht)) (ptValid_of_validPre hp.1)] at this
      simpa [List.map_take] using this
  obtain ⟨A, hA⟩ := argTy_point (C := C) hlt hnr
  rw [tyLook_eq hv, ΘK_ty_id hW hd hpsT' hpl' hC hA rfl hnat (ptValid_of_validPre hv)]
  exact hpt k' σ c C hC args hlt hnr (fun i hi hri => (hpoint i hi hri).2)

end

end Model.Canon
