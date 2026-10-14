import Model.Whnf.Per2

/-!
# The binary relation of inductive types is a partial equivalence
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' k'' m : ℕ}

theorem Comp2_empty (m k : ℕ) (f : Hom k m) : Comp2 S ∅ m k f = Pack2.bot := by
  rw [Comp2_eq]; unfold compF2; rw [dif_neg (by simp)]

theorem perP_bot : PERP Pack2.bot :=
  ⟨fun h => h.elim, fun h => h.elim, fun h => h.elim, fun h => h.elim, fun h => h.elim⟩

/-- The point argument relations of an inductive type's code are partial equivalences. -/
theorem perP_tyLook {Θ : SData m} (ih : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → PER2 S n (Θ.ty c j n g pre))
    {n : ℕ} (h : Hom n m) (c j : ℕ) (pre : List V) :
    PERP (Comp2 S (tyLook (shapeV (Θ.restr h)) c j pre) n n (Hom.id n)) := by
  rcases tyLook_cases (Θ.restr h) c j pre with h0 | h0
  · rw [h0, Comp2_empty]; exact perP_bot
  · rw [tyLook_eq h0]
    exact ih c j n (h.comp (Hom.id n)) pre (ptValid_of_validPre h0) n (Hom.id n)

section
variable {k0 : ℕ} (Θ : SData m) (f : Hom k0 m)

/-- The argument clause of an inductive type, at the restrictions of `g`, from the parameters `ps`
(at which the arguments are related) to the parameters `ps'`. -/
def argRelH (S : Sig) (k : ℕ) (g : Hom k k0) (ps ps' : Tm) : Prop :=
  ∀ k'' (σ' : ISub k'' k) (c : ℕ) (C : Ctor) (args args' : List Tm), (dataD S Θ.idx).ctors[c]? = some C →
    args.length < C.args.length → args'.length = args.length → C.isRec args.length = false →
    (∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
      DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k'' (g.comp σ'.hom)
        (.data Θ.idx (ps.isub σ')) args[j] args'[j]) →
    (∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = false →
      dataP2 S Θ f k'' (g.comp σ'.hom) c j ((args.take j).map (semK S k''))
        ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList
          ((args.take j).reverse ++ (ps.isub σ').toList.reverse))
        args[j] args'[j]) →
    (Comp2 S (tyLook (shapeV (Θ.restr (f.comp (g.comp σ'.hom)))) c args.length (args.map (semK S k'')))
      k'' k'' (Hom.id k'')).ty
      ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList
        (args.reverse ++ (ps.isub σ').toList.reverse))
      ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList
        (args'.reverse ++ (ps'.isub σ').toList.reverse))

theorem argRel2_iff {k : ℕ} {f : Hom k m} {k' : ℕ} (σ : ISub k' k) {ps ps' : Tm} :
    argRel2 S Θ f k' σ ps ps' ↔ argRelH Θ f S k' σ.hom ps ps' := by
  unfold argRel2 argRelH; simp only [ISub.hom_comp]

theorem argRelH_isub {k : ℕ} {g : Hom k k0} {ps ps' : Tm} (h : argRelH Θ f S k g ps ps') (σ : ISub k' k) :
    argRelH Θ f S k' (g.comp σ.hom) (ps.isub σ) (ps'.isub σ) := by
  intro k3 σ3 c C args args' hC hl hl' hr hrec hpt
  have := h k3 (σ.comp σ3) c C args args' hC hl hl' hr
    (fun j hj hj' hrj => by have := hrec j hj hj' hrj; rwa [Hom.comp_assoc, ← ISub.hom_comp, Tm.isub_isub] at this)
    (fun j hj hj' hrj => by have := hpt j hj hj' hrj; rwa [Hom.comp_assoc, ← ISub.hom_comp, Tm.isub_isub] at this)
  rwa [Hom.comp_assoc, ← ISub.hom_comp, Tm.isub_isub, Tm.isub_isub]

end

section dr
variable (hW : WfSig S) {k0 : ℕ} {Θ : SData m} (f : Hom k0 m)
  (hP : ∀ {n : ℕ} (h : Hom n m) (c j : ℕ) (pre : List V), PERP (Comp2 S (tyLook (shapeV (Θ.restr h)) c j pre) n n (Hom.id n)))
include hW hP

omit hP in
/-- Related arguments have equal values. -/
theorem args_sem {k : ℕ} {g : Hom k k0} {C : Ctor} {ps : Tm} {c : ℕ} {args args' : List Tm}
    (hrec : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
      DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g (.data Θ.idx ps) args[j] args'[j])
    (hpt : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = false →
      dataP2 S Θ f k g c j ((args.take j).map (semK S k))
        ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList ((args.take j).reverse ++ ps.toList.reverse))
        args[j] args'[j])
    (hl : args.length = args'.length) : args.map (semK S k) = args'.map (semK S k) := by
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  simp only [List.getElem_map]
  simp only [List.length_map] at h1 h2
  cases hr : C.isRec i
  · have := hpt i h1 h2 hr
    unfold dataP2 at this
    exact semK_eq hW (Comp2_el this).1.2.2
  · cases hrec i h1 h2 hr with
    | intro he _ => exact semK_eq hW he

omit hW hP in
theorem redT_data_eq {k : ℕ} {ps ps2 : Tm} (h : RedT S k (.data Θ.idx ps) (.data Θ.idx ps2)) : ps2 = ps := by
  have := RedW.unique h.1 (redW_self (by simp [step]))
  injection this

omit hW hP in
/-- The argument clause for the restrictions of a parameter list. -/
theorem hypData {k : ℕ} {g : Hom k k0} {ps : Tm} (hR : argRelH Θ f S k g ps ps) :
    ∀ k' (σ : ISub k' k) ps2, RedT S k' ((Tm.data Θ.idx ps).isub σ) (.data Θ.idx ps2) →
      argRelH Θ f S k' (g.comp σ.hom) ps2 ps2 := by
  intro k' σ ps2 h
  obtain rfl := redT_data_eq h
  exact argRelH_isub Θ f hR σ

omit hW hP in
/-- The argument clause at the identity. -/
theorem argRelH_id {k : ℕ} {g : Hom k k0} {ps ps' : Tm} (hR : argRelH Θ f S k g ps ps')
    (hpc : ps.closedB 0 k = true) (hpc' : ps'.closedB 0 k = true) {c : ℕ} {C : Ctor} {args args' : List Tm}
    (hC : (dataD S Θ.idx).ctors[c]? = some C) (hl : args.length < C.args.length) (hl' : args'.length = args.length)
    (hr : C.isRec args.length = false)
    (hrec : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
      DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g (.data Θ.idx ps) args[j] args'[j])
    (hpt : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = false →
      dataP2 S Θ f k g c j ((args.take j).map (semK S k))
        ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList ((args.take j).reverse ++ ps.toList.reverse))
        args[j] args'[j]) :
    (Comp2 S (tyLook (shapeV (Θ.restr (f.comp g))) c args.length (args.map (semK S k))) k k (Hom.id k)).ty
      ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList (args.reverse ++ ps.toList.reverse))
      ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList (args'.reverse ++ ps'.toList.reverse)) := by
  have := hR k (ISub.id k) c C args args' hC hl hl' hr
    (fun j hj hj' hrj => by rw [ISub.hom_id, Hom.comp_id, isub_id_of_closed hpc]; exact hrec j hj hj' hrj)
    (fun j hj hj' hrj => by rw [ISub.hom_id, Hom.comp_id, isub_id_of_closed hpc]; exact hpt j hj hj' hrj)
  rwa [ISub.hom_id, Hom.comp_id, isub_id_of_closed hpc, isub_id_of_closed hpc'] at this

omit hP in
/-- Closed parameters of a typed normal form. -/
theorem ps_closed {k : ℕ} {A ps : Tm} (hA : RedT S k A (.data Θ.idx ps)) (hAt : IsTyK S k A) : ps.closedB 0 k = true := by
  have := closed_of_isTyK hW (hAt.of_tyEq hA.2)
  simpa [Tm.closedB] using this

/-- Related elements of an inductive type, swapped. -/
theorem DR2_symm : ∀ {k : ℕ} {g : Hom k k0} {A t t' : Tm},
    DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t' →
    (∀ k' (σ : ISub k' k) ps, RedT S k' (A.isub σ) (.data Θ.idx ps) → argRelH Θ f S k' (g.comp σ.hom) ps ps) →
    DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t' t := by
  intro k g A t t' hr
  refine DR2.rec (motive_1 := fun k g A t t' _ =>
      (∀ k' (σ : ISub k' k) ps, RedT S k' (A.isub σ) (.data Θ.idx ps) → argRelH Θ f S k' (g.comp σ.hom) ps ps) →
      DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t' t)
    (motive_2 := fun k g A t t' _ => (∀ ps, RedT S k A (.data Θ.idx ps) → argRelH Θ f S k g ps ps) →
      DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t' t) ?_ ?_ ?_ hr
  · intro k g A t t' he _ ih hyp
    exact .intro he.symm fun k' σ => ih k' σ fun ps hps => hyp k' σ ps hps
  · intro k g A t t' ps qs qs' c C args args' rs rs' hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl'
      hrec hpt ihrec hyp
    have hR := hyp ps hA
    have hpc : ps.closedB 0 k = true := ps_closed hW hA (isTyK_of_ty hW (HasTy.eqL heq))
    refine .con hm' hm heq.symm hC hA hpl ht' ht hrs' hrs (fun i r r' h1 h2 => I_eq_symm (hreq i r' r h2 h1))
      hsc' hsc hl' hl (fun j hj' hj hr => ihrec j hj hj' hr (hypData f hR)) (fun j hj' hj hr => ?_)
    have x := hpt j hj hj' hr
    have hsem := args_sem hW f hrec hpt (by omega)
    have hsemj : (args'.take j).map (semK S k) = (args.take j).map (semK S k) := by
      rw [List.map_take, List.map_take, hsem]
    have hlj : (args.take j).length = j := by simp; omega
    have hty := argRelH_id f hR hpc hpc (args := args.take j) (args' := args'.take j) hC (by rw [hlj]; omega)
      (by simp; omega) (by rw [hlj]; exact hr)
      (fun i hi hi' hri => by
        simp only [List.getElem_take]; exact hrec i (by simp at hi; omega) (by simp at hi'; omega) hri)
      (fun i hi hi' hri => by
        simp only [List.getElem_take, List.take_take]
        rw [Nat.min_eq_left (by simp at hi; omega)]
        exact hpt i (by simp at hi; omega) (by simp at hi'; omega) hri)
    rw [hlj] at hty
    have P := hP (f.comp g) c j ((args.take j).map (semK S k))
    unfold dataP2 at x ⊢
    rw [hsemj]
    have y := P.symEl hty x
    exact P.conv hty y
  · intro k g A t t' ps qs qs' u u' a a' φ φ' hm hm' heq hH hA hpl ht ht' hs hs' h12 h21 ha hu iha ihu hyp
    have hR := hyp ps hA
    refine .hcomp hm' hm heq.symm hH hA hpl ht' ht hs' hs h21 h12 (iha (hypData f hR))
      (fun k' σ r hr hh => ihu k' σ r hr ?_ ?_)
    · rw [holds_iff_entails (I.scoped_subst hs σ.sc)]
      exact ent_trans ((holds_iff_entails (I.scoped_subst hs' σ.sc)).1 hh) (ent_subst h21 σ.τ)
    · intro k'' σ' ps2 h
      rw [Tm.isub_isub] at h
      obtain rfl := redT_data_eq h
      rw [Hom.comp_assoc, ← ISub.hom_comp]
      exact argRelH_isub Θ f hR (σ.comp σ')

/-- Related elements of an inductive type compose. -/
theorem DR2_trans : ∀ {k : ℕ} {g : Hom k k0} {A t t' : Tm},
    DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t' → ∀ {t'' : Tm},
    DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t' t'' →
    (∀ k' (σ : ISub k' k) ps, RedT S k' (A.isub σ) (.data Θ.idx ps) → argRelH Θ f S k' (g.comp σ.hom) ps ps) →
    DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t'' := by
  intro k g A t t' hr
  refine DR2.rec (motive_1 := fun k g A t t' _ => ∀ {t'' : Tm},
      DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t' t'' →
      (∀ k' (σ : ISub k' k) ps, RedT S k' (A.isub σ) (.data Θ.idx ps) → argRelH Θ f S k' (g.comp σ.hom) ps ps) →
      DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t'')
    (motive_2 := fun k g A t t' _ => ∀ {t'' : Tm},
      DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t' t'' →
      (∀ ps, RedT S k A (.data Θ.idx ps) → argRelH Θ f S k g ps ps) →
      DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t'') ?_ ?_ ?_ hr
  · intro k g A t t' he _ ih t'' h2 hyp
    cases h2 with
    | intro he2 hh2 => exact .intro (he.trans he2) fun k' σ => ih k' σ (hh2 k' σ) fun ps hps => hyp k' σ ps hps
  · intro k g A t t' ps qs qs' c C args args' rs rs' hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl'
      hrec hpt ihrec t'' h2 hyp
    have hR := hyp ps hA
    have hpc : ps.closedB 0 k = true := ps_closed hW hA (isTyK_of_ty hW (HasTy.eqL heq))
    cases h2 with
    | hcomp _ _ _ _ _ _ ht2 =>
      have := RedW.unique ht'.1 ht2.1; cases this
    | con hm2 hm2' heq2 hC2 hA2 hpl2 ht2 ht2' hrs2 hrs2' hreq2 hsc2 hsc2' hl2 hl2' hrec2 hpt2 =>
      have e := RedW.unique ht'.1 ht2.1
      simp only [Tm.con.injEq] at e
      obtain ⟨-, rfl, rfl, ea, rfl⟩ := e
      have ea' := congrArg Tm.toList ea
      simp only [toList_ofList] at ea'
      subst ea'
      have e2 := RedW.unique hA.1 hA2.1
      simp only [Tm.data.injEq] at e2
      obtain ⟨-, rfl⟩ := e2
      obtain rfl := Option.some.inj (hC.symm.trans hC2)
      refine .con hm hm2' (heq.trans heq2) hC hA hpl ht ht2' hrs hrs2'
        (fun i r r'' h1 h3 => ?_) hsc hsc2' hl hl2' (fun j hj hj'' hr => ?_) (fun j hj hj'' hr => ?_)
      · obtain ⟨r', h2⟩ : ∃ r', rs'[i]? = some r' := by
          refine ⟨rs'[i]'?_, List.getElem?_eq_getElem _⟩
          have := (List.getElem?_eq_some_iff.1 h1).1; omega
        exact I_eq_trans (hreq i r r' h1 h2) (hreq2 i r' r'' h2 h3)
      · exact ihrec j hj (by omega) hr (hrec2 j (by omega) hj'' hr) (hypData f hR)
      · have x := hpt j hj (by omega) hr
        have y := hpt2 j (by omega) hj'' hr
        have hsem := args_sem hW f hrec hpt (by omega)
        have hsemj : (args'.take j).map (semK S k) = (args.take j).map (semK S k) := by
          rw [List.map_take, List.map_take, hsem]
        have hlj : (args.take j).length = j := by simp; omega
        have hty := argRelH_id f hR hpc hpc (args := args.take j) (args' := args'.take j) hC
          (by rw [hlj]; omega) (by simp; omega) (by rw [hlj]; exact hr)
          (fun i hi hi' hri => by
            simp only [List.getElem_take]; exact hrec i (by simp at hi; omega) (by simp at hi'; omega) hri)
          (fun i hi hi' hri => by
            simp only [List.getElem_take, List.take_take]
            rw [Nat.min_eq_left (by simp at hi; omega)]
            exact hpt i (by simp at hi; omega) (by simp at hi'; omega) hri)
        rw [hlj] at hty
        have P := hP (f.comp g) c j ((args.take j).map (semK S k))
        unfold dataP2 at x y ⊢
        rw [hsemj] at y
        exact P.transEl hty x (P.conv (P.symTy hty) y)
  · intro k g A t t' ps qs qs' u u' a a' φ φ' hm hm' heq hH hA hpl ht ht' hs hs' h12 h21 ha hu iha ihu t'' h2 hyp
    have hR := hyp ps hA
    cases h2 with
    | con _ _ _ _ _ _ ht2 =>
      have := RedW.unique ht'.1 ht2.1; cases this
    | hcomp hm2 hm2' heq2 hH2 hA2 hpl2 ht2 ht2' hs2 hs2' h122 h212 ha2 hu2 =>
      have e := RedW.unique ht'.1 ht2.1
      simp only [Tm.hcomp.injEq, Tm.data.injEq] at e
      obtain ⟨⟨-, rfl⟩, rfl, rfl, rfl⟩ := e
      have e2 := RedW.unique hA.1 hA2.1
      simp only [Tm.data.injEq] at e2
      obtain ⟨-, rfl⟩ := e2
      refine .hcomp hm hm2' (heq.trans heq2) hH hA hpl ht ht2' hs hs2' (ent_trans h12 h122) (ent_trans h212 h21)
        (iha ha2 (hypData f hR)) (fun k' σ r hr hh => ihu k' σ r hr hh (hu2 k' σ r hr ?_) ?_)
      · rw [holds_iff_entails (I.scoped_subst hs' σ.sc)]
        exact ent_trans ((holds_iff_entails (I.scoped_subst hs σ.sc)).1 hh) (ent_subst h12 σ.τ)
      · intro k'' σ' ps2 h
        rw [Tm.isub_isub] at h
        obtain rfl := redT_data_eq h
        rw [Hom.comp_assoc, ← ISub.hom_comp]
        exact argRelH_isub Θ f hR (σ.comp σ')

end dr

end

end Model.Whnf
