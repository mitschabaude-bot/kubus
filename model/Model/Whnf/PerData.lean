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

/-- The parameter relations of an inductive type's code are partial equivalences. -/
theorem perP_parEntry {Θ : SData m} (ihp : ∀ n (g : Hom n m) j t X, vnth (Θ.pt n g) j = ZFSet.pair t X → PER2 S n X)
    {k0 : ℕ} (f : Hom k0 m) {k' : ℕ} (σ : ISub k' k0) (j : ℕ) :
    PERP (Comp2 S (π2 (parEntry Θ f k' σ j)) k' k' (Hom.id k')) := by
  by_cases h : ∃ t X, parEntry Θ f k' σ j = ZFSet.pair t X
  · obtain ⟨t, X, e⟩ := h
    rw [e, π2_pair]
    exact ihp k' _ j t X e k' (Hom.id k')
  · have : π2 (parEntry Θ f k' σ j) = ∅ := by
      simp only [π2]; rw [dif_neg]; rintro ⟨a, b, e⟩; exact h ⟨a, b, e⟩
    rw [this, Comp2_empty]; exact perP_bot


theorem data_len_of {d : ℕ} {ps : Tm} (hW : WfSig S) (h : IsTyK S k (.data d ps)) :
    ps.toList.length = (dataD S d).params.length := by
  obtain ⟨l, hd | hd⟩ := h
  · obtain ⟨D, hD, hl⟩ := gen_data (spec_to_minimal hW hd) rfl
    have : dataD S d = D := by unfold dataD; rw [hD]
    rw [this]; exact hl
  · cases hd

theorem parRel2_symm {Θ : SData m} (ihp : ∀ n (g : Hom n m) j t X, vnth (Θ.pt n g) j = ZFSet.pair t X → PER2 S n X)
    {k0 : ℕ} (f : Hom k0 m) {k' : ℕ} (σ : ISub k' k0) {ps ps' : Tm} (h : parRel2 S Θ f k' σ ps ps') :
    parRel2 S Θ f k' σ ps' ps := by
  intro j p' p e1 e2
  have P := perP_parEntry ihp f σ j
  obtain ⟨h1, h0⟩ := h j p p' e2 e1
  refine ⟨fun t => P.symTy (h1 t), fun t Aj hA => ?_⟩
  obtain ⟨hty, hel⟩ := h0 t Aj hA
  exact ⟨P.symTy hty, P.conv hty (P.symEl hty hel)⟩

theorem parRel2_trans {Θ : SData m} (ihp : ∀ n (g : Hom n m) j t X, vnth (Θ.pt n g) j = ZFSet.pair t X → PER2 S n X)
    {k0 : ℕ} (f : Hom k0 m) {k' : ℕ} (σ : ISub k' k0) {ps ps2 ps'' : Tm} (hl : ps2.toList.length = ps.toList.length)
    (h : parRel2 S Θ f k' σ ps ps2) (h' : parRel2 S Θ f k' σ ps2 ps'') :
    parRel2 S Θ f k' σ ps ps'' := by
  intro j p p'' e1 e3
  have hj : j < ps2.toList.length := by rw [hl]; exact (List.getElem?_eq_some_iff.1 e1).1
  have e2 : ps2.toList[j]? = some ps2.toList[j] := List.getElem?_eq_getElem hj
  have P := perP_parEntry ihp f σ j
  obtain ⟨a1, a0⟩ := h j p _ e1 e2
  obtain ⟨b1, b0⟩ := h' j _ p'' e2 e3
  refine ⟨fun t => P.transTy (a1 t) (b1 t), fun t Aj hA => ?_⟩
  obtain ⟨t1, l1⟩ := a0 t Aj hA
  obtain ⟨t2, l2⟩ := b0 t Aj hA
  exact ⟨P.transTy t1 t2, P.transEl t1 l1 (P.conv (P.symTy t1) l2)⟩

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

mutual
/-- Related elements of an inductive type, swapped. -/
theorem DR2_symm : ∀ {k : ℕ} {g : Hom k k0} {A t t' : Tm},
    DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t' →
    (∀ k' (σ : ISub k' k) ps, RedT S k' (A.isub σ) (.data Θ.idx ps) → argRelH Θ f S k' (g.comp σ.hom) ps ps) →
    DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t' t
  | _, _, _, _, _, .intro he hh hc hc', hyp =>
    .intro he.symm (fun k' σ => DR2At_symm (hh k' σ) fun ps hps => hyp k' σ ps hps) hc' hc

/-- Related elements of an inductive type at a stage, swapped. -/
theorem DR2At_symm : ∀ {k : ℕ} {g : Hom k k0} {A t t' : Tm},
    DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t' →
    (∀ ps, RedT S k A (.data Θ.idx ps) → argRelH Θ f S k g ps ps) →
    DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t' t
  | k, g, A, t, t', .con (ps := ps) (c := c) (args := args) (args' := args') hm hm' heq hC hA hpl ht ht' hrs hrs'
      hreq hsc hsc' hl hl' hrec hpt, hyp => by
    have hR := hyp ps hA
    have hpc : ps.closedB 0 k = true := ps_closed hW hA (isTyK_of_ty hW (HasTy.eqL heq))
    refine .con hm' hm heq.symm hC hA hpl ht' ht hrs' hrs (fun i r r' h1 h2 => I_eq_symm (hreq i r' r h2 h1))
      hsc' hsc hl' hl (fun j hj' hj hr => DR2_symm (hrec j hj hj' hr) (hypData f hR)) (fun j hj' hj hr => ?_)
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
  | k, g, A, t, t', .hcomp (ps := ps) hm hm' heq hH hA hpl ht ht' hs hs' h12 h21 ha hu, hyp => by
    have hR := hyp ps hA
    refine .hcomp hm' hm heq.symm hH hA hpl ht' ht hs' hs h21 h12 (DR2_symm ha (hypData f hR))
      (fun k' σ r hr hh => DR2_symm (hu k' σ r hr ?_) ?_)
    · rw [holds_iff_entails (I.scoped_subst hs σ.sc)]
      exact ent_trans ((holds_iff_entails (I.scoped_subst hs' σ.sc)).1 hh) (ent_subst h21 σ.τ)
    · intro k'' σ' ps2 h
      rw [Tm.isub_isub] at h
      obtain rfl := redT_data_eq h
      rw [Hom.comp_assoc, ← ISub.hom_comp]
      exact argRelH_isub Θ f hR (σ.comp σ')
end

mutual
/-- Related elements of an inductive type compose. -/
theorem DR2_trans : ∀ {k : ℕ} {g : Hom k k0} {A t t' t'' : Tm},
    DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t' →
    DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t' t'' →
    (∀ k' (σ : ISub k' k) ps, RedT S k' (A.isub σ) (.data Θ.idx ps) → argRelH Θ f S k' (g.comp σ.hom) ps ps) →
    DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t''
  | _, _, _, _, _, _, .intro he hh hc _, .intro he2 hh2 _ hc2, hyp =>
    .intro (he.trans he2) (fun k' σ => DR2At_trans (hh k' σ) (hh2 k' σ) fun ps hps => hyp k' σ ps hps) hc hc2

/-- Related elements of an inductive type at a stage compose. -/
theorem DR2At_trans : ∀ {k : ℕ} {g : Hom k k0} {A t t' t'' : Tm},
    DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t' →
    DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t' t'' →
    (∀ ps, RedT S k A (.data Θ.idx ps) → argRelH Θ f S k g ps ps) →
    DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t''
  | k, g, A, t, t', t'', .con (ps := ps) (c := c) (C := C) (args := args) (args' := args') (rs' := rs') hm hm' heq hC hA hpl ht ht'
      hrs hrs' hreq hsc hsc' hl hl' hrec hpt, h2, hyp => by
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
      · exact DR2_trans (hrec j hj (by omega) hr) (hrec2 j (by omega) hj'' hr) (hypData f hR)
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
  | k, g, A, t, t', t'', .hcomp (ps := ps) hm hm' heq hH hA hpl ht ht' hs hs' h12 h21 ha hu, h2, hyp => by
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
        (DR2_trans ha ha2 (hypData f hR)) (fun k' σ r hr hh => DR2_trans (hu k' σ r hr hh) (hu2 k' σ r hr ?_) ?_)
      · rw [holds_iff_entails (I.scoped_subst hs' σ.sc)]
        exact ent_trans ((holds_iff_entails (I.scoped_subst hs σ.sc)).1 hh) (ent_subst h12 σ.τ)
      · intro k'' σ' ps2 h
        rw [Tm.isub_isub] at h
        obtain rfl := redT_data_eq h
        rw [Hom.comp_assoc, ← ISub.hom_comp]
        exact argRelH_isub Θ f hR (σ.comp σ')
end

/-- A related prefix of arguments is related to itself. -/
theorem prefix_refl {k : ℕ} {g : Hom k k0} {ps : Tm} (hR : argRelH Θ f S k g ps ps) (hpc : ps.closedB 0 k = true)
    {c : ℕ} {C : Ctor} (hC : (dataD S Θ.idx).ctors[c]? = some C) {args args' : List Tm}
    (hl : args.length ≤ C.args.length) (hl' : args'.length = args.length)
    (hrec : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
      DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g (.data Θ.idx ps) args[j] args'[j])
    (hpt : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = false →
      dataP2 S Θ f k g c j ((args.take j).map (semK S k))
        ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList ((args.take j).reverse ++ ps.toList.reverse))
        args[j] args'[j]) :
    (∀ j (hj : j < args.length), C.isRec j = true →
      DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g (.data Θ.idx ps) args[j] args[j]) ∧
    (∀ j (hj : j < args.length), C.isRec j = false →
      dataP2 S Θ f k g c j ((args.take j).map (semK S k))
        ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList ((args.take j).reverse ++ ps.toList.reverse))
        args[j] args[j]) := by
  refine ⟨fun j hj hr => ?_, fun j hj hr => ?_⟩
  · have h1 := hrec j hj (by omega) hr
    exact DR2_trans hW f hP h1 (DR2_symm hW f hP h1 (hypData f hR)) (hypData f hR)
  · have hlj : (args.take j).length = j := by simp; omega
    have hty := argRelH_id f hR hpc hpc (args := args.take j) (args' := args'.take j) hC
      (by rw [hlj]; omega) (by simp; omega) (by rw [hlj]; exact hr)
      (fun i hi hi' hri => by
        simp only [List.getElem_take]; exact hrec i (by simp at hi; omega) (by simp at hi'; omega) hri)
      (fun i hi hi' hri => by
        simp only [List.getElem_take, List.take_take]
        rw [Nat.min_eq_left (by simp at hi; omega)]
        exact hpt i (by simp at hi; omega) (by simp at hi'; omega) hri)
    rw [hlj] at hty
    have x := hpt j hj (by omega) hr
    unfold dataP2 at x ⊢
    exact (hP (f.comp g) c j _).reflEl hty x

/-- Related elements of an inductive type, at a related type. -/
theorem DR2_conv : ∀ {k : ℕ} {g : Hom k k0} {A t t' : Tm},
    DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t' → ∀ {A' : Tm}, TyEq S k A A' →
    (∀ k' (σ : ISub k' k) ps ps', RedT S k' (A.isub σ) (.data Θ.idx ps) → RedT S k' (A'.isub σ) (.data Θ.idx ps') →
      argRelH Θ f S k' (g.comp σ.hom) ps ps' ∧ argRelH Θ f S k' (g.comp σ.hom) ps ps ∧
      argRelH Θ f S k' (g.comp σ.hom) ps' ps') →
    (∀ k' (σ : ISub k' k), ∃ ps', RedT S k' (A'.isub σ) (.data Θ.idx ps') ∧ ps' = Tm.ofList ps'.toList) →
    DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A' t t' := by
  intro k g A t t' hr
  refine DR2.rec (motive_1 := fun k g A t t' _ => ∀ {A' : Tm}, TyEq S k A A' →
      (∀ k' (σ : ISub k' k) ps ps', RedT S k' (A.isub σ) (.data Θ.idx ps) → RedT S k' (A'.isub σ) (.data Θ.idx ps') →
        argRelH Θ f S k' (g.comp σ.hom) ps ps' ∧ argRelH Θ f S k' (g.comp σ.hom) ps ps ∧
        argRelH Θ f S k' (g.comp σ.hom) ps' ps') →
      (∀ k' (σ : ISub k' k), ∃ ps', RedT S k' (A'.isub σ) (.data Θ.idx ps') ∧ ps' = Tm.ofList ps'.toList) →
      DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A' t t')
    (motive_2 := fun k g A t t' _ => ∀ {A' ps' : Tm}, TyEq S k A A' → RedT S k A' (.data Θ.idx ps') →
      ps' = Tm.ofList ps'.toList →
      (∀ ps, RedT S k A (.data Θ.idx ps) →
        argRelH Θ f S k g ps ps' ∧ argRelH Θ f S k g ps ps ∧ argRelH Θ f S k g ps' ps') →
      DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A' t t') ?_ ?_ ?_ hr
  · intro k g A t t' he _ _ _ ih ihc ihc' A' hE hyp hex
    refine .intro (he.tyConv hE) (fun k' σ => ?_) (fun k' σ w hw k'' ρ => ?_) (fun k' σ w hw k'' ρ => ?_)
    · obtain ⟨ps', hps', hpl'⟩ := hex k' σ
      exact ih k' σ (hE.isub hW σ) hps' hpl' fun ps hps => hyp k' σ ps ps' hps hps'
    · obtain ⟨ps', hps', hpl'⟩ := hex k'' (σ.comp ρ)
      exact ihc k' σ w hw k'' ρ (hE.isub hW _) hps' hpl' fun ps hps => hyp k'' (σ.comp ρ) ps ps' hps hps'
    · obtain ⟨ps', hps', hpl'⟩ := hex k'' (σ.comp ρ)
      exact ihc' k' σ w hw k'' ρ (hE.isub hW _) hps' hpl' fun ps hps => hyp k'' (σ.comp ρ) ps ps' hps hps'
  · intro k g A t t' ps qs qs' c C args args' rs rs' hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl'
      hrec hpt ihrec A' ps' hE hA' hpl' hyp
    obtain ⟨hR, hRd, hRd'⟩ := hyp ps hA
    have hpc : ps.closedB 0 k = true := ps_closed hW hA (isTyK_of_ty hW (HasTy.eqL heq))
    have hpc' : ps'.closedB 0 k = true := ps_closed hW hA' ((isTyK_of_ty hW (HasTy.eqL heq)).of_tyEq hE)
    have hdd : TyEq S k (.data Θ.idx ps) (.data Θ.idx ps') := (hA.2.symm.trans hW hE).trans hW hA'.2
    refine .con hm hm' (heq.tyConv hE) hC hA' hpl' ⟨ht.1, ht.2.tyConv hE⟩ ⟨ht'.1, ht'.2.tyConv hE⟩ hrs hrs' hreq
      hsc hsc' hl hl' (fun j hj hj' hr => ?_) (fun j hj hj' hr => ?_)
    · refine ihrec j hj hj' hr hdd (fun k' σ ps2 ps2' h1 h2 => ?_) (fun k' σ => ⟨ps'.isub σ,
        ⟨redW_self rfl, TyEq.refl _⟩, isList_subst hpl' _ _⟩)
      obtain rfl := redT_data_eq h1
      obtain rfl := redT_data_eq h2
      exact ⟨argRelH_isub Θ f hR σ, argRelH_isub Θ f hRd σ, argRelH_isub Θ f hRd' σ⟩
    · obtain ⟨hrecd, hptd⟩ := prefix_refl hW f hP hRd hpc hC (by omega) (by omega) hrec hpt
      have hlj : (args.take j).length = j := by simp; omega
      have hty := argRelH_id f hR hpc hpc' (args := args.take j) (args' := args.take j) hC
        (by rw [hlj]; omega) rfl (by rw [hlj]; exact hr)
        (fun i hi _ hri => by
          simp only [List.getElem_take]; exact hrecd i (by simp at hi; omega) hri)
        (fun i hi _ hri => by
          simp only [List.getElem_take, List.take_take]
          rw [Nat.min_eq_left (by simp at hi; omega)]
          exact hptd i (by simp at hi; omega) hri)
      rw [hlj] at hty
      have x := hpt j hj hj' hr
      unfold dataP2 at x ⊢
      exact (hP (f.comp g) c j _).conv hty x
  · intro k g A t t' ps qs qs' u u' a a' φ φ' hm hm' heq hH hA hpl ht ht' hs hs' h12 h21 ha hu iha ihu A' ps' hE hA'
      hpl' hyp
    obtain ⟨hR, hRd, hRd'⟩ := hyp ps hA
    have hdd : TyEq S k (.data Θ.idx ps) (.data Θ.idx ps') := (hA.2.symm.trans hW hE).trans hW hA'.2
    have hyp2 : ∀ k' (σ : ISub k' k) ps2 ps2', RedT S k' ((Tm.data Θ.idx ps).isub σ) (.data Θ.idx ps2) →
        RedT S k' ((Tm.data Θ.idx ps').isub σ) (.data Θ.idx ps2') →
        argRelH Θ f S k' (g.comp σ.hom) ps2 ps2' ∧ argRelH Θ f S k' (g.comp σ.hom) ps2 ps2 ∧
        argRelH Θ f S k' (g.comp σ.hom) ps2' ps2' := by
      intro k' σ ps2 ps2' h1 h2
      obtain rfl := redT_data_eq h1
      obtain rfl := redT_data_eq h2
      exact ⟨argRelH_isub Θ f hR σ, argRelH_isub Θ f hRd σ, argRelH_isub Θ f hRd' σ⟩
    have hex2 : ∀ k' (σ : ISub k' k), ∃ ps2', RedT S k' ((Tm.data Θ.idx ps').isub σ) (.data Θ.idx ps2') ∧
        ps2' = Tm.ofList ps2'.toList := fun k' σ =>
      ⟨ps'.isub σ, ⟨redW_self rfl, TyEq.refl _⟩, isList_subst hpl' _ _⟩
    refine .hcomp hm hm' (heq.tyConv hE) hH hA' hpl' ⟨ht.1, ht.2.tyConv hE⟩ ⟨ht'.1, ht'.2.tyConv hE⟩ hs hs' h12 h21
      (iha hdd hyp2 hex2) (fun k' σ r hr hh => ihu k' σ r hr hh (hdd.isub hW σ) ?_ ?_)
    · intro k'' σ' ps2 ps2' h1 h2
      rw [Tm.isub_isub] at h1 h2
      obtain rfl := redT_data_eq h1
      obtain rfl := redT_data_eq h2
      rw [Hom.comp_assoc, ← ISub.hom_comp]
      exact ⟨argRelH_isub Θ f hR (σ.comp σ'), argRelH_isub Θ f hRd (σ.comp σ'), argRelH_isub Θ f hRd' (σ.comp σ')⟩
    · intro k'' σ'
      rw [Tm.isub_isub]
      exact ⟨ps'.isub (σ.comp σ'), ⟨redW_self rfl, TyEq.refl _⟩, isList_subst hpl' _ _⟩

/-- A related prefix of arguments, at related parameters. -/
theorem prefix_conv {k : ℕ} {g : Hom k k0} {ps ps' : Tm} (hR : argRelH Θ f S k g ps ps')
    (hRd : argRelH Θ f S k g ps ps) (hRd' : argRelH Θ f S k g ps' ps')
    (hpc : ps.closedB 0 k = true) (hpc' : ps'.closedB 0 k = true) (hpl' : ps' = Tm.ofList ps'.toList)
    (hdd : TyEq S k (.data Θ.idx ps) (.data Θ.idx ps'))
    {c : ℕ} {C : Ctor} (hC : (dataD S Θ.idx).ctors[c]? = some C) {args args' : List Tm}
    (hl : args.length ≤ C.args.length) (hl' : args'.length = args.length)
    (hrec : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
      DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g (.data Θ.idx ps) args[j] args'[j])
    (hpt : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = false →
      dataP2 S Θ f k g c j ((args.take j).map (semK S k))
        ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList ((args.take j).reverse ++ ps.toList.reverse))
        args[j] args'[j]) :
    (∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
      DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g (.data Θ.idx ps') args[j] args'[j]) ∧
    (∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = false →
      dataP2 S Θ f k g c j ((args.take j).map (semK S k))
        ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList ((args.take j).reverse ++ ps'.toList.reverse))
        args[j] args'[j]) := by
  refine ⟨fun j hj hj' hr => ?_, fun j hj hj' hr => ?_⟩
  · refine DR2_conv hW f hP (hrec j hj hj' hr) hdd (fun k' σ ps2 ps2' h1 h2 => ?_) (fun k' σ =>
      ⟨ps'.isub σ, ⟨redW_self rfl, TyEq.refl _⟩, isList_subst hpl' _ _⟩)
    obtain rfl := redT_data_eq h1
    obtain rfl := redT_data_eq h2
    exact ⟨argRelH_isub Θ f hR σ, argRelH_isub Θ f hRd σ, argRelH_isub Θ f hRd' σ⟩
  · obtain ⟨hrecd, hptd⟩ := prefix_refl hW f hP hRd hpc hC hl hl' hrec hpt
    have hlj : (args.take j).length = j := by simp; omega
    have hty := argRelH_id f hR hpc hpc' (args := args.take j) (args' := args.take j) hC
      (by rw [hlj]; omega) rfl (by rw [hlj]; exact hr)
      (fun i hi _ hri => by
        simp only [List.getElem_take]; exact hrecd i (by simp at hi; omega) hri)
      (fun i hi _ hri => by
        simp only [List.getElem_take, List.take_take]
        rw [Nat.min_eq_left (by simp at hi; omega)]
        exact hptd i (by simp at hi; omega) hri)
    rw [hlj] at hty
    have x := hpt j hj hj' hr
    unfold dataP2 at x ⊢
    exact (hP (f.comp g) c j _).conv hty x

/-- Composition of argument clauses. -/
theorem argRelH_comp {k : ℕ} {g : Hom k k0} {ps ps' ps'' : Tm} (r1 : argRelH Θ f S k g ps ps')
    (d : argRelH Θ f S k g ps ps) (d' : argRelH Θ f S k g ps' ps') (r2 : argRelH Θ f S k g ps' ps'')
    (hT : IsTyK S k (.data Θ.idx ps)) (hT' : IsTyK S k (.data Θ.idx ps')) (hT'' : IsTyK S k (.data Θ.idx ps''))
    (hpl' : ps' = Tm.ofList ps'.toList)
    (hdd : TyEq S k (.data Θ.idx ps) (.data Θ.idx ps')) : argRelH Θ f S k g ps ps'' := by
  intro k'' σ' c C args args'' hC hl hl'' hr hrec hpt
  have r1σ := argRelH_isub Θ f r1 σ'
  have dσ := argRelH_isub Θ f d σ'
  have d'σ := argRelH_isub Θ f d' σ'
  have r2σ := argRelH_isub Θ f r2 σ'
  have hcl : ∀ {X : Tm}, IsTyK S k (.data Θ.idx X) → (X.isub σ').closedB 0 k'' = true := fun h => by
    have := closed_of_isTyK hW (h.isub hW σ'); simpa [Tm.closedB] using this
  obtain ⟨hrecd, hptd⟩ := prefix_refl hW f hP dσ (hcl hT) hC hl.le hl'' hrec hpt
  have a := argRelH_id f r1σ (hcl hT) (hcl hT') (args := args) (args' := args) hC hl rfl hr
    (fun i hi _ hri => hrecd i hi hri) (fun i hi _ hri => hptd i hi hri)
  obtain ⟨hrec', hpt'⟩ := prefix_conv hW f hP r1σ dσ d'σ (hcl hT) (hcl hT') (isList_subst hpl' _ _)
    (hdd.isub hW σ') hC hl.le hl'' hrec hpt
  have b := argRelH_id f r2σ (hcl hT') (hcl hT'') (args := args) (args' := args'') hC hl hl'' hr hrec' hpt'
  exact (hP _ c args.length _).transTy a b

end dr

theorem per2_dataC (hW : WfSig S) {Θ : SData m}
    (ih : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → PER2 S n (Θ.ty c j n g pre))
    (ihp : ∀ n (g : Hom n m) j t X, vnth (Θ.pt n g) j = ZFSet.pair t X → PER2 S n X) :
    PER2 S m (dataC Θ) := by
  intro k f
  have hP : ∀ {n : ℕ} (h : Hom n m) (c j : ℕ) (pre : List V),
      PERP (Comp2 S (tyLook (shapeV (Θ.restr h)) c j pre) n n (Hom.id n)) := fun h c j pre => perP_tyLook ih h c j pre
  rw [Comp2_dataC]
  -- the diagonal clause of a related type, at its normal forms
  have diagOf : ∀ {T T' : Tm}, (∀ k' (σ : ISub k' k), ∃ ps ps',
      RedT S k' (T.isub σ) (.data Θ.idx ps) ∧ RedT S k' (T'.isub σ) (.data Θ.idx ps') ∧
      ps = Tm.ofList ps.toList ∧ ps' = Tm.ofList ps'.toList ∧
      argRel2 S Θ f k' σ ps ps' ∧ argRel2 S Θ f k' σ ps' ps ∧ argRel2 S Θ f k' σ ps ps ∧
      argRel2 S Θ f k' σ ps' ps' ∧ parRel2 S Θ f k' σ ps ps') →
      ∀ k' (σ : ISub k' k) ps, RedT S k' (T.isub σ) (.data Θ.idx ps) →
        argRelH Θ f S k' ((Hom.id k).comp σ.hom) ps ps := by
    intro T T' h k' σ ps hps
    obtain ⟨ps0, -, h1, -, -, -, -, -, hd, -, -⟩ := h k' σ
    obtain rfl : ps = ps0 := by have := RedW.unique hps.1 h1.1; injection this
    rw [Hom.id_comp]; exact (argRel2_iff Θ σ).1 hd
  refine ⟨fun {T T'} hT => ?_, fun {T T' T''} hT hT' => ?_, fun {T T' t t'} hT ht => ?_,
    fun {T T' t t' t''} hT ht ht' => ?_, fun {T T' t t'} hT ht => ?_⟩
  · obtain ⟨hb, hall, hc, hc'⟩ := hT
    refine ⟨base_symm hb, fun k' σ => ?_, hc', hc⟩
    obtain ⟨ps, ps', h1, h2, hl, hl', r12, r21, d, d', pr⟩ := hall k' σ
    exact ⟨ps', ps, h2, h1, hl', hl, r21, r12, d', d, parRel2_symm ihp f σ pr⟩
  · obtain ⟨hb, hall, hc, -⟩ := hT
    obtain ⟨hb', hall', -, hc''⟩ := hT'
    refine ⟨base_trans hW hb hb', fun k' σ => ?_, hc, hc''⟩
    obtain ⟨ps, ps', h1, h2, hl, hl', r12, r21, d, d', pr⟩ := hall k' σ
    obtain ⟨ps2, ps'', g1, g2, hl2, hl'', r12', r21', d2, d'', pr'⟩ := hall' k' σ
    obtain rfl : ps2 = ps' := by have := RedW.unique g1.1 h2.1; injection this
    have hTd : IsTyK S k' (.data Θ.idx ps) := (hb.1.isub hW σ).of_tyEq h1.2
    have hTd' : IsTyK S k' (.data Θ.idx ps2) := (hb.2.1.isub hW σ).of_tyEq h2.2
    have hTd'' : IsTyK S k' (.data Θ.idx ps'') := (hb'.2.1.isub hW σ).of_tyEq g2.2
    have hdd : TyEq S k' (.data Θ.idx ps) (.data Θ.idx ps2) :=
      (h1.2.symm.trans hW (hb.2.2.2.2.isub hW σ)).trans hW h2.2
    have hdd' : TyEq S k' (.data Θ.idx ps'') (.data Θ.idx ps2) :=
      (g2.2.symm.trans hW (hb'.2.2.2.2.isub hW σ).symm).trans hW g1.2
    rw [argRel2_iff] at r12 r21 d d' r12' r21' d2 d''
    exact ⟨ps, ps'', h1, g2, hl, hl'', (argRel2_iff Θ σ).2 (argRelH_comp hW f hP r12 d d' r12' hTd hTd' hTd'' hl' hdd),
      (argRel2_iff Θ σ).2 (argRelH_comp hW f hP r21' d'' d' r21 hTd'' hTd' hTd hl' hdd'), (argRel2_iff Θ σ).2 d,
      (argRel2_iff Θ σ).2 d'', parRel2_trans ihp f σ
        (by rw [data_len_of hW hTd', data_len_of hW hTd]) pr pr'⟩
  · obtain ⟨he, hmem, -, hdr⟩ := ht
    exact ⟨he.symm, by rw [← semK_eq hW he.2.2]; exact hmem, he.symm, DR2_symm hW f hP hdr (diagOf hT.2.1)⟩
  · obtain ⟨he, hmem, -, hdr⟩ := ht
    obtain ⟨he', -, -, hdr'⟩ := ht'
    exact ⟨he.trans he', hmem, he.trans he', DR2_trans hW f hP hdr hdr' (diagOf hT.2.1)⟩
  · obtain ⟨he, hmem, -, hdr⟩ := ht
    have hTT := hT.1.2.2.2.2
    refine ⟨he.conv hTT, hmem, he.conv hTT, DR2_conv hW f hP hdr hTT (fun k' σ ps ps' h1 h2 => ?_) (fun k' σ => ?_)⟩
    · obtain ⟨ps0, ps0', g1, g2, -, -, r12, -, d, d', -⟩ := hT.2.1 k' σ
      obtain rfl : ps = ps0 := by have := RedW.unique h1.1 g1.1; injection this
      obtain rfl : ps' = ps0' := by have := RedW.unique h2.1 g2.1; injection this
      rw [Hom.id_comp]
      exact ⟨(argRel2_iff Θ σ).1 r12, (argRel2_iff Θ σ).1 d, (argRel2_iff Θ σ).1 d'⟩
    · obtain ⟨ps0, ps0', -, g2, -, hl', -⟩ := hT.2.1 k' σ
      exact ⟨ps0', g2, hl'⟩

end

end Model.Whnf
