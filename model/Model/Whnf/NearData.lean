import Model.Whnf.NearInv

/-!
# Near invariance of the relations of inductive types

Related elements of an inductive type stay related when both sides are replaced by near typed terms
(`DR2_near2`, by induction on the relation), and the type relation of an inductive type's code is
invariant under near parameters (`argRelH_nearR`, `argRelH_nearL`, `parRel2_nearR`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' : ℕ}

/-- Invariance under near terms on the right, for a single pack. -/
def NIP (S : Sig) (k : ℕ) (R : Pack2) : Prop :=
  (∀ A A' A'', R.ty A A' → TmNear A' A'' → IsTyK S k A'' → R.ty A A'') ∧ NIel S k R

theorem NIP.of_NI2 {m : ℕ} {X : V} (h : NI2 S m X) (f : Hom k m) : NIP S k (Comp2 S X m k f) :=
  ⟨fun A A' A'' hA hn hT => (h k f A A' A'' A A A).1 hA hn hT,
    fun A t t' t'' hAA ht hn hu => (h k f A A A t t' t'').2 hAA ht hn hu⟩

theorem nip_bot : NIP S k Pack2.bot := ⟨fun _ _ _ h => h.elim, fun _ _ _ _ h => h.elim⟩

section
variable {R : Pack2} (P : PERP R) (N : NIP S k R)
include P N

theorem NIP.tyL {A A' A'' : Tm} (h : R.ty A' A) (hn : TmNear A' A'') (hA : IsTyK S k A'') : R.ty A'' A :=
  P.symTy (N.1 _ _ _ (P.symTy h) hn hA)

theorem NIP.ty2 {A A' B B' : Tm} (h : R.ty A B) (hA : TmNear A A') (hA' : IsTyK S k A') (hB : TmNear B B')
    (hB' : IsTyK S k B') : R.ty A' B' :=
  NIP.tyL P N (N.1 _ _ _ h hB hB') hA hA'

theorem NIP.el2 {A B t t' u u' : Tm} (hAB : R.ty A B) (h : R.el A t u) (ht : TmNear t t')
    (ht' : HasTy S k .one [] t' A) (hu : TmNear u u') (hu' : HasTy S k .one [] u' A) : R.el A t' u' := by
  have hAA := P.reflTy hAB
  have x := N.2 _ _ _ _ hAA h hu hu'
  exact P.symEl hAA (N.2 _ _ _ _ hAA (P.symEl hAA x) ht ht')

end

/-- The point argument relations of an inductive type's code are invariant under near terms. -/
theorem niP_tyLook {m : ℕ} {Θ : SData m} (ni : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → NI2 S n (Θ.ty c j n g pre))
    {n : ℕ} (h : Hom n m) (c j : ℕ) (pre : List V) :
    NIP S n (Comp2 S (tyLook (shapeV (Θ.restr h)) c j pre) n n (Hom.id n)) := by
  rcases tyLook_cases (Θ.restr h) c j pre with h0 | h0
  · rw [h0, Comp2_empty]; exact nip_bot
  · rw [tyLook_eq h0]
    exact NIP.of_NI2 (ni c j n (h.comp (Hom.id n)) pre (ptValid_of_validPre h0)) (Hom.id n)

/-- The parameter relations of an inductive type's code are invariant under near terms. -/
theorem niP_parEntry {m : ℕ} {Θ : SData m} (nip : ∀ n (g : Hom n m) j t X, vnth (Θ.pt n g) j = ZFSet.pair t X → NI2 S n X)
    {k0 : ℕ} (f : Hom k0 m) {k' : ℕ} (σ : ISub k' k0) (j : ℕ) :
    NIP S k' (Comp2 S (π2 (parEntry Θ f k' σ j)) k' k' (Hom.id k')) := by
  by_cases h : ∃ t X, parEntry Θ f k' σ j = ZFSet.pair t X
  · obtain ⟨t, X, e⟩ := h
    rw [e, π2_pair]
    exact NIP.of_NI2 (nip k' _ j t X e) (Hom.id k')
  · have : π2 (parEntry Θ f k' σ j) = ∅ := by
      simp only [π2]; rw [dif_neg]; rintro ⟨a, b, e⟩; exact h ⟨a, b, e⟩
    rw [this, Comp2_empty]; exact nip_bot

/-! ### Lists -/

theorem near_ofList_inv : ∀ {L : List Tm} {x : Tm}, TmNear (Tm.ofList L) x → ∃ L', x = Tm.ofList L' ∧ NearL L L'
  | [], _, h => by cases h; exact ⟨[], rfl, .nil⟩
  | a :: L, _, h => by
    cases h with
    | tcons ha hL =>
      obtain ⟨L', rfl, h'⟩ := near_ofList_inv hL
      exact ⟨_ :: L', rfl, .cons ha h'⟩

theorem forall2_getElem? {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
    ∀ {i : ℕ} {a : α} {b : β}, l[i]? = some a → l'[i]? = some b → R a b
  | _, _, .nil, _, _, _, h, _ => by simp at h
  | _, _, .cons hab h, 0, _, _, e1, e2 => by simp at e1 e2; subst e1; subst e2; exact hab
  | _, _, .cons _ h, i + 1, _, _, e1, e2 => by simp at e1 e2; exact forall2_getElem? h e1 e2

theorem nearL_getElem {L L' : List Tm} (h : NearL L L') {i : ℕ} (h1 : i < L.length) (h2 : i < L'.length) :
    TmNear L[i] L'[i] :=
  forall2_getElem? h (List.getElem?_eq_getElem h1) (List.getElem?_eq_getElem h2)

theorem nearL_take {L L' : List Tm} (h : NearL L L') (j : ℕ) : NearL (L.take j) (L'.take j) := by
  induction h generalizing j with
  | nil => simp
  | cons h1 _ ih => cases j with
    | zero => simp
    | succ j => simp only [List.take_succ_cons]; exact .cons h1 (ih j)

/-! ### Related elements of inductive types -/

theorem data_decl_of (hW : WfSig S) {d : ℕ} {ps : Tm} (h : IsTyK S k (.data d ps)) :
    S[d]? = some (.data (dataD S d)) := by
  obtain ⟨l, hd | hd⟩ := h
  · obtain ⟨D, hD, -⟩ := gen_data (spec_to_minimal hW hd) rfl
    have : dataD S d = D := by unfold dataD; rw [hD]
    rw [this]; exact hD
  · cases hd

section dr
variable (hW : WfSig S) (hN : NearTy S) {m k0 : ℕ} {Θ : SData m} (f : Hom k0 m)
  (hP : ∀ {n : ℕ} (h : Hom n m) (c j : ℕ) (pre : List V), PERP (Comp2 S (tyLook (shapeV (Θ.restr h)) c j pre) n n (Hom.id n)))
  (hQ : ∀ {n : ℕ} (h : Hom n m) (c j : ℕ) (pre : List V), NIP S n (Comp2 S (tyLook (shapeV (Θ.restr h)) c j pre) n n (Hom.id n)))
include hW hN hP hQ

omit hW hN hP hQ in
theorem DR2.eqTm {g : Hom k k0} {A t t' : Tm}
    (h : DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t') : EqTm S k .one [] t t' A := by
  cases h with | intro he _ _ _ => exact he

omit hW hN hP hQ in
theorem DR2At.eqTm {g : Hom k k0} {A t t' : Tm}
    (h : DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t') : EqTm S k .one [] t t' A := by
  cases h with
  | con _ _ he => exact he
  | hcomp _ _ he => exact he

omit hW hN hP hQ in
/-- The normal forms of the left side of related elements of an inductive type are typed. -/
theorem DR2At.whnfL {g : Hom k k0} {A t t' w : Tm}
    (h : DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t') (hw : RedW S t w) :
    HasTy S k .one [] w A := by
  cases h with
  | con _ _ _ _ _ _ ht => rw [RedW.unique hw ht.1]; exact HasTy.eqR ht.2
  | hcomp _ _ _ _ _ _ ht => rw [RedW.unique hw ht.1]; exact HasTy.eqR ht.2

omit hW hN hP hQ in
theorem DR2At.whnfR {g : Hom k k0} {A t t' w : Tm}
    (h : DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t') (hw : RedW S t' w) :
    HasTy S k .one [] w A := by
  cases h with
  | con _ _ _ _ _ _ _ ht' => rw [RedW.unique hw ht'.1]; exact HasTy.eqR ht'.2
  | hcomp _ _ _ _ _ _ _ ht' => rw [RedW.unique hw ht'.1]; exact HasTy.eqR ht'.2

set_option maxHeartbeats 2000000 in
mutual
/-- Related elements of an inductive type, replaced by near typed terms on both sides. -/
theorem DR2_near2 : ∀ {k : ℕ} {g : Hom k k0} {A t t' t2 t2' : Tm},
    DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t' → TmNear t t2 → TmNear t' t2' →
    HasTy S k .one [] t2 A → HasTy S k .one [] t2' A →
    (∀ k' (σ : ISub k' k) ps, RedT S k' (A.isub σ) (.data Θ.idx ps) → argRelH Θ f S k' (g.comp σ.hom) ps ps) →
    DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t2 t2'
  | k, g, A, t, t', t2, t2', .intro he hh hc hc', n1, n2, h1, h2, hyp => by
    have e1 := eq_near hW hN (HasTy.eqL he) n1 (good_of_ty hW h1)
    have e2 := eq_near hW hN (HasTy.eqR he) n2 (good_of_ty hW h2)
    have hh2 : ∀ k' (σ : ISub k' k), DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k'
        (g.comp σ.hom) (A.isub σ) (t2.isub σ) (t2'.isub σ) := fun k' σ =>
      DR2At_near2 (hh k' σ) (n1.isub σ) (n2.isub σ) (HasTy.isubS hW h1 σ) (HasTy.isubS hW h2 σ)
        fun ps hps => hyp k' σ ps hps
    refine .intro ((e1.symm.trans he).trans e2) hh2 (fun k' σ w hw k'' ρ => ?_) (fun k' σ w hw k'' ρ => ?_)
    · obtain ⟨w0, hw0, nw⟩ := redW_near hw (n1.symm.isub σ)
      have tw := HasTy.isubS hW ((hh2 k' σ).whnfL f hw) ρ
      rw [Tm.isub_isub] at tw
      have hyp2 : ∀ ps, RedT S k'' (A.isub (σ.comp ρ)) (.data Θ.idx ps) →
          argRelH Θ f S k'' (g.comp (σ.comp ρ).hom) ps ps := fun ps hps => hyp k'' (σ.comp ρ) ps hps
      exact DR2At_near2 (hc k' σ w0 hw0 k'' ρ) (nw.symm.isub ρ) (n1.isub (σ.comp ρ)) tw
        (HasTy.isubS hW h1 _) hyp2
    · obtain ⟨w0, hw0, nw⟩ := redW_near hw (n2.symm.isub σ)
      have tw := HasTy.isubS hW ((hh2 k' σ).whnfR f hw) ρ
      rw [Tm.isub_isub] at tw
      exact DR2At_near2 (hc' k' σ w0 hw0 k'' ρ) (nw.symm.isub ρ) (n2.isub (σ.comp ρ)) tw
        (HasTy.isubS hW h2 _) fun ps hps => hyp k'' (σ.comp ρ) ps hps

/-- Related elements of an inductive type at a stage, replaced by near typed terms on both sides. -/
theorem DR2At_near2 : ∀ {k : ℕ} {g : Hom k k0} {A t t' t2 t2' : Tm},
    DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t' → TmNear t t2 → TmNear t' t2' →
    HasTy S k .one [] t2 A → HasTy S k .one [] t2' A →
    (∀ ps, RedT S k A (.data Θ.idx ps) → argRelH Θ f S k g ps ps) →
    DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t2 t2'
  | k, g, A, t, t', t2, t2', .con (ps := ps) (c := c) (C := C) (args := args) (args' := args') (rs := rs) (rs' := rs')
      hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt, n1, n2, h1, h2, hyp => by
    have hR := hyp ps hA
    have hAt := isTyK_of_ty hW (HasTy.eqL heq)
    have hpc : ps.closedB 0 k = true := ps_closed hW hA hAt
    have hD := data_decl_of hW (hAt.of_tyEq hA.2)
    have gps : goodB S k ps = true := by
      have := good_of_isTyK hW (hAt.of_tyEq hA.2); simpa [goodB] using this
    have e1 := eq_near hW hN (HasTy.eqL heq) n1 (good_of_ty hW h1)
    have e2 := eq_near hW hN (HasTy.eqR heq) n2 (good_of_ty hW h2)
    obtain ⟨w, hw, nw⟩ := RedE.near hW hN ht (HasTy.eqL heq) n1 (good_of_ty hW h1)
    obtain ⟨w', hw', nw'⟩ := RedE.near hW hN ht' (HasTy.eqR heq) n2 (good_of_ty hW h2)
    cases nw with | @con _ _ _ qs2 _ X _ rs2 _ nargs nrs =>
    cases nw' with | @con _ _ _ qs2' _ X' _ rs2' _ nargs' nrs' =>
    obtain ⟨args2, rfl, nA⟩ := near_ofList_inv nargs
    obtain ⟨args2', rfl, nA'⟩ := near_ofList_inv nargs'
    have gw := red_good hW hw.1.1 (good_of_ty hW h1)
    have gw' := red_good hW hw'.1.1 (good_of_ty hW h2)
    simp only [goodB, Bool.and_eq_true, List.all_eq_true] at gw gw'
    have ga : ∀ x ∈ args2, goodB S k x = true := by
      have := goodB_toList gw.1.1.2; rwa [toList_ofList] at this
    have ga' : ∀ x ∈ args2', goodB S k x = true := by
      have := goodB_toList gw'.1.1.2; rwa [toList_ofList] at this
    have l2 : args2.length = args.length := nA.length_eq.symm
    have l2' : args2'.length = args'.length := nA'.length_eq.symm
    -- the arguments are typed
    have targ : ∀ i (hi : i < args.length) (hi' : i < args'.length), ∃ T, HasTy S k .one [] args[i] T ∧
        HasTy S k .one [] args'[i] T := by
      intro i hi hi'
      cases hr : C.isRec i
      · have := (Comp2_el (hpt i hi hi' hr)).1; exact ⟨_, this.1, this.2.1⟩
      · have := DR2.eqTm f (hrec i hi hi' hr); exact ⟨_, HasTy.eqL this, HasTy.eqR this⟩
    have hsem : ∀ j, j ≤ args.length → (args2.take j).map (semK S k) = (args.take j).map (semK S k) := by
      intro j hj
      apply List.ext_getElem (by simp [l2])
      intro i hi1 hi2
      simp only [List.getElem_map, List.getElem_take]
      simp only [List.length_map, List.length_take] at hi1 hi2
      obtain ⟨T, hT, -⟩ := targ i (by omega) (by omega)
      exact (semK_eq hW (eq_near hW hN hT (nearL_getElem nA (by omega) (by omega)) (ga _ (List.getElem_mem _)))).symm
    refine .con (by unfold dataMem at hm ⊢; rwa [← semK_eq hW e1]) (by unfold dataMem at hm' ⊢; rwa [← semK_eq hW e2])
      ((e1.symm.trans heq).trans e2) hC hA hpl hw hw' (by rw [← hrs]; exact nrs.length_eq.symm)
      (by rw [← hrs']; exact nrs'.length_eq.symm) (fun i r r' er er' => ?_) (fun r hr => sc_iff.1 (gw.1.2 r hr))
      (fun r hr => sc_iff.1 (gw'.1.2 r hr)) (by omega) (by omega) (fun j hj hj' hr => ?_) (fun j hj hj' hr => ?_)
    · have hi : i < rs.length := by
        have := (List.getElem?_eq_some_iff.1 er).1; rw [← nrs.length_eq] at this; exact this
      have hi' : i < rs'.length := by
        have := (List.getElem?_eq_some_iff.1 er').1; rw [← nrs'.length_eq] at this; exact this
      have a := forall2_getElem? nrs (List.getElem?_eq_getElem hi) er
      have b := forall2_getElem? nrs' (List.getElem?_eq_getElem hi') er'
      exact I_eq_trans (I_eq_symm a) (I_eq_trans (hreq i _ _ (List.getElem?_eq_getElem hi)
        (List.getElem?_eq_getElem hi')) b)
    · have ex := DR2.eqTm f (hrec j (by omega) (by omega) hr)
      have nj := nearL_getElem nA (by omega) hj
      have nj' := nearL_getElem nA' (by omega) hj'
      exact DR2_near2 (hrec j (by omega) (by omega) hr) nj nj' (HasTy.near' hW hN (HasTy.eqL ex) nj (ga _ (List.getElem_mem _)))
        (HasTy.near' hW hN (HasTy.eqR ex) nj' (ga' _ (List.getElem_mem _))) (hypData f hR)
    · have x := hpt j (by omega) (by omega) hr
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
      have Q := hQ (f.comp g) c j ((args.take j).map (semK S k))
      have hX := P.reflTy hty
      have nX : TmNear ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList ((args.take j).reverse ++ ps.toList.reverse))
          ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList ((args2.take j).reverse ++ ps.toList.reverse)) :=
        near_substList (nearL_append (nearL_reverse (nearL_take nA j)) (nearL_refl _)) (TmNear.refl _)
      have gX : goodB S k ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList
          ((args2.take j).reverse ++ ps.toList.reverse)) = true := by
        refine good_substList (good_argTy hW hD hC _ _ _) fun y hy => ?_
        rcases List.mem_append.1 hy with h | h
        · exact ga y (List.mem_of_mem_take (List.mem_reverse.1 h))
        · exact goodB_toList gps y (List.mem_reverse.1 h)
      have hX2 := Q.1 _ _ _ hX nX (tyEq_near hW hN (Comp2_ty_base hX).2.1 nX gX).2
      unfold dataP2 at x ⊢
      have x2 := P.conv hX2 x
      have hx := (Comp2_el x2).1
      have nj := nearL_getElem nA (by omega) hj
      have nj' := nearL_getElem nA' (by omega) hj'
      rw [hsem j (by omega)]
      exact NIP.el2 P Q (P.reflTy' hX2) x2 nj (HasTy.near' hW hN hx.1 nj (ga _ (List.getElem_mem _))) nj'
        (HasTy.near' hW hN hx.2.1 nj' (ga' _ (List.getElem_mem _)))
  | k, g, A, t, t', t2, t2', .hcomp (ps := ps) (φ := φ0) hm hm' heq hH hA hpl ht ht' hs hs' h12 h21 ha hu, n1, n2, h1, h2, hyp => by
    have hR := hyp ps hA
    have e1 := eq_near hW hN (HasTy.eqL heq) n1 (good_of_ty hW h1)
    have e2 := eq_near hW hN (HasTy.eqR heq) n2 (good_of_ty hW h2)
    obtain ⟨w, hw, nw⟩ := RedE.near hW hN ht (HasTy.eqL heq) n1 (good_of_ty hW h1)
    obtain ⟨w', hw', nw'⟩ := RedE.near hW hN ht' (HasTy.eqR heq) n2 (good_of_ty hW h2)
    cases nw with | hcomp nX nφ nu na =>
    cases nw' with | hcomp nX' nφ' nu' na' =>
    cases nX with | data _ =>
    cases nX' with | data _ =>
    have gw := red_good hW hw.1.1 (good_of_ty hW h1)
    have gw' := red_good hW hw'.1.1 (good_of_ty hW h2)
    simp only [goodB, Bool.and_eq_true] at gw gw'
    have ea := DR2.eqTm f ha
    refine .hcomp (by unfold dataMem at hm ⊢; rwa [← semK_eq hW e1]) (by unfold dataMem at hm' ⊢; rwa [← semK_eq hW e2])
      ((e1.symm.trans heq).trans e2) hH hA hpl hw hw' (sc_iff.1 gw.1.1.2) (sc_iff.1 gw'.1.1.2)
      (ent_trans nφ.2 (ent_trans h12 nφ'.1)) (ent_trans nφ'.2 (ent_trans h21 nφ.1))
      (DR2_near2 ha na na' (HasTy.near' hW hN (HasTy.eqL ea) na gw.2) (HasTy.near' hW hN (HasTy.eqR ea) na' gw'.2)
        (hypData f hR)) (fun k' σ r hr hh => ?_)
    have hh' : (ival (idEnv k') (φ0.subst σ.τ)).holds := by
      rw [holds_iff_entails (I.scoped_subst hs σ.sc)]
      exact ent_trans ((holds_iff_entails (I.scoped_subst (sc_iff.1 gw.1.1.2) σ.sc)).1 hh) (ent_subst nφ.2 σ.τ)
    have eu := DR2.eqTm f (hu k' σ r hr hh')
    have nu1 := (nu.isub σ.up).dinst (I_eq_refl r)
    have nu1' := (nu'.isub σ.up).dinst (I_eq_refl r)
    refine DR2_near2 (hu k' σ r hr hh') nu1 nu1'
      (HasTy.near' hW hN (HasTy.eqL eu) nu1 (goodB_dinst (good_isub gw.1.2 σ.up) (sc_iff.2 hr)))
      (HasTy.near' hW hN (HasTy.eqR eu) nu1' (goodB_dinst (good_isub gw'.1.2 σ.up) (sc_iff.2 hr))) ?_
    intro k'' σ' ps2 h
    rw [Tm.isub_isub] at h
    obtain rfl := redT_data_eq h
    rw [Hom.comp_assoc, ← ISub.hom_comp]
    exact argRelH_isub Θ f hR (σ.comp σ')
termination_by structural _ _ _ _ _ _ _ h => h
end

/-- Arguments related at the parameters `ps1` are related at near parameters `ps2` with an argument clause,
given their recursive arguments related at `ps2`. -/
theorem prefix_nearConv {k : ℕ} {g : Hom k k0} {ps1 ps2 : Tm} (hR2 : argRelH Θ f S k g ps2 ps2)
    (hpc2 : ps2.closedB 0 k = true) (hn : TmNear ps1 ps2)
    {c : ℕ} {C : Ctor} (hC : (dataD S Θ.idx).ctors[c]? = some C) {args args' : List Tm}
    (hl : args.length ≤ C.args.length) (hl' : args'.length = args.length)
    (hrec2 : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
      DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g (.data Θ.idx ps2) args[j] args'[j])
    (hpt1 : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = false →
      dataP2 S Θ f k g c j ((args.take j).map (semK S k))
        ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList ((args.take j).reverse ++ ps1.toList.reverse))
        args[j] args'[j]) :
    ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = false →
      dataP2 S Θ f k g c j ((args.take j).map (semK S k))
        ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList ((args.take j).reverse ++ ps2.toList.reverse))
        args[j] args'[j] := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj hj' hr
  have hlj : (args.take j).length = j := by simp; omega
  -- the prefix, related at `ps2`
  have hrecp : ∀ i (hi : i < (args.take j).length) (hi' : i < (args'.take j).length), C.isRec i = true →
      DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g (.data Θ.idx ps2) (args.take j)[i] (args'.take j)[i] :=
    fun i hi hi' hri => by
      simp only [List.getElem_take]; exact hrec2 i (by simp at hi; omega) (by simp at hi'; omega) hri
  have hptp : ∀ i (hi : i < (args.take j).length) (hi' : i < (args'.take j).length), C.isRec i = false →
      dataP2 S Θ f k g c i (((args.take j).take i).map (semK S k))
        ((C.argTy Θ.idx (dataD S Θ.idx).params.length i).substList (((args.take j).take i).reverse ++ ps2.toList.reverse))
        (args.take j)[i] (args'.take j)[i] := fun i hi hi' hri => by
    simp only [List.getElem_take, List.take_take]
    rw [Nat.min_eq_left (by simp at hi; omega)]
    exact ih i (by simp at hi; omega) (by simp at hi; omega) (by simp at hi'; omega) hri
  obtain ⟨hrecd, hptd⟩ := prefix_refl hW f hP hR2 hpc2 hC (by simp; omega) (by simp; omega) hrecp hptp
  have hty := argRelH_id f hR2 hpc2 hpc2 (args := args.take j) (args' := args.take j) hC (by rw [hlj]; omega) rfl
    (by rw [hlj]; exact hr) (fun i hi _ hri => hrecd i hi hri) (fun i hi _ hri => hptd i hi hri)
  rw [hlj] at hty
  have P := hP (f.comp g) c j ((args.take j).map (semK S k))
  have Q := hQ (f.comp g) c j ((args.take j).map (semK S k))
  have nX : TmNear ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList ((args.take j).reverse ++ ps2.toList.reverse))
      ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList ((args.take j).reverse ++ ps1.toList.reverse)) :=
    near_substList (nearL_append (nearL_refl _) (nearL_reverse (toList_near hn.symm))) (TmNear.refl _)
  have x := hpt1 j hj hj' hr
  unfold dataP2 at x ⊢
  have hx := (Comp2_el x).1
  have gX : goodB S k ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList
      ((args.take j).reverse ++ ps1.toList.reverse)) = true :=
    good_of_isTyK hW (isTyK_of_ty hW hx.1)
  have hX := NIP.tyL P Q hty nX (tyEq_near hW hN (Comp2_ty_base hty).2.1 nX gX).2
  exact P.conv hX x

set_option maxHeartbeats 2000000 in
mutual
/-- Related elements of an inductive type are related at a near type with an argument clause. -/
theorem DR2_tyNear : ∀ {k : ℕ} {g : Hom k k0} {A t t' A2 : Tm},
    DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t' → TmNear A A2 → IsTyK S k A2 →
    (∀ k' (σ : ISub k' k) ps, RedT S k' (A2.isub σ) (.data Θ.idx ps) → argRelH Θ f S k' (g.comp σ.hom) ps ps) →
    DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A2 t t'
  | k, g, A, t, t', A2, .intro he hh hc hc', hn, hA2, hyp => by
    have e := (tyEq_near hW hN (isTyK_of_ty hW (HasTy.eqL he)) hn (good_of_isTyK hW hA2)).1
    exact .intro (he.tyConv e)
      (fun k' σ => DR2At_tyNear (hh k' σ) (hn.isub σ) (hA2.isub hW σ) fun ps hps => hyp k' σ ps hps)
      (fun k' σ w hw k'' ρ => DR2At_tyNear (hc k' σ w hw k'' ρ) (hn.isub _) (hA2.isub hW _)
        fun ps hps => hyp k'' (σ.comp ρ) ps hps)
      (fun k' σ w hw k'' ρ => DR2At_tyNear (hc' k' σ w hw k'' ρ) (hn.isub _) (hA2.isub hW _)
        fun ps hps => hyp k'' (σ.comp ρ) ps hps)
termination_by structural _ _ _ _ _ _ h => h

theorem DR2At_tyNear : ∀ {k : ℕ} {g : Hom k k0} {A t t' A2 : Tm},
    DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A t t' → TmNear A A2 → IsTyK S k A2 →
    (∀ ps, RedT S k A2 (.data Θ.idx ps) → argRelH Θ f S k g ps ps) →
    DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g A2 t t'
  | k, g, A, t, t', A2, .con (ps := ps) (c := c) (C := C) (args := args) (args' := args')
      hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt, hn, hA2, hyp => by
    have hAt := isTyK_of_ty hW (HasTy.eqL heq)
    have e := (tyEq_near hW hN hAt hn (good_of_isTyK hW hA2)).1
    obtain ⟨W, hW2, nW⟩ := RedT.near hW hN hA hAt hn (good_of_isTyK hW hA2)
    cases nW with | @data _ _ ps2 nps =>
    have hR2 := hyp ps2 hW2
    have hd2 := RedT.isTyK hW hW2 hA2
    have hpc2 : ps2.closedB 0 k = true := ps_closed hW hW2 hA2
    have hpl2 : ps2 = Tm.ofList ps2.toList := by
      rw [hpl] at nps
      obtain ⟨L, rfl, -⟩ := near_ofList_inv nps
      rw [toList_ofList]
    have hrec2 : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
        DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g (.data Θ.idx ps2) args[j] args'[j] :=
      fun j hj hj' hr => DR2_tyNear (hrec j hj hj' hr) (.data nps) hd2 (hypData f hR2)
    exact .con hm hm' (heq.tyConv e) hC hW2 hpl2 ⟨ht.1, ht.2.tyConv e⟩ ⟨ht'.1, ht'.2.tyConv e⟩ hrs hrs' hreq hsc hsc'
      hl hl' hrec2 (prefix_nearConv hW hN f hP hQ hR2 hpc2 nps hC (by omega) (by omega) hrec2 hpt)
  | k, g, A, t, t', A2, .hcomp (ps := ps) hm hm' heq hH hA hpl ht ht' hs hs' h12 h21 ha hu, hn, hA2, hyp => by
    have hAt := isTyK_of_ty hW (HasTy.eqL heq)
    have e := (tyEq_near hW hN hAt hn (good_of_isTyK hW hA2)).1
    obtain ⟨W, hW2, nW⟩ := RedT.near hW hN hA hAt hn (good_of_isTyK hW hA2)
    cases nW with | @data _ _ ps2 nps =>
    have hR2 := hyp ps2 hW2
    have hd2 := RedT.isTyK hW hW2 hA2
    have hpl2 : ps2 = Tm.ofList ps2.toList := by
      rw [hpl] at nps
      obtain ⟨L, rfl, -⟩ := near_ofList_inv nps
      rw [toList_ofList]
    refine .hcomp hm hm' (heq.tyConv e) hH hW2 hpl2 ⟨ht.1, ht.2.tyConv e⟩ ⟨ht'.1, ht'.2.tyConv e⟩ hs hs' h12 h21
      (DR2_tyNear ha (.data nps) hd2 (hypData f hR2)) (fun k' σ r hr hh =>
        DR2_tyNear (hu k' σ r hr hh) ((TmNear.data nps).isub σ) (hd2.isub hW σ) ?_)
    intro k'' σ' ps3 h
    rw [Tm.isub_isub] at h
    obtain rfl := redT_data_eq h
    rw [Hom.comp_assoc, ← ISub.hom_comp]
    exact argRelH_isub Θ f hR2 (σ.comp σ')
termination_by structural _ _ _ _ _ _ h => h
end

omit hN hP hQ in
/-- Related arguments are good. -/
theorem args_good {k : ℕ} {g : Hom k k0} {ps : Tm} {c : ℕ} {C : Ctor} {args args' : List Tm}
    (hl' : args'.length = args.length)
    (hrec : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
      DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g (.data Θ.idx ps) args[j] args'[j])
    (hpt : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = false →
      dataP2 S Θ f k g c j ((args.take j).map (semK S k))
        ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList ((args.take j).reverse ++ ps.toList.reverse))
        args[j] args'[j]) :
    (∀ x ∈ args, goodB S k x = true) ∧ (∀ x ∈ args', goodB S k x = true) := by
  have key : ∀ j (hj : j < args.length) (hj' : j < args'.length), goodB S k args[j] = true ∧ goodB S k args'[j] = true := by
    intro j hj hj'
    cases hr : C.isRec j
    · have := (Comp2_el (hpt j hj hj' hr)).1; exact ⟨good_of_ty hW this.1, good_of_ty hW this.2.1⟩
    · have := DR2.eqTm f (hrec j hj hj' hr); exact ⟨good_of_ty hW (HasTy.eqL this), good_of_ty hW (HasTy.eqR this)⟩
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx; exact (key j hj (by omega)).1
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx; exact (key j (by omega) hj).2

/-- The argument clause, at near parameters on the right. -/
theorem argRelH_nearR {k : ℕ} {g : Hom k k0} {ps ps' ps'' : Tm} (hD : S[Θ.idx]? = some (.data (dataD S Θ.idx)))
    (h : argRelH Θ f S k g ps ps') (hn : TmNear ps' ps'') (gps : goodB S k ps'' = true) : argRelH Θ f S k g ps ps'' := by
  intro k'' σ' c C args args' hC hl hl' hr hrec hpt
  have x := h k'' σ' c C args args' hC hl hl' hr hrec hpt
  have nX : TmNear ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList
        (args'.reverse ++ (ps'.isub σ').toList.reverse))
      ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList
        (args'.reverse ++ (ps''.isub σ').toList.reverse)) :=
    near_substList (nearL_append (nearL_refl _) (nearL_reverse (toList_near (hn.isub σ')))) (TmNear.refl _)
  have gX : goodB S k'' ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList
      (args'.reverse ++ (ps''.isub σ').toList.reverse)) = true := by
    refine good_substList (good_argTy hW hD hC _ _ _) fun y hy => ?_
    rcases List.mem_append.1 hy with h | h
    · exact (args_good hW f hl' hrec hpt).2 y (List.mem_reverse.1 h)
    · exact goodB_toList (good_isub gps σ') y (List.mem_reverse.1 h)
  exact (hQ _ c _ _).1 _ _ _ x nX (tyEq_near hW hN (Comp2_ty_base x).2.2.1 nX gX).2

/-- The argument clause, at near parameters on the left. -/
theorem argRelH_nearL {k : ℕ} {g : Hom k k0} {ps ps' ps'' : Tm} (hD : S[Θ.idx]? = some (.data (dataD S Θ.idx)))
    (h : argRelH Θ f S k g ps ps') (hd : argRelH Θ f S k g ps ps) (hps : IsTyK S k (.data Θ.idx ps))
    (hn : TmNear ps'' ps) (gps : goodB S k ps'' = true) : argRelH Θ f S k g ps'' ps' := by
  intro k'' σ' c C args args' hC hl hl' hr hrec hpt
  have hdσ := argRelH_isub Θ f hd σ'
  have hpsσ : IsTyK S k'' (.data Θ.idx (ps.isub σ')) := hps.isub hW σ'
  have hpc : (ps.isub σ').closedB 0 k'' = true := by
    have := closed_of_isTyK hW hpsσ; simpa [Tm.closedB] using this
  have hrec2 : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
      DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k'' (g.comp σ'.hom) (.data Θ.idx (ps.isub σ'))
        args[j] args'[j] := fun j hj hj' hr' =>
    DR2_tyNear hW hN f hP hQ (hrec j hj hj' hr') (.data (hn.isub σ')) hpsσ (hypData f hdσ)
  have hpt2 := prefix_nearConv hW hN f hP hQ hdσ hpc (hn.isub σ') hC hl.le hl' hrec2 hpt
  have x := h k'' σ' c C args args' hC hl hl' hr hrec2 hpt2
  have nX : TmNear ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList
        (args.reverse ++ (ps.isub σ').toList.reverse))
      ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList
        (args.reverse ++ (ps''.isub σ').toList.reverse)) :=
    near_substList (nearL_append (nearL_refl _) (nearL_reverse (toList_near (hn.symm.isub σ')))) (TmNear.refl _)
  have gX : goodB S k'' ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList
      (args.reverse ++ (ps''.isub σ').toList.reverse)) = true := by
    refine good_substList (good_argTy hW hD hC _ _ _) fun y hy => ?_
    rcases List.mem_append.1 hy with h | h
    · exact (args_good hW f hl' hrec hpt).1 y (List.mem_reverse.1 h)
    · exact goodB_toList (good_isub gps σ') y (List.mem_reverse.1 h)
  have P := hP (f.comp (g.comp σ'.hom)) c args.length (args.map (semK S k''))
  exact NIP.tyL P (hQ _ c _ _) x nX (tyEq_near hW hN (Comp2_ty_base x).2.1 nX gX).2

end dr

theorem good_param (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) {j : ℕ} {A : Tm}
    (hA : D.params[j]? = some A) (m : ℕ) : goodB S m A = true := by
  rcases ((hW.2 d D hD).2.1 j A hA).2.2 with h | ⟨l, -, rfl⟩
  · exact goodB_mono A (good_ty (Model.Canon.htr_of hW d h)) (Nat.zero_le m)
  · rfl

/-- The parameter clause, at near parameters on the right. -/
theorem parRel2_nearR (hW : WfSig S) (hN : NearTy S) {m : ℕ} {Θ : SData m}
    (ihp : ∀ n (g : Hom n m) j t X, vnth (Θ.pt n g) j = ZFSet.pair t X → PER2 S n X)
    (nip : ∀ n (g : Hom n m) j t X, vnth (Θ.pt n g) j = ZFSet.pair t X → NI2 S n X)
    {k0 : ℕ} (f : Hom k0 m) {k' : ℕ} (σ : ISub k' k0) {ps ps' ps'' : Tm} (hD : S[Θ.idx]? = some (.data (dataD S Θ.idx)))
    (h : parRel2 S Θ f k' σ ps ps') (hn : TmNear ps' ps'') (gps : goodB S k' ps'' = true) :
    parRel2 S Θ f k' σ ps ps'' := by
  intro j p p'' e1 e3
  have nL := toList_near hn
  have hj : j < ps'.toList.length := by
    have := (List.getElem?_eq_some_iff.1 e3).1; rw [← nL.length_eq] at this; exact this
  have e2 : ps'.toList[j]? = some ps'.toList[j] := List.getElem?_eq_getElem hj
  have np := forall2_getElem? nL e2 e3
  have gp : goodB S k' p'' = true := goodB_toList gps p'' (List.mem_of_getElem? e3)
  have P := perP_parEntry ihp f σ j
  have Q := niP_parEntry nip f σ j
  obtain ⟨a1, a0⟩ := h j p _ e1 e2
  refine ⟨fun t => ?_, fun t Aj hA => ?_⟩
  · have x := a1 t
    exact Q.1 _ _ _ x np (tyEq_near hW hN (Comp2_ty_base x).2.2.1 np gp).2
  · obtain ⟨x, y⟩ := a0 t Aj hA
    have nX : TmNear (Aj.substList (ps'.toList.take j).reverse) (Aj.substList (ps''.toList.take j).reverse) :=
      near_substList (nearL_reverse (nearL_take nL j)) (TmNear.refl _)
    have gX : goodB S k' (Aj.substList (ps''.toList.take j).reverse) = true :=
      good_substList (good_param hW hD hA k') fun z hz =>
        goodB_toList gps z (List.mem_of_mem_take (List.mem_reverse.1 hz))
    have hy := (Comp2_el y).1
    exact ⟨Q.1 _ _ _ x nX (tyEq_near hW hN (Comp2_ty_base x).2.2.1 nX gX).2,
      Q.2 _ _ _ _ (P.reflTy x) y np (HasTy.near' hW hN hy.2.1 np gp)⟩


/-- The relations of an inductive type's code are invariant under near terms. -/
theorem ni2_dataC (hW : WfSig S) (hN : NearTy S) {m : ℕ} {Θ : SData m}
    (ih : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → PER2 S n (Θ.ty c j n g pre))
    (ihp : ∀ n (g : Hom n m) j t X, vnth (Θ.pt n g) j = ZFSet.pair t X → PER2 S n X)
    (ni : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → NI2 S n (Θ.ty c j n g pre))
    (nip : ∀ n (g : Hom n m) j t X, vnth (Θ.pt n g) j = ZFSet.pair t X → NI2 S n X) :
    NI2 S m (dataC Θ) := by
  intro k f T T' T'' t t' t''
  have hP : ∀ {n : ℕ} (h : Hom n m) (c j : ℕ) (pre : List V),
      PERP (Comp2 S (tyLook (shapeV (Θ.restr h)) c j pre) n n (Hom.id n)) := fun h c j pre => perP_tyLook ih h c j pre
  have hQ : ∀ {n : ℕ} (h : Hom n m) (c j : ℕ) (pre : List V),
      NIP S n (Comp2 S (tyLook (shapeV (Θ.restr h)) c j pre) n n (Hom.id n)) := fun h c j pre => niP_tyLook ni h c j pre
  rw [Comp2_dataC]
  refine ⟨fun h hn hT => ⟨base_near hW hN h.1 hn hT, fun k' σ => ?_⟩, fun hTT h hn hu => ?_⟩
  · obtain ⟨ps, ps', h1, h2, hl, hl', r12, r21, d, d', pr⟩ := h.2 k' σ
    have hT' := h.1.2.1
    obtain ⟨W, h2'', nW⟩ := RedT.near hW hN h2 (hT'.isub hW σ) (hn.isub σ) (good_of_isTyK hW (hT.isub hW σ))
    cases nW with | @data _ _ ps'' nps =>
    have hd' := RedT.isTyK hW h2 (hT'.isub hW σ)
    have hD := data_decl_of hW hd'
    have gps : goodB S k' ps'' = true := by
      have := good_whnf hW h2'' (good_of_isTyK hW (hT.isub hW σ)); simpa [goodB] using this
    have hl'' : ps'' = Tm.ofList ps''.toList := by
      rw [hl'] at nps
      obtain ⟨L, rfl, -⟩ := near_ofList_inv nps
      rw [toList_ofList]
    rw [argRel2_iff] at r12 r21 d d'
    have r1 := argRelH_nearR hW hN f hP hQ hD r12 nps gps
    have r2 := argRelH_nearL hW hN f hP hQ hD r21 d' hd' nps.symm gps
    have d2 := argRelH_nearL hW hN f hP hQ hD (argRelH_nearR hW hN f hP hQ hD d' nps gps) d' hd' nps.symm gps
    exact ⟨ps, ps'', h1, h2'', hl, hl'', (argRel2_iff Θ σ).2 r1, (argRel2_iff Θ σ).2 r2, (argRel2_iff Θ σ).2 d,
      (argRel2_iff Θ σ).2 d2, parRel2_nearR hW hN ihp nip f σ hD pr nps gps⟩
  · obtain ⟨hE, hmem, -, hdr⟩ := h
    have hE' : EB S k T t t'' := ⟨hE.1, hu, hE.2.2.trans (eq_near hW hN hE.2.1 hn (good_of_ty hW hu))⟩
    refine ⟨hE', hmem, hE', DR2_near2 hW hN f hP hQ hdr (TmNear.refl t) hn hE.1 hu fun k' σ ps hps => ?_⟩
    obtain ⟨ps0, -, g1, -, -, -, -, -, hd, -, -⟩ := hTT.2 k' σ
    obtain rfl : ps = ps0 := by have := RedW.unique hps.1 g1.1; injection this
    rw [Hom.id_comp]; exact (argRel2_iff Θ σ).1 hd

end

end Model.Whnf
