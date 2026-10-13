import Model.Canon.KanData
import Model.Canon.ProjHcomp
import Model.Canon.KanFill

/-!
# Canonicity: composition in inductive types without path constructors (`hcompCon`)

A computable base is a constructor (its relation has no `hcomp` nodes), and so is the tube on its
face (`TubeCanon`), whose arguments are given uniformly by the projections (`hcompCon_premises`).
The composite is then the constructor of the componentwise composites (`hcompCon`): compositions
in the inductive type for recursive arguments (by induction on the relation of the base) and
heterogeneous compositions along the argument type lines for point arguments. The lines are
computable at valid earlier fillers, which needs the composition filler of the recursive
arguments, again by induction.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

/-- The computability clause of an inductive type's line for its argument types. -/
def ArgClause (S : Sig) {m : ℕ} (Θ : SData m) {n : ℕ} (f : Hom n m) (ps : Tm) : Prop :=
  ∀ k' (σ : ISub k' n) (c : ℕ) (C : Ctor) (args : List Tm), (dataD S Θ.idx).ctors[c]? = some C →
    args.length < C.args.length → C.isRec args.length = false →
    (∀ j (hj : j < args.length), C.isRec j = true →
      DR S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP S Θ f) k' σ.hom ((Tm.data Θ.idx ps).isub σ) args[j]) →
    (∀ j (hj : j < args.length), C.isRec j = false →
      dataP S Θ f k' σ.hom c j ((args.take j).map (semK S k'))
        ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList ((args.take j).reverse ++ (ps.isub σ).toList.reverse))
        args[j]) →
    (Comp S (tyLook (shapeV (Θ.restr (f.comp σ.hom))) c args.length (args.map (semK S k'))) k' k' (Hom.id k')).ty
      ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList (args.reverse ++ (ps.isub σ).toList.reverse))

variable (hW : WfSig S)
include hW

/-- A constructor in the relation of an inductive type without path constructors, restricted and
retyped at a restriction of the type: its arguments are typed and computable there. -/
theorem con_restrict {Θ : SData m} (hΘ : Θ.Good)
    (ihT : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → KR S n (Θ.ty c j n g pre))
    {D : DataDecl} (hD : S[Θ.idx]? = some (.data D)) (hH : D.isHIT = false)
    {k0 : ℕ} {f : Hom k0 m} {P : Tm} (hall : ArgClause S Θ f P)
    {k' : ℕ} {g : Hom k' k0} {A t qs : Tm} {c : ℕ} {C : Ctor} {args : List Tm} {rs : List I}
    (hC : D.ctors[c]? = some C) (hrs : rs.length = C.dims) (hqs : qs = Tm.ofList qs.toList)
    (hAeq : TyEq S k' A (.data Θ.idx qs))
    (he : EqTm S k' .one [] t (.con Θ.idx c qs (Tm.ofList args) rs) A) (hlen : args.length = C.args.length)
    (hrec : ∀ j (hj : j < args.length), C.isRec j = true →
      DR S Θ.idx D (dataMem S Θ f) (dataP S Θ f) k' g (.data Θ.idx qs) args[j])
    (hpt : ∀ j (hj : j < args.length), C.isRec j = false →
      dataP S Θ f k' g c j ((args.take j).map (semK S k'))
        ((C.argTy Θ.idx D.params.length j).substList ((args.take j).reverse ++ qs.toList.reverse)) args[j])
    {k'' : ℕ} (σ' : ISub k'' k') (ρ : ISub k'' k0) (hg : g.comp σ'.hom = ρ.hom) {l : ℕ}
    (hpT : HasTy S k'' .one [] (.data Θ.idx (P.isub ρ)) (.univ l))
    (hA : TyEq S k'' (A.isub σ') (.data Θ.idx (P.isub ρ))) :
    HasTele0 S k'' .one [] (Tm.ofList (args.map (·.isub σ'))) (C.argTys Θ.idx D.params.length)
      (P.isub ρ).toList.reverse ∧
    EqTm S k'' .one [] (t.isub σ') (.con Θ.idx c (P.isub ρ) (Tm.ofList (args.map (·.isub σ'))) [])
      (.data Θ.idx (P.isub ρ)) ∧
    (∀ j (hj : j < args.length), C.isRec j = true →
      DR S Θ.idx D (dataMem S Θ f) (dataP S Θ f) k'' ρ.hom ((Tm.data Θ.idx P).isub ρ) ((args[j]).isub σ')) ∧
    (∀ j (hj : j < args.length), C.isRec j = false →
      RE S k'' ((C.argTy Θ.idx D.params.length j).substList
        (((args.map (·.isub σ')).take j).reverse ++ (P.isub ρ).toList.reverse)) ((args[j]).isub σ')) := by
  have hS := sigClosed_of_wfSig hW
  have hdD := dataD_eq hW hD
  have hrs0 : rs = [] := List.eq_nil_of_length_eq_zero (by rw [hrs, (nonHIT_ctor hH hC).1])
  subst hrs0
  set d := Θ.idx with hd
  set p := P.isub ρ with hp
  -- the restricted constructor
  have he' : EqTm S k'' .one [] (t.isub σ')
      (.con d c (qs.isub σ') (Tm.ofList (args.map (·.isub σ'))) []) (A.isub σ') := by
    have := EqTm.isubS hW he σ'
    rwa [show (Tm.con d c qs (Tm.ofList args) []).isub σ' =
      .con d c (qs.isub σ') ((Tm.ofList args).isub σ') [] from rfl, ofList_isub] at this
  have hqL : TyEq S k'' (.data d (qs.isub σ')) (.data d p) := (hAeq.isub hW σ').symm.trans hW hA
  have hcon := spec_to_minimal hW (HasTy.eqR he')
  obtain ⟨hI, -⟩ := gen_conF hcon rfl
  obtain ⟨-, D0, C0, hD0, hC0, hqs', hdq, hqt, haq, -, -⟩ := hI
  rw [hD] at hD0; cases hD0; rw [hC] at hC0; cases hC0
  obtain ⟨lq, eq⟩ := tyEq_eq hW hqL ⟨_, hpT⟩
  obtain ⟨D', hD', hPt⟩ := gen_data_tele (spec_to_minimal hW hpT) rfl
  rw [hD] at hD'; cases hD'
  have hPl : p = Tm.ofList p.toList := tele_isList hPt
  have hret := args_retype hW hD hC hqs' hPl hqt hPt (spec_to_minimal_eq hW eq) haq
  rw [toList_ofList] at hret
  obtain ⟨htele, hteq⟩ := hret
  have hMem : ∀ k1 (f1 : Hom k1 k0) t t' A, EqTm S k1 .one [] t t' A → dataMem S Θ f k1 f1 t →
      dataMem S Θ f k1 f1 t' := fun k1 f1 t t' A e hm => by unfold dataMem at hm ⊢; rwa [← semK_eq hW e]
  refine ⟨htele, ?_, ?_, ?_⟩
  · -- the constructor at the restricted parameters
    have hpd : HasTy0 S k'' .one [] (.data d p) (.univ D.level) := HasTy0.data hD (hW.2 d D hD).1 hPt
    have hcp := HasTy0.con (rs := []) hD hC hPl hpd hPt htele (by simp [(nonHIT_ctor hH hC).1]) (by simp)
    have hcq := HasTy0.conv hcp (EqTm0.symm (spec_to_minimal_eq hW eq))
    have eps := EqTele0.dataInj hD hqt hPt (spec_to_minimal_eq hW eq)
    have hc0 := HasTy0.con (rs := []) hD hC hqs' hdq hqt haq (by simp [(nonHIT_ctor hH hC).1]) (by simp)
    have ec := EqTm0.con hD hC hc0 hcq eps (EqTele0.refl haq) rfl (fun _ _ _ h => by simp at h)
    exact (he'.tyConv hA).trans (EqTm.tyConv (minimal_to_spec_eq ec) (.inr ⟨lq, eq⟩))
  · intro i hi hri
    have := DR.isub hW hΘ f ihT (hdD ▸ hrec i hi hri) k'' σ'
    rw [hdD, hg] at this
    exact DR.conv hW hMem this hqL (EqTm.refl ((this.typed).tyConv hqL))
  · intro i hi hri
    unfold ArgClause at hall
    rw [hdD] at hall
    set as := args.map (·.isub σ') with has
    have hasi : ∀ j (hj : j < args.length), as[j]'(by simp [as]; omega) = (args[j]).isub σ' := by
      intro j hj; simp [as]
    have hargT : ∀ j (hj : j < args.length), ∃ T, HasTy S k' .one [] args[j] T := by
      intro j hj
      cases hrj : C.isRec j
      · have := hpt j hj hrj; unfold dataP at this; exact ⟨_, (Comp_el_typed this).1⟩
      · exact ⟨_, (hrec j hj hrj).typed⟩
    have hpre : ∀ j, j ≤ args.length → ((args.take j).map (semK S k')).map (res σ'.hom) =
        (as.take j).map (semK S k'') := by
      intro j hj
      apply List.ext_getElem (by simp [as])
      intro x h1 h2
      simp only [List.getElem_map, List.getElem_take, as]
      obtain ⟨T, hT⟩ := hargT x (by simp at h1; omega)
      exact (semK_isubS hW hT σ').symm
    have hXq : ∀ j, j ≤ args.length → ((C.argTy d D.params.length j).substList
        ((args.take j).reverse ++ qs.toList.reverse)).isub σ' =
        (C.argTy d D.params.length j).substList ((as.take j).reverse ++ (qs.isub σ').toList.reverse) := by
      intro j hj
      rw [substList_isub (argTy_closed hS hD hC j), List.map_append, List.map_reverse, List.map_reverse,
        ← List.map_take, toList_isub hqs σ']
    let Valid : ℕ → Prop := fun j =>
      (∀ i (hi : i < j) (hi' : i < as.length), C.isRec i = true →
        DR S d D (dataMem S Θ f) (dataP S Θ f) k'' ρ.hom ((Tm.data d P).isub ρ) as[i]) ∧
      (∀ i (hi : i < j) (hi' : i < as.length), C.isRec i = false →
        dataP S Θ f k'' ρ.hom c i ((as.take i).map (semK S k''))
          ((C.argTy d D.params.length i).substList ((as.take i).reverse ++ p.toList.reverse)) as[i])
    have clause : ∀ j (hj : j < as.length), C.isRec j = false → Valid j →
        (Comp S (tyLook (shapeV (Θ.restr (f.comp ρ.hom))) c j ((as.take j).map (semK S k''))) k'' k''
          (Hom.id k'')).ty ((C.argTy d D.params.length j).substList ((as.take j).reverse ++ p.toList.reverse)) := by
      intro j hj hr hv
      have hlj : (as.take j).length = j := by simp; omega
      have := hall k'' ρ c C (as.take j) hC (by simp [as] at hj ⊢; omega) (by rw [hlj]; exact hr)
        (fun i hi hri => by
          rw [hlj] at hi; rw [List.getElem_take]; exact hv.1 i hi (by omega) hri)
        (fun i hi hri => by
          rw [hlj] at hi; rw [List.getElem_take, List.take_take, Nat.min_eq_left hi.le]
          exact hv.2 i hi (by omega) hri)
      rwa [hlj] at this
    have hrecR : ∀ i (hi : i < args.length), C.isRec i = true →
        DR S d D (dataMem S Θ f) (dataP S Θ f) k'' ρ.hom ((Tm.data d P).isub ρ) (as[i]'(by simp [as]; omega)) := by
      intro i hi hri
      have := DR.isub hW hΘ f ihT (hdD ▸ hrec i hi hri) k'' σ'
      rw [hdD, hg, ← hasi i hi] at this
      exact DR.conv hW hMem this hqL (EqTm.refl ((this.typed).tyConv hqL))
    have hptR : ∀ i (hi : i < args.length), C.isRec i = false →
        dataP S Θ f k'' ρ.hom c i ((as.take i).map (semK S k''))
          ((C.argTy d D.params.length i).substList ((as.take i).reverse ++ (qs.isub σ').toList.reverse))
          (as[i]'(by simp [as]; omega)) := by
      intro i hi hri
      have := dataP_isub hΘ f ihT (hpt i hi hri) σ'
      rw [hg, hpre i hi.le, hXq i hi.le, ← hasi i hi] at this
      exact this
    have conv : ∀ j (hj : j < args.length), C.isRec j = false → Valid j →
        RE S k'' ((C.argTy d D.params.length j).substList ((as.take j).reverse ++ p.toList.reverse))
          (as[j]'(by simp [as]; omega)) := by
      intro j hj hr hv
      have tyXp := clause j (by simp [as]; omega) hr hv
      obtain ⟨l', e⟩ := hteq j (by simp [as]; omega)
      have eT : TyEq S k'' ((C.argTy d D.params.length j).substList ((as.take j).reverse ++ (qs.isub σ').toList.reverse))
          ((C.argTy d D.params.length j).substList ((as.take j).reverse ++ p.toList.reverse)) :=
        .inr ⟨l', minimal_to_spec_eq e⟩
      have hel := hptR j hj hr
      unfold dataP at hel
      have hre : RE S k'' ((C.argTy d D.params.length j).substList ((as.take j).reverse ++ (qs.isub σ').toList.reverse))
          (as[j]'(by simp [as]; omega)) := by
        unfold RE; rw [semK_tyEq hW eT, ← Comp_eq_semK tyXp]; exact hel
      exact hre.conv_ty hW eT
    have key : ∀ j, j ≤ args.length → Valid j := by
      intro j
      induction j with
      | zero => intro _; exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      | succ j ih =>
        intro hj
        have hv := ih (by omega)
        refine ⟨fun i hi hi' hri => ?_, fun i hi hi' hri => ?_⟩
        · by_cases hij : i < j
          · exact hv.1 i hij hi' hri
          obtain rfl : i = j := by omega
          exact hrecR i (by omega) hri
        · by_cases hij : i < j
          · exact hv.2 i hij hi' hri
          obtain rfl : i = j := by omega
          have tyXp := clause i hi' hri hv
          show (Comp S _ k'' k'' (Hom.id k'')).el _ _
          rw [Comp_eq_semK tyXp]
          exact conv i (by omega) hri hv
    rw [← hasi i hi]
    exact conv i hi hri ⟨fun i' hi'' hi' hr' => (key args.length (Nat.le_refl _)).1 i' (by omega) hi' hr',
      fun i' hi'' hi' hr' => (key args.length (Nat.le_refl _)).2 i' (by omega) hi' hr'⟩

end

end Model.Canon
