import Model.Whnf.Valid2Elim
import Model.Whnf.Kan2DataT
import Model.Whnf.Fund2Aux

/-!
# Transport of constructors

The binary validity of `transpCon` for inductive types without path constructors: the contracta at
related substitutions are related by the transport of related constructors along related literal lines
(`TC.rel`), and where the face holds the contractum is related to the constructor (`tcon_face`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

section
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hW hD

/-- The `transpCon` contractum under a substitution. -/
theorem tCon_subst {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {ps : Tm} (hps : IsList ps)
    (hpl : ps.toList.length = D.params.length) (φ : I) {X : List Tm} (hXl : X.length = C.args.length)
    (σ : ℕ → Tm) (τ : ℕ → I) :
    (Tm.con d c (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] X)) []).subst σ τ =
      tCon d D c C (ps.subst (dupS σ) (I.up τ)) (φ.subst τ) (X.map (·.subst σ τ)) := by
  have h := transpTele_subst (σ := σ) (τ := τ) (fun j => argTy_closed hW hD hC j) hpl φ X 0 [] rfl
  show Tm.con d c ((ps.dinst .one).subst σ τ) ((Tm.ofList _).subst σ τ) [] = _
  rw [ofList_subst, h, dinst_subst, ← toList_subst hps]
  simp only [List.map_nil]
  rw [transpTele_tOuts d D C _ _ (by simp [hXl])]
  rfl

/-- An argument type of a constructor under a substitution. -/
theorem argTy_substList_subst {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {P0 : Tm} (hP0 : IsList P0)
    (hlen : P0.toList.length = D.params.length) {L : List Tm} {i : ℕ} (hi : i ≤ L.length)
    (σ : ℕ → Tm) (τ : ℕ → I) :
    ((C.argTy d D.params.length i).substList ((L.take i).reverse ++ P0.toList.reverse)).subst σ τ =
      (C.argTy d D.params.length i).substList (((L.map (·.subst σ τ)).take i).reverse ++
        (P0.subst σ τ).toList.reverse) := by
  have hcl : (C.argTy d D.params.length i).closedB ((L.take i).reverse ++ P0.toList.reverse).length 0 = true := by
    simp only [List.length_append, List.length_reverse, List.length_take, hlen, Nat.min_eq_left hi]
    rw [Nat.add_comm]; exact argTy_closed hW hD hC i
  rw [substList_subst hcl, List.map_append, List.map_reverse, List.map_reverse, List.map_take,
    ← toList_subst hP0]

variable (hH : D.isHIT = false) (hp : D.params ≠ [])
include hH hp

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-- **Transport of a constructor** of an inductive type without path constructors. -/
theorem valid_transpCon {ci : ℕ} {C : Ctor} {ps qs args T : Tm} {φ : I} {rs : List I}
    (hC : D.ctors[ci]? = some C) (hpl : ps = Tm.ofList ps.toList)
    (hty : HasTy0 S Ψ Φ Γ (.transp (.data d ps) φ (.con d ci qs args rs)) T)
    (hu : HasTy0 S Ψ Φ Γ (.con d ci (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs) T)
    (heq : EqTm0 S Ψ Φ Γ (.transp (.data d ps) φ (.con d ci qs args rs)) (.con d ci (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs) T)
    (hva : VTele2 S Ψ Φ Γ args args (C.argTys d D.params.length) (ps.dinst .zero).toList.reverse)
    (hv : Valid2 S Ψ Φ Γ (.transp (.data d ps) φ (.con d ci qs args rs))
      (.transp (.data d ps) φ (.con d ci qs args rs)) T)
    (hinv : TranspInv S Ψ Φ Γ (.data d ps) φ (.con d ci qs args rs) T) :
    Valid2 S Ψ Φ Γ (.transp (.data d ps) φ (.con d ci qs args rs)) (.con d ci (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs) T := by
  obtain ⟨l, hφ, hLV, hCV, haV, htr, hL, hc, ha⟩ := hinv
  -- no interval arguments
  obtain ⟨D1, C1, hD1, hC1, -, -, -, hrs⟩ := gen_con ha rfl
  rw [hD] at hD1; cases hD1
  rw [hC] at hC1; cases hC1
  rw [dims_of_not_hit hH hC, List.length_eq_zero_iff] at hrs
  subst hrs
  obtain ⟨hal, -, hXl, -⟩ := VTele2.shape hva
  simp only [Ctor.argTys, List.length_map, List.length_range] at hXl
  -- the line at the parameters, typed at the level of the inductive type
  obtain ⟨D2, hD2, hpt⟩ := gen_data_tele hL rfl
  rw [hD] at hD2; cases hD2
  have hLD : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (.data d ps) (.univ D.level) :=
    HasTy0.data hD (hW.2 d D hD).1 hpt
  have hpsl : ps.toList.length = D.params.length := by simpa using Meta.tele_length hpt
  have hty1 : HasTy0 S Ψ Φ Γ (.transp (.data d ps) φ (.con d ci qs args [])) ((Tm.data d ps).dinst .one) :=
    HasTy0.transp hL hφ hc ha
  have hT : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L T) (c.R T) := fun k c => (hv k c).1
  have tyB : ∀ {k4 : ℕ} {X Z : Tm}, RT2 S k4 X Z → TyEq S k4 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  -- the substituted arguments
  have hXL : ∀ {k : ℕ} (c : CSub2 S Ψ Φ Γ k), c.L args = Tm.ofList (args.toList.map c.L) := by
    intro k c
    show args.subst c.γ c.σ.τ = _
    conv_lhs => rw [hal]
    exact ofList_subst _ _ _
  have hXR : ∀ {k : ℕ} (c : CSub2 S Ψ Φ Γ k), c.R args = Tm.ofList (args.toList.map c.R) := by
    intro k c
    show args.subst c.γ' c.σ'.τ = _
    conv_lhs => rw [hal]
    exact ofList_subst _ _ _
  -- the contracta
  have eL : ∀ {k : ℕ} (c : CSub2 S Ψ Φ Γ k), c.L (.con d ci (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) []) =
      tCon d D ci C ((c.up hW).L ps) (φ.subst c.σ.τ) (args.toList.map c.L) :=
    fun c => tCon_subst hW hD hC hpl hpsl φ hXl _ _
  have eR : ∀ {k : ℕ} (c : CSub2 S Ψ Φ Γ k), c.R (.con d ci (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) []) =
      tCon d D ci C ((c.up hW).R ps) (φ.subst c.σ'.τ) (args.toList.map c.R) :=
    fun c => tCon_subst hW hD hC hpl hpsl φ hXl _ _
  -- the literal lines at a related substitution
  have hPL : ∀ {k : ℕ} (c : CSub2 S Ψ Φ Γ k), HasTy S (k + 1) .one [] (.data d ((c.up hW).L ps)) (.univ D.level) :=
    fun c => (c.up hW).ty hW hLD
  have hQL : ∀ {k : ℕ} (c : CSub2 S Ψ Φ Γ k), HasTy S (k + 1) .one [] (.data d ((c.up hW).R ps)) (.univ D.level) :=
    fun c => (c.up hW).tyR hW hLD
  have hd1 : ∀ {k : ℕ} (c : CSub2 S Ψ Φ Γ k),
      HasTy S k .one [] (.data d (((c.up hW).L ps).dinst .one)) (.univ D.level) := by
    intro k c
    have := HasTy.isubS hW (hPL c) (ISub.cons .one trivial (ISub.id k))
    rwa [show (Tm.data d ((c.up hW).L ps)).isub (ISub.cons .one trivial (ISub.id k)) =
      .data d (((c.up hW).L ps).isub (ISub.cons .one trivial (ISub.id k))) from rfl,
      isub_cons_id_of_closed (data_closed hW hD (hPL c))] at this
  have s1 : ∀ {k : ℕ} (c : CSub2 S Ψ Φ Γ k), RT2 S k (.data d (((c.up hW).L ps).dinst .one))
      (.data d (((c.up hW).L ps).dinst .one)) := by
    intro k c
    have := lineRob_of_valid hW hLV (c.diagL hW) k (ISub.id k) .one .one trivial trivial (I_eq_refl _)
    change RT2 S k (Tm.data d (((c.up hW).L ps).isub _)) (Tm.data d (((c.up hW).L ps).isub _)) at this
    rwa [isub_cons_id_of_closed (data_closed hW hD (hPL c))] at this
  have hRQ1 : ∀ {k : ℕ} (c : CSub2 S Ψ Φ Γ k), RT2 S k (.data d (((c.up hW).L ps).dinst .one))
      (.data d (((c.up hW).R ps).dinst .one)) := by
    intro k c
    have := lineRob_of_valid hW hLV c k (ISub.id k) .one .one trivial trivial (I_eq_refl _)
    change RT2 S k (Tm.data d (((c.up hW).L ps).isub _)) (Tm.data d (((c.up hW).R ps).isub _)) at this
    rwa [isub_cons_id_of_closed (data_closed hW hD (hPL c)),
      isub_cons_id_of_closed (data_closed hW hD (hQL c))] at this
  have eT1 : ∀ {k : ℕ} (c : CSub2 S Ψ Φ Γ k), c.L ((Tm.data d ps).dinst .one) = .data d (((c.up hW).L ps).dinst .one) :=
    fun c => CSub2.L_dinst hW c _ _
  have eT0 : ∀ {k : ℕ} (c : CSub2 S Ψ Φ Γ k), c.L ((Tm.data d ps).dinst .zero) = .data d (((c.up hW).L ps).dinst .zero) :=
    fun c => CSub2.L_dinst hW c _ _
  -- the transport data at a related substitution
  have hTC : ∀ {k : ℕ} (c : CSub2 S Ψ Φ Γ k), TC S k d D ((c.up hW).L ps) ((c.up hW).R ps) (φ.subst c.σ.τ)
      (φ.subst c.σ'.τ) ci C (c.L qs) (c.R qs) (args.toList.map c.L) (args.toList.map c.R) [] [] := by
    intro k c
    have h1 := c.ty hW hty1
    have h1' := c.tyR' hW hty1
    have h1e := c.eq hW (EqTm0.refl hty1)
    rw [eT1] at h1 h1' h1e
    change HasTy S k .one [] (.transp (.data d ((c.up hW).L ps)) (φ.subst c.σ.τ)
      (.con d ci (c.L qs) (c.L args) [])) _ at h1
    change HasTy S k .one [] (.transp (.data d ((c.up hW).R ps)) (φ.subst c.σ'.τ)
      (.con d ci (c.R qs) (c.R args) [])) _ at h1'
    change EqTm S k .one [] (.transp (.data d ((c.up hW).L ps)) (φ.subst c.σ.τ)
      (.con d ci (c.L qs) (c.L args) [])) (.transp (.data d ((c.up hW).R ps)) (φ.subst c.σ'.τ)
      (.con d ci (c.R qs) (c.R args) [])) _ at h1e
    rw [hXL c] at h1 h1e
    rw [hXR c] at h1' h1e
    exact {
      hW := hW, hD := hD, hp := hp, hC := hC, hPL := hPL c,
      hR := fun k3 τ y y' hy hy' hE => lineRob_of_valid hW hLV c k3 τ y y' hy hy' hE,
      hRL := fun k3 τ y y' hy hy' hE => lineRob_of_valid hW hLV (c.diagL hW) k3 τ y y' hy hy' hE,
      hφs := I.scoped_subst hφ c.σ.sc,
      h12 := c.ent_LR (ent_refl φ), h21 := c.ent_RL (ent_refl φ),
      hLC := lineConst_of_valid hW hφ hCV c, hty := h1, hty' := h1', heq := h1e,
      hargs0 := fun i hi => by
        have hi0 : i < args.toList.length := by omega
        have h := (VTele2.get hva i hi0 hi0 (by simp [Ctor.argTys]; exact hi) k c).2
        simp only [Ctor.argTys, List.getElem_map, List.getElem_range] at h
        have hP0 : IsList (ps.dinst .zero) := isList_subst hpl _ _
        have hP0l : (ps.dinst .zero).toList.length = D.params.length := by
          show (ps.subst _ _).toList.length = _; rw [toList_subst hpl]; simp [hpsl]
        have e3 := argTy_substList_subst hW hD hC hP0 hP0l (L := args.toList) (i := i) hi0.le c.γ c.σ.τ
        change RE2 S k (((C.argTy d D.params.length i).substList
          ((args.toList.take i).reverse ++ (ps.dinst .zero).toList.reverse)).subst c.γ c.σ.τ) _ _ at h
        rw [e3, show (ps.dinst .zero).subst c.γ c.σ.τ = ((c.up hW).L ps).dinst .zero from
          CSub2.L_dinst hW c ps .zero] at h
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map,
          List.getElem?_eq_getElem hi0]
        exact h,
      hrecT := fun i hi hri k3 τ y y' hy hy' hE _ => by
        have hk := hLV.kanV hW (k3 + 1) ((c.restr hW τ.up.tail).cons y y' hy hy' hE)
        rw [CSub2.cons_restr_L, isub_up_dinst _ _ _ hy] at hk
        exact KanT2.at (hk.2 k3 (Hom.id (k3 + 1)) _ _
          (lineRob_of_valid hW hLV c (k3 + 1) τ.up.tail y y' hy hy' hE)) _ _,
      conR := fun Y Y' hYl hY'l hcT he hargs =>
        RE2_con_args_id hW hD hH (hd1 c) (s1 c) hC Y Y' hYl hY'l hcT he hargs }
  -- the contracta are valid
  have hyA : Valid2 S Ψ Φ Γ (.con d ci (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) [])
      (.con d ci (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) [])
      ((Tm.data d ps).dinst .one) := by
    intro k c
    have hT1 := hLV.tySelf hW (c.cons .one .one trivial trivial (I_eq_refl _))
    rw [CSub2.L_cons hW, CSub2.R_cons hW] at hT1
    refine ⟨by rw [CSub2.L_dinst hW, CSub2.R_dinst hW]; exact hT1, ?_⟩
    rw [eT1, eL, eR]
    exact (hTC c).rel
  have hyT := valid_conv_tr hyA htr hT
  -- where the face holds: the constructor
  have hb : Valid2 S Ψ (cof Φ φ) Γ (.con d ci qs args []) (.con d ci (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) []) T := by
    intro k c
    have hXs : (cof Φ φ).Scoped Ψ := ⟨scoped_of_ty ha, hφ⟩
    let c0 := c.restrictTo (ent_and_left Φ φ)
    have hf : I.Entails .one (φ.subst c0.σ.τ) := ent_trans c.face (ent_subst (ent_and_right _ _) c.σ.τ)
    have hf' : I.Entails .one (φ.subst c0.σ'.τ) := ent_trans hf (c0.ent_LR (ent_refl φ))
    refine ⟨hT k c0, htr k c0 _ _ ?_⟩
    rw [eT1 c0]
    -- the constructor at the left, against the constructor at the right
    have r0 := (haV k c0).2
    rw [eT0 c0] at r0
    have lc := lineConst_of_valid hW hφ hCV c0 k (ISub.id k) .one trivial
      (by rw [I_subst_id (I.scoped_subst hφ c0.σ.sc)]; exact (holds_iff_entails (I.scoped_subst hφ c0.σ.sc)).2 hf)
    change RT2 S k (Tm.data d (((c0.up hW).L ps).isub _)) (Tm.data d (((c0.up hW).L ps).isub _)) at lc
    rw [isub_cons_id_of_closed (data_closed hW hD (hPL c0)),
      isub_cons_id_of_closed (data_closed hW hD (hPL c0))] at lc
    have hX1 := tyCode_of_univ hW (hd1 c0)
    have r1 := RE2.conv hW (RT2.symm hW hX1 lc) r0
    -- the contractum at the right, against the constructor at the right
    let cR := c0.diagR hW
    have hty1R := cR.ty hW hty1
    rw [CSub2.L_dinst hW] at hty1R
    change HasTy S k .one [] (.transp (.data d ((c0.up hW).R ps)) (φ.subst c0.σ'.τ)
      (.con d ci (c0.R qs) (c0.R args) [])) (Tm.data d (((c0.up hW).R ps).dinst .one)) at hty1R
    rw [hXR c0] at hty1R
    have rb := (haV k cR).2
    rw [CSub2.L_dinst hW] at rb
    change RE2 S k (Tm.data d (((c0.up hW).R ps).dinst .zero)) (c0.R (.con d ci qs args [])) (c0.R (.con d ci qs args [])) at rb
    change RE2 S k _ (.con d ci (c0.R qs) (c0.R args) []) (.con d ci (c0.R qs) (c0.R args) []) at rb
    rw [hXR c0] at rb
    have tf := tcon_face hW hD hp hH hC (hQL c0)
      (fun k3 τ y y' hy hy' hE => lineRob_of_valid hW hLV cR k3 τ y y' hy hy' hE)
      (lineConst_of_valid hW hφ hCV cR) (I.scoped_subst hφ c0.σ'.sc) hf' hty1R rb
    have hRR := hRQ1 c0
    have r2 := RE2.conv hW (RT2.symm hW hX1 hRR) (RE2.symm hW (RT2.refl' hW hX1 hRR) tf)
    show RE2 S k _ (c0.L (.con d ci qs args [])) (c0.R (.con d ci (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) []))
    rw [eR c0]
    change RE2 S k _ (.con d ci (c0.L qs) (c0.L args) []) _
    change RE2 S k _ (.con d ci (c0.L qs) (c0.L args) []) (.con d ci (c0.R qs) (c0.R args) []) at r1
    rw [hXR c0] at r1
    exact RE2.trans hW (s1 c0) r1 r2
  refine valid_comp_rule hW hv hyT hb fun k c => ⟨fun hn => ?_, fun hf => ?_⟩
  · have hs := step_transp_con hD hp hH hC hn (X := args.toList.map c.L) (ps := (c.up hW).L ps)
      (qs := c.L qs) (by simp [hXl])
    refine ⟨.step ?_ (.refl _), ((c.diagL hW).eq hW heq)⟩
    rw [eL c]
    show step S (.transp (.data d ((c.up hW).L ps)) (φ.subst c.σ.τ) (.con d ci (c.L qs) (c.L args) [])) = _
    rw [hXL c]; exact hs
  · exact ⟨.step (step_transp_face hf) (.refl _), EqTm.transpFace hf (c.ty hW hty)⟩

end

end

end Model.Whnf
