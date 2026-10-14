import Model.Whnf.Valid2TranspHcomp
import Model.Whnf.Kan2DataHITConRel

/-!
# Constructors of higher inductive types

The binary validity of the constructors of higher inductive types (`con`, `conEq`) from the relation
of constructors with related arguments (`con_rel`), and of their boundaries (`conBnd`) from the
closed instance `HITHyp2.conBnd`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

/-- Related telescopes restrict to smaller faces. -/
theorem VTele2.restrict (hW : WfSig S) {Ψ : ℕ} {Φ Φ' : I} {Γ : Ctx} (he : I.Entails Φ' Φ) :
    ∀ {ts ts' : Tm} {Δ prev : List Tm}, VTele2 S Ψ Φ Γ ts ts' Δ prev → VTele2 S Ψ Φ' Γ ts ts' Δ prev
  | .tnil, .tnil, [], _, _ => trivial
  | .tcons _ _, .tcons _ _, _ :: _, _, ⟨h1, h2⟩ => ⟨valid_restrict hW he h1, VTele2.restrict hW he h2⟩
  | .tnil, .tnil, _ :: _, _, h => h.elim
  | .tnil, .tcons _ _, _, _, h => by cases h
  | .tcons _ _, .tnil, _, _, h => by cases h
  | .tcons _ _, .tcons _ _, [], _, h => h.elim

/-- The inverted typing of a constructor at `T`. -/
def ConInv (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (d c : ℕ) (ps args : Tm) (rs : List I) (T : Tm) : Prop :=
  ∃ D C, S[d]? = some (.data D) ∧ D.ctors[c]? = some C ∧
    Valid2 S Ψ Φ Γ (.data d ps) (.data d ps) (.univ D.level) ∧
    VTele2 S Ψ Φ Γ args args (C.argTys d D.params.length) ps.toList.reverse ∧
    HasTy0 S Ψ Φ Γ (.con d c ps args rs) (.data d ps) ∧ ElTr2 S Ψ Φ Γ (.data d ps) T

theorem ConInv.conv (hW : WfSig S) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {d c : ℕ} {ps args : Tm} {rs : List I} {T T' : Tm}
    {m : ℕ} (h : ConInv S Ψ Φ Γ d c ps args rs T) (hT : Valid2 S Ψ Φ Γ T T' (.univ m)) :
    ConInv S Ψ Φ Γ d c ps args rs T' := by
  obtain ⟨D, C, h0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨D, C, h0, h1, h2, h3, h4, h5.trans (ElTr2.of_valid hW hT)⟩

theorem ConInv.restrict (hW : WfSig S) {Ψ : ℕ} {Φ Φ' : I} {Γ : Ctx} {d c : ℕ} {ps args : Tm} {rs : List I} {T : Tm}
    (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ) (h : ConInv S Ψ Φ Γ d c ps args rs T) :
    ConInv S Ψ Φ' Γ d c ps args rs T := by
  obtain ⟨D, C, h0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨D, C, h0, h1, valid_restrict hW he h2, VTele2.restrict hW he h3, HasTy0.restrict hs he h4, h5.restrict he⟩

theorem ConInv.cumul (hW : WfSig S) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {d c : ℕ} {ps args : Tm} {rs : List I} {l : ℕ}
    (hl : l + 1 ≤ maxLevel) (h : ConInv S Ψ Φ Γ d c ps args rs (.univ l)) :
    ConInv S Ψ Φ Γ d c ps args rs (.univ (l + 1)) := by
  obtain ⟨D, C, h0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨D, C, h0, h1, h2, h3, h4, h5.trans (ElTr2.cumul hW hl)⟩

section
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = true)
  (hyp : HITHyp2 S)
include hW hD hH hyp
variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-- **Constructors** of a higher inductive type (formation and congruence), at valid arguments. -/
theorem valid_conH {c : ℕ} {C : Ctor} {ps ps' args args' : Tm} {rs rs' : List I}
    (hC : D.ctors[c]? = some C) (hpl : ps = Tm.ofList ps.toList)
    (hcon : HasTy0 S Ψ Φ Γ (.con d c ps args rs) (.data d ps))
    (hcon' : HasTy0 S Ψ Φ Γ (.con d c ps' args' rs') (.data d ps))
    (hpsl : ps.toList.length = D.params.length) (hal : args = Tm.ofList args.toList)
    (hal' : args' = Tm.ofList args'.toList) (hall : args.toList.length = C.args.length)
    (hrs : rs.length = rs'.length) (hreq : ∀ (i : ℕ) (r r' : I), rs[i]? = some r → rs'[i]? = some r' → I.Eq r r')
    (hvd : Valid2 S Ψ Φ Γ (.data d ps) (.data d ps) (.univ D.level))
    (hva : VTele2 S Ψ Φ Γ args args' (C.argTys d D.params.length) ps.toList.reverse) :
    Valid2 S Ψ Φ Γ (.con d c ps args rs) (.con d c ps' args' rs') (.data d ps) := by
  have hdD := dataD_eq hW hD
  intro k c'
  have hvdk := hvd k c'
  have hPT : HasTy S k .one [] (.data d (c'.L ps)) (.univ D.level) := (RE2.typed hvdk.2).1
  have hPP : RT2 S k (.data d (c'.L ps)) (.data d (c'.L ps)) := by
    have := (RE2_univ_iff hW).1 hvdk.2
    exact RT2.refl hW (tyCode_of_univ hW hPT) this.2.2
  refine ⟨((RE2_univ_iff hW).1 hvdk.2).2.2, ?_⟩
  have hpc : (c'.L ps).closedB 0 k = true := by
    have := closed_of_ty hW hPT; simpa [Tm.closedB] using this
  have eP : (c'.L ps).isub (ISub.id k) = c'.L ps := isub_id_of_closed hpc
  have hY : c'.L args = Tm.ofList (args.toList.map c'.L) := by
    show args.subst c'.γ c'.σ.τ = _
    conv_lhs => rw [hal]
    exact ofList_subst _ _ _
  have hY' : c'.R args' = Tm.ofList (args'.toList.map c'.R) := by
    show args'.subst c'.γ' c'.σ'.τ = _
    conv_lhs => rw [hal']
    exact ofList_subst _ _ _
  have hcT := c'.ty hW hcon
  have hcT' := c'.tyR' hW hcon'
  change HasTy S k .one [] (.con d c (c'.L ps) (c'.L args) (rs.map (·.subst c'.σ.τ))) (.data d (c'.L ps)) at hcT
  change HasTy S k .one [] (.con d c (c'.R ps') (c'.R args') (rs'.map (·.subst c'.σ'.τ))) (.data d (c'.L ps)) at hcT'
  rw [hY] at hcT
  rw [hY'] at hcT'
  show RE2 S k (.data d (c'.L ps)) (.con d c (c'.L ps) (c'.L args) (rs.map (·.subst c'.σ.τ)))
    (.con d c (c'.R ps') (c'.R args') (rs'.map (·.subst c'.σ'.τ)))
  rw [hY, hY']
  have hrs2 : List.Forall₂ I.Eq (rs.map (·.subst c'.σ.τ)) (rs'.map (·.subst c'.σ'.τ)) :=
    forall2_ieq (by simp [hrs]) fun i r r' h1 h2 => by
      simp only [List.getElem?_map, Option.map_eq_some_iff] at h1 h2
      obtain ⟨r0, h1, rfl⟩ := h1
      obtain ⟨r0', h2, rfl⟩ := h2
      exact c'.ieq_subst (hreq i r0 r0' h1 h2)
  have key := con_rel hW hD hPT hPP hH hyp c (ISub.id k) hC (q := c'.L ps) (q' := c'.R ps')
    (X := args.toList.map c'.L) (X' := args'.toList.map c'.R) (by rw [eP]; exact hcT) (by rw [eP]; exact hcT')
    hrs2 (fun i hi => ?_)
  · rwa [eP] at key
  rw [eP]
  have hi0 : i < args.toList.length := by omega
  have hi0' : i < args'.toList.length := by
    have := (VTele2.shape hva).2.2.2; simp [Ctor.argTys] at this; omega
  have h := (VTele2.get hva i hi0 hi0' (by simp [Ctor.argTys]; exact hi) k c').2
  simp only [Ctor.argTys, List.getElem_map, List.getElem_range] at h
  have hcl : (C.argTy d D.params.length i).closedB ((args.toList.take i).reverse ++ ps.toList.reverse).length 0 = true := by
    simp only [List.length_append, List.length_reverse, List.length_take, hpsl, Nat.min_eq_left hi0.le]
    rw [Nat.add_comm]; exact argTy_closed hW hD hC i
  have e3 : c'.L ((C.argTy d D.params.length i).substList ((args.toList.take i).reverse ++ ps.toList.reverse)) =
      (C.argTy d D.params.length i).substList (((args.toList.map c'.L).take i).reverse ++ (c'.L ps).toList.reverse) := by
    show ((C.argTy d D.params.length i).substList _).subst c'.γ c'.σ.τ = _
    rw [substList_subst hcl, List.map_append, List.map_reverse, List.map_reverse, List.map_take,
      ← toList_subst hpl]
  rw [e3] at h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map,
    List.getElem?_eq_getElem hi0, List.getElem?_eq_getElem hi0']
  exact h

/-- **Boundaries of constructors** of a higher inductive type, from their closed instance. -/
theorem valid_conBnd {c : ℕ} {C : Ctor} {ps args T : Tm} {rs : List I} {kb : ℕ} {ψ : I} {b : Tm}
    (hC : D.ctors[c]? = some C) (hk : C.bnd[kb]? = some (ψ, b)) (hent : I.Entails Φ (Ctor.cofAt ψ rs))
    (hpl : ps = Tm.ofList ps.toList) (hal : args = Tm.ofList args.toList)
    (hv : Valid2 S Ψ Φ Γ (.con d c ps args rs) (.con d c ps args rs) T)
    (hinv : ConInv S Ψ Φ Γ d c ps args rs T) :
    Valid2 S Ψ Φ Γ (.con d c ps args rs) (Ctor.bndAt b ps.toList args.toList rs) T := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨D1, C1, hD1, hC1, hvd, hva, hcon, htr⟩ := hinv
  rw [hD] at hD1; cases hD1
  rw [hC] at hC1; cases hC1
  obtain ⟨D2, C2, hD2, hC2, -, hpsl, hall, hrsl⟩ := gen_con hcon rfl
  rw [hD] at hD2; cases hD2
  rw [hC] at hC2; cases hC2
  have hb := hS.bnd _ _ _ _ _ _ _ hD hC hk
  intro k c'
  refine ⟨(hv k c').1, RE2.trans hW (hv.tyLL hW c') (hv k c').2 ?_⟩
  -- the right instance
  let cR := c'.diagR hW
  have hPT : HasTy S k .one [] (.data d (c'.R ps)) (.univ D.level) := (RE2.typed (hvd k cR).2).1
  have hPP : RT2 S k (.data d (c'.R ps)) (.data d (c'.R ps)) := hvd.ty hW cR
  have hY : c'.R args = Tm.ofList (args.toList.map c'.R) := by
    show args.subst c'.γ' c'.σ'.τ = _
    conv_lhs => rw [hal]
    exact ofList_subst _ _ _
  have hcT := cR.ty hW hcon
  change HasTy S k .one [] (.con d c (c'.R ps) (c'.R args) (rs.map (·.subst c'.σ'.τ))) (.data d (c'.R ps)) at hcT
  rw [hY] at hcT
  have hent' : I.Entails .one (Ctor.cofAt ψ (rs.map (·.subst c'.σ'.τ))) := by
    have := ent_trans c'.face' (ent_subst hent c'.σ'.τ)
    rwa [KubusCore.Meta.cofAt_subst (h := by rw [hrsl]; exact hb.1)] at this
  have hargs : ∀ i (hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
      (((args.toList.map c'.R).take i).reverse ++ (c'.R ps).toList.reverse))
      ((args.toList.map c'.R).getD i .abort) ((args.toList.map c'.R).getD i .abort) := by
    intro i hi
    have hi0 : i < args.toList.length := by simpa using hall ▸ hi
    have h := (VTele2.get hva i hi0 hi0 (by simp [Ctor.argTys]; exact hi) k cR).2
    simp only [Ctor.argTys, List.getElem_map, List.getElem_range] at h
    have hcl : (C.argTy d D.params.length i).closedB ((args.toList.take i).reverse ++ ps.toList.reverse).length 0 = true := by
      simp only [List.length_append, List.length_reverse, List.length_take, hpsl, Nat.min_eq_left hi0.le]
      rw [Nat.add_comm]; exact argTy_closed hW hD hC i
    have e3 : cR.L ((C.argTy d D.params.length i).substList ((args.toList.take i).reverse ++ ps.toList.reverse)) =
        (C.argTy d D.params.length i).substList (((args.toList.map c'.R).take i).reverse ++ (c'.R ps).toList.reverse) := by
      show ((C.argTy d D.params.length i).substList _).subst c'.γ' c'.σ'.τ = _
      rw [substList_subst hcl, List.map_append, List.map_reverse, List.map_reverse, List.map_take,
        ← toList_subst hpl]
    rw [e3] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi0]
    exact h
  have key := hyp.conBnd hD hH hC hk hent' hPT hPP (by simpa using hall) hcT hargs
  have eB : c'.R (Ctor.bndAt b ps.toList args.toList rs) =
      Ctor.bndAt b (c'.R ps).toList (args.toList.map c'.R) (rs.map (·.subst c'.σ'.τ)) := by
    show (Ctor.bndAt b ps.toList args.toList rs).subst c'.γ' c'.σ'.τ = _
    rw [KubusCore.Meta.bndAt_subst (hb := by rw [hpsl, hall, hrsl]; exact hb.2), ← toList_subst hpl]
  have eC : c'.R (.con d c ps args rs) = .con d c (c'.R ps) (Tm.ofList (args.toList.map c'.R))
      (rs.map (·.subst c'.σ'.τ)) := by
    rw [← hY]; rfl
  rw [eB, eC]
  have k2 := htr k cR _ _ key
  exact RE2.conv hW (RT2.symm hW (hv.tyCode hW c') (hv k c').1) k2

end

end

end Model.Whnf
