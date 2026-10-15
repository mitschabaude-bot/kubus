import Model.Whnf.Valid2TranspCon
import Model.Whnf.TranspCon2H

/-!
# Validity of transport of HIT constructors

The argument transports give `TC.rel`. At a boundary, `TC.transp_relH` compares the transport
of the boundary with the boundary at the transported arguments.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

section
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hW hD

variable (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1)) (hp : D.params ≠ [])
include hH hyp hp

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-- **Transport of a constructor** of a higher inductive type. -/
theorem valid_transpConH {ci : ℕ} {C : Ctor} {ps qs args T : Tm} {φ : I} {rs : List I}
    (hC : D.ctors[ci]? = some C) (hpl : ps = Tm.ofList ps.toList)
    (hva : VTele2 S Ψ Φ Γ args args (C.argTys d D.params.length) (ps.dinst .zero).toList.reverse)
    (hv : Valid2 S Ψ Φ Γ (.transp (.data d ps) φ (.con d ci qs args rs))
      (.transp (.data d ps) φ (.con d ci qs args rs)) T)
    (hinv : TranspInv S Ψ Φ Γ (.data d ps) φ (.con d ci qs args rs) T) :
    Valid2 S Ψ Φ Γ (.transp (.data d ps) φ (.con d ci qs args rs)) (.con d ci (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs) T := by
  obtain ⟨l, hφ, hLV, hCV, haV, htr, hL, hc, ha⟩ := hinv
  obtain ⟨hal, -, hXl, -⟩ := VTele2.shape hva
  simp only [Ctor.argTys, List.length_map, List.length_range] at hXl
  -- the line at the parameters, typed at the level of the inductive type
  obtain ⟨D2, hD2, hpt⟩ := gen_data_tele hL rfl
  rw [hD] at hD2; cases hD2
  have hLD : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (.data d ps) (.univ D.level) :=
    HasTy0.data hD (hW.2 d D hD).1 hpt
  have hpsl : ps.toList.length = D.params.length := by simpa using Meta.tele_length hpt
  have hty1 : HasTy0 S Ψ Φ Γ (.transp (.data d ps) φ (.con d ci qs args rs)) ((Tm.data d ps).dinst .one) :=
    HasTy0.transp hL hφ hc ha
  have hT : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L T) (c.R T) := fun k c => (hv k c).1
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
  have eR : ∀ {k : ℕ} (c : CSub2 S Ψ Φ Γ k), c.R (.con d ci (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs) =
      tConR d D ci C ((c.up hW).R ps) (φ.subst c.σ'.τ) (args.toList.map c.R) (rs.map (·.subst c.σ'.τ)) :=
    fun c => tConR_subst hW hD hC hpl hpsl φ hXl rs _ _
  -- the literal lines at a related substitution
  have hPL : ∀ {k : ℕ} (c : CSub2 S Ψ Φ Γ k), HasTy S (k + 1) .one [] (.data d ((c.up hW).L ps)) (.univ D.level) :=
    fun c => (c.up hW).ty hW hLD
  have hQL : ∀ {k : ℕ} (c : CSub2 S Ψ Φ Γ k), HasTy S (k + 1) .one [] (.data d ((c.up hW).R ps)) (.univ D.level) :=
    fun c => (c.up hW).tyR hW hLD
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
  -- the transport data at a related substitution
  have hTC : ∀ {k : ℕ} (c : CSub2 S Ψ Φ Γ k), TC S k d D ((c.up hW).L ps) ((c.up hW).R ps) (φ.subst c.σ.τ)
      (φ.subst c.σ'.τ) ci C (c.L qs) (c.R qs) (args.toList.map c.L) (args.toList.map c.R) (rs.map (·.subst c.σ.τ)) (rs.map (·.subst c.σ'.τ)) := by
    intro k c
    have h1 := c.ty hW hty1
    have h1' := c.tyR' hW hty1
    have h1e := c.eq hW (EqTm0.refl hty1)
    rw [eT1] at h1 h1' h1e
    change HasTy S k .one [] (.transp (.data d ((c.up hW).L ps)) (φ.subst c.σ.τ)
      (.con d ci (c.L qs) (c.L args) (rs.map (·.subst c.σ.τ)))) _ at h1
    change HasTy S k .one [] (.transp (.data d ((c.up hW).R ps)) (φ.subst c.σ'.τ)
      (.con d ci (c.R qs) (c.R args) (rs.map (·.subst c.σ'.τ)))) _ at h1'
    change EqTm S k .one [] (.transp (.data d ((c.up hW).L ps)) (φ.subst c.σ.τ)
      (.con d ci (c.L qs) (c.L args) (rs.map (·.subst c.σ.τ)))) (.transp (.data d ((c.up hW).R ps)) (φ.subst c.σ'.τ)
      (.con d ci (c.R qs) (c.R args) (rs.map (·.subst c.σ'.τ)))) _ at h1e
    rw [hXL c] at h1 h1e
    rw [hXR c] at h1' h1e
    exact {
      hW := hW, hD := hD, hp := hp, hC := hC, hPL := hPL c,
      hR := fun k3 τ y y' hy hy' hE => lineRob_of_valid hW hLV c k3 τ y y' hy hy' hE,
      hRL := fun k3 τ y y' hy hy' hE => lineRob_of_valid hW hLV (c.diagL hW) k3 τ y y' hy hy' hE,
      hφs := I.scoped_subst hφ c.σ.sc,
      h12 := c.ent_LR (ent_refl φ), h21 := c.ent_RL (ent_refl φ),
      hLC := lineConst_of_valid hW hφ hCV c, hty := h1, hty' := h1', heq := h1e,
      hargs0 := transpCon_args0 hW hD hC hpl hpsl hva c,
      hrecT := fun i hi hri k3 τ y y' hy hy' hE _ => by
        have hk := hLV.kanV hW (k3 + 1) ((c.restr hW τ.up.tail).cons y y' hy hy' hE)
        rw [CSub2.cons_restr_L, isub_up_dinst _ _ _ hy] at hk
        exact KanT2.at (hk.2 k3 (Hom.id (k3 + 1)) _ _
          (lineRob_of_valid hW hLV c (k3 + 1) τ.up.tail y y' hy hy' hE)) _ _,
      conR := conR_hit hW hD hH hyp hC (hPL c)
        (fun k3 τ y y' hy hy' hE => lineRob_of_valid hW hLV (c.diagL hW) k3 τ y y' hy hy' hE)
        (by
          suffices ∀ xs : List I, List.Forall₂ I.Eq (xs.map (·.subst c.σ.τ)) (xs.map (·.subst c.σ'.τ)) from this rs
          intro xs
          induction xs with
          | nil => exact .nil
          | cons r xs ih => exact .cons (c.ieq_subst (I_eq_refl r)) ih) }
  have hyA : Valid2 S Ψ Φ Γ (.transp (.data d ps) φ (.con d ci qs args rs))
      (.con d ci (ps.dinst .one)
        (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs)
      ((Tm.data d ps).dinst .one) := by
    intro k c
    refine ⟨by rw [CSub2.L_dinst hW, CSub2.R_dinst hW]; exact hRQ1 c, ?_⟩
    rw [eT1, eR]
    change RE2 S k _ (.transp (.data d ((c.up hW).L ps)) (φ.subst c.σ.τ)
      (.con d ci (c.L qs) (c.L args) (rs.map (·.subst c.σ.τ)))) _
    rw [hXL c]
    exact RE2.trans hW (s1 c) ((hTC (c.diagL hW)).transp_relH hH hyp) (hTC c).rel
  exact valid_conv_tr hyA htr hT

end

end

end Model.Whnf
