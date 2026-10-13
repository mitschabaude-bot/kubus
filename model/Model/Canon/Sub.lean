import Model.Canon.Comp

/-!
# Canonicity: interval substitutions between stages

The algebra of `ISub` (composition, lifting, extension) on terms and on cube maps, typing and
values of closed terms under substitution, and faces: a face holds at the identity environment
iff it is entailed by `1`.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore ZFSet

noncomputable section

variable {S : Sig} {k k' k'' k3 m n : ℕ}

namespace ISub

@[ext] theorem ext' {σ σ' : ISub k' k} (h : σ.τ = σ'.τ) : σ = σ' := by
  cases σ; cases σ'; simp only at h; subst h; rfl

theorem I.subst_scoped_id {r : I} {n : ℕ} (hr : r.Scoped n) {τ : ℕ → I} (hτ : ∀ i < n, τ i = .var i) :
    r.subst τ = r := by
  induction r <;> simp_all [I.subst, I.Scoped]

theorem id_comp (σ : ISub k' k) : (ISub.id k).comp σ = σ := by
  ext i; simp only [comp, id]
  split
  · rfl
  · rename_i h; rw [σ.hi i (by omega)]; rfl

theorem comp_id (σ : ISub k' k) : σ.comp (ISub.id k') = σ := by
  ext i; simp only [comp]
  by_cases h : i < k
  · exact I.subst_scoped_id (σ.sc i h) fun j hj => by simp [id, hj]
  · rw [σ.hi i (by omega)]; rfl

theorem comp_assoc (σ : ISub k' k) (σ' : ISub k'' k') (σ'' : ISub k3 k'') :
    (σ.comp σ').comp σ'' = σ.comp (σ'.comp σ'') := by
  ext i; simp only [comp]; exact Meta.I_subst_subst _ _ _

end ISub

theorem Tm.isub_isub (t : Tm) (σ : ISub k' k) (σ' : ISub k'' k') :
    (t.isub σ).isub σ' = t.isub (σ.comp σ') := by
  simp only [Tm.isub, Meta.subst_subst]; rfl

/-! ### Values -/

theorem ival_subst (ρ : IEnv m) (r : I) (τ : ℕ → I) : ival ρ (r.subst τ) = ival (fun i => ival ρ (τ i)) r := by
  apply DM.ext; funext p; simp only [ival.fn, Cof.eval_subst]

/-- The environment of an interval substitution is the restricted identity environment. -/
theorem env_isub (σ : ISub k' k) : (fun i => ival (idEnv k') (σ.τ i)) = (idEnv k).restr σ.hom := by
  funext i
  by_cases h : i < k
  · simp only [IEnv.restr, idEnv, dif_pos h]
    apply DM.ext; funext p
    simp only [DM.restr_fn, DM.var_fn, Hom.app, ISub.hom]
    congr 3; omega
  · rw [σ.hi i (by omega)]
    simp only [IEnv.restr, idEnv, dif_neg h]
    apply DM.ext; funext p; simp [I.eval]

theorem ISub.hom_comp (σ : ISub k' k) (σ' : ISub k'' k') : (σ.comp σ').hom = σ.hom.comp σ'.hom := by
  funext j
  simp only [ISub.hom, ISub.comp, Hom.comp]
  rw [ival_subst, env_isub, ival.restr]

theorem ISub.hom_id (k : ℕ) : (ISub.id k).hom = Hom.id k := by
  funext j
  simp only [ISub.hom, ISub.id, if_pos (show k - 1 - j.1 < k by omega)]
  apply DM.ext; funext p
  simp only [ival_idEnv_fn, I.eval, Pt.rev, dif_pos (show k - 1 - j.1 < k by omega)]
  simp only [Hom.id, DM.var_fn]
  congr 1; ext; simp; omega

theorem ISub.hom_cons (r : I) (hr : r.Scoped k') (σ : ISub k' k) :
    (ISub.cons r hr σ).hom = Hom.snoc σ.hom (ival (idEnv k') r) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [ISub.hom, ISub.cons, Hom.snoc, Fin.snoc_last, Fin.val_last,
      show k + 1 - 1 - k = 0 by omega]
  · simp only [ISub.hom, ISub.cons, Hom.snoc, Fin.snoc_castSucc, Fin.val_castSucc,
      show k + 1 - 1 - j.1 = (k - 1 - j.1) + 1 by omega]

theorem ISub.hom_tail (σ : ISub k' (k + 1)) : σ.tail.hom = (Hom.wk k).comp σ.hom := by
  funext j
  simp only [ISub.hom, ISub.tail, Hom.comp, Hom.wk]
  apply DM.ext; funext p
  simp only [DM.restr_fn, DM.var_fn, Hom.app, show k - 1 - j.1 + 1 = k + 1 - 1 - j.1 by omega]
  rfl

theorem ISub.hom_up (σ : ISub k' k) : σ.up.hom = Hom.lift σ.hom := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [ISub.hom, ISub.up, Hom.lift, Hom.snoc, Fin.snoc_last, Fin.val_last,
      show k + 1 - 1 - k = 0 by omega, I.up]
    rw [← idEnv_ext]; rfl
  · simp only [ISub.hom, ISub.up, Hom.lift, Hom.snoc, Fin.snoc_castSucc, Fin.val_castSucc,
      show k + 1 - 1 - j.1 = (k - 1 - j.1) + 1 by omega, I.up, Hom.comp]
    rw [ival_shift, ← idEnv_ext, ← ival.restr]; rfl

variable (hW : WfSig S)
include hW

theorem HasTy.isubS {t A : Tm} (ht : HasTy S k .one [] t A) (σ : ISub k' k) :
    HasTy S k' .one [] (t.isub σ) (A.isub σ) := HasTy.isub hW ht σ.τ σ.sc

theorem EqTm.isubS {t u A : Tm} (ht : EqTm S k .one [] t u A) (σ : ISub k' k) :
    EqTm S k' .one [] (t.isub σ) (u.isub σ) (A.isub σ) := EqTm.isub hW ht σ.τ σ.sc

theorem semK_isubS {t A : Tm} (ht : HasTy S k .one [] t A) (σ : ISub k' k) :
    semK S k' (t.isub σ) = res σ.hom (semK S k t) := by
  have hok := sigOK_of_wfSig _ S rfl hW
  have hnat := ((sound_ty hok ht).2.2.2 k (idEnv k) (γ0 k) (isPoint_idEnv S k)).2.1 k' σ.hom
  unfold semK
  rw [show t.isub σ = t.dsubst σ.τ from rfl, sem_dsubst, env_isub, ← γ0_restr σ.hom, hnat]

omit hW

/-! ### Faces -/

theorem holds_iff_entails {φ : I} (hφ : φ.Scoped k) : (ival (idEnv k) φ).holds ↔ I.Entails .one φ := by
  rw [Meta.entails_iff]
  constructor
  · intro h ρ hρ _
    let p : Pt k := fun j => ρ (k - 1 - j)
    have := (DM.holds_iff _).1 h p
    rw [ival_idEnv_fn] at this
    rw [← this]
    apply Cof.eval_congr hφ
    intro n hn
    simp only [Pt.rev, dif_pos hn, p]
    congr 1; omega
  · intro h
    have := h (Pt.rev (Pt.allA k)) (fun i => by
      simp only [Pt.rev, Pt.allA]; split <;> simp [Meta.isK3]) rfl
    show (ival (idEnv k) φ).fn (Pt.allA k) = _
    rw [ival_idEnv_fn]; exact this

/-- Cofibrations with the same face entail each other. -/
theorem ent_of_face_eq {φ ψ : I} (hφ : φ.Scoped k) (hψ : ψ.Scoped k)
    (h : (ival (idEnv k) φ).face = (ival (idEnv k) ψ).face) : I.Entails φ ψ := by
  rw [Meta.entails_iff]
  intro ρ hρ h1
  let p : Pt k := fun j => ρ (k - 1 - j)
  have e : ∀ χ : I, χ.Scoped k → (ival (idEnv k) χ).fn p = χ.eval ρ := by
    intro χ hχ
    rw [ival_idEnv_fn]
    apply Cof.eval_congr hχ
    intro n hn
    simp only [Pt.rev, dif_pos hn, p]
    congr 1; omega
  have hp : p ∈ (ival (idEnv k) ψ).face := h ▸ ⟨fun j => hρ _, by rw [e φ hφ]; exact h1⟩
  rw [← e ψ hψ]; exact hp.2

/-- A cofibration holding at the generic point is constantly `1` in the De Morgan algebra. -/
theorem ieq_one_of_holds {φ : I} (hφ : φ.Scoped k) (h : (ival (idEnv k) φ).holds) : I.Eq φ .one := by
  intro ρ
  let p : Pt k := fun j => ρ (k - 1 - j)
  have := (DM.holds_iff _).1 h p
  rw [ival_idEnv_fn] at this
  show I.eval ρ φ = I.M4.one
  rw [← this]
  apply Cof.eval_congr hφ
  intro n hn
  simp only [Pt.rev, dif_pos hn, p]
  congr 1; omega

theorem ieq_zero_of_holds_neg {r : I} (hr : r.Scoped k) (h : (ival (idEnv k) (.neg r)).holds) : I.Eq r .zero := by
  intro ρ
  have := ieq_one_of_holds (φ := .neg r) hr h ρ
  simp only [I.eval] at this ⊢
  generalize I.eval ρ r = x at this ⊢
  cases x <;> first | rfl | (simp [I.M4.neg, I.M4.ofPair, I.M4.toPair] at this)

end

end Model.Canon
