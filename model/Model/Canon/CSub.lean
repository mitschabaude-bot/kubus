import Model.Canon.KripkeAll

/-!
# Canonicity: computable substitutions

Computable elements and types at the type's own code (`RE`, `RT`), and computable substitutions
from a context into a stage (`CSub`), with their restriction and extension.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

/-- A computable element of a closed type at stage `k` (at the type's own code). -/
def RE (S : Sig) (k : ℕ) (A t : Tm) : Prop := (Comp S (semK S k A) k k (Hom.id k)).el A t

/-- A computable closed type at stage `k`. -/
def RT (S : Sig) (k : ℕ) (A : Tm) : Prop := (Comp S (semK S k A) k k (Hom.id k)).ty A

/-- A computable substitution from the context `Ψ; Φ; Γ` to stage `k`. -/
structure CSub (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (k : ℕ) where
  σ : ISub k Ψ
  γ : ℕ → Tm
  face : I.Entails .one (Φ.subst σ.τ)
  nat : ∀ x, Natural S (γ x) k (idEnv k) (γ0 k)
  look : ∀ x A, Γ.lookup x = some A → RE S k (A.subst γ σ.τ) (γ x)

/-! ### Computable substitutions -/

namespace CSub

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx} (c : CSub S Ψ Φ Γ k)

/-- The point of the model given by a computable substitution. -/
def ρ : IEnv k := (idEnv Ψ).restr c.σ.hom
def γv : ℕ → V := fun x => semK S k (c.γ x)

theorem semK_subst (t : Tm) : semK S k (t.subst c.γ c.σ.τ) = sem S t k c.ρ c.γv := by
  unfold semK; rw [sem_subst S t k _ _ _ _ c.nat, env_isub]; rfl

theorem kv (x : ℕ) : IsKV k (c.γv x) := by
  have := c.nat x k (Hom.id k)
  rw [IEnv.restr_id, γ0_restr] at this
  show IsKV k (semK S k (c.γ x))
  unfold semK; rw [this]; exact isKV_res _ _

variable (hW : WfSig S)
include hW

theorem isPoint : IsPoint S Φ Γ k c.ρ c.γv where
  cof := by
    have := entails_holds c.face (ρ := idEnv k) (by rw [ival_one]; rfl)
    rw [ival_subst, env_isub] at this; exact this
  typ x A h := by
    have := (Comp_el_typed (c.look x A h)).2
    rw [El_res, Hom.comp_id, c.semK_subst] at this
    exact this
  kv := c.kv

theorem tySub : TySub S Ψ Φ Γ k .one [] c.γ c.σ.τ :=
  ⟨c.σ.sc, trivial, c.face, fun x A h => spec_to_minimal hW (Comp_el_typed (c.look x A h)).1, Wf0.nil trivial⟩

theorem ty {t A : Tm} (h : HasTy0 S Ψ Φ Γ t A) : HasTy S k .one [] (t.subst c.γ c.σ.τ) (A.subst c.γ c.σ.τ) :=
  minimal_to_spec ((sub_ty (sigClosed_of_wfSig hW) h).2.1 (c.tySub hW))

theorem eq {t u A : Tm} (h : EqTm0 S Ψ Φ Γ t u A) :
    EqTm S k .one [] (t.subst c.γ c.σ.τ) (u.subst c.γ c.σ.τ) (A.subst c.γ c.σ.τ) :=
  minimal_to_spec_eq ((sub_eq (sigClosed_of_wfSig hW) h).2 (c.tySub hW))

/-- Restrict to a smaller face. -/
def restrictTo {Φ' : I} (he : I.Entails Φ' Φ) (c : CSub S Ψ Φ' Γ k) : CSub S Ψ Φ Γ k :=
  { c with face := ent_trans c.face (ent_subst he _) }

end CSub

/-- The type of a typed closed term has a type code. -/
theorem tyCode_of_ty (hW : WfSig S) {t A : Tm} (ht : HasTy S k .one [] t A) : TyCode k (semK S k A) :=
  ((sound_ty (sigOK_of_wfSig _ S rfl hW) ht).2.2.2 k (idEnv k) (γ0 k) (isPoint_idEnv S k)).2.2.1

theorem RE.conv (hW : WfSig S) {A B t t' : Tm} (h : RE S k A t) (hAB : TyEq S k A B)
    (htt : EqTm S k .one [] t t' B) : RE S k B t' := by
  unfold RE at h ⊢
  rw [← semK_tyEq hW hAB]
  exact ((cv_tyCode hW (tyCode_of_ty hW (Comp_el_typed h).1)) k (Hom.id k) A B t t').2 h hAB htt

theorem RE.conv_ty (hW : WfSig S) {A B t : Tm} (h : RE S k A t) (hAB : TyEq S k A B) : RE S k B t :=
  h.conv hW hAB (EqTm.refl ((Comp_el_typed h).1.tyConv hAB))


/-! ### Restriction and extension -/

theorem natural_of_ty (hW : WfSig S) {t A : Tm} (ht : HasTy S k .one [] t A) : Natural S t k (idEnv k) (γ0 k) :=
  ((sound_ty (sigOK_of_wfSig _ S rfl hW) ht).2.2.2 k (idEnv k) (γ0 k) (isPoint_idEnv S k)).2.1

theorem mem_of_ty (hW : WfSig S) {t A : Tm} (ht : HasTy S k .one [] t A) : semK S k t ∈ El (semK S k A) (Hom.id k) :=
  ((sound_ty (sigOK_of_wfSig _ S rfl hW) ht).2.2.2 k (idEnv k) (γ0 k) (isPoint_idEnv S k)).1

theorem natural_isub {t : Tm} (h : Natural S t k (idEnv k) (γ0 k)) (σ : ISub k' k) :
    Natural S (t.isub σ) k' (idEnv k') (γ0 k') := by
  intro k'' f
  have e : ∀ {n : ℕ} (g : Hom n k'), sem S (t.isub σ) n ((idEnv k').restr g) (TEnv.restr (γ0 k') g) =
      res (σ.hom.comp g) (semK S k t) := by
    intro n g
    rw [show t.isub σ = t.dsubst σ.τ from rfl, sem_dsubst]
    have : (fun i => ival ((idEnv k').restr g) (σ.τ i)) = (idEnv k).restr (σ.hom.comp g) := by
      funext i; rw [ival.restr, ← IEnv.restr_restr, ← env_isub]; rfl
    rw [this, γ0_restr, ← γ0_restr (σ.hom.comp g)]; exact h n _
  rw [e f, ← IEnv.restr_id (idEnv k'), ← γ0_restr (Hom.id k'), e (Hom.id k'), res_res, Hom.comp_id]

theorem RE.isub (hW : WfSig S) {A t : Tm} (h : RE S k A t) (σ : ISub k' k) : RE S k' (A.isub σ) (t.isub σ) := by
  have ht := (Comp_el_typed h).1
  have hX := tyCode_of_ty hW ht
  unfold RE at h ⊢
  have := ((kr_tyCode hW hX) k (Hom.id k) k' σ A t).2 h
  rw [Hom.id_comp, Comp_eq_res (IsKV.ne_empty hX.fib.kv)] at this
  rwa [semK_isubTy hW (isTyK_of_ty hW ht)]

theorem RT.isub (hW : WfSig S) {A : Tm} (h : RT S k A) (hA : IsTyK S k A) (hX : TyCode k (semK S k A))
    (σ : ISub k' k) : RT S k' (A.isub σ) := by
  unfold RT at h ⊢
  have := ((kr_tyCode hW hX) k (Hom.id k) k' σ A A).1 h
  rw [Hom.id_comp, Comp_eq_res (IsKV.ne_empty hX.fib.kv)] at this
  rwa [semK_isubTy hW hA]

namespace CSub

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

theorem subst_isub (c : CSub S Ψ Φ Γ k) (t : Tm) (σ' : ISub k' k) :
    (t.subst c.γ c.σ.τ).isub σ' = t.subst (fun x => (c.γ x).isub σ') (c.σ.comp σ').τ := by
  simp only [Tm.isub, subst_subst]; rfl

/-- Restriction of a computable substitution. -/
def restr (hW : WfSig S) (c : CSub S Ψ Φ Γ k) (σ' : ISub k' k) : CSub S Ψ Φ Γ k' where
  σ := c.σ.comp σ'
  γ := fun x => (c.γ x).isub σ'
  face := by
    have := ent_subst c.face σ'.τ
    rwa [I_subst_subst] at this
  nat x := natural_isub (c.nat x) σ'
  look x A h := by
    have := (c.look x A h).isub hW σ'
    rwa [subst_isub] at this

theorem restr_subst (hW : WfSig S) (c : CSub S Ψ Φ Γ k) (t : Tm) (σ' : ISub k' k) :
    t.subst (c.restr hW σ').γ (c.restr hW σ').σ.τ = (t.subst c.γ c.σ.τ).isub σ' := (subst_isub c t σ').symm

/-- Extension of a computable substitution by a computable element. -/
def ext (hW : WfSig S) (c : CSub S Ψ Φ Γ k) (A a : Tm) (ha : RE S k (A.subst c.γ c.σ.τ) a) :
    CSub S Ψ Φ (A :: Γ) k where
  σ := c.σ
  γ := consT a c.γ
  face := c.face
  nat x := by
    cases x with
    | zero => exact natural_of_ty hW (Comp_el_typed ha).1
    | succ x => exact c.nat x
  look x B h := by
    cases x with
    | zero =>
      simp only [Ctx.lookup, Option.some.injEq] at h; subst h
      rw [shift_consT]; exact ha
    | succ x =>
      simp only [Ctx.lookup, Option.map_eq_some_iff] at h
      obtain ⟨B', hB', rfl⟩ := h
      rw [shift_consT]; exact c.look x B' hB'

/-- Instantiation of a line context at an interval term. -/
def cons (c : CSub S Ψ Φ Γ k) (r : I) (hr : r.Scoped k) : CSub S (Ψ + 1) Φ.shift Γ.dshift k where
  σ := ISub.cons r hr c.σ
  γ := c.γ
  face := by
    show I.Entails .one (Φ.shift.subst (consI r c.σ.τ))
    rw [I.shift, I_ren_subst]; exact c.face
  nat := c.nat
  look x B h := by
    rw [lookup_dshift, Option.map_eq_some_iff] at h
    obtain ⟨B', hB', rfl⟩ := h
    show RE S k (B'.dshift.subst c.γ (consI r c.σ.τ)) (c.γ x)
    rw [dshift_consI]; exact c.look x B' hB'

end CSub

/-- The weakening of a stage by a new line variable (index `0`). -/
def ISub.wk (k : ℕ) : ISub (k + 1) k :=
  ⟨fun i => if i < k then .var (i + 1) else .zero, fun i hi => by simp [hi, I.Scoped],
    fun i hi => by simp [show ¬ i < k by omega]⟩

theorem natural_dshift {t : Tm} (h : Natural S t k (idEnv k) (γ0 k)) :
    Natural S t.dshift (k + 1) (idEnv (k + 1)) (γ0 (k + 1)) := by
  intro n f
  have e : ∀ {n : ℕ} (g : Hom n (k + 1)), sem S t.dshift n ((idEnv (k + 1)).restr g) (TEnv.restr (γ0 (k + 1)) g) =
      res ((Hom.wk k).comp g) (semK S k t) := by
    intro n g
    rw [sem_dshift_tail, IEnv.tail_restr, ← idEnv_ext]
    show sem S t n (((idEnv k).restr (Hom.wk k)).restr g) _ = _
    rw [IEnv.restr_restr, γ0_restr, ← γ0_restr ((Hom.wk k).comp g)]; exact h n _
  rw [e f, ← IEnv.restr_id (idEnv (k + 1)), ← γ0_restr (Hom.id (k + 1)), e (Hom.id (k + 1)), res_res,
    Hom.comp_id]

theorem dshift_eq_isub (hW : WfSig S) {t A : Tm} (ht : HasTy S k .one [] t A) :
    EqTm S (k + 1) .one [] (t.isub (ISub.wk k)) t.dshift (A.isub (ISub.wk k)) := by
  have hS := sigClosed_of_wfSig hW
  have h0 := spec_to_minimal hW ht
  have hw : Wf0 S (k + 1) .one [] := Wf0.nil trivial
  have k1 : TySub S k .one [] (k + 1) .one [] Tm.var (ISub.wk k).τ :=
    ⟨(ISub.wk k).sc, trivial, I.entails_refl _, fun x A h => by simp [Ctx.lookup] at h, hw⟩
  have k2 : TySub S k .one [] (k + 1) .one [] Tm.var (fun i => .var (i + 1)) :=
    ⟨fun i hi => by simp [I.Scoped]; omega, trivial, I.entails_refl _, fun x A h => by simp [Ctx.lookup] at h, hw⟩
  have kE : EqSub S k [] (k + 1) .one [] Tm.var (ISub.wk k).τ Tm.var (fun i => .var (i + 1)) :=
    ⟨fun x A h => by simp [Ctx.lookup] at h, fun i hi => by simp [ISub.wk, hi]; intro ρ; rfl⟩
  have := minimal_to_spec_eq ((sub_ty hS h0).2.2 k1 k2 kE)
  rwa [← dshift_eq] at this

theorem RE.dshift (hW : WfSig S) {A t : Tm} (h : RE S k A t) : RE S (k + 1) A.dshift t.dshift := by
  have ht := (Comp_el_typed h).1
  have h1 := h.isub hW (ISub.wk k)
  refine h1.conv hW ?_ ?_
  · obtain ⟨l, hA | rfl⟩ := isTyK_of_ty hW ht
    · exact .inr ⟨l, dshift_eq_isub hW hA⟩
    · exact .inl rfl
  · obtain ⟨l, hA | rfl⟩ := isTyK_of_ty hW ht
    · exact (dshift_eq_isub hW ht).conv (dshift_eq_isub hW hA)
    · exact dshift_eq_isub hW ht

namespace CSub

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-- Lifting a computable substitution under an interval binder. -/
def up (hW : WfSig S) (c : CSub S Ψ Φ Γ k) : CSub S (Ψ + 1) Φ.shift Γ.dshift (k + 1) where
  σ := c.σ.up
  γ := dupS c.γ
  face := by
    show I.Entails .one (Φ.shift.subst (I.up c.σ.τ))
    rw [I_shift_subst_up]; exact ent_shift c.face
  nat x := natural_dshift (c.nat x)
  look x B h := by
    rw [lookup_dshift, Option.map_eq_some_iff] at h
    obtain ⟨B', hB', rfl⟩ := h
    show RE S (k + 1) (B'.dshift.subst (dupS c.γ) (I.up c.σ.τ)) (c.γ x).dshift
    rw [dshift_dup_subst]; exact (c.look x B' hB').dshift hW

end CSub

theorem semK_isub_of_nat {t : Tm} (h : Natural S t k (idEnv k) (γ0 k)) (σ : ISub k' k) :
    semK S k' (t.isub σ) = res σ.hom (semK S k t) := by
  unfold semK
  rw [show t.isub σ = t.dsubst σ.τ from rfl, sem_dsubst, env_isub, ← γ0_restr σ.hom, h]

theorem subst_up_isub_inst (B a : Tm) (γ : ℕ → Tm) (τ : ℕ → I) (σ : ISub k' k) :
    ((B.subst (Tm.up γ) τ).isub σ).inst a = B.subst (consT a fun x => (γ x).isub σ) (fun i => (τ i).subst σ.τ) := by
  simp only [Tm.isub, Tm.inst, subst_subst]
  apply subst_congr
  · intro x; cases x with
    | zero => rfl
    | succ x =>
      simp only [Tm.up, consT]
      rw [shift_subst]
      exact subst_congr (fun n => rfl) (fun i => I_subst_var _) _
  · intro i; exact I_subst_var _

namespace CSub

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

theorem restr_ρ (hW : WfSig S) (c : CSub S Ψ Φ Γ k) (σ : ISub k' k) : (c.restr hW σ).ρ = c.ρ.restr σ.hom := by
  simp only [ρ, restr, ISub.hom_comp, IEnv.restr_restr]

theorem restr_γv (hW : WfSig S) (c : CSub S Ψ Φ Γ k) (σ : ISub k' k) :
    (c.restr hW σ).γv = TEnv.restr c.γv σ.hom := by
  funext x; simp only [γv, restr, TEnv.restr]; exact semK_isub_of_nat (c.nat x) σ

theorem ext_ρ (hW : WfSig S) (c : CSub S Ψ Φ Γ k) (A a : Tm) (ha : RE S k (A.subst c.γ c.σ.τ) a) :
    (c.ext hW A a ha).ρ = c.ρ := rfl

theorem ext_γv (hW : WfSig S) (c : CSub S Ψ Φ Γ k) (A a : Tm) (ha : RE S k (A.subst c.γ c.σ.τ) a) :
    (c.ext hW A a ha).γv = TEnv.cons c.γv (semK S k a) := by
  funext x; cases x <;> rfl

end CSub

/-- Computable elements of a universe are the computable types. -/
theorem RE_univ_iff (hW : WfSig S) {l : ℕ} {T : Tm} :
    RE S k (.univ l) T ↔ HasTy S k .one [] T (.univ l) ∧ semK S k T ∈ ZFSet.sep (WF l k) (Vt l) ∧ RT S k T := by
  unfold RE RT
  rw [show semK S k (.univ l) = univC k l from rfl, Comp_univC]
  constructor
  · rintro ⟨ht, -, -, hm, hrt⟩; exact ⟨ht, hm, hrt⟩
  · rintro ⟨ht, hm, hrt⟩
    refine ⟨ht, ?_, TyEq.refl _, hm, hrt⟩
    rw [res_id (isKV_univC _), El_univC]; exact hm

theorem RE_univ_of (hW : WfSig S) {l : ℕ} {T : Tm} (ht : HasTy S k .one [] T (.univ l)) (hrt : RT S k T) :
    RE S k (.univ l) T := by
  refine (RE_univ_iff hW).2 ⟨ht, ?_, hrt⟩
  have := mem_of_ty hW ht
  rwa [show semK S k (.univ l) = univC k l from rfl, El_univC] at this

namespace CSub

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

theorem up_restr_subst (hW : WfSig S) (c : CSub S Ψ Φ Γ k) (σ : ISub k' k) (t : Tm) :
    t.subst ((c.restr hW σ).up hW).γ ((c.restr hW σ).up hW).σ.τ = (t.subst (c.up hW).γ (c.up hW).σ.τ).isub σ.up := by
  simp only [up, restr, Tm.isub, subst_subst, ISub.up, ISub.comp]
  apply subst_congr
  · intro x; exact (isub_dshift (c.γ x) σ).symm
  · intro i; exact (I_up_comp _ _ i).symm

theorem cons_restr_subst (hW : WfSig S) (c : CSub S Ψ Φ Γ k) (σ : ISub k' k) (r : I) (hr : r.Scoped k') (t : Tm) :
    t.subst ((c.restr hW σ).cons r hr).γ ((c.restr hW σ).cons r hr).σ.τ =
      ((t.subst (c.up hW).γ (c.up hW).σ.τ).isub σ.up).dinst r := by
  rw [← up_restr_subst]
  exact (dup_dinst t _ _ r).symm

end CSub

end

end Model.Canon
