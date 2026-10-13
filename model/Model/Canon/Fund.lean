import Model.Canon.KripkeAll

/-!
# Canonicity: the fundamental lemma

Every typed term, instantiated by a computable substitution (an interval substitution into a
stage satisfying the face, and computable closed terms for the variables), is computable at its
instantiated type. By induction on minimal typing derivations; the definitions and the
declarations of inductive types are computable by an outer induction on their index in the
signature (`Hyp`).
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

/-- The definitions and inductive types below `n` are computable. -/
structure Hyp (S : Sig) (n : ℕ) : Prop where
  defn : ∀ i < n, ∀ t A, S[i]? = some (.defn t A) → ∀ k, RE S k A t

/-- Computability of the elements of a telescope. -/
def TeleComp (S : Sig) (k : ℕ) : Tm → List Tm → List Tm → Prop
  | .tnil, [], _ => True
  | .tcons a as, A :: Δ, prev => RE S k (A.substList prev) a ∧ TeleComp S k as Δ (a :: prev)
  | _, _, _ => False


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

variable (hW : WfSig S) {n : ℕ} (hH : Hyp S n)
include hW hH

mutual

theorem fund_ty {Ψ Φ Γ t A} : HasTy0 S Ψ Φ Γ t A → t.ConstsLt n → ∀ k (c : CSub S Ψ Φ Γ k),
    RE S k (A.subst c.γ c.σ.τ) (t.subst c.γ c.σ.τ)
  | @HasTy0.var _ Ψ Φ Γ x A h0 h1 => fun _ k c => c.look x A h1
  | @HasTy0.conv _ Ψ Φ Γ t A B l h0 h1 => fun hc k c => by
    have ih := fund_ty h0 hc k c
    exact ih.conv_ty hW (.inr ⟨l, c.eq hW h1⟩)
  | @HasTy0.restrict _ Ψ Φ Φ' Γ t A h0 h1 h2 => fun hc k c => fund_ty h2 hc k (CSub.restrictTo h1 c)
  | @HasTy0.const _ Ψ Φ Γ i t A h0 h1 => fun hc k c => by
    obtain ⟨htc, hAc, -, -⟩ := hW.1 i t A h1
    have hA : A.subst c.γ c.σ.τ = A := closed_subst_id hAc (fun x hx => absurd hx (Nat.not_lt_zero _))
      (fun i hi => absurd hi (Nat.not_lt_zero _))
    have hty := c.ty hW (HasTy0.const h0 h1)
    rw [hA] at hty ⊢
    exact (hH.defn i hc t A h1 k).conv hW (TyEq.refl _) (EqTm.symm (EqTm.delta hty h1))
  | @HasTy0.univ _ Ψ Φ Γ l h0 h1 => fun _ k c => by
    have hty := c.ty hW (HasTy0.univ h0 h1)
    show (Comp S (semK S k (.univ (l + 1))) k k (Hom.id k)).el (.univ (l + 1)) (.univ l)
    have hsem : ∀ l', semK S k (.univ l') = univC k l' := fun l' => rfl
    rw [hsem, Comp_univC]
    dsimp only
    rw [hsem]
    have hmem : univC k l ∈ ZFSet.sep (WF (l + 1) k) (Vt (l + 1)) :=
      ZFSet.mem_sep.2 ⟨univC_mem_Vt (by unfold maxLevel at h0; omega), wf_univC⟩
    refine ⟨hty, ?_, TyEq.refl _, hmem, ?_⟩
    · rw [res_id (isKV_univC _), El_univC]; exact hmem
    · rw [Comp_univC]
      exact ⟨⟨⟨l, .inr rfl⟩, by rw [hsem, res_id (isKV_univC _)]⟩, TyEq.refl _⟩
  | @HasTy0.cumul _ Ψ Φ Γ A l h0 h1 => fun hc k c => by
    have ih := fund_ty h1 hc k c
    have hty := c.ty hW (HasTy0.cumul h0 h1)
    have hsem : ∀ l', semK S k (.univ l') = univC k l' := fun l' => rfl
    show (Comp S (semK S k (.univ (l + 1))) k k (Hom.id k)).el (.univ (l + 1)) _
    change (Comp S (semK S k (.univ l)) k k (Hom.id k)).el (.univ l) _ at ih
    rw [hsem, Comp_univC] at ih ⊢
    dsimp only at ih ⊢
    obtain ⟨-, -, -, hm, hrt⟩ := ih
    have hm' := ZFSet.mem_sep.1 hm
    have hmem : semK S k (A.subst c.γ c.σ.τ) ∈ ZFSet.sep (WF (l + 1) k) (Vt (l + 1)) :=
      ZFSet.mem_sep.2 ⟨Vt_subset_succ l (by unfold maxLevel at h0; omega) hm'.1, hm'.2.cumul⟩
    refine ⟨hty, ?_, TyEq.refl _, hmem, hrt⟩
    rw [res_id (isKV_univC _), El_univC]; exact hmem
  | @HasTy0.pi _ Ψ Φ Γ A B l h0 h1 => fun hc k c => by
    sorry
  | @HasTy0.lam _ Ψ Φ Γ A B t l h0 h1 => fun hc k c => by
    sorry
  | @HasTy0.app _ Ψ Φ Γ A B f a h0 h1 => fun hc k c => by
    sorry
  | @HasTy0.sigma _ Ψ Φ Γ A B l h0 h1 => fun hc k c => by
    sorry
  | @HasTy0.pair _ Ψ Φ Γ A B a b l h0 h1 h2 => fun hc k c => by
    sorry
  | @HasTy0.fst _ Ψ Φ Γ A B p h0 => fun hc k c => by
    sorry
  | @HasTy0.snd _ Ψ Φ Γ A B p h0 => fun hc k c => by
    sorry
  | @HasTy0.path _ Ψ Φ Γ A a b l h0 h1 h2 => fun hc k c => by
    sorry
  | @HasTy0.plam _ Ψ Φ Γ A a b t l h0 h1 h2 h3 => fun hc k c => by
    sorry
  | @HasTy0.papp _ Ψ Φ Γ A a b p r h0 h1 => fun hc k c => by
    sorry
  | @HasTy0.ipi _ Ψ Φ Γ A l h0 h1 => fun hc k c => by
    sorry
  | @HasTy0.ilam _ Ψ Φ Γ A t l h0 h1 => fun hc k c => by
    sorry
  | @HasTy0.iapp _ Ψ Φ Γ A p r h0 h1 => fun hc k c => by
    sorry
  | @HasTy0.split _ Ψ Φ Γ A φ ψ t u l h0 h1 h2 h3 h4 h5 h6 => fun hc k c => by
    sorry
  | @HasTy0.abort _ Ψ Φ Γ A l h0 h1 => fun hc k c => by
    sorry
  | @HasTy0.transp _ Ψ Φ Γ A φ a l h0 h1 h2 h3 => fun hc k c => by
    sorry
  | @HasTy0.hcomp _ Ψ Φ Γ A φ u a l h0 h1 h2 h3 h4 => fun hc k c => by
    sorry
  | @HasTy0.glue _ Ψ Φ Γ A φ T e l h0 h1 h2 h3 => fun hc k c => by
    sorry
  | @HasTy0.glueEl _ Ψ Φ Γ A φ T e t a l h0 h1 h2 h3 h4 => fun hc k c => by
    sorry
  | @HasTy0.unglue _ Ψ Φ Γ A φ T e g l h0 h1 h2 h3 => fun hc k c => by
    sorry
  | @HasTy0.data _ Ψ Φ Γ d D ps h0 h1 h2 => fun hc k c => by
    have ih := fund_tele h2
    sorry
  | @HasTy0.con _ Ψ Φ Γ d D c C ps args rs h0 h1 h2 h3 h4 h5 h6 h7 => fun hc k c => by
    have ihp := fund_tele h4
    have iha := fund_tele h5
    sorry
  | @HasTy0.elim _ Ψ Φ Γ d D ps P bs t m h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => fun hc k c => by
    have iht := fund_ty h9
    sorry

theorem fund_tele {Ψ Φ Γ ts Δ prev} : HasTele0 S Ψ Φ Γ ts Δ prev → ts.ConstsLt n → ∀ k (c : CSub S Ψ Φ Γ k),
    TeleComp S k (ts.subst c.γ c.σ.τ) Δ (prev.map (·.subst c.γ c.σ.τ))
  | @HasTele0.nil _ Ψ Φ Γ prev h0 => fun _ k c => by simp [TeleComp, Tm.subst]
  | @HasTele0.cons _ Ψ Φ Γ a as A Δ prev h0 h1 => fun hc k c => by
    have iha := fund_ty h0 hc.1 k c
    have ihas := fund_tele h1 hc.2 k c
    sorry

end

end

end Model.Canon
