import Model.Canon.Syn

/-!
# Canonicity: computability is stable under restriction
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' k'' m : ℕ}

/-! ### Interval substitution of the type and term formers -/

theorem isub_pi (A B : Tm) (σ : ISub k' k) : (Tm.pi A B).isub σ = .pi (A.isub σ) (B.isub σ) := by
  simp only [Tm.isub, Tm.subst, up_var]

theorem isub_sigma (A B : Tm) (σ : ISub k' k) : (Tm.sigma A B).isub σ = .sigma (A.isub σ) (B.isub σ) := by
  simp only [Tm.isub, Tm.subst, up_var]

theorem isub_app (f a : Tm) (σ : ISub k' k) : (Tm.app f a).isub σ = .app (f.isub σ) (a.isub σ) := rfl
theorem isub_fst (p : Tm) (σ : ISub k' k) : (Tm.fst p).isub σ = .fst (p.isub σ) := rfl
theorem isub_snd (p : Tm) (σ : ISub k' k) : (Tm.snd p).isub σ = .snd (p.isub σ) := rfl
theorem isub_univ (l : ℕ) (σ : ISub k' k) : (Tm.univ l).isub σ = .univ l := rfl

theorem isub_inst (B a : Tm) (σ : ISub k' k) : (B.inst a).isub σ = (B.isub σ).inst (a.isub σ) := by
  simp only [Tm.isub, Tm.inst, subst_subst]
  congr 1
  · funext n; cases n <;> rfl
  · funext i; exact (I_subst_var _).symm

theorem ISub.comp_hom (f : Hom k m) (σ : ISub k' k) (σ' : ISub k'' k') :
    (f.comp σ.hom).comp σ'.hom = f.comp (σ.comp σ').hom := by
  rw [ISub.hom_comp, Hom.comp_assoc]


theorem ISub.up_comp (σ : ISub k' k) (σ' : ISub k'' k') : (σ.comp σ').up = σ.up.comp σ'.up := by
  ext i; simp only [ISub.up, ISub.comp]; exact (I_up_comp _ _ i).symm

theorem lift_hom_comp (f : Hom k m) (σ : ISub k' k) (σ' : ISub k'' k') :
    (Hom.lift (f.comp σ.hom)).comp σ'.up.hom = (Hom.lift f).comp (σ.comp σ').up.hom := by
  rw [ISub.hom_up, ISub.hom_up, ← Hom.lift_comp, Hom.comp_assoc, Hom.lift_comp, ISub.hom_comp]

theorem lift_cons (f : Hom k m) (σ : ISub k' k) (r : I) (hr : r.Scoped k'') (σ' : ISub k'' k') :
    (Hom.lift (f.comp σ.hom)).comp (ISub.cons r hr σ').hom = (Hom.lift f).comp (ISub.cons r hr (σ.comp σ')).hom := by
  rw [ISub.hom_cons, ISub.hom_cons, lift_comp_snoc, lift_comp_snoc, ISub.comp_hom]

theorem isub_path (L a b : Tm) (σ : ISub k' k) :
    (Tm.path L a b).isub σ = .path (L.isub σ.up) (a.isub σ) (b.isub σ) := rfl
theorem isub_ipi (L : Tm) (σ : ISub k' k) : (Tm.ipi L).isub σ = .ipi (L.isub σ.up) := rfl
theorem isub_papp (p : Tm) (r : I) (σ : ISub k' k) : (Tm.papp p r).isub σ = .papp (p.isub σ) (r.subst σ.τ) := rfl

/-- Computability is Kripke: stable under every interval substitution. -/
def KR (S : Sig) (m : ℕ) (X : V) : Prop :=
  ∀ k (f : Hom k m) k' (σ : ISub k' k) (A t : Tm),
    ((Comp S X m k f).ty A → (Comp S X m k' (f.comp σ.hom)).ty (A.isub σ)) ∧
    ((Comp S X m k f).el A t → (Comp S X m k' (f.comp σ.hom)).el (A.isub σ) (t.isub σ))

variable (hW : WfSig S)
include hW

theorem semK_isubTy {A : Tm} (hA : IsTyK S k A) (σ : ISub k' k) :
    semK S k' (A.isub σ) = res σ.hom (semK S k A) := by
  obtain ⟨l, hA | rfl⟩ := hA
  · exact semK_isubS hW hA σ
  · show semK S k' (.univ l) = res σ.hom (semK S k (.univ l))
    simp [semK, sem_univ, res_univC]

theorem mem_isub {X : V} (hX : Fib X m) {f : Hom k m} {t A : Tm} (ht : HasTy S k .one [] t A)
    (hmem : semK S k t ∈ El (res f X) (Hom.id k)) (σ : ISub k' k) :
    semK S k' (t.isub σ) ∈ El (res (f.comp σ.hom) X) (Hom.id k') := by
  rw [semK_isubS hW ht, El_res, Hom.comp_id]
  rw [El_res, Hom.comp_id] at hmem
  exact hX.elRes _ _ _ hmem _ _

theorem kr_piC {A B : V} (hX : Fib (piC m A B) m) (hA : A ≠ ∅) : KR S m (piC m A B) := by
  intro k f k' σ T t
  rw [Comp_piC A B hA, Comp_piC A B hA]
  constructor
  · rintro ⟨⟨hT, hsem⟩, A1, B1, hE, hall⟩
    refine ⟨⟨hT.isub hW σ, ?_⟩, A1.isub σ, B1.isub σ, ?_, fun k'' σ' => ?_⟩
    · rw [semK_isubTy hW hT σ, hsem, res_res]
    · have := hE.isub hW σ; rwa [isub_pi] at this
    · obtain ⟨h1, h2⟩ := hall k'' (σ.comp σ')
      rw [ISub.comp_hom, Tm.isub_isub]
      refine ⟨h1, fun a ha => ?_⟩
      rw [Tm.isub_isub]; exact h2 a ha
  · rintro ⟨ht, hmem, -, A1, B1, hE, hall⟩
    refine ⟨HasTy.isubS hW ht σ, mem_isub hW hX ht hmem σ, HasTy.isubS hW ht σ, A1.isub σ, B1.isub σ, ?_,
      fun k'' σ' a ha => ?_⟩
    · have := hE.isub hW σ; rwa [isub_pi] at this
    · rw [ISub.id_comp] at ha ⊢
      rw [ISub.comp_hom, Tm.isub_isub] at ha
      have := hall k'' (σ.comp σ') a (by rw [ISub.id_comp]; exact ha)
      rw [ISub.id_comp] at this
      rw [ISub.comp_hom, Tm.isub_isub, Tm.isub_isub]; exact this

theorem kr_sigmaC {A B : V} (hX : Fib (sigmaC m A B) m) (hA : A ≠ ∅) : KR S m (sigmaC m A B) := by
  intro k f k' σ T t
  rw [Comp_sigmaC A B hA, Comp_sigmaC A B hA]
  constructor
  · rintro ⟨⟨hT, hsem⟩, A1, B1, hE, hall⟩
    refine ⟨⟨hT.isub hW σ, ?_⟩, A1.isub σ, B1.isub σ, ?_, fun k'' σ' => ?_⟩
    · rw [semK_isubTy hW hT σ, hsem, res_res]
    · have := hE.isub hW σ; rwa [isub_sigma] at this
    · obtain ⟨h1, h2⟩ := hall k'' (σ.comp σ')
      rw [ISub.comp_hom, Tm.isub_isub]
      refine ⟨h1, fun a ha => ?_⟩
      rw [Tm.isub_isub]; exact h2 a ha
  · rintro ⟨ht, hmem, -, A1, B1, hE, hall⟩
    refine ⟨HasTy.isubS hW ht σ, mem_isub hW hX ht hmem σ, HasTy.isubS hW ht σ, A1.isub σ, B1.isub σ, ?_,
      fun k'' σ' => ?_⟩
    · have := hE.isub hW σ; rwa [isub_sigma] at this
    · have := hall k'' (σ.comp σ')
      simp only [ISub.id_comp, ISub.comp_hom, Tm.isub_isub] at this ⊢; exact this

theorem kr_pathC {L a0 a1 : V} (hX : Fib (pathC m L a0 a1) m) (hL : L ≠ ∅) : KR S m (pathC m L a0 a1) := by
  intro k f k' σ T t
  rw [Comp_pathC L a0 a1 hL, Comp_pathC L a0 a1 hL]
  constructor
  · rintro ⟨⟨hT, hsem⟩, L1, b0, b1, hE, hall⟩
    refine ⟨⟨hT.isub hW σ, ?_⟩, L1.isub σ.up, b0.isub σ, b1.isub σ, ?_, fun k'' σ' => ?_⟩
    · rw [semK_isubTy hW hT σ, hsem, res_res]
    · have := hE.isub hW σ; rwa [isub_path] at this
    · obtain ⟨h1, h2, h3⟩ := hall k'' (σ.comp σ')
      rw [lift_hom_comp, lift_cons, lift_cons, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, ← ISub.up_comp]
      exact ⟨h1, h2, h3⟩
  · rintro ⟨ht, hmem, -, L1, b0, b1, hE, hall⟩
    refine ⟨HasTy.isubS hW ht σ, mem_isub hW hX ht hmem σ, HasTy.isubS hW ht σ, L1.isub σ.up, b0.isub σ,
      b1.isub σ, ?_, fun k'' σ' r hr => ?_⟩
    · have := hE.isub hW σ; rwa [isub_path] at this
    · have := hall k'' (σ.comp σ') r hr
      simp only [ISub.id_comp] at this ⊢
      rw [lift_cons, Tm.isub_isub, Tm.isub_isub, ← ISub.up_comp]; exact this

theorem kr_ipiC {L : V} (hX : Fib (ipiC m L) m) (hL : L ≠ ∅) : KR S m (ipiC m L) := by
  intro k f k' σ T t
  rw [Comp_ipiC L hL, Comp_ipiC L hL]
  constructor
  · rintro ⟨⟨hT, hsem⟩, L1, hE, hall⟩
    refine ⟨⟨hT.isub hW σ, ?_⟩, L1.isub σ.up, ?_, fun k'' σ' => ?_⟩
    · rw [semK_isubTy hW hT σ, hsem, res_res]
    · have := hE.isub hW σ; rwa [isub_ipi] at this
    · have h1 := hall k'' (σ.comp σ')
      rw [lift_hom_comp, Tm.isub_isub, ← ISub.up_comp]; exact h1
  · rintro ⟨ht, hmem, -, L1, hE, hall⟩
    refine ⟨HasTy.isubS hW ht σ, mem_isub hW hX ht hmem σ, HasTy.isubS hW ht σ, L1.isub σ.up, ?_,
      fun k'' σ' r hr => ?_⟩
    · have := hE.isub hW σ; rwa [isub_ipi] at this
    · have := hall k'' (σ.comp σ') r hr
      simp only [ISub.id_comp] at this ⊢
      rw [lift_cons, Tm.isub_isub, Tm.isub_isub, ← ISub.up_comp]; exact this

theorem kr_emptyC : KR S m (emptyC m) := by
  intro k f k' σ T t
  rw [Comp_emptyC, Comp_emptyC]
  refine ⟨fun ⟨hT, hsem⟩ => ⟨hT.isub hW σ, ?_⟩, fun h => h⟩
  rw [semK_isubTy hW hT σ, hsem, res_res]

theorem kr_univC {l : ℕ} (ih : ∀ m' X, WF l m' X → KR S m' X) : KR S m (univC m l) := by
  intro k f k' σ T t
  rw [Comp_univC, Comp_univC]
  constructor
  · rintro ⟨⟨hT, hsem⟩, hE⟩
    refine ⟨⟨hT.isub hW σ, ?_⟩, ?_⟩
    · rw [semK_isubTy hW hT σ, hsem, res_res]
    · have := hE.isub hW σ; rwa [isub_univ] at this
  · rintro ⟨ht, hmem, hE, hm, hty⟩
    have hm' : semK S k' (t.isub σ) ∈ ZFSet.sep (WF l k') (Vt l) := by
      rw [ZFSet.mem_sep] at hm ⊢
      rw [semK_isubS hW ht]
      exact ⟨res_mem_Vt hm.1 _, hm.2.res _⟩
    refine ⟨HasTy.isubS hW ht σ, ?_, by have := hE.isub hW σ; rwa [isub_univ] at this, hm', ?_⟩
    · rw [semK_isubS hW ht, El_res, Hom.comp_id]
      rw [El_res, Hom.comp_id] at hmem
      exact (WF.fib (show WF (l + 1) m (univC m l) from wf_univC)).elRes _ _ _ hmem _ _
    · have hY : WF l k (semK S k t) := (ZFSet.mem_sep.1 hm).2
      have := ((ih k _ hY) k (Hom.id k) k' σ t t).1 hty
      rw [Hom.id_comp] at this
      rw [semK_isubS hW ht, ← Comp_eq_res (IsKV.ne_empty hY.fib.kv) σ.hom]
      exact this

end

end Model.Canon
