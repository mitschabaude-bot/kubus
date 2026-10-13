import Model.InterpLemmas

/-!
# Basic equations for the interpretation of the type and term formers
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

/-- The interval environment of a point of a context weakened by an interval variable. -/
def IEnv.tail (ρ : IEnv m) : IEnv m := fun i => ρ (i + 1)

theorem ival_shift (ρ : IEnv m) (r : I) : ival ρ r.shift = ival ρ.tail r := by
  rw [I.shift, ival_ren]; rfl

theorem IEnv.tail_restr (ρ : IEnv m) (f : Hom k m) : (ρ.restr f).tail = ρ.tail.restr f := rfl

theorem IEnv.tail_cons (ρ : IEnv m) (r : DM m) : (ρ.cons r).tail = ρ := rfl

theorem sem_dshift_tail (t : Tm) (ρ : IEnv m) (γ : ℕ → V) : sem S t.dshift m ρ γ = sem S t m ρ.tail γ := by
  rw [Tm.dshift, sem_ren]; rfl

@[simp] theorem sem_univ (l : ℕ) (ρ : IEnv m) (γ : ℕ → V) : sem S (.univ l) m ρ γ = univC m l := rfl

@[simp] theorem sem_var (x : ℕ) (ρ : IEnv m) (γ : ℕ → V) : sem S (.var x) m ρ γ = γ x := rfl

theorem TEnv.restr_id_of_kv {γ : ℕ → V} (h : ∀ x, IsKV m (γ x)) : TEnv.restr γ (Hom.id m) = γ := by
  funext x; exact res_id (h x)

theorem sem_pi {A B : Tm} {ρ : IEnv m} {γ : ℕ → V} (hA : IsKV m (sem S A m ρ γ)) :
    sem S (.pi A B) m ρ γ = piC m (sem S A m ρ γ)
      (famV m (sem S A m ρ γ) fun k f a => sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)) := by
  simp only [sem, interp] at hA ⊢; rw [if_pos hA]

theorem kv_of_sem_pi {A B : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : sem S (.pi A B) m ρ γ ≠ ∅) :
    IsKV m (sem S A m ρ γ) := by
  simp only [sem, interp] at h ⊢; split at h
  · assumption
  · exact absurd rfl h

theorem sem_lam (A t : Tm) (ρ : IEnv m) (γ : ℕ → V) :
    sem S (.lam A t) m ρ γ = lamV m (fun _ f => El (sem S A m ρ γ) f)
      (fun k f a => sem S t k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)) := rfl

theorem sem_app_of_nat {f a : Tm} {ρ : IEnv m} {γ : ℕ → V} (ha : Natural S a m ρ γ) :
    sem S (.app f a) m ρ γ = appV m (sem S f m ρ γ) (sem S a m ρ γ) := by
  simp only [sem, interp]; exact if_pos ha

theorem sem_sigma {A B : Tm} {ρ : IEnv m} {γ : ℕ → V} (hA : IsKV m (sem S A m ρ γ)) :
    sem S (.sigma A B) m ρ γ = sigmaC m (sem S A m ρ γ)
      (famV m (sem S A m ρ γ) fun k f a => sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)) := by
  simp only [sem, interp] at hA ⊢; rw [if_pos hA]

theorem kv_of_sem_sigma {A B : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : sem S (.sigma A B) m ρ γ ≠ ∅) :
    IsKV m (sem S A m ρ γ) := by
  simp only [sem, interp] at h ⊢; split at h
  · assumption
  · exact absurd rfl h

theorem sem_pair_of_kv {a b : Tm} {ρ : IEnv m} {γ : ℕ → V} (ha : IsKV m (sem S a m ρ γ))
    (hb : IsKV m (sem S b m ρ γ)) : sem S (.pair a b) m ρ γ = pairV m (sem S a m ρ γ) (sem S b m ρ γ) := by
  simp only [sem, interp] at ha hb ⊢; rw [if_pos ⟨ha, hb⟩]

theorem kv_of_sem_pair {a b : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : sem S (.pair a b) m ρ γ ≠ ∅) :
    IsKV m (sem S a m ρ γ) ∧ IsKV m (sem S b m ρ γ) := by
  simp only [sem, interp] at h ⊢; split at h
  · assumption
  · exact absurd rfl h

theorem sem_fst (p : Tm) (ρ : IEnv m) (γ : ℕ → V) : sem S (.fst p) m ρ γ = fstV m (sem S p m ρ γ) := rfl

theorem sem_snd (p : Tm) (ρ : IEnv m) (γ : ℕ → V) : sem S (.snd p) m ρ γ = sndV m (sem S p m ρ γ) := rfl

theorem IEnv.eq_cons_tail (ρ : IEnv m) : ρ = ρ.tail.cons (ρ 0) := by funext i; cases i <;> rfl

theorem IEnv.exists_cons (ρ : IEnv m) : ∃ ρ' r, ρ = IEnv.cons ρ' r := ⟨_, _, ρ.eq_cons_tail⟩

@[simp] theorem ival_zero (ρ : IEnv m) : ival ρ .zero = DM.zero m := by ext p; simp [I.eval]

@[simp] theorem ival_one (ρ : IEnv m) : ival ρ .one = DM.one m := by ext p; simp [I.eval]

/-- The line at the generic point, `⟦A⟧(ρ.ext, γ.wk)`. -/
abbrev lineV (S : Sig) (A : Tm) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V) : V :=
  sem S A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))

theorem line_endpt {A : Tm} {ρ : IEnv m} {γ : ℕ → V} (hγ : ∀ x, IsKV m (γ x))
    (hN : Natural S A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))) (r : DM m) :
    sem S A m (ρ.cons r) γ = res (Hom.endpt m r) (lineV S A m ρ γ) := by
  rw [← hN m (Hom.endpt m r), IEnv.ext_restr_endpt, TEnv.restr_restr, Hom.wk_comp_endpt,
    TEnv.restr_id_of_kv hγ]

theorem line_endpt_nat {A : Tm} {ρ : IEnv m} {γ : ℕ → V} (hγ : ∀ x, IsKV m (γ x))
    (hN : Natural S A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))) (r : DM m) :
    Natural S A m (ρ.cons r) γ := by
  have := hN.restr (Hom.endpt m r)
  rwa [IEnv.ext_restr_endpt, TEnv.restr_restr, Hom.wk_comp_endpt, TEnv.restr_id_of_kv hγ] at this

theorem line_restr {A : Tm} {ρ : IEnv m} {γ : ℕ → V}
    (hN : Natural S A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))) (f : Hom k m) :
    lineV S A k (ρ.restr f) (TEnv.restr γ f) = res (Hom.lift f) (lineV S A m ρ γ) := by
  show sem S A (k + 1) _ (TEnv.restr (TEnv.restr γ f) (Hom.wk k)) = _
  rw [← hN (k + 1) (Hom.lift f), IEnv.ext_restr_lift, TEnv.restr_restr, TEnv.restr_restr,
    Hom.wk_comp_lift]

theorem line_restr_nat {A : Tm} {ρ : IEnv m} {γ : ℕ → V}
    (hN : Natural S A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))) (f : Hom k m) :
    Natural S A (k + 1) (ρ.restr f).ext (TEnv.restr (TEnv.restr γ f) (Hom.wk k)) := by
  have := hN.restr (Hom.lift f)
  rwa [IEnv.ext_restr_lift, TEnv.restr_restr, Hom.wk_comp_lift, ← TEnv.restr_restr] at this

theorem sem_path {A a b : Tm} {ρ : IEnv m} {γ : ℕ → V}
    (hN : Natural S A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))) (hL : IsKV (m + 1) (lineV S A m ρ γ))
    (ha : IsKV m (sem S a m ρ γ)) (hb : IsKV m (sem S b m ρ γ)) :
    sem S (.path A a b) m ρ γ = pathC m (lineV S A m ρ γ) (sem S a m ρ γ) (sem S b m ρ γ) := by
  simp only [sem, interp]; exact if_pos ⟨hN, hL, ha, hb⟩

theorem kv_of_sem_path {A a b : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : sem S (.path A a b) m ρ γ ≠ ∅) :
    Natural S A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) ∧ IsKV (m + 1) (lineV S A m ρ γ) ∧
      IsKV m (sem S a m ρ γ) ∧ IsKV m (sem S b m ρ γ) := by
  simp only [sem, interp] at h; split at h
  · assumption
  · exact absurd rfl h

theorem sem_plam {t : Tm} {ρ : IEnv m} {γ : ℕ → V}
    (h : Natural S t (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))) :
    sem S (.plam t) m ρ γ = pathOfLine m (lineV S t m ρ γ) := by
  simp only [sem, interp]; exact if_pos h

theorem nat_of_sem_plam {t : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : sem S (.plam t) m ρ γ ≠ ∅) :
    Natural S t (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) := by
  simp only [sem, interp] at h; split at h
  · assumption
  · exact absurd rfl h

theorem sem_papp (p : Tm) (r : I) (ρ : IEnv m) (γ : ℕ → V) :
    sem S (.papp p r) m ρ γ = pappV m (sem S p m ρ γ) (ival ρ r) := rfl

end

end Model
