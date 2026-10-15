import Model.Whnf.Fund2Aux

/-!
# Substitution for semantic validity

`Valid2` is stable under the substitutions the contracta of the computation rules are built with:
term renamings along context embeddings (`valid_ren`, e.g. weakening), interval substitutions of the
innermost interval variables (`valid_dsub`, e.g. `dinst`, `bind2`, the reversal of a line), and the
instantiation of the innermost term variable (`valid_inst`). Each pulls related closing substitutions
of the target back to the source.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' : ℕ}

/-! ### Term renamings -/

/-- Pulling a related substitution back along a term renaming that embeds `Γ` into `Δ`. -/
def CSub2.ren {Ψ : ℕ} {Φ : I} {Γ Δ : Ctx} (ρ : ℕ → ℕ)
    (hρ : ∀ x A, Γ.lookup x = some A → Δ.lookup (ρ x) = some (A.ren ρ id)) (c : CSub2 S Ψ Φ Δ k) :
    CSub2 S Ψ Φ Γ k where
  σ := c.σ
  σ' := c.σ'
  hσ := c.hσ
  γ x := c.γ (ρ x)
  γ' x := c.γ' (ρ x)
  hγ y := c.hγ (ρ y)
  hγ' y := c.hγ' (ρ y)
  face := c.face
  look x A h := by
    have := c.look (ρ x) _ (hρ x A h)
    rwa [subst_ren] at this
  lookT x A h k' ρ' τ1 τ2 h1 h2 b1 b2 := by
    have := c.lookT (ρ x) _ (hρ x A h) k' ρ' τ1 τ2 h1 h2 b1 b2
    rw [subst_ren, subst_ren] at this
    convert this using 2 <;> (funext y; cases b1 <;> cases b2 <;> rfl)

theorem CSub2.ren_L {Ψ : ℕ} {Φ : I} {Γ Δ : Ctx} (ρ : ℕ → ℕ)
    (hρ : ∀ x A, Γ.lookup x = some A → Δ.lookup (ρ x) = some (A.ren ρ id)) (c : CSub2 S Ψ Φ Δ k) (t : Tm) :
    (c.ren ρ hρ).L t = c.L (t.ren ρ id) := by
  simp only [CSub2.L, CSub2.ren, subst_ren]; rfl

theorem CSub2.ren_R {Ψ : ℕ} {Φ : I} {Γ Δ : Ctx} (ρ : ℕ → ℕ)
    (hρ : ∀ x A, Γ.lookup x = some A → Δ.lookup (ρ x) = some (A.ren ρ id)) (c : CSub2 S Ψ Φ Δ k) (t : Tm) :
    (c.ren ρ hρ).R t = c.R (t.ren ρ id) := by
  simp only [CSub2.R, CSub2.ren, subst_ren]; rfl

/-- Validity along a term renaming that embeds the contexts. -/
theorem valid_ren {Ψ : ℕ} {Φ : I} {Γ Δ : Ctx} (ρ : ℕ → ℕ)
    (hρ : ∀ x A, Γ.lookup x = some A → Δ.lookup (ρ x) = some (A.ren ρ id)) {t u A : Tm}
    (h : Valid2 S Ψ Φ Γ t u A) : Valid2 S Ψ Φ Δ (t.ren ρ id) (u.ren ρ id) (A.ren ρ id) := by
  intro k c
  have := h k (c.ren ρ hρ)
  rwa [CSub2.ren_L, CSub2.ren_L, CSub2.ren_R, CSub2.ren_R] at this

theorem lookup_shift_ren {Γ : Ctx} {B : Tm} : ∀ x A, Γ.lookup x = some A →
    Ctx.lookup (B :: Γ) (x + 1) = some (A.ren (· + 1) id) := by
  intro x A h
  simp only [Ctx.lookup, h, Option.map_some]
  rfl

/-- Weakening by a term variable. -/
theorem valid_wk {Ψ : ℕ} {Φ : I} {Γ : Ctx} (B : Tm) {t u A : Tm} (h : Valid2 S Ψ Φ Γ t u A) :
    Valid2 S Ψ Φ (B :: Γ) t.shift u.shift A.shift :=
  valid_ren (· + 1) lookup_shift_ren h

/-! ### Interval substitutions of the innermost interval variables -/

/-- A context weakened by `n` interval variables. -/
def Ctx.dren (n : ℕ) (Γ : Ctx) : Ctx := Γ.map (·.ren id (· + n))

theorem Ctx.lookup_dren (n : ℕ) (Γ : Ctx) (x : ℕ) : (Ctx.dren n Γ).lookup x = (Γ.lookup x).map (·.ren id (· + n)) :=
  lookup_map (fun t => by simp only [Tm.shift, ren_ren]; congr 1) x

theorem Ctx.dren_zero (Γ : Ctx) : Ctx.dren 0 Γ = Γ := by
  simp only [Ctx.dren]
  conv_rhs => rw [← List.map_id Γ]
  congr 1; funext t; simp [ren_eq_subst, subst_var]

theorem Ctx.dren_one (Γ : Ctx) : Ctx.dren 1 Γ = Γ.dshift := rfl

theorem Ctx.dren_two (Γ : Ctx) : Ctx.dren 2 Γ = Γ.dshift.dshift := by
  simp only [Ctx.dren, Ctx.dshift, List.map_map]
  congr 1; funext t; simp only [Function.comp, Tm.dshift, ren_ren]; rfl

/-- The pulled-back interval substitution. -/
def dsubISub {n m Ψ0 : ℕ} (τ : ℕ → I) (hτ : ∀ i < n, (τ i).Scoped (Ψ0 + m))
    (hτs : ∀ i, τ (i + n) = .var (i + m)) (σ0 : ISub k (Ψ0 + m)) : ISub k (Ψ0 + n) :=
  ⟨fun i => if i < Ψ0 + n then (τ i).subst σ0.τ else .zero, fun i hi => by
    dsimp only; rw [if_pos hi]
    by_cases hin : i < n
    · exact I.scoped_subst (hτ i hin) σ0.sc
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + n := ⟨i - n, by omega⟩
      rw [hτs]; exact σ0.sc _ (by omega), fun i hi => by dsimp only; rw [if_neg (by omega)]⟩

theorem dsubISub_shift {n m Ψ0 : ℕ} (τ : ℕ → I) (hτ : ∀ i < n, (τ i).Scoped (Ψ0 + m))
    (hτs : ∀ i, τ (i + n) = .var (i + m)) (σ0 : ISub k (Ψ0 + m)) (i : ℕ) :
    (dsubISub τ hτ hτs σ0).τ (i + n) = σ0.τ (i + m) := by
  show (if i + n < Ψ0 + n then (τ (i + n)).subst σ0.τ else .zero) = _
  by_cases h : i + n < Ψ0 + n
  · rw [if_pos h, hτs]; rfl
  · rw [if_neg h, σ0.hi _ (by omega)]

theorem dsubISub_lt {n m Ψ0 : ℕ} (τ : ℕ → I) (hτ : ∀ i < n, (τ i).Scoped (Ψ0 + m))
    (hτs : ∀ i, τ (i + n) = .var (i + m)) (σ0 : ISub k (Ψ0 + m)) {i : ℕ} (hi : i < Ψ0 + n) :
    (dsubISub τ hτ hτs σ0).τ i = (τ i).subst σ0.τ := if_pos hi

/-- Pulling a related substitution back along two pointwise equal interval substitutions of the innermost
variables. -/
def CSub2.dsub2 {n m Ψ0 : ℕ} {Φs Φ' : I} {Γ0 : Ctx} (τ τ' : ℕ → I) (hτ : ∀ i < n, (τ i).Scoped (Ψ0 + m))
    (hτs : ∀ i, τ (i + n) = .var (i + m)) (hτ' : ∀ i < n, (τ' i).Scoped (Ψ0 + m))
    (hτs' : ∀ i, τ' (i + n) = .var (i + m)) (heq : ∀ i < n, I.Eq (τ i) (τ' i)) (hΦs : Φs.Scoped (Ψ0 + n))
    (hent : I.Entails Φ' (Φs.subst τ)) (c : CSub2 S (Ψ0 + m) Φ' (Ctx.dren m Γ0) k) :
    CSub2 S (Ψ0 + n) Φs (Ctx.dren n Γ0) k where
  σ := dsubISub τ hτ hτs c.σ
  σ' := dsubISub τ' hτ' hτs' c.σ'
  hσ i := by
    show I.Eq (if i < Ψ0 + n then (τ i).subst c.σ.τ else .zero) (if i < Ψ0 + n then (τ' i).subst c.σ'.τ else .zero)
    split
    · rename_i hi
      refine I_eq_trans (I_eq_subst_congr c.hσ _) (I_eq_subst ?_ _)
      by_cases hin : i < n
      · exact heq i hin
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + n := ⟨i - n, by omega⟩
        rw [hτs, hτs']; exact I_eq_refl _
    · exact I_eq_refl _
  γ := c.γ
  γ' := c.γ'
  hγ := c.hγ
  hγ' := c.hγ'
  face := by
    rw [I_subst_congr_scoped (fun i hi => dsubISub_lt τ hτ hτs c.σ hi) hΦs, ← I_subst_subst]
    exact ent_trans c.face (ent_subst hent c.σ.τ)
  look x A h := by
    rw [Ctx.lookup_dren, Option.map_eq_some_iff] at h
    obtain ⟨A0, hA0, rfl⟩ := h
    have := c.look x (A0.ren id (· + m)) (by rw [Ctx.lookup_dren, hA0]; rfl)
    rw [subst_ren] at this ⊢
    convert this using 2
    funext i; exact dsubISub_shift τ hτ hτs c.σ i
  lookT x A h k' ρ τ1 τ2 h1 h2 b1 b2 := by
    rw [Ctx.lookup_dren, Option.map_eq_some_iff] at h
    obtain ⟨A0, hA0, rfl⟩ := h
    -- realize the source substitutions as target ones
    let lift : ISub k' (Ψ0 + n) → ISub k' (Ψ0 + m) := fun τ1 =>
      ⟨fun i => if i < m then (c.σ.comp ρ).τ i else τ1.τ (i - m + n), fun i hi => by
        dsimp only; split
        · exact (c.σ.comp ρ).sc i hi
        · exact τ1.sc _ (by omega), fun i hi => by dsimp only; rw [if_neg (by omega)]; exact τ1.hi _ (by omega)⟩
    have hlift : ∀ τ1 : ISub k' (Ψ0 + n), INear ((dsubISub τ hτ hτs c.σ).comp ρ) τ1 →
        INear (c.σ.comp ρ) (lift τ1) := by
      intro τ1 hn i
      show I.Eq ((c.σ.comp ρ).τ i) (if i < m then (c.σ.comp ρ).τ i else τ1.τ (i - m + n))
      split
      · exact I_eq_refl _
      · have := hn (i - m + n)
        have e : ((dsubISub τ hτ hτs c.σ).comp ρ).τ (i - m + n) = (c.σ.comp ρ).τ i := by
          show ((dsubISub τ hτ hτs c.σ).τ (i - m + n)).subst ρ.τ = (c.σ.τ i).subst ρ.τ
          rw [dsubISub_shift]; congr 2; omega
        rwa [e] at this
    have hsh : ∀ τ1 : ISub k' (Ψ0 + n), (fun i => (lift τ1).τ (i + m)) = fun i => τ1.τ (i + n) := by
      intro τ1; funext i
      show (if i + m < m then _ else τ1.τ (i + m - m + n)) = _
      rw [if_neg (by omega)]; congr 1; omega
    have := c.lookT x (A0.ren id (· + m)) (by rw [Ctx.lookup_dren, hA0]; rfl) k' ρ (lift τ1) (lift τ2)
      (hlift τ1 h1) (hlift τ2 h2) b1 b2
    rw [subst_ren, subst_ren] at this ⊢
    rwa [hsh, hsh] at this

/-- Pulling a related substitution back along an interval substitution of the innermost variables. -/
abbrev CSub2.dsub {n m Ψ0 : ℕ} {Φs Φ' : I} {Γ0 : Ctx} (τ : ℕ → I) (hτ : ∀ i < n, (τ i).Scoped (Ψ0 + m))
    (hτs : ∀ i, τ (i + n) = .var (i + m)) (hΦs : Φs.Scoped (Ψ0 + n))
    (hent : I.Entails Φ' (Φs.subst τ)) (c : CSub2 S (Ψ0 + m) Φ' (Ctx.dren m Γ0) k) :
    CSub2 S (Ψ0 + n) Φs (Ctx.dren n Γ0) k :=
  c.dsub2 τ τ hτ hτs hτ hτs (fun _ _ => I_eq_refl _) hΦs hent

theorem CSub2.dsub_L {n m Ψ0 : ℕ} {Φs Φ' : I} {Γ0 : Ctx} (τ : ℕ → I) (hτ : ∀ i < n, (τ i).Scoped (Ψ0 + m))
    (hτs : ∀ i, τ (i + n) = .var (i + m)) (hΦs : Φs.Scoped (Ψ0 + n))
    (hent : I.Entails Φ' (Φs.subst τ)) (c : CSub2 S (Ψ0 + m) Φ' (Ctx.dren m Γ0) k)
    {t : Tm} {N : ℕ} (ht : t.closedB N (Ψ0 + n) = true) :
    (c.dsub τ hτ hτs hΦs hent).L t = c.L (t.dsubst τ) := by
  simp only [CSub2.L, CSub2.dsub, Tm.dsubst, subst_subst]
  exact closed_subst_eq t N (Ψ0 + n) _ _ _ _ ht (fun x _ => rfl) fun i hi => dsubISub_lt τ hτ hτs c.σ hi

theorem CSub2.dsub_R {n m Ψ0 : ℕ} {Φs Φ' : I} {Γ0 : Ctx} (τ : ℕ → I) (hτ : ∀ i < n, (τ i).Scoped (Ψ0 + m))
    (hτs : ∀ i, τ (i + n) = .var (i + m)) (hΦs : Φs.Scoped (Ψ0 + n))
    (hent : I.Entails Φ' (Φs.subst τ)) (c : CSub2 S (Ψ0 + m) Φ' (Ctx.dren m Γ0) k)
    {t : Tm} {N : ℕ} (ht : t.closedB N (Ψ0 + n) = true) :
    (c.dsub τ hτ hτs hΦs hent).R t = c.R (t.dsubst τ) := by
  simp only [CSub2.R, CSub2.dsub, Tm.dsubst, subst_subst]
  exact closed_subst_eq t N (Ψ0 + n) _ _ _ _ ht (fun x _ => rfl) fun i hi => dsubISub_lt τ hτ hτs c.σ' hi

/-- Validity along an interval substitution of the innermost interval variables. -/
theorem valid_dsub {n m Ψ0 : ℕ} {Φs Φ' : I} {Γ0 : Ctx} (τ : ℕ → I) (hτ : ∀ i < n, (τ i).Scoped (Ψ0 + m))
    (hτs : ∀ i, τ (i + n) = .var (i + m)) (hΦs : Φs.Scoped (Ψ0 + n))
    (hent : I.Entails Φ' (Φs.subst τ)) {t u A : Tm} {N : ℕ}
    (ht : t.closedB N (Ψ0 + n) = true) (hu : u.closedB N (Ψ0 + n) = true) (hA : A.closedB N (Ψ0 + n) = true)
    (h : Valid2 S (Ψ0 + n) Φs (Ctx.dren n Γ0) t u A) :
    Valid2 S (Ψ0 + m) Φ' (Ctx.dren m Γ0) (t.dsubst τ) (u.dsubst τ) (A.dsubst τ) := by
  intro k c
  have := h k (c.dsub τ hτ hτs hΦs hent)
  rwa [CSub2.dsub_L τ hτ hτs hΦs hent c ht, CSub2.dsub_L τ hτ hτs hΦs hent c hA,
    CSub2.dsub_R τ hτ hτs hΦs hent c hu, CSub2.dsub_R τ hτ hτs hΦs hent c hA] at this

theorem CSub2.dsub2_R {n m Ψ0 : ℕ} {Φs Φ' : I} {Γ0 : Ctx} (τ τ' : ℕ → I) (hτ : ∀ i < n, (τ i).Scoped (Ψ0 + m))
    (hτs : ∀ i, τ (i + n) = .var (i + m)) (hτ' : ∀ i < n, (τ' i).Scoped (Ψ0 + m))
    (hτs' : ∀ i, τ' (i + n) = .var (i + m)) (heq : ∀ i < n, I.Eq (τ i) (τ' i)) (hΦs : Φs.Scoped (Ψ0 + n))
    (hent : I.Entails Φ' (Φs.subst τ)) (c : CSub2 S (Ψ0 + m) Φ' (Ctx.dren m Γ0) k)
    {t : Tm} {N : ℕ} (ht : t.closedB N (Ψ0 + n) = true) :
    (c.dsub2 τ τ' hτ hτs hτ' hτs' heq hΦs hent).R t = c.R (t.dsubst τ') := by
  simp only [CSub2.R, CSub2.dsub2, Tm.dsubst, subst_subst]
  exact closed_subst_eq t N (Ψ0 + n) _ _ _ _ ht (fun x _ => rfl) fun i hi => dsubISub_lt τ' hτ' hτs' c.σ' hi

/-- Validity along two pointwise equal interval substitutions of the innermost interval variables. -/
theorem valid_dsub2 {n m Ψ0 : ℕ} {Φs Φ' : I} {Γ0 : Ctx} (τ τ' : ℕ → I) (hτ : ∀ i < n, (τ i).Scoped (Ψ0 + m))
    (hτs : ∀ i, τ (i + n) = .var (i + m)) (hτ' : ∀ i < n, (τ' i).Scoped (Ψ0 + m))
    (hτs' : ∀ i, τ' (i + n) = .var (i + m)) (heq : ∀ i < n, I.Eq (τ i) (τ' i)) (hΦs : Φs.Scoped (Ψ0 + n))
    (hent : I.Entails Φ' (Φs.subst τ)) {t u A : Tm} {N : ℕ}
    (ht : t.closedB N (Ψ0 + n) = true) (hu : u.closedB N (Ψ0 + n) = true) (hA : A.closedB N (Ψ0 + n) = true)
    (h : Valid2 S (Ψ0 + n) Φs (Ctx.dren n Γ0) t u A) :
    Valid2 S (Ψ0 + m) Φ' (Ctx.dren m Γ0) (t.dsubst τ) (u.dsubst τ') (A.dsubst τ) := by
  intro k c
  have := h k (c.dsub2 τ τ' hτ hτs hτ' hτs' heq hΦs hent)
  have eL : ∀ {x : Tm}, x.closedB N (Ψ0 + n) = true →
      (c.dsub2 τ τ' hτ hτs hτ' hτs' heq hΦs hent).L x = c.L (x.dsubst τ) := fun hx => by
    simp only [CSub2.L, CSub2.dsub2, Tm.dsubst, subst_subst]
    exact closed_subst_eq _ N (Ψ0 + n) _ _ _ _ hx (fun x _ => rfl) fun i hi => dsubISub_lt τ hτ hτs c.σ hi
  have hA' : RT2 S k (c.L (A.dsubst τ)) ((c.dsub2 τ τ' hτ hτs hτ' hτs' heq hΦs hent).R A) := by
    have := this.1; rwa [eL hA] at this
  rw [eL ht, eL hA, CSub2.dsub2_R τ τ' hτ hτs hτ' hτs' heq hΦs hent c hu] at this
  refine ⟨?_, this.2⟩
  have h1 := (h k (c.dsub τ hτ hτs hΦs hent)).1
  rwa [CSub2.dsub_L τ hτ hτs hΦs hent c hA, CSub2.dsub_R τ hτ hτs hΦs hent c hA] at h1

/-! ### Common instances of `valid_dsub` -/

theorem I_ren_add0 (Φ : I) : Φ.ren (· + 0) = Φ := I_subst_var Φ

theorem I_shift_inst0 (Φ : I) (r : I) : Φ.shift.subst (I.inst0 r) = Φ := by
  rw [I_shift_subst]; exact I_subst_var Φ

theorem valid_dwk' {Ψ : ℕ} {Φ : I} {Γ : Ctx} {t u A : Tm} {N : ℕ}
    (ht : t.closedB N Ψ = true) (hu : u.closedB N Ψ = true) (hA : A.closedB N Ψ = true) (hΦ : Φ.Scoped Ψ)
    (h : Valid2 S Ψ Φ Γ t u A) : Valid2 S (Ψ + 1) Φ.shift Γ.dshift t.dshift u.dshift A.dshift := by
  have h' : Valid2 S (Ψ + 0) Φ (Ctx.dren 0 Γ) t u A := by rwa [Ctx.dren_zero]
  have := valid_dsub (n := 0) (m := 1) (fun i => .var (i + 1)) (fun i hi => absurd hi (Nat.not_lt_zero _))
    (fun i => rfl) hΦ (ent_refl _) ht hu hA h'
  simpa only [Tm.dsubst, dshift_eq] using this

theorem valid_dinst' {Ψ : ℕ} {Φ : I} {Γ : Ctx} {t u A : Tm} {N : ℕ} (r : I) (hr : r.Scoped Ψ)
    (ht : t.closedB N (Ψ + 1) = true) (hu : u.closedB N (Ψ + 1) = true) (hA : A.closedB N (Ψ + 1) = true)
    (hΦ : Φ.Scoped Ψ) (h : Valid2 S (Ψ + 1) Φ.shift Γ.dshift t u A) :
    Valid2 S Ψ Φ Γ (t.dinst r) (u.dinst r) (A.dinst r) := by
  have := valid_dsub (n := 1) (m := 0) (Ψ0 := Ψ) (Φs := Φ.shift) (Φ' := Φ) (Γ0 := Γ) (I.inst0 r)
    (fun i hi => by rcases Nat.lt_one_iff.1 hi with rfl; exact hr)
    (fun i => rfl) (KubusCore.I.scoped_shift hΦ) (by rw [I_shift_inst0]; exact ent_refl _)
    ht hu hA h
  rwa [Ctx.dren_zero] at this

theorem valid_dsub11 {Ψ : ℕ} {Φs Φ' : I} {Γ : Ctx} {t u A : Tm} {N : ℕ} (τ : ℕ → I) (hτ0 : (τ 0).Scoped (Ψ + 1))
    (hτs : ∀ i, τ (i + 1) = .var (i + 1)) (hΦs : Φs.Scoped (Ψ + 1)) (hent : I.Entails Φ' (Φs.subst τ))
    (ht : t.closedB N (Ψ + 1) = true) (hu : u.closedB N (Ψ + 1) = true) (hA : A.closedB N (Ψ + 1) = true)
    (h : Valid2 S (Ψ + 1) Φs Γ.dshift t u A) :
    Valid2 S (Ψ + 1) Φ' Γ.dshift (t.dsubst τ) (u.dsubst τ) (A.dsubst τ) :=
  valid_dsub (n := 1) (m := 1) (Ψ0 := Ψ) (Γ0 := Γ) τ (fun i hi => by rcases Nat.lt_one_iff.1 hi with rfl; exact hτ0)
    hτs hΦs hent ht hu hA h

theorem valid_dsub12 {Ψ : ℕ} {Φs Φ' : I} {Γ : Ctx} {t u A : Tm} {N : ℕ} (τ : ℕ → I) (hτ0 : (τ 0).Scoped (Ψ + 2))
    (hτs : ∀ i, τ (i + 1) = .var (i + 2)) (hΦs : Φs.Scoped (Ψ + 1)) (hent : I.Entails Φ' (Φs.subst τ))
    (ht : t.closedB N (Ψ + 1) = true) (hu : u.closedB N (Ψ + 1) = true) (hA : A.closedB N (Ψ + 1) = true)
    (h : Valid2 S (Ψ + 1) Φs Γ.dshift t u A) :
    Valid2 S (Ψ + 1 + 1) Φ' Γ.dshift.dshift (t.dsubst τ) (u.dsubst τ) (A.dsubst τ) := by
  have := valid_dsub (n := 1) (m := 2) (Ψ0 := Ψ) (Γ0 := Γ) τ (fun i hi => by rcases Nat.lt_one_iff.1 hi with rfl; exact hτ0)
    hτs hΦs hent ht hu hA h
  rwa [Ctx.dren_two] at this

theorem valid_dsub22 {Ψ : ℕ} {Φs Φ' : I} {Γ : Ctx} {t u A : Tm} {N : ℕ} (τ : ℕ → I)
    (hτ : ∀ i < 2, (τ i).Scoped (Ψ + 2)) (hτs : ∀ i, τ (i + 2) = .var (i + 2)) (hΦs : Φs.Scoped (Ψ + 2))
    (hent : I.Entails Φ' (Φs.subst τ))
    (ht : t.closedB N (Ψ + 2) = true) (hu : u.closedB N (Ψ + 2) = true) (hA : A.closedB N (Ψ + 2) = true)
    (h : Valid2 S (Ψ + 1 + 1) Φs Γ.dshift.dshift t u A) :
    Valid2 S (Ψ + 1 + 1) Φ' Γ.dshift.dshift (t.dsubst τ) (u.dsubst τ) (A.dsubst τ) := by
  have h' : Valid2 S (Ψ + 2) Φs (Ctx.dren 2 Γ) t u A := by rw [Ctx.dren_two]; exact h
  have := valid_dsub (n := 2) (m := 2) (Ψ0 := Ψ) (Γ0 := Γ) τ hτ hτs hΦs hent ht hu hA h'
  rwa [Ctx.dren_two] at this

/-! ### Instantiation of the innermost term variable -/

theorem inst_subst_consT (t a : Tm) (σ : ℕ → Tm) (τ : ℕ → I) :
    (t.inst a).subst σ τ = t.subst (consT (a.subst σ τ) σ) τ := by
  simp only [Tm.inst, subst_subst]
  apply subst_congr
  · intro n; cases n <;> rfl
  · intro i; rfl

variable (hW : WfSig S)
include hW

/-- Validity of an instantiation, from the validity of the instantiated term and the argument. -/
theorem valid_inst {Ψ : ℕ} {Φ : I} {Γ : Ctx} {A B t u a a' : Tm} {l : ℕ}
    (hA : Valid2 S Ψ Φ Γ A A (.univ l)) (ha : Valid2 S Ψ Φ Γ a a' A) (h : Valid2 S Ψ Φ (A :: Γ) t u B) :
    Valid2 S Ψ Φ Γ (t.inst a) (u.inst a') (B.inst a) := by
  intro k c
  have haa := valid_trans hW ha (valid_symm hW ha)
  have hrob := CSub2.tyRob_of hW (fun k c => hA.tySelf hW c) c
  have h1 := h k (c.ext hW A (c.L a) (c.R a') (ha k c).2 hrob)
  have h2 := h k (c.ext hW A (c.L a) (c.R a) (haa k c).2 hrob)
  simp only [CSub2.L, CSub2.R, inst_subst_consT]
  exact ⟨h2.1, h1.2⟩

end

end Model.Whnf
