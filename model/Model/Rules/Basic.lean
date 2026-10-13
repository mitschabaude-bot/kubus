import Model.InterpLemmas

/-!
# Helpers for the rule lemmas

* the shape tag of a code, and inversion of well-formedness for universe codes;
* good codes (`TyCode`) are fibrant and stable under restriction;
* points of contexts: restriction, extension, interval weakening.
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

/-! ### Shape tags -/

/-- The tag of a code at its own stage. -/
def codeTag (m : ℕ) (c : V) : V := π1 (shapeOf c (Hom.id m))

@[simp] theorem codeTag_emptyC : codeTag m (emptyC m) = natZ tEmpty := by
  simp [codeTag, emptyC, emptyDatum, tagZ]

@[simp] theorem codeTag_piC (A B : V) : codeTag m (piC m A B) = natZ tPi := by
  simp [codeTag, piC, piDatum, tagZ]

@[simp] theorem codeTag_sigmaC (A B : V) : codeTag m (sigmaC m A B) = natZ tSigma := by
  simp [codeTag, sigmaC, sigmaDatum, tagZ]

@[simp] theorem codeTag_pathC (L a0 a1 : V) : codeTag m (pathC m L a0 a1) = natZ tPath := by
  simp [codeTag, pathC, pathDatum, tagZ]

@[simp] theorem codeTag_ipiC (L : V) : codeTag m (ipiC m L) = natZ tIPi := by
  simp [codeTag, ipiC, ipiDatum, tagZ]

@[simp] theorem codeTag_univC (l : ℕ) : codeTag m (univC m l) = natZ tUniv := by
  unfold univC univCode; simp [codeTag, univDatum, tagZ]

theorem codeTag_glueC {A : V} {φ : Cof m} {Tp ep : V} (hn : ¬ φ.holds) (hφ : φ.IsCof) :
    codeTag m (glueC m A φ Tp ep) = natZ tGlue := by
  unfold codeTag glueC
  rw [shapeOf_mkKV, hφ.restr_id, if_neg hn]
  simp [glueDatum, tagZ]

theorem univC_level_inj {l l' : ℕ} (h : univC m l = univC m l') : l = l' := by
  have := congrArg (fun c => shapeOf c (Hom.id m)) h
  unfold univC univCode at this
  simp only [shapeOf_mkKV, univDatum, π1_quad, tagZ_inj, natZ_inj, true_and] at this
  exact this

/-- Inversion: a well-formed code that is a universe is a smaller universe. -/
theorem WF.univ_lt {l l' : ℕ} (h : WF l' m (univC m l)) : l < l' := by
  generalize hc : univC m l = c at h
  have htag : codeTag m c = natZ tUniv := by rw [← hc]; simp
  unfold WF at h
  cases h with
  | empty => simp [tEmpty, tUniv] at htag
  | pi => simp [tPi, tUniv] at htag
  | sigma => simp [tSigma, tUniv] at htag
  | path => simp [tPath, tUniv] at htag
  | ipi => simp [tIPi, tUniv] at htag
  | @univ _ l'' hl'' =>
    rw [Ucodes_lt m hl''] at hc; rw [univC_level_inj hc]; exact hl''
  | glue _ hφ hn => rw [codeTag_glueC hn hφ] at htag; simp [tGlue, tUniv] at htag

/-! ### Good codes -/

theorem fib_univC' (l : ℕ) : Fib (univC m l) m :=
  fib_univC (fun k c hc => (wf_props l k c hc).1.kv) (fun k c hc n h => (wf_props l k c hc).2 n h)
    (fun _ _ hc _ h => res_mem_Vt hc h)

theorem TyCode.fib {c : V} (h : TyCode m c) : Fib c m := by
  obtain ⟨l, -, h | rfl⟩ := h
  · exact h.1.fib
  · exact fib_univC' l

theorem TyCode.res {c : V} (h : TyCode m c) (f : Hom k m) : TyCode k (res f c) := by
  obtain ⟨l, hl, h | rfl⟩ := h
  · exact ⟨l, hl, Or.inl ⟨h.1.res f, res_mem_Vt h.2 f⟩⟩
  · exact ⟨l, hl, Or.inr (res_univC l f)⟩

theorem TyCode.univ_le {l : ℕ} (h : TyCode m (univC m l)) : l ≤ maxLevel := by
  obtain ⟨l', hl', h | h⟩ := h
  · have := h.1.univ_lt; omega
  · rw [univC_level_inj h]; exact hl'

/-- An element of a universe of a good level is a good code. -/
theorem TyCode.of_mem_univ {l : ℕ} (hl : TyCode m (univC m l)) {c : V}
    (hc : c ∈ El (univC m l) (Hom.id m)) : TyCode m c := by
  rw [El_univC, ZFSet.mem_sep] at hc
  exact ⟨l, hl.univ_le, Or.inl ⟨hc.2, hc.1⟩⟩

end

end Model

/-! ### Syntax: renaming and lookup -/

namespace KubusCore

theorem Tm.upRen_comp (ρ1 ρ2 : ℕ → ℕ) : (fun x => Tm.upRen ρ2 (Tm.upRen ρ1 x)) = Tm.upRen (fun x => ρ2 (ρ1 x)) := by
  funext x; cases x <;> rfl

theorem I.ren_ren (r : I) (δ1 δ2 : ℕ → ℕ) : (r.ren δ1).ren δ2 = r.ren (fun i => δ2 (δ1 i)) := by
  induction r <;> simp_all [I.ren, I.subst]

theorem Tm.ren_ren : ∀ (t : Tm) (ρ1 δ1 ρ2 δ2 : ℕ → ℕ),
    (t.ren ρ1 δ1).ren ρ2 δ2 = t.ren (fun x => ρ2 (ρ1 x)) (fun i => δ2 (δ1 i)) := by
  intro t
  induction t <;> intros <;> simp_all [Tm.ren, I.ren_ren, Tm.upRen_comp]

theorem Tm.shift_dshift (t : Tm) : t.dshift.shift = t.shift.dshift := by
  simp only [Tm.shift, Tm.dshift, Tm.ren_ren]; rfl

theorem Ctx.lookup_dshift : ∀ (Γ : Ctx) (x : ℕ), Γ.dshift.lookup x = (Γ.lookup x).map Tm.dshift
  | [], _ => rfl
  | A :: _, 0 => by simp [Ctx.dshift, Ctx.lookup, Tm.shift_dshift]
  | _ :: Γ, x + 1 => by
    have := Ctx.lookup_dshift Γ x
    simp only [Ctx.dshift, List.map_cons, Ctx.lookup] at this ⊢
    rw [this, Option.map_map, Option.map_map]
    congr 1; funext t; exact Tm.shift_dshift t

end KubusCore

/-! ### Points -/

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

theorem IsPoint.restr {Ψ : ℕ} {Φ : I} {Γ : Ctx} {ρ : IEnv m} {γ : ℕ → V} (hwf : SemWf S Ψ Φ Γ)
    (hp : IsPoint S Φ Γ m ρ γ) (f : Hom k m) : IsPoint S Φ Γ k (ρ.restr f) (TEnv.restr γ f) where
  cof := by rw [ival.restr]; exact hp.cof.restr f
  typ x A hl := by
    obtain ⟨hty, hnat⟩ := hwf.2.2 m ρ γ hp x A hl
    rw [hnat k f, El_res, Hom.comp_id]
    have := hty.fib.elRes _ _ _ (hp.typ x A hl) k f
    rwa [Hom.id_comp] at this
  kv x := isKV_res f (γ x)

theorem IsPoint.cons {Φ : I} {Γ : Ctx} {ρ : IEnv m} {γ : ℕ → V} {A : Tm} {a : V}
    (hp : IsPoint S Φ Γ m ρ γ) (ha : a ∈ El (sem S A m ρ γ) (Hom.id m)) (hakv : IsKV m a) :
    IsPoint S Φ (A :: Γ) m ρ (TEnv.cons γ a) where
  kv x := by cases x with
    | zero => exact hakv
    | succ x => exact hp.kv x
  cof := hp.cof
  typ x B hl := by
    cases x with
    | zero =>
      simp only [Ctx.lookup, Option.some.injEq] at hl; subst hl
      rw [sem_shift]; exact ha
    | succ x =>
      simp only [Ctx.lookup, Option.map_eq_some_iff] at hl
      obtain ⟨B', hB', rfl⟩ := hl
      rw [sem_shift]; exact hp.typ x B' hB'

theorem TEnv.eq_cons (γ : ℕ → V) : γ = TEnv.cons (fun x => γ (x + 1)) (γ 0) := by
  funext x; cases x <;> rfl

theorem IsPoint.tail {Φ : I} {Γ : Ctx} {ρ : IEnv m} {γ : ℕ → V} {A : Tm}
    (hp : IsPoint S Φ (A :: Γ) m ρ γ) :
    IsPoint S Φ Γ m ρ (fun x => γ (x + 1)) ∧ γ 0 ∈ El (sem S A m ρ (fun x => γ (x + 1))) (Hom.id m) := by
  refine ⟨⟨hp.cof, fun x B hl => ?_, fun x => hp.kv (x + 1)⟩, ?_⟩
  · have := hp.typ (x + 1) B.shift (by simp [Ctx.lookup, hl])
    rwa [TEnv.eq_cons γ, sem_shift] at this
  · have := hp.typ 0 A.shift (by simp [Ctx.lookup])
    rwa [TEnv.eq_cons γ, sem_shift] at this

theorem IsPoint.of_entails {Φ Φ' : I} {Γ : Ctx} {ρ : IEnv m} {γ : ℕ → V} (h : I.Entails Φ' Φ)
    (hp : IsPoint S Φ' Γ m ρ γ) : IsPoint S Φ Γ m ρ γ :=
  ⟨entails_holds h hp.cof, hp.typ, hp.kv⟩

/-- The interval environment of a point of a context weakened by an interval variable. -/
def IEnv.tail (ρ : IEnv m) : IEnv m := fun i => ρ (i + 1)

theorem ival_shift (ρ : IEnv m) (r : I) : ival ρ r.shift = ival ρ.tail r := by
  rw [I.shift, ival_ren]; rfl

theorem sem_dshift_tail (t : Tm) (ρ : IEnv m) (γ : ℕ → V) : sem S t.dshift m ρ γ = sem S t m ρ.tail γ := by
  rw [Tm.dshift, sem_ren]; rfl

theorem isPoint_dshift_iff {Φ : I} {Γ : Ctx} {ρ : IEnv m} {γ : ℕ → V} :
    IsPoint S Φ.shift Γ.dshift m ρ γ ↔ IsPoint S Φ Γ m ρ.tail γ := by
  constructor
  · intro hp
    refine ⟨by rw [← ival_shift]; exact hp.cof, fun x A hl => ?_, hp.kv⟩
    have := hp.typ x A.dshift (by rw [Ctx.lookup_dshift, hl]; rfl)
    rwa [sem_dshift_tail] at this
  · intro hp
    refine ⟨by rw [ival_shift]; exact hp.cof, fun x A hl => ?_, hp.kv⟩
    rw [Ctx.lookup_dshift, Option.map_eq_some_iff] at hl
    obtain ⟨A', hA', rfl⟩ := hl
    rw [sem_dshift_tail]; exact hp.typ x A' hA'

theorem IEnv.tail_restr (ρ : IEnv m) (f : Hom k m) : (ρ.restr f).tail = ρ.tail.restr f := rfl

theorem IEnv.tail_cons (ρ : IEnv m) (r : DM m) : (ρ.cons r).tail = ρ := rfl

end

end Model

namespace KubusCore

theorem Tm.ConstsLt.ren {n : ℕ} : ∀ {t : Tm} (_ : t.ConstsLt n) (ρ δ : ℕ → ℕ), (t.ren ρ δ).ConstsLt n := by
  intro t
  induction t <;> intros <;> simp_all [Tm.ren, Tm.ConstsLt]

theorem Tm.ConstsLt.subst {n : ℕ} : ∀ {t : Tm} (_ : t.ConstsLt n) {σ : ℕ → Tm} (_ : ∀ x, (σ x).ConstsLt n)
    (τ : ℕ → I), (t.subst σ τ).ConstsLt n := by
  intro t
  induction t with
  | var x => intro _ σ hσ τ; exact hσ x
  | pi A B ihA ihB =>
    intro h σ hσ τ
    exact ⟨ihA h.1 hσ τ, ihB h.2 (fun x => by cases x <;> [trivial; exact (hσ _).ren _ _]) τ⟩
  | lam A B ihA ihB =>
    intro h σ hσ τ
    exact ⟨ihA h.1 hσ τ, ihB h.2 (fun x => by cases x <;> [trivial; exact (hσ _).ren _ _]) τ⟩
  | sigma A B ihA ihB =>
    intro h σ hσ τ
    exact ⟨ihA h.1 hσ τ, ihB h.2 (fun x => by cases x <;> [trivial; exact (hσ _).ren _ _]) τ⟩
  | path A a b ihA iha ihb =>
    intro h σ hσ τ; exact ⟨ihA h.1 (fun x => (hσ x).ren _ _) _, iha h.2.1 hσ τ, ihb h.2.2 hσ τ⟩
  | plam t ih => intro h σ hσ τ; exact ih h (fun x => (hσ x).ren _ _) _
  | ipi A ih => intro h σ hσ τ; exact ih h (fun x => (hσ x).ren _ _) _
  | transp A φ a ihA iha =>
    intro h σ hσ τ; exact ⟨ihA h.1 (fun x => (hσ x).ren _ _) _, iha h.2 hσ τ⟩
  | hcomp A φ u a ihA ihu iha =>
    intro h σ hσ τ; exact ⟨ihA h.1 hσ τ, ihu h.2.1 (fun x => (hσ x).ren _ _) _, iha h.2.2 hσ τ⟩
  | _ => intros; simp_all [Tm.subst, Tm.ConstsLt]

theorem Tm.ConstsLt.inst {n : ℕ} {t a : Tm} (ht : t.ConstsLt n) (ha : a.ConstsLt n) :
    (t.inst a).ConstsLt n :=
  ht.subst (fun x => by cases x <;> [exact ha; trivial]) _

theorem Tm.ConstsLt.dsubst {n : ℕ} {t : Tm} (ht : t.ConstsLt n) (τ : ℕ → I) : (t.dsubst τ).ConstsLt n :=
  ht.subst (σ := Tm.var) (fun _ => trivial) _

theorem Tm.ConstsLt.dinst {n : ℕ} {t : Tm} (ht : t.ConstsLt n) (r : I) : (t.dinst r).ConstsLt n :=
  ht.dsubst _

end KubusCore

namespace Model

open KubusCore

noncomputable section

variable {S : Sig} {k m n : ℕ}

@[simp] theorem sem_univ (l : ℕ) (ρ : IEnv m) (γ : ℕ → V) : sem S (.univ l) m ρ γ = univC m l := rfl
@[simp] theorem sem_var (x : ℕ) (ρ : IEnv m) (γ : ℕ → V) : sem S (.var x) m ρ γ = γ x := rfl

/-- A term of a universe denotes a good code. -/
theorem SemTy.ty_at {Ψ : ℕ} {Φ : I} {Γ : Ctx} {A : Tm} {l : ℕ} (h : SemTy S Ψ Φ Γ A (.univ l))
    {ρ : IEnv m} {γ : ℕ → V} (hp : IsPoint S Φ Γ m ρ γ) : TyOK S A m ρ γ ∧ Natural S A m ρ γ := by
  obtain ⟨hmem, hnat, hty, -⟩ := h.2.2.2 m ρ γ hp
  exact ⟨TyCode.of_mem_univ hty hmem, hnat⟩

theorem SemTy.wf {Ψ : ℕ} {Φ : I} {Γ : Ctx} {t A : Tm} (h : SemTy S Ψ Φ Γ t A) : SemWf S Ψ Φ Γ := h.1

theorem SemWf.cons {Ψ : ℕ} {Φ : I} {Γ : Ctx} {A : Tm} {l : ℕ} (h0 : SemTy S Ψ Φ Γ A (.univ l)) :
    SemWf S Ψ Φ (A :: Γ) := by
  refine ⟨h0.1.1, fun x B hl => ?_, fun m ρ γ hp x B hl => ?_⟩
  · cases x with
    | zero => simp only [Ctx.lookup, Option.some.injEq] at hl; subst hl; exact h0.2.1.ren _ _
    | succ x =>
      simp only [Ctx.lookup, Option.map_eq_some_iff] at hl
      obtain ⟨B', hB', rfl⟩ := hl
      exact (h0.1.2.1 x B' hB').ren _ _
  · obtain ⟨hpt, -⟩ := hp.tail
    rw [TEnv.eq_cons γ] at hp ⊢
    cases x with
    | zero =>
      simp only [Ctx.lookup, Option.some.injEq] at hl; subst hl
      obtain ⟨hty, hnat⟩ := h0.ty_at hpt
      exact ⟨by unfold TyOK; rw [sem_shift]; exact hty, hnat.shift _⟩
    | succ x =>
      simp only [Ctx.lookup, Option.map_eq_some_iff] at hl
      obtain ⟨B', hB', rfl⟩ := hl
      obtain ⟨hty, hnat⟩ := h0.1.2.2 m ρ _ hpt x B' hB'
      exact ⟨by unfold TyOK; rw [sem_shift]; exact hty, hnat.shift _⟩

end

end Model

namespace KubusCore

theorem I.Scoped.shift {r : I} {Ψ : ℕ} (h : r.Scoped Ψ) : r.shift.Scoped (Ψ + 1) := by
  induction r <;> simp_all [I.shift, I.ren, I.subst, I.Scoped]

theorem I.Scoped.of_shift {r : I} {Ψ : ℕ} (h : r.shift.Scoped (Ψ + 1)) : r.Scoped Ψ := by
  induction r <;> simp_all [I.shift, I.ren, I.subst, I.Scoped]

theorem Tm.constsLt_ren_iff {n : ℕ} : ∀ (t : Tm) (ρ δ : ℕ → ℕ), (t.ren ρ δ).ConstsLt n ↔ t.ConstsLt n := by
  intro t
  induction t <;> intros <;> simp_all [Tm.ren, Tm.ConstsLt]

theorem Tm.ConstsLt.of_ren {n : ℕ} {t : Tm} {ρ δ : ℕ → ℕ} (h : (t.ren ρ δ).ConstsLt n) : t.ConstsLt n :=
  (Tm.constsLt_ren_iff t ρ δ).1 h

end KubusCore

namespace Model

open KubusCore

noncomputable section

variable {S : Sig} {k m n : ℕ}

theorem sem_inst {t a : Tm} {ρ : IEnv m} {γ : ℕ → V} (ha : Natural S a m ρ γ) :
    sem S (t.inst a) m ρ γ = sem S t m ρ (TEnv.cons γ (sem S a m ρ γ)) := by
  rw [Tm.inst, sem_subst S t m ρ γ _ _ (fun x => by cases x <;> [exact ha; exact natural_var S _ ρ γ])]
  congr 1; funext x; cases x <;> rfl

theorem sem_dinst {t : Tm} {r : I} {ρ : IEnv m} {γ : ℕ → V} :
    sem S (t.dinst r) m ρ γ = sem S t m (ρ.cons (ival ρ r)) γ := by
  rw [Tm.dinst, Tm.dsubst, sem_subst S t m ρ γ _ _ (fun x => natural_var S x ρ γ)]
  congr 1; funext i; cases i <;> rfl

theorem Natural.dshift_tail {t : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : Natural S t m ρ.tail γ) :
    Natural S t.dshift m ρ γ := by
  intro k f
  rw [sem_dshift_tail, sem_dshift_tail, IEnv.tail_restr, h]

theorem Natural.of_dshift_tail {t : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : Natural S t.dshift m ρ γ) :
    Natural S t m ρ.tail γ := by
  intro k f
  have := h k f
  rwa [sem_dshift_tail, sem_dshift_tail, IEnv.tail_restr] at this

theorem Natural.inst {t a : Tm} {ρ : IEnv m} {γ : ℕ → V} (ha : Natural S a m ρ γ)
    (ht : Natural S t m ρ (TEnv.cons γ (sem S a m ρ γ))) : Natural S (t.inst a) m ρ γ := by
  intro k f
  rw [sem_inst (ha.restr f), sem_inst ha, ha k f, ← TEnv.restr_cons, ht k f]

theorem Natural.dinst {t : Tm} {r : I} {ρ : IEnv m} {γ : ℕ → V}
    (ht : Natural S t m (ρ.cons (ival ρ r)) γ) : Natural S (t.dinst r) m ρ γ := by
  intro k f
  rw [sem_dinst, sem_dinst, ival.restr, ← IEnv.cons_restr, ht k f]

theorem SemWf.dshift {Ψ : ℕ} {Φ : I} {Γ : Ctx} (h : SemWf S Ψ Φ Γ) : SemWf S (Ψ + 1) Φ.shift Γ.dshift := by
  refine ⟨h.1.shift, fun x A hl => ?_, fun m ρ γ hp x A hl => ?_⟩
  · rw [Ctx.lookup_dshift, Option.map_eq_some_iff] at hl
    obtain ⟨A', hA', rfl⟩ := hl
    exact (h.2.1 x A' hA').ren _ _
  · rw [Ctx.lookup_dshift, Option.map_eq_some_iff] at hl
    obtain ⟨A', hA', rfl⟩ := hl
    obtain ⟨hty, hnat⟩ := h.2.2 m ρ.tail γ (isPoint_dshift_iff.1 hp) x A' hA'
    exact ⟨by unfold TyOK; rw [sem_dshift_tail]; exact hty, hnat.dshift_tail⟩

theorem SemWf.of_dshift {Ψ : ℕ} {Φ : I} {Γ : Ctx} (h : SemWf S (Ψ + 1) Φ.shift Γ.dshift) : SemWf S Ψ Φ Γ := by
  refine ⟨h.1.of_shift, fun x A hl => ?_, fun m ρ γ hp x A hl => ?_⟩
  · exact (h.2.1 x A.dshift (by rw [Ctx.lookup_dshift, hl]; rfl)).of_ren
  · have hp' : IsPoint S Φ.shift Γ.dshift m (ρ.cons (DM.zero m)) γ := isPoint_dshift_iff.2 hp
    obtain ⟨hty, hnat⟩ := h.2.2 m _ γ hp' x A.dshift (by rw [Ctx.lookup_dshift, hl]; rfl)
    refine ⟨by unfold TyOK at hty; rwa [sem_dshift_tail] at hty, ?_⟩
    have := hnat.of_dshift_tail; exact this

end

end Model

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

theorem not_isKV_empty : ¬ IsKV m (∅ : V) := by
  rintro ⟨F, h⟩
  have : ZFSet.pair (enc (⟨m, Hom.id m⟩ : Dom m)) (F m (Hom.id m)) ∈ (∅ : V) := by
    rw [h]; exact mem_fnC.2 ⟨⟨m, Hom.id m⟩, rfl⟩
  exact ZFSet.notMem_empty _ this

theorem Fib.empty_notMem {c : V} (hc : Fib c m) (f : Hom k m) : (∅ : V) ∉ El c f :=
  fun h => not_isKV_empty (hc.elKV _ _ _ h)

theorem TyOK.ne_empty {A : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : TyOK S A m ρ γ) {v : V}
    (hv : v ∈ El (sem S A m ρ γ) (Hom.id m)) : v ≠ ∅ := by
  rintro rfl; exact (TyCode.fib h).empty_notMem _ hv

theorem isPoint_cof_iff {Φ φ : I} {Γ : Ctx} {ρ : IEnv m} {γ : ℕ → V} :
    IsPoint S (cof Φ φ) Γ m ρ γ ↔ IsPoint S Φ Γ m ρ γ ∧ (ival ρ φ).holds := by
  constructor
  · intro hp; exact ⟨⟨(holds_and.1 hp.cof).1, hp.typ, hp.kv⟩, (holds_and.1 hp.cof).2⟩
  · rintro ⟨hp, h⟩; exact ⟨holds_and.2 ⟨hp.cof, h⟩, hp.typ, hp.kv⟩

/-- Transfer typing along equal denotations. -/
theorem SemTy.of_eq {Ψ : ℕ} {Φ : I} {Γ : Ctx} {t t' A : Tm} (h : SemTy S Ψ Φ Γ t A)
    (ht' : t'.ConstsLt S.length)
    (he : ∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ → sem S t' m ρ γ = sem S t m ρ γ) :
    SemTy S Ψ Φ Γ t' A := by
  refine ⟨h.1, ht', h.2.2.1, fun m ρ γ hp => ?_⟩
  obtain ⟨hmem, hnat, hty, hnatA⟩ := h.2.2.2 m ρ γ hp
  refine ⟨he m ρ γ hp ▸ hmem, fun k f => ?_, hty, hnatA⟩
  rw [he k _ _ (hp.restr h.1 f), he m ρ γ hp, hnat k f]

/-- Transfer typing along equal denotations of the type. -/
theorem SemTy.retype {Ψ : ℕ} {Φ : I} {Γ : Ctx} {t A B : Tm} (h : SemTy S Ψ Φ Γ t A)
    (hB : B.ConstsLt S.length)
    (he : ∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ → sem S A m ρ γ = sem S B m ρ γ) :
    SemTy S Ψ Φ Γ t B := by
  refine ⟨h.1, h.2.1, hB, fun m ρ γ hp => ?_⟩
  obtain ⟨hmem, hnat, hty, hnatA⟩ := h.2.2.2 m ρ γ hp
  refine ⟨he m ρ γ hp ▸ hmem, hnat, by unfold TyOK; rw [← he m ρ γ hp]; exact hty, fun k f => ?_⟩
  rw [← he k _ _ (hp.restr h.1 f), ← he m ρ γ hp, hnatA k f]

theorem sem_dset {t : Tm} {i : ℕ} {d : I} {ρ : IEnv m} {γ : ℕ → V} :
    sem S (t.dset i d) m ρ γ = sem S t m (fun n => if n = i then ival ρ d else ρ n) γ := by
  rw [Tm.dset, Tm.dsubst, sem_subst S t m ρ γ _ _ (fun x => natural_var S x ρ γ)]
  congr 1; funext n; split <;> rfl

/-- The denotation of a system at a point where one of the faces holds and the branches agree on
the overlap. -/
theorem sem_split {φ ψ : I} {t u : Tm} {ρ : IEnv m} {γ : ℕ → V}
    (hcov : (ival ρ φ).holds ∨ (ival ρ ψ).holds)
    (hover : (ival ρ φ).holds → (ival ρ ψ).holds → sem S t m ρ γ = sem S u m ρ γ) :
    sem S (.split φ t ψ u) m ρ γ = if (ival ρ φ).holds then sem S t m ρ γ else sem S u m ρ γ := by
  simp only [sem, interp]
  split
  · rw [if_pos (hover ‹_›)]
  · rw [if_pos (hcov.resolve_left ‹_›)]

theorem DM.restr_holds_of {r : DM m} (h : r.holds) (f : Hom k m) : (r.restr f).holds := h.restr f

end

end Model

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

theorem sem_split_cases {φ ψ : I} {t u : Tm} {ρ : IEnv m} {γ : ℕ → V}
    (hne : sem S (.split φ t ψ u) m ρ γ ≠ ∅) :
    ((ival ρ φ).holds ∧ sem S (.split φ t ψ u) m ρ γ = sem S t m ρ γ ∧
        ((ival ρ ψ).holds → sem S t m ρ γ = sem S u m ρ γ)) ∨
      (¬ (ival ρ φ).holds ∧ (ival ρ ψ).holds ∧ sem S (.split φ t ψ u) m ρ γ = sem S u m ρ γ) := by
  simp only [sem, interp] at hne ⊢
  split at hne
  · split at hne
    · left; rw [if_pos ‹_›, if_pos ‹_›]; exact ⟨‹_›, rfl, ‹_›⟩
    · exact absurd rfl hne
  · split at hne
    · right; rw [if_neg ‹_›, if_pos ‹_›]; exact ⟨‹_›, ‹_›, rfl⟩
    · exact absurd rfl hne

end

end Model

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

theorem TEnv.restr_id_of_kv {γ : ℕ → V} (h : ∀ x, IsKV m (γ x)) : TEnv.restr γ (Hom.id m) = γ := by
  funext x; exact res_id (h x)

theorem Vt_below {l : ℕ} {x c : V} (h : Below x c) (hc : c ∈ Vt l) : x ∈ Vt l := by
  induction h with
  | single h => exact Vt_trans l hc h
  | tail _ h ih => exact ih (Vt_trans l hc h)

/-- The codomain family values are below a Π-code. -/
theorem below_piC_fam (A B : V) (hB : IsKV m B) (a : V) (ha : ∃ y, ZFSet.pair a y ∈ dat B m (Hom.id m)) :
    Below (apZ (dat B m (Hom.id m)) a) (piC m A B) := by
  have h1 : Below (apZ (dat B m (Hom.id m)) a) B :=
    (below_apZ ha).trans (below_dat hB _)
  have h2 : Below (res (Hom.id m) B) (piC m A B) := by
    unfold piC
    refine Below.trans ?_ (below_dat_mkKV _ (Hom.id m))
    simp only [piDatum, quad, tagZ]
    exact ((below_pair_right _ _).trans (below_pair_right _ _)).trans (below_pair_left _ _)
  rw [res_id hB] at h2
  exact h1.trans h2

/-- Inversion of well-formedness for Π-codes. -/
theorem WF.pi_inv {l : ℕ} {A B : V} (hA : IsKV m A) (hB : IsKV m B) (h : WF l m (piC m A B)) :
    WF l m A ∧ (∀ k (f : Hom k m), ∀ a ∈ El A f, WF l k (apZ (dat B k f) a)) ∧
      (∀ k (f : Hom k m), ∀ a ∈ El A f, ∀ n (g : Hom n k),
        Model.res g (apZ (dat B k f) a) = apZ (dat B n (f.comp g)) (Model.res g a)) := by
  generalize hc : piC m A B = c at h
  have htag : codeTag m c = natZ tPi := by rw [← hc]; simp
  unfold WF at h
  cases h with
  | empty => simp [tEmpty, tPi] at htag
  | @pi _ A' B' hA' _ _ hfam hcoh =>
    obtain ⟨rfl, rfl⟩ := piC_inj hA hB ((wf_props l _ A' hA').1.kv) ‹_› hc
    exact ⟨hA', hfam, hcoh⟩
  | sigma => simp [tSigma, tPi] at htag
  | path => simp [tPath, tPi] at htag
  | ipi => simp [tIPi, tPi] at htag
  | univ => rw [Ucodes_lt _ ‹_›, codeTag_univC] at htag; simp [tUniv, tPi] at htag
  | glue _ hφ hn => rw [codeTag_glueC hn hφ] at htag; simp [tGlue, tPi] at htag

end

end Model

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

/-- Π-codes of small components are small. TODO (closure plumbing for `Vt`). -/
theorem piC_mem_Vt {l : ℕ} {A B : V} (hA : A ∈ Vt l)
    (hB : ∀ k (f : Hom k m), ∀ a ∈ El A f, apZ (dat B k f) a ∈ Vt l) : piC m A B ∈ Vt l := by
  sorry

theorem sem_pi {A B : Tm} {ρ : IEnv m} {γ : ℕ → V} (hA : IsKV m (sem S A m ρ γ)) :
    sem S (.pi A B) m ρ γ = piC m (sem S A m ρ γ)
      (famV m (sem S A m ρ γ) fun k f a => sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)) := by
  simp only [sem, interp] at hA ⊢; rw [if_pos hA]

theorem kv_of_sem_pi {A B : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : sem S (.pi A B) m ρ γ ≠ ∅) :
    IsKV m (sem S A m ρ γ) := by
  simp only [sem, interp] at h ⊢; split at h
  · assumption
  · exact absurd rfl h

theorem dat_famV (A : V) (F : (k : ℕ) → Hom k m → V → V) (f : Hom k m) :
    dat (famV m A F) k f = fnZ (El A f) (F k f) := by simp [famV]

theorem apZ_dat_famV (A : V) (F : (k : ℕ) → Hom k m → V → V) (f : Hom k m) {a : V} (ha : a ∈ El A f) :
    apZ (dat (famV m A F) k f) a = F k f a := by rw [dat_famV, apZ_fnZ _ ha]

theorem res_famV (A : V) (F : (k : ℕ) → Hom k m → V → V) (h : Hom n m) :
    res h (famV m A F) = famV n (res h A) (fun k' g => F k' (h.comp g)) := by
  simp only [famV, res_lamV, El_res]

/-- Extending a point of `Γ` by an element of `A`, restricted along `f`. -/
theorem IsPoint.ext {Ψ : ℕ} {Φ : I} {Γ : Ctx} {A : Tm} {ρ : IEnv m} {γ : ℕ → V}
    (hwf : SemWf S Ψ Φ Γ) (hp : IsPoint S Φ Γ m ρ γ) (hAty : TyOK S A m ρ γ) (hAnat : Natural S A m ρ γ)
    (f : Hom k m) {a : V} (ha : a ∈ El (sem S A m ρ γ) f) :
    IsPoint S Φ (A :: Γ) k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a) :=
  (hp.restr hwf f).cons (by rw [hAnat k f, El_res, Hom.comp_id]; exact ha) (hAty.fib.elKV _ _ _ ha)

theorem below_piC_dom (A B : V) (hA : IsKV m A) : Below A (piC m A B) := by
  have h2 : Below (res (Hom.id m) A) (piC m A B) := by
    unfold piC
    refine Below.trans ?_ (below_dat_mkKV _ (Hom.id m))
    simp only [piDatum, quad, tagZ]
    exact ((below_pair_left _ _).trans (below_pair_right _ _)).trans (below_pair_left _ _)
  rwa [res_id hA] at h2

theorem mem_El_univ_iff {l : ℕ} {c : V} : c ∈ El (univC m l) (Hom.id m) ↔ c ∈ Vt l ∧ WF l m c := by
  rw [El_univC, ZFSet.mem_sep]

end

end Model

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

theorem isKV_famV (A : V) (F : (k : ℕ) → Hom k m → V → V) : IsKV m (famV m A F) := by
  unfold famV lamV; exact isKV_mkKV _

/-- What a Π-type of a universe gives at a point. -/
theorem SemTy.pi_at {Ψ : ℕ} {Φ : I} {Γ : Ctx} {A B : Tm} {l : ℕ}
    (h : SemTy S Ψ Φ Γ (.pi A B) (.univ l)) {ρ : IEnv m} {γ : ℕ → V} (hp : IsPoint S Φ Γ m ρ γ) :
    IsKV m (sem S A m ρ γ) ∧
    sem S (.pi A B) m ρ γ = piC m (sem S A m ρ γ)
      (famV m (sem S A m ρ γ) fun k f a => sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)) ∧
    piC m (sem S A m ρ γ)
      (famV m (sem S A m ρ γ) fun k f a => sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)) ∈ Vt l ∧
    WF l m (piC m (sem S A m ρ γ)
      (famV m (sem S A m ρ γ) fun k f a => sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a))) := by
  obtain ⟨hmem, -, hUty, -⟩ := h.2.2.2 m ρ γ hp
  have hAkv := kv_of_sem_pi (hUty.ne_empty hmem)
  rw [sem_pi hAkv, sem_univ, mem_El_univ_iff] at hmem
  exact ⟨hAkv, sem_pi hAkv, hmem⟩

theorem SemTy.piDom {Ψ : ℕ} {Φ : I} {Γ : Ctx} {A B : Tm} {l : ℕ}
    (h : SemTy S Ψ Φ Γ (.pi A B) (.univ l)) : SemTy S Ψ Φ Γ A (.univ l) := by
  refine ⟨h.1, h.2.1.1, trivial, fun m ρ γ hp => ?_⟩
  obtain ⟨-, hnat, hUty, hUnat⟩ := h.2.2.2 m ρ γ hp
  obtain ⟨hAkv, hsem, hV, hWF⟩ := h.pi_at hp
  obtain ⟨hAWF, -, -⟩ := WF.pi_inv hAkv (isKV_famV _ _) hWF
  refine ⟨mem_El_univ_iff.2 ⟨Vt_below (below_piC_dom _ _ hAkv) hV, hAWF⟩, fun k f => ?_, hUty, hUnat⟩
  obtain ⟨hAkv', hsem', -, -⟩ := h.pi_at (hp.restr h.1 f)
  have := hnat k f
  rw [hsem', hsem, res_piC] at this
  exact (piC_inj hAkv' (isKV_famV _ _) (isKV_res _ _) (isKV_res _ _) this).1

theorem SemTy.piCod {Ψ : ℕ} {Φ : I} {Γ : Ctx} {A B : Tm} {l : ℕ}
    (h : SemTy S Ψ Φ Γ (.pi A B) (.univ l)) : SemTy S Ψ Φ (A :: Γ) B (.univ l) := by
  refine ⟨SemWf.cons h.piDom, h.2.1.2, trivial, fun m ρ γ hp => ?_⟩
  obtain ⟨hpt, ha⟩ := hp.tail
  obtain ⟨-, -, hUty, hUnat⟩ := h.2.2.2 m ρ _ hpt
  obtain ⟨hAkv, -, hV, hWF⟩ := h.pi_at hpt
  obtain ⟨-, hfam, hcoh⟩ := WF.pi_inv hAkv (isKV_famV _ _) hWF
  have hval : ∀ k (f : Hom k m) a, a ∈ El (sem S A m ρ fun x => γ (x + 1)) f →
      apZ (dat (famV m (sem S A m ρ fun x => γ (x + 1)) fun k f a =>
        sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr (fun x => γ (x + 1)) f) a)) k f) a =
      sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr (fun x => γ (x + 1)) f) a) :=
    fun k f a ha => apZ_dat_famV _ _ _ ha
  have hid : sem S B m ρ γ = sem S B m (ρ.restr (Hom.id m))
      (TEnv.cons (TEnv.restr (fun x => γ (x + 1)) (Hom.id m)) (γ 0)) := by
    rw [IEnv.restr_id, TEnv.restr_id_of_kv (fun x => hpt.kv x), ← TEnv.eq_cons]
  refine ⟨?_, fun k f => ?_, hUty, hUnat⟩
  · rw [sem_univ, mem_El_univ_iff, hid, ← hval m (Hom.id m) _ ha]
    exact ⟨Vt_below (below_piC_fam _ _ (isKV_famV _ _) _ ⟨_, by rw [dat_famV]; exact mem_fnZ.2 ⟨_, ha, rfl⟩⟩) hV,
      hfam m _ _ ha⟩
  · have hfa : res f (γ 0) ∈ El (sem S A m ρ fun x => γ (x + 1)) f := by
      have := ((h.piDom.ty_at hpt).1.fib).elRes _ _ _ ha k f; rwa [Hom.id_comp] at this
    have e1 : res f (sem S B m ρ γ) = sem S B k (ρ.restr f)
        (TEnv.cons (TEnv.restr (fun x => γ (x + 1)) f) (res f (γ 0))) := by
      rw [hid, ← hval m (Hom.id m) _ ha, hcoh m (Hom.id m) _ ha k f, Hom.id_comp, hval k f _ hfa]
    rw [e1]; conv_lhs => rw [TEnv.eq_cons γ]
    rw [TEnv.restr_cons]

end

end Model

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

/-- A good Π-code is a well-formed small code. -/
theorem TyCode.pi_inv {A B : V} (hA : IsKV m A) (h : TyCode m (piC m A B)) :
    ∃ l ≤ maxLevel, piC m A B ∈ Vt l ∧ WF l m (piC m A B) := by
  obtain ⟨l, hl, h | h⟩ := h
  · exact ⟨l, hl, h.2, h.1⟩
  · have := congrArg (codeTag m) h; simp [tPi, tUniv] at this

theorem TyOK.pi_at {A B : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : TyOK S (.pi A B) m ρ γ) :
    IsKV m (sem S A m ρ γ) ∧ ∃ l ≤ maxLevel,
      sem S (.pi A B) m ρ γ ∈ Vt l ∧ WF l m (sem S (.pi A B) m ρ γ) := by
  have hne : sem S (.pi A B) m ρ γ ≠ ∅ := by
    intro he; unfold TyOK at h; rw [he] at h; exact not_isKV_empty h.fib.kv
  have hAkv := kv_of_sem_pi hne
  refine ⟨hAkv, ?_⟩
  unfold TyOK at h; rw [sem_pi hAkv] at h ⊢
  exact h.pi_inv hAkv

/-- Point extension in a context whose first type is converted. -/
theorem SemTy.ctx_conv {Ψ : ℕ} {Φ : I} {Γ : Ctx} {A A' t T : Tm} {l : ℕ}
    (h : SemTy S Ψ Φ (A :: Γ) t T) (hA : SemEq S Ψ Φ Γ A A' (.univ l)) : SemTy S Ψ Φ (A' :: Γ) t T := by
  have hpt : ∀ m (ρ : IEnv m) γ, IsPoint S Φ (A' :: Γ) m ρ γ → IsPoint S Φ (A :: Γ) m ρ γ := by
    intro m ρ γ hp
    obtain ⟨hpt, ha⟩ := hp.tail
    rw [TEnv.eq_cons γ]
    rw [← hA.2.2 m ρ _ hpt] at ha
    exact hpt.cons ha (hp.kv 0)
  refine ⟨SemWf.cons hA.2.1, h.2.1, h.2.2.1, fun m ρ γ hp => h.2.2.2 m ρ γ (hpt m ρ γ hp)⟩

end

end Model

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

theorem sem_lam (A t : Tm) (ρ : IEnv m) (γ : ℕ → V) :
    sem S (.lam A t) m ρ γ = lamV m (fun _ f => El (sem S A m ρ γ) f)
      (fun k f a => sem S t k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)) := rfl

theorem sem_app_of_nat {f a : Tm} {ρ : IEnv m} {γ : ℕ → V} (ha : Natural S a m ρ γ) :
    sem S (.app f a) m ρ γ = appV m (sem S f m ρ γ) (sem S a m ρ γ) := by
  simp only [sem, interp]; exact if_pos ha

theorem nat_of_sem_app {f a : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : sem S (.app f a) m ρ γ ≠ ∅) :
    Natural S a m ρ γ := by
  simp only [sem, interp] at h; split at h
  · rename_i hc; exact hc
  · exact absurd rfl h

end

end Model
