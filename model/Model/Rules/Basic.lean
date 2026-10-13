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

theorem IsPoint.cons {Φ : I} {Γ : Ctx} {ρ : IEnv m} {γ : ℕ → V} {A : Tm} {a : V}
    (hp : IsPoint S Φ Γ m ρ γ) (ha : a ∈ El (sem S A m ρ γ) (Hom.id m)) :
    IsPoint S Φ (A :: Γ) m ρ (TEnv.cons γ a) where
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
  refine ⟨⟨hp.cof, fun x B hl => ?_⟩, ?_⟩
  · have := hp.typ (x + 1) B.shift (by simp [Ctx.lookup, hl])
    rwa [TEnv.eq_cons γ, sem_shift] at this
  · have := hp.typ 0 A.shift (by simp [Ctx.lookup])
    rwa [TEnv.eq_cons γ, sem_shift] at this

theorem IsPoint.of_entails {Φ Φ' : I} {Γ : Ctx} {ρ : IEnv m} {γ : ℕ → V} (h : I.Entails Φ' Φ)
    (hp : IsPoint S Φ' Γ m ρ γ) : IsPoint S Φ Γ m ρ γ :=
  ⟨entails_holds h hp.cof, hp.typ⟩

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
    refine ⟨by rw [← ival_shift]; exact hp.cof, fun x A hl => ?_⟩
    have := hp.typ x A.dshift (by rw [Ctx.lookup_dshift, hl]; rfl)
    rwa [sem_dshift_tail] at this
  · intro hp
    refine ⟨by rw [ival_shift]; exact hp.cof, fun x A hl => ?_⟩
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
  · intro hp; exact ⟨⟨(holds_and.1 hp.cof).1, hp.typ⟩, (holds_and.1 hp.cof).2⟩
  · rintro ⟨hp, h⟩; exact ⟨holds_and.2 ⟨hp.cof, h⟩, hp.typ⟩

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
