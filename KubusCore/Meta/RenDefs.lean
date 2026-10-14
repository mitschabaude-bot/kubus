import KubusCore.Meta.Gen
import KubusCore.Meta.Near

/-!
# Metatheory: typed renamings

A renaming of term variables by `ρ` and of interval variables by an injective `δ`, as the
substitution `(rS ρ, rI δ)`. `TyRen` says it maps the context `Ψ; Φ; Γ` into `Ψ'; Φ'; Δ`;
`CtxRen` says that the types of a context can be renamed along any typed renaming (it is
part of the induction hypothesis of the renaming theorem, and provides the well-formedness
of extended targets).
-/

namespace KubusCore.Meta

open Tm

def rS (ρ : Nat → Nat) : Nat → Tm := fun n => .var (ρ n)
def rI (δ : Nat → Nat) : Nat → I := fun i => .var (δ i)

def upRenN : Nat → (Nat → Nat) → Nat → Nat
  | 0, ρ => ρ
  | k + 1, ρ => upRen (upRenN k ρ)

theorem up_rS (ρ : Nat → Nat) : up (rS ρ) = rS (upRen ρ) := by funext n; cases n <;> rfl
theorem dupS_rS (ρ : Nat → Nat) : dupS (rS ρ) = rS ρ := rfl
theorem Iup_rI (δ : Nat → Nat) : I.up (rI δ) = rI (upRen δ) := by funext n; cases n <;> rfl
theorem upN_rS (k : Nat) (ρ : Nat → Nat) : upN k (rS ρ) = rS (upRenN k ρ) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [upN, upRenN, ih, up_rS]
theorem dupN_rS (m : Nat) (ρ : Nat → Nat) : dupN m (rS ρ) = rS ρ := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [dupN, ih, dupS_rS]
theorem IupN_rI (m : Nat) (δ : Nat → Nat) : IupN m (rI δ) = rI (upRenN m δ) := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [IupN, upRenN, ih, Iup_rI]

theorem upRen_inj {δ : Nat → Nat} (h : ∀ i j, δ i = δ j → i = j) : ∀ i j, upRen δ i = upRen δ j → i = j := by
  intro i j hij
  cases i <;> cases j <;> simp_all [upRen]
  exact h _ _ hij

theorem upRenN_inj {δ : Nat → Nat} (h : ∀ i j, δ i = δ j → i = j) (k : Nat) :
    ∀ i j, upRenN k δ i = upRenN k δ j → i = j := by
  induction k with
  | zero => exact h
  | succ k ih => exact upRen_inj ih

theorem upRenN_lt (k : Nat) (δ : Nat → Nat) {i : Nat} (h : i < k) : upRenN k δ i = i := by
  induction k generalizing i with
  | zero => omega
  | succ k ih => cases i with
    | zero => rfl
    | succ i => simp only [upRenN, upRen]; rw [ih (by omega)]

theorem upRenN_add (k : Nat) (δ : Nat → Nat) (i : Nat) : upRenN k δ (i + k) = δ i + k := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp only [upRenN]; rw [show i + (k + 1) = (i + k) + 1 by omega]; simp only [upRen, ih]; omega

theorem upRenN_bound {δ : Nat → Nat} {Ψ Ψ' : Nat} (h : ∀ i < Ψ, δ i < Ψ') (k : Nat) :
    ∀ i < Ψ + k, upRenN k δ i < Ψ' + k := by
  intro i hi
  by_cases hk : i < k
  · rw [upRenN_lt k δ hk]; omega
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + k := ⟨i - k, by omega⟩
    rw [upRenN_add]; have := h j (by omega); omega

/-! ## Interval weakening of contexts -/

/-- Weaken by `k` interval variables (as a substitution). -/
def wkIv (k : Nat) : Nat → I := fun i => .var (i + k)

def ctxWkI (k : Nat) (Γ : Ctx) : Ctx := Γ.map (·.subst Tm.var (wkIv k))

theorem Ctx_dshift_eq (Γ : Ctx) : Γ.dshift = ctxWkI 1 Γ := by
  simp only [Ctx.dshift, ctxWkI]; congr 1; funext t; rw [dshift_eq]; rfl

theorem I_shift_eq (r : I) : r.shift = r.subst (wkIv 1) := rfl

theorem I_ren_add_eq (r : I) (k : Nat) : r.ren (· + k) = r.subst (wkIv k) := rfl

theorem Ctx_ren_add_eq (Γ : Ctx) (k : Nat) : Γ.map (·.ren id (· + k)) = ctxWkI k Γ := by
  simp only [ctxWkI]; congr 1; funext t; rw [ren_eq_subst]; rfl

theorem lookup_map {Γ : Ctx} {f : Tm → Tm} (hf : ∀ t, (f t).shift = f t.shift) (x : Nat) :
    Ctx.lookup (Γ.map f) x = (Γ.lookup x).map f := by
  induction Γ generalizing x with
  | nil => rfl
  | cons A Γ ih =>
    cases x with
    | zero => simp [Ctx.lookup, hf]
    | succ x => simp [Ctx.lookup, ih, Option.map_map, Function.comp_def, hf]

theorem shift_substI (t : Tm) (τ : Nat → I) :
    (t.subst Tm.var τ).shift = t.shift.subst Tm.var τ := by
  rw [shift_eq, shift_eq, subst_subst, subst_subst]
  simp only [Tm.subst, I.subst, I_subst_var]

theorem lookup_wkI (Γ : Ctx) (k x : Nat) :
    (ctxWkI k Γ).lookup x = (Γ.lookup x).map (·.subst Tm.var (wkIv k)) :=
  lookup_map (fun t => shift_substI t _) x

theorem wkI_wkI (Γ : Ctx) (k k' : Nat) : ctxWkI k' (ctxWkI k Γ) = ctxWkI (k + k') Γ := by
  simp only [ctxWkI, List.map_map]; congr 1; funext t
  simp only [Function.comp, subst_subst]
  apply subst_congr <;> intro n <;> simp [wkIv, Tm.subst, I.subst]; omega

theorem wkI_zero (Γ : Ctx) : ctxWkI 0 Γ = Γ := by
  simp only [ctxWkI]
  conv => rhs; rw [← List.map_id Γ]
  congr 1; funext t; exact subst_id_of (fun _ => rfl) (fun _ => rfl) t

theorem I_wkI_wkI (r : I) (k k' : Nat) : (r.subst (wkIv k)).subst (wkIv k') = r.subst (wkIv (k + k')) := by
  rw [I_subst_subst]; apply I_subst_congr; intro i; simp [wkIv, I.subst]; omega

theorem I_wkI_zero (r : I) : r.subst (wkIv 0) = r := by
  rw [show wkIv 0 = I.var from rfl, I_subst_var]

/-! ## Typed renamings -/

variable {S : Sig}

/-- `Δ` and all its interval weakenings are well-formed, under any stronger restriction. -/
def WfAll (S : Sig) (Ψ : Nat) (Φ : I) (Δ : Ctx) : Prop :=
  ∀ k Φ'', Φ''.Scoped (Ψ + k) → I.Entails Φ'' (Φ.subst (wkIv k)) → Wf0 S (Ψ + k) Φ'' (ctxWkI k Δ)

theorem WfAll.wf {Ψ Φ Δ} (h : WfAll S Ψ Φ Δ) (hs : Φ.Scoped Ψ) : Wf0 S Ψ Φ Δ := by
  have := h 0 Φ hs (by rw [I_wkI_zero]; exact ent_refl _)
  rwa [wkI_zero] at this

theorem WfAll.mono {Ψ Φ Φ1 Δ} (h : WfAll S Ψ Φ Δ) (he : I.Entails Φ1 Φ) : WfAll S Ψ Φ1 Δ :=
  fun k Φ'' hs he' => h k Φ'' hs (ent_trans he' (ent_subst he _))

theorem WfAll.wk {Ψ Φ Δ} (h : WfAll S Ψ Φ Δ) (k : Nat) {Φ1} (he : I.Entails Φ1 (Φ.subst (wkIv k))) :
    WfAll S (Ψ + k) Φ1 (ctxWkI k Δ) := by
  intro k' Φ'' hs he'
  have := h (k + k') Φ'' (by rwa [← Nat.add_assoc]) (by
    rw [← I_wkI_wkI]; exact ent_trans he' (ent_subst he _))
  rw [wkI_wkI, Nat.add_assoc]; exact this

structure TyRen (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (Ψ' : Nat) (Φ' : I) (Δ : Ctx)
    (ρ δ : Nat → Nat) : Prop where
  inj : ∀ i j, δ i = δ j → i = j
  bound : ∀ i < Ψ, δ i < Ψ'
  hscoped : Φ'.Scoped Ψ'
  ent : I.Entails Φ' (Φ.subst (rI δ))
  look : ∀ x A, Γ.lookup x = some A → Δ.lookup (ρ x) = some (A.subst (rS ρ) (rI δ))
  wf : WfAll S Ψ' Φ' Δ

/-- The types of `Γ` can be renamed along any typed renaming. -/
def CtxRen (S : Sig) (Ψ : Nat) (Φ : I) : Ctx → Prop
  | [] => True
  | A :: Γ => CtxRen S Ψ Φ Γ ∧ ∀ Ψ' Φ' Δ ρ δ, TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ →
      ∃ l, HasTy0 S Ψ' Φ' Δ (A.subst (rS ρ) (rI δ)) (univ l)

theorem TyRen.restrict {Ψ Φ Γ Ψ' Φ' Δ ρ δ} (h : TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ) {Φ1 Φ1' : I}
    (hs : Φ1'.Scoped Ψ') (h1 : I.Entails Φ1' Φ') (h2 : I.Entails Φ1' (Φ1.subst (rI δ))) :
    TyRen S Ψ Φ1 Γ Ψ' Φ1' Δ ρ δ :=
  ⟨h.inj, h.bound, hs, h2, h.look, h.wf.mono h1⟩

theorem TyRen.sc {Ψ Φ Γ Ψ' Φ' Δ ρ δ} (h : TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ) {r : I}
    (hr : r.Scoped Ψ) : (r.subst (rI δ)).Scoped Ψ' :=
  scoped_subst hr fun i hi => h.bound i hi

/-- Restrict the source and the target by a cofibration. -/
theorem TyRen.underCof {Ψ Φ Γ Ψ' Φ' Δ ρ δ} (h : TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ) {φ : I} (hφ : φ.Scoped Ψ) :
    TyRen S Ψ (cof Φ φ) Γ Ψ' (cof Φ' (φ.subst (rI δ))) Δ ρ δ :=
  h.restrict ⟨h.hscoped, h.sc hφ⟩ (ent_and_left _ _) (ent_and_mono h.ent (ent_refl _))

theorem CtxRen.restrict {Ψ Φ Φ1} (he : I.Entails Φ1 Φ) : ∀ {Γ}, CtxRen S Ψ Φ Γ → CtxRen S Ψ Φ1 Γ
  | [], _ => trivial
  | _ :: _, ⟨h1, h2⟩ => ⟨CtxRen.restrict he h1, fun Ψ' Φ' Δ ρ δ hR =>
      h2 Ψ' Φ' Δ ρ δ (hR.restrict hR.hscoped (ent_refl _) (ent_trans hR.ent (ent_subst he _)))⟩

/-- Weaken the target by `k` interval variables. -/
theorem TyRen.wkI {Ψ Φ Γ Ψ' Φ' Δ ρ δ} (h : TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ) (k : Nat) {Φ1 : I}
    (hs : Φ1.Scoped (Ψ' + k)) (he : I.Entails Φ1 (Φ'.subst (wkIv k))) :
    TyRen S Ψ Φ Γ (Ψ' + k) Φ1 (ctxWkI k Δ) ρ (fun i => δ i + k) where
  inj i j hij := h.inj i j (by omega)
  bound i hi := by have := h.bound i hi; omega
  hscoped := hs
  ent := by
    refine ent_trans he ?_
    have := ent_subst h.ent (wkIv k)
    rw [I_subst_subst] at this
    exact this
  look x A hx := by
    rw [lookup_wkI, h.look x A hx]
    simp only [Option.map_some, subst_subst]
    congr 1
  wf := h.wf.wk k he

theorem TyRen.up {Ψ Φ Γ Ψ' Φ' Δ ρ δ} (h : TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ) {A : Tm}
    (hA : CtxRen S Ψ Φ (A :: Γ)) :
    TyRen S Ψ Φ (A :: Γ) Ψ' Φ' (A.subst (rS ρ) (rI δ) :: Δ) (upRen ρ) δ where
  inj := h.inj
  bound := h.bound
  hscoped := h.hscoped
  ent := h.ent
  look x B hx := by
    cases x with
    | zero =>
      simp only [Ctx.lookup, Option.some.injEq] at hx; subst hx
      show some _ = some _
      simp only [shift_eq, subst_subst]; congr 1
    | succ x =>
      simp only [Ctx.lookup, Option.map_eq_some_iff] at hx
      obtain ⟨B0, hB0, rfl⟩ := hx
      show Ctx.lookup _ (ρ x + 1) = _
      simp only [Ctx.lookup, h.look x B0 hB0, Option.map_some, shift_eq, subst_subst]
      congr 1
  wf k Φ'' hs he := by
    obtain ⟨l, hl⟩ := hA.2 _ _ _ _ _ (h.wkI k hs he)
    have hw := h.wf k Φ'' hs he
    simp only [ctxWkI, List.map_cons]
    refine Wf0.cons (l := l) ?_
    have e : (A.subst (rS ρ) (rI δ)).subst Tm.var (wkIv k) = A.subst (rS ρ) (rI fun i => δ i + k) := by
      rw [subst_subst]; rfl
    rw [e]; exact hl

/-- Lift a typed renaming under `m` interval binders. -/
theorem TyRen.dupN {Ψ Φ Γ Ψ' Φ' Δ ρ δ} (h : TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ) (m : Nat) :
    TyRen S (Ψ + m) (Φ.subst (wkIv m)) (ctxWkI m Γ) (Ψ' + m) (Φ'.subst (wkIv m)) (ctxWkI m Δ) ρ
      (upRenN m δ) where
  inj := upRenN_inj h.inj m
  bound := upRenN_bound h.bound m
  hscoped := scoped_subst h.hscoped fun i hi => show i + m < Ψ' + m by omega
  ent := by
    refine ent_trans (ent_subst h.ent (wkIv m)) ?_
    rw [I_subst_subst, I_subst_subst]
    apply eq_ent; apply I_eq_subst_congr; intro i
    simp only [rI, wkIv, I.subst, upRenN_add]; exact I_eq_refl _
  look x A hx := by
    rw [lookup_wkI] at hx
    obtain ⟨A0, hA0, rfl⟩ := Option.map_eq_some_iff.1 hx
    rw [lookup_wkI, h.look x A0 hA0]
    simp only [Option.map_some, subst_subst]
    congr 1
    apply subst_congr
    · intro n; rfl
    · intro i; simp only [rI, wkIv, I.subst, upRenN_add]
  wf := h.wf.wk m (ent_refl _)

theorem TyRen.dup {Ψ Φ Γ Ψ' Φ' Δ ρ δ} (h : TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ) :
    TyRen S (Ψ + 1) Φ.shift Γ.dshift (Ψ' + 1) Φ'.shift Δ.dshift ρ (upRen δ) := by
  rw [Ctx_dshift_eq, Ctx_dshift_eq, I_shift_eq, I_shift_eq]
  exact h.dupN 1

/-- The renaming of a context extension. -/
def renExt (ρ δ : Nat → Nat) : List Tm → List Tm
  | [] => []
  | A :: E => A.subst (rS (upRenN E.length ρ)) (rI δ) :: renExt ρ δ E

theorem renExt_length (ρ δ : Nat → Nat) (E : List Tm) : (renExt ρ δ E).length = E.length := by
  induction E <;> simp_all [renExt]

theorem TyRen.ext {Ψ Φ Γ Ψ' Φ' Δ ρ δ} (h : TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ) :
    ∀ E : List Tm, CtxRen S Ψ Φ (E ++ Γ) →
      TyRen S Ψ Φ (E ++ Γ) Ψ' Φ' (renExt ρ δ E ++ Δ) (upRenN E.length ρ) δ
  | [], _ => h
  | A :: E, hc => by
    have := (TyRen.ext h E hc.1).up hc
    simpa [renExt, upRenN] using this

theorem renExt_range_append (ρ δ : Nat → Nat) (f : Nat → Tm) (E2 : List Tm) (k : Nat) :
    renExt ρ δ ((List.range k).reverse.map f ++ E2) =
      (List.range k).reverse.map (fun j => (f j).subst (rS (upRenN (j + E2.length) ρ)) (rI δ)) ++
        renExt ρ δ E2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.map_cons, List.cons_append, renExt]
    rw [ih]
    congr 3
    simp [List.length_append, List.length_map, List.length_reverse, List.length_range]

theorem renExt_wkI (ρ δ : Nat → Nat) (m : Nat) (E : List Tm) :
    renExt ρ (upRenN m δ) (ctxWkI m E) = ctxWkI m (renExt ρ δ E) := by
  induction E with
  | nil => rfl
  | cons A E ih =>
    simp only [ctxWkI, List.map_cons, renExt, List.length_map] at *
    rw [ih]
    congr 1
    simp only [subst_subst]
    apply subst_congr
    · intro n; rfl
    · intro i; simp only [rI, wkIv, I.subst, upRenN_add]

theorem upRenN_eq_upN (k : Nat) (ρ : Nat → Nat) : rS (upRenN k ρ) = upN k (rS ρ) := (upN_rS k ρ).symm

theorem ctxWkI_append (m : Nat) (E Γ : List Tm) : ctxWkI m (E ++ Γ) = ctxWkI m E ++ ctxWkI m Γ := by
  simp [ctxWkI]

/-- Lift a typed renaming under `m` interval binders, a restriction by `ψ` over them, and a
context extension `E`. -/
theorem TyRen.extI {Ψ Φ Γ Ψ' Φ' Δ ρ δ} (h : TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ) (m : Nat) {ψ : I}
    (hψ : ψ.Scoped m) (E : List Tm)
    (hctx : CtxRen S (Ψ + m) (KubusCore.cof (Φ.ren (· + m)) ψ) (ctxWkI m (E ++ Γ))) :
    TyRen S (Ψ + m) (KubusCore.cof (Φ.ren (· + m)) ψ) (ctxWkI m (E ++ Γ))
      (Ψ' + m) (KubusCore.cof (Φ'.ren (· + m)) ψ) (ctxWkI m (renExt ρ δ E ++ Δ))
      (upRenN E.length ρ) (upRenN m δ) := by
  have hψ' : ψ.subst (rI (upRenN m δ)) = ψ :=
    subst_scoped_id hψ fun i hi => by simp only [rI]; rw [upRenN_lt _ _ hi]
  have h1 := (h.dupN m).restrict (Φ1 := KubusCore.cof (Φ.ren (· + m)) ψ)
    (Φ1' := KubusCore.cof (Φ'.ren (· + m)) ψ)
    ⟨(h.dupN m).hscoped, scoped_mono hψ (by omega)⟩ (ent_and_left _ _)
    (by
      show I.Entails (.and _ ψ) (.and _ (ψ.subst _))
      rw [hψ', I_ren_add_eq, I_ren_add_eq]
      exact ent_and_mono (h.dupN m).ent (ent_refl _))
  rw [ctxWkI_append] at hctx
  have h2 := h1.ext _ hctx
  rw [renExt_wkI, ctxWkI, List.length_map, ← ctxWkI] at h2
  rw [ctxWkI_append, ctxWkI_append]
  exact h2

/-- The branch context of the eliminator, renamed. -/
theorem TyRen.branch {Ψ Φ Γ Ψ' Φ' Δ ρ δ} (hS : SigClosed S) (h : TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ)
    {d : Nat} {D : DataDecl} {c : Nat} {C : Ctor} (hd : S[d]? = some (.data D))
    (hc : D.ctors[c]? = some C) {ps P : Tm} (hps : IsList ps) (hlen : ps.toList.length = D.params.length)
    {ψ : I} (hψ : ψ.Scoped C.dims)
    (hctx : CtxRen S (Ψ + C.dims) (KubusCore.cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)) :
    TyRen S (Ψ + C.dims) (KubusCore.cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)
      (Ψ' + C.dims) (KubusCore.cof (Φ'.ren (· + C.dims)) ψ)
      (D.branchCtx d C (ps.subst (rS ρ) (rI δ)) (P.subst (rS (upRen ρ)) (rI δ)) Δ)
      (upRenN (C.args.length + C.recPos.length) ρ) (upRenN C.dims δ) := by
  let E := (List.range C.recPos.length).reverse.map (DataDecl.branchIhTy C P) ++
    (List.range C.args.length).reverse.map (DataDecl.branchArgTy d D.params.length C ps)
  have hsrc : D.branchCtx d C ps P Γ = ctxWkI C.dims (E ++ Γ) := by
    unfold DataDecl.branchCtx; rw [Ctx_ren_add_eq, List.append_assoc]
  have hlenE : E.length = C.args.length + C.recPos.length := by
    simp [E, List.length_append, List.length_map, List.length_reverse, List.length_range]; omega
  have hE : renExt ρ δ E =
      (List.range C.recPos.length).reverse.map (DataDecl.branchIhTy C (P.subst (rS (upRen ρ)) (rI δ))) ++
      (List.range C.args.length).reverse.map
        (DataDecl.branchArgTy d D.params.length C (ps.subst (rS ρ) (rI δ))) := by
    simp only [E]
    rw [renExt_range_append, ← List.append_nil (List.map _ (List.range C.args.length).reverse),
      renExt_range_append]
    simp only [renExt, List.length_nil, List.append_nil, List.length_map, List.length_reverse,
      List.length_range, Nat.add_zero]
    congr 1
    · apply List.map_congr_left; intro s hs
      have hs' := List.mem_range.1 (List.mem_reverse.1 hs)
      rw [upRenN_eq_upN, show s + C.args.length = C.args.length + s by omega,
        branchIhTy_subst _ _ hs', up_rS]
    · apply List.map_congr_left; intro k _
      rw [upRenN_eq_upN, branchArgTy_subst _ _ (argTy_closed hS hd hc k) hps hlen]
  have htgt : D.branchCtx d C (ps.subst (rS ρ) (rI δ)) (P.subst (rS (upRen ρ)) (rI δ)) Δ =
      ctxWkI C.dims (renExt ρ δ E ++ Δ) := by
    rw [hE]; unfold DataDecl.branchCtx; rw [Ctx_ren_add_eq, List.append_assoc]
  rw [hsrc] at hctx ⊢
  rw [htgt, ← hlenE]
  exact h.extI C.dims hψ E hctx

end KubusCore.Meta
