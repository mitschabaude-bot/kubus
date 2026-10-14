import Model.Whnf.Near
import Model.Whnf.Sound

/-!
# Good terms: scoped interval points and constructors with their interval arguments

`goodB S m t`: the interval points and faces of `t` are scoped below `m` (under binders, below the
extended stage), and every constructor of `t` is a constructor of the signature with as many interval
arguments as it has dimensions. Typed closed terms are good, and reduction preserves goodness
(`step_good`). Unlike closedness, goodness does not constrain term variables: the contracta of
inductive types substitute parameter lists, which leave term variables when the lists are too short.

Goodness and nearness give closedness (`closed_of_near_good`): reducts of near terms are near
(`step_near`), so the weak-head normal form of a term near a typed one is closed when the term is good.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta

/-- A constructor of the signature applied to as many interval arguments as it has dimensions. -/
def conOK (S : Sig) (d c : ℕ) (rs : List I) : Bool :=
  match S[d]? with
  | some (.data D) => match D.ctors[c]? with
    | some C => rs.length == C.dims
    | none => false
  | _ => false

/-- Interval points scoped below `m`, constructors with their interval arguments. -/
def goodB (S : Sig) (m : ℕ) : Tm → Bool
  | .var _ | .const _ | .univ _ | .abort | .tnil => true
  | .pi A B | .sigma A B | .lam A B | .app A B | .pair A B | .tcons A B => goodB S m A && goodB S m B
  | .fst p | .snd p => goodB S m p
  | .path A a b => goodB S (m + 1) A && goodB S m a && goodB S m b
  | .plam t | .ipi t => goodB S (m + 1) t
  | .papp p r => goodB S m p && r.scopedB m
  | .split φ t ψ u => φ.scopedB m && goodB S m t && ψ.scopedB m && goodB S m u
  | .transp A φ a => goodB S (m + 1) A && φ.scopedB m && goodB S m a
  | .hcomp A φ u a => goodB S m A && φ.scopedB m && goodB S (m + 1) u && goodB S m a
  | .glue A φ T e => goodB S m A && φ.scopedB m && goodB S m T && goodB S m e
  | .glueEl φ e t a => φ.scopedB m && goodB S m e && goodB S m t && goodB S m a
  | .unglue φ e g => φ.scopedB m && goodB S m e && goodB S m g
  | .data _ ps => goodB S m ps
  | .con d c ps args rs => goodB S m ps && goodB S m args && rs.all (·.scopedB m) && conOK S d c rs
  | .elim _ ps P bs t => goodB S m ps && goodB S m P && goodB S m bs && goodB S m t

variable {S : Sig}

/-! ### Interval points -/

theorem sc_iff {r : I} {m : ℕ} : r.scopedB m = true ↔ r.Scoped m := I.scopedB_iff m r

theorem sc_subst {r : I} {m m' : ℕ} (h : r.scopedB m = true) {τ : ℕ → I} (hτ : ∀ i < m, (τ i).scopedB m' = true) :
    (r.subst τ).scopedB m' = true :=
  sc_iff.2 (scoped_subst (sc_iff.1 h) fun i hi => sc_iff.1 (hτ i hi))

theorem sc_ren {r : I} {m m' : ℕ} (h : r.scopedB m = true) {δ : ℕ → ℕ} (hδ : ∀ i < m, δ i < m') :
    (r.ren δ).scopedB m' = true :=
  sc_subst h fun i hi => by simp [I.scopedB, hδ i hi]

theorem sc_shift {r : I} {m : ℕ} (h : r.scopedB m = true) : r.shift.scopedB (m + 1) = true :=
  sc_ren h fun i hi => by omega

theorem sc_mono {r : I} {m m' : ℕ} (h : r.scopedB m = true) (hm : m ≤ m') : r.scopedB m' = true :=
  sc_iff.2 (scoped_mono (sc_iff.1 h) hm)

theorem sc_up {τ : ℕ → I} {m m' : ℕ} (hτ : ∀ i < m, (τ i).scopedB m' = true) :
    ∀ i < m + 1, (I.up τ i).scopedB (m' + 1) = true
  | 0, _ => by simp [I.up, I.scopedB]
  | i + 1, hi => sc_shift (hτ i (by omega))

theorem sc_inst0 {r : I} {m : ℕ} (hr : r.scopedB m = true) : ∀ i < m + 1, (I.inst0 r i).scopedB m = true
  | 0, _ => hr
  | i + 1, hi => by simp [I.inst0, I.scopedB]; omega

theorem sc_ofFace {m : ℕ} : ∀ {α : I.Face}, (∀ l ∈ α, l.1 < m) → (I.ofFace α).scopedB m = true
  | [], _ => rfl
  | (i, d) :: α, h => by
    simp only [I.ofFace, List.foldr_cons] at *
    have hi := h (i, d) (List.mem_cons_self ..)
    have := sc_ofFace (α := α) fun l hl => h l (List.mem_cons_of_mem _ hl)
    simp only [I.ofFace] at this
    simp only [I.scopedB, Bool.and_eq_true]
    exact ⟨by cases d <;> simp [I.lit, I.scopedB, hi], this⟩

theorem sc_ofFaces {m : ℕ} : ∀ {cs : List I.Face}, (∀ α ∈ cs, ∀ l ∈ α, l.1 < m) → (I.ofFaces cs).scopedB m = true
  | [], _ => rfl
  | α :: cs, h => by
    simp only [I.ofFaces, List.foldr_cons] at *
    have := sc_ofFaces (cs := cs) fun β hβ => h β (List.mem_cons_of_mem _ hβ)
    simp only [I.ofFaces] at this
    simp [I.scopedB, sc_ofFace (h α (List.mem_cons_self ..)), this]

theorem sc_forall0 {φ : I} {m : ℕ} (h : φ.scopedB (m + 1) = true) : φ.forall0.scopedB m = true := by
  unfold I.forall0
  refine sc_ofFaces fun α hα l hl => ?_
  obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hα
  obtain ⟨⟨i, d⟩, hl', rfl⟩ := List.mem_map.1 hl
  obtain ⟨hβf, hβ0⟩ := List.mem_filter.1 hβ
  have h1 := faces_scoped (sc_iff.1 h) β hβf (i, d) hl'
  have h2 : i ≠ 0 := by
    have := List.all_eq_true.1 hβ0 (i, d) hl'
    simpa using this
  simp only; omega

/-! ### Renaming and substitution -/

theorem goodB_mono (t : Tm) : ∀ {m m' : ℕ}, goodB S m t = true → m ≤ m' → goodB S m' t = true := by
  induction t with
  | var | const | univ | abort | tnil => intros; rfl
  | pi A B ihA ihB | sigma A B ihA ihB | lam A B ihA ihB | app A B ihA ihB | pair A B ihA ihB
    | tcons A B ihA ihB =>
    intro m m' h hm; simp only [goodB, Bool.and_eq_true] at h ⊢; exact ⟨ihA h.1 hm, ihB h.2 hm⟩
  | fst p ih | snd p ih | data _ p ih => intro m m' h hm; simp only [goodB] at h ⊢; exact ih h hm
  | plam t ih | ipi t ih => intro m m' h hm; simp only [goodB] at h ⊢; exact ih h (by omega)
  | path A a b ihA iha ihb =>
    intro m m' h hm; simp only [goodB, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ihA h.1.1 (by omega), iha h.1.2 hm⟩, ihb h.2 hm⟩
  | papp p r ih =>
    intro m m' h hm; simp only [goodB, Bool.and_eq_true] at h ⊢; exact ⟨ih h.1 hm, sc_mono h.2 hm⟩
  | split φ t ψ u iht ihu =>
    intro m m' h hm; simp only [goodB, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨sc_mono h.1.1.1 hm, iht h.1.1.2 hm⟩, sc_mono h.1.2 hm⟩, ihu h.2 hm⟩
  | transp A φ a ihA iha =>
    intro m m' h hm; simp only [goodB, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ihA h.1.1 (by omega), sc_mono h.1.2 hm⟩, iha h.2 hm⟩
  | hcomp A φ u a ihA ihu iha =>
    intro m m' h hm; simp only [goodB, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨ihA h.1.1.1 hm, sc_mono h.1.1.2 hm⟩, ihu h.1.2 (by omega)⟩, iha h.2 hm⟩
  | glue A φ T e ihA ihT ihe =>
    intro m m' h hm; simp only [goodB, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨ihA h.1.1.1 hm, sc_mono h.1.1.2 hm⟩, ihT h.1.2 hm⟩, ihe h.2 hm⟩
  | glueEl φ e t a ihe iht iha =>
    intro m m' h hm; simp only [goodB, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨sc_mono h.1.1.1 hm, ihe h.1.1.2 hm⟩, iht h.1.2 hm⟩, iha h.2 hm⟩
  | unglue φ e g ihe ihg =>
    intro m m' h hm; simp only [goodB, Bool.and_eq_true] at h ⊢
    exact ⟨⟨sc_mono h.1.1 hm, ihe h.1.2 hm⟩, ihg h.2 hm⟩
  | con d c ps args rs ihps iha =>
    intro m m' h hm; simp only [goodB, Bool.and_eq_true, List.all_eq_true] at h ⊢
    exact ⟨⟨⟨ihps h.1.1.1 hm, iha h.1.1.2 hm⟩, fun r hr => sc_mono (h.1.2 r hr) hm⟩, h.2⟩
  | elim d ps P bs t ihps ihP ihbs iht =>
    intro m m' h hm; simp only [goodB, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨ihps h.1.1.1 hm, ihP h.1.1.2 hm⟩, ihbs h.1.2 hm⟩, iht h.2 hm⟩

theorem conOK_map (d c : ℕ) (rs : List I) (f : I → I) : conOK S d c (rs.map f) = conOK S d c rs := by
  unfold conOK; simp only [List.length_map]

theorem goodB_ren (t : Tm) : ∀ {m m' : ℕ} {ρ δ : ℕ → ℕ}, goodB S m t = true → (∀ i < m, δ i < m') →
    goodB S m' (t.ren ρ δ) = true := by
  have hup : ∀ {m m' : ℕ} {δ : ℕ → ℕ}, (∀ i < m, δ i < m') → ∀ i < m + 1, Tm.upRen δ i < m' + 1 := by
    intro m m' δ h i hi; cases i with
    | zero => simp [Tm.upRen]
    | succ i => simp only [Tm.upRen]; have := h i (by omega); omega
  induction t with
  | var | const | univ | abort | tnil => intros; rfl
  | pi A B ihA ihB | sigma A B ihA ihB | lam A B ihA ihB | app A B ihA ihB | pair A B ihA ihB
    | tcons A B ihA ihB =>
    intro m m' ρ δ h hδ; simp only [goodB, Bool.and_eq_true, Tm.ren] at h ⊢; exact ⟨ihA h.1 hδ, ihB h.2 hδ⟩
  | fst p ih | snd p ih | data _ p ih =>
    intro m m' ρ δ h hδ; simp only [goodB, Tm.ren] at h ⊢; exact ih h hδ
  | plam t ih | ipi t ih =>
    intro m m' ρ δ h hδ; simp only [goodB, Tm.ren] at h ⊢; exact ih h (hup hδ)
  | path A a b ihA iha ihb =>
    intro m m' ρ δ h hδ; simp only [goodB, Bool.and_eq_true, Tm.ren] at h ⊢
    exact ⟨⟨ihA h.1.1 (hup hδ), iha h.1.2 hδ⟩, ihb h.2 hδ⟩
  | papp p r ih =>
    intro m m' ρ δ h hδ; simp only [goodB, Bool.and_eq_true, Tm.ren] at h ⊢; exact ⟨ih h.1 hδ, sc_ren h.2 hδ⟩
  | split φ t ψ u iht ihu =>
    intro m m' ρ δ h hδ; simp only [goodB, Bool.and_eq_true, Tm.ren] at h ⊢
    exact ⟨⟨⟨sc_ren h.1.1.1 hδ, iht h.1.1.2 hδ⟩, sc_ren h.1.2 hδ⟩, ihu h.2 hδ⟩
  | transp A φ a ihA iha =>
    intro m m' ρ δ h hδ; simp only [goodB, Bool.and_eq_true, Tm.ren] at h ⊢
    exact ⟨⟨ihA h.1.1 (hup hδ), sc_ren h.1.2 hδ⟩, iha h.2 hδ⟩
  | hcomp A φ u a ihA ihu iha =>
    intro m m' ρ δ h hδ; simp only [goodB, Bool.and_eq_true, Tm.ren] at h ⊢
    exact ⟨⟨⟨ihA h.1.1.1 hδ, sc_ren h.1.1.2 hδ⟩, ihu h.1.2 (hup hδ)⟩, iha h.2 hδ⟩
  | glue A φ T e ihA ihT ihe =>
    intro m m' ρ δ h hδ; simp only [goodB, Bool.and_eq_true, Tm.ren] at h ⊢
    exact ⟨⟨⟨ihA h.1.1.1 hδ, sc_ren h.1.1.2 hδ⟩, ihT h.1.2 hδ⟩, ihe h.2 hδ⟩
  | glueEl φ e t a ihe iht iha =>
    intro m m' ρ δ h hδ; simp only [goodB, Bool.and_eq_true, Tm.ren] at h ⊢
    exact ⟨⟨⟨sc_ren h.1.1.1 hδ, ihe h.1.1.2 hδ⟩, iht h.1.2 hδ⟩, iha h.2 hδ⟩
  | unglue φ e g ihe ihg =>
    intro m m' ρ δ h hδ; simp only [goodB, Bool.and_eq_true, Tm.ren] at h ⊢
    exact ⟨⟨sc_ren h.1.1 hδ, ihe h.1.2 hδ⟩, ihg h.2 hδ⟩
  | con d c ps args rs ihps iha =>
    intro m m' ρ δ h hδ; simp only [goodB, Bool.and_eq_true, List.all_eq_true, Tm.ren, conOK_map] at h ⊢
    refine ⟨⟨⟨ihps h.1.1.1 hδ, iha h.1.1.2 hδ⟩, fun r hr => ?_⟩, h.2⟩
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
    exact sc_ren (h.1.2 r0 hr0) hδ
  | elim d ps P bs t ihps ihP ihbs iht =>
    intro m m' ρ δ h hδ; simp only [goodB, Bool.and_eq_true, Tm.ren] at h ⊢
    exact ⟨⟨⟨ihps h.1.1.1 hδ, ihP h.1.1.2 hδ⟩, ihbs h.1.2 hδ⟩, iht h.2 hδ⟩

theorem goodB_shift {t : Tm} {m : ℕ} (h : goodB S m t = true) : goodB S m t.shift = true :=
  goodB_ren t h fun _ hi => hi

theorem goodB_dshift {t : Tm} {m : ℕ} (h : goodB S m t = true) : goodB S (m + 1) t.dshift = true :=
  goodB_ren t h fun i hi => by simp; omega

theorem goodB_subst (t : Tm) : ∀ {m m' : ℕ} {σ : ℕ → Tm} {τ : ℕ → I}, goodB S m t = true →
    (∀ x, goodB S m' (σ x) = true) → (∀ i < m, (τ i).scopedB m' = true) →
    goodB S m' (t.subst σ τ) = true := by
  have hup : ∀ {m' : ℕ} {σ : ℕ → Tm}, (∀ x, goodB S m' (σ x) = true) → ∀ x, goodB S m' (Tm.up σ x) = true := by
    intro m' σ h x; cases x with
    | zero => rfl
    | succ x => exact goodB_shift (h x)
  have hd : ∀ {m' : ℕ} {σ : ℕ → Tm}, (∀ x, goodB S m' (σ x) = true) →
      ∀ x, goodB S (m' + 1) ((fun n => (σ n).dshift) x) = true := fun h x => goodB_dshift (h x)
  induction t with
  | var x => intro m m' σ τ _ hσ _; exact hσ x
  | const | univ | abort | tnil => intros; rfl
  | pi A B ihA ihB | sigma A B ihA ihB | lam A B ihA ihB =>
    intro m m' σ τ h hσ hτ; simp only [goodB, Bool.and_eq_true, Tm.subst] at h ⊢
    exact ⟨ihA h.1 hσ hτ, ihB h.2 (hup hσ) hτ⟩
  | app A B ihA ihB | pair A B ihA ihB | tcons A B ihA ihB =>
    intro m m' σ τ h hσ hτ; simp only [goodB, Bool.and_eq_true, Tm.subst] at h ⊢
    exact ⟨ihA h.1 hσ hτ, ihB h.2 hσ hτ⟩
  | fst p ih | snd p ih | data _ p ih =>
    intro m m' σ τ h hσ hτ; simp only [goodB, Tm.subst] at h ⊢; exact ih h hσ hτ
  | plam t ih | ipi t ih =>
    intro m m' σ τ h hσ hτ; simp only [goodB, Tm.subst] at h ⊢; exact ih h (hd hσ) (sc_up hτ)
  | path A a b ihA iha ihb =>
    intro m m' σ τ h hσ hτ; simp only [goodB, Bool.and_eq_true, Tm.subst] at h ⊢
    exact ⟨⟨ihA h.1.1 (hd hσ) (sc_up hτ), iha h.1.2 hσ hτ⟩, ihb h.2 hσ hτ⟩
  | papp p r ih =>
    intro m m' σ τ h hσ hτ; simp only [goodB, Bool.and_eq_true, Tm.subst] at h ⊢
    exact ⟨ih h.1 hσ hτ, sc_subst h.2 hτ⟩
  | split φ t ψ u iht ihu =>
    intro m m' σ τ h hσ hτ; simp only [goodB, Bool.and_eq_true, Tm.subst] at h ⊢
    exact ⟨⟨⟨sc_subst h.1.1.1 hτ, iht h.1.1.2 hσ hτ⟩, sc_subst h.1.2 hτ⟩, ihu h.2 hσ hτ⟩
  | transp A φ a ihA iha =>
    intro m m' σ τ h hσ hτ; simp only [goodB, Bool.and_eq_true, Tm.subst] at h ⊢
    exact ⟨⟨ihA h.1.1 (hd hσ) (sc_up hτ), sc_subst h.1.2 hτ⟩, iha h.2 hσ hτ⟩
  | hcomp A φ u a ihA ihu iha =>
    intro m m' σ τ h hσ hτ; simp only [goodB, Bool.and_eq_true, Tm.subst] at h ⊢
    exact ⟨⟨⟨ihA h.1.1.1 hσ hτ, sc_subst h.1.1.2 hτ⟩, ihu h.1.2 (hd hσ) (sc_up hτ)⟩, iha h.2 hσ hτ⟩
  | glue A φ T e ihA ihT ihe =>
    intro m m' σ τ h hσ hτ; simp only [goodB, Bool.and_eq_true, Tm.subst] at h ⊢
    exact ⟨⟨⟨ihA h.1.1.1 hσ hτ, sc_subst h.1.1.2 hτ⟩, ihT h.1.2 hσ hτ⟩, ihe h.2 hσ hτ⟩
  | glueEl φ e t a ihe iht iha =>
    intro m m' σ τ h hσ hτ; simp only [goodB, Bool.and_eq_true, Tm.subst] at h ⊢
    exact ⟨⟨⟨sc_subst h.1.1.1 hτ, ihe h.1.1.2 hσ hτ⟩, iht h.1.2 hσ hτ⟩, iha h.2 hσ hτ⟩
  | unglue φ e g ihe ihg =>
    intro m m' σ τ h hσ hτ; simp only [goodB, Bool.and_eq_true, Tm.subst] at h ⊢
    exact ⟨⟨sc_subst h.1.1 hτ, ihe h.1.2 hσ hτ⟩, ihg h.2 hσ hτ⟩
  | con d c ps args rs ihps iha =>
    intro m m' σ τ h hσ hτ
    simp only [goodB, Bool.and_eq_true, List.all_eq_true, Tm.subst, conOK_map] at h ⊢
    refine ⟨⟨⟨ihps h.1.1.1 hσ hτ, iha h.1.1.2 hσ hτ⟩, fun r hr => ?_⟩, h.2⟩
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
    exact sc_subst (h.1.2 r0 hr0) hτ
  | elim d ps P bs t ihps ihP ihbs iht =>
    intro m m' σ τ h hσ hτ; simp only [goodB, Bool.and_eq_true, Tm.subst] at h ⊢
    exact ⟨⟨⟨ihps h.1.1.1 hσ hτ, ihP h.1.1.2 (hup hσ) hτ⟩, ihbs h.1.2 hσ hτ⟩, iht h.2 hσ hτ⟩

theorem goodB_dsubst {t : Tm} {m m' : ℕ} (h : goodB S m t = true) {τ : ℕ → I}
    (hτ : ∀ i < m, (τ i).scopedB m' = true) : goodB S m' (t.dsubst τ) = true :=
  goodB_subst t h (fun _ => rfl) hτ

theorem goodB_dinst {t : Tm} {m : ℕ} (h : goodB S (m + 1) t = true) {r : I} (hr : r.scopedB m = true) :
    goodB S m (t.dinst r) = true :=
  goodB_dsubst h (sc_inst0 hr)

theorem goodB_inst {t a : Tm} {m : ℕ} (h : goodB S m t = true) (ha : goodB S m a = true) :
    goodB S m (t.inst a) = true :=
  goodB_subst t h (fun x => by cases x <;> first | exact ha | rfl) fun i hi => by simp [I.scopedB, hi]

/-! ### Typed terms are good -/

theorem goodB_ofList {m : ℕ} : ∀ {L : List Tm}, (∀ t ∈ L, goodB S m t = true) → goodB S m (Tm.ofList L) = true
  | [], _ => rfl
  | t :: L, h => by
    simp only [Tm.ofList, goodB, Bool.and_eq_true]
    exact ⟨h t (List.mem_cons_self ..), goodB_ofList fun t' ht' => h t' (List.mem_cons_of_mem _ ht')⟩

theorem goodB_toList {m : ℕ} : ∀ {t : Tm}, goodB S m t = true → ∀ x ∈ t.toList, goodB S m x = true
  | .tcons a as, h, x, hx => by
    simp only [goodB, Bool.and_eq_true] at h
    simp only [Tm.toList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h.1
    · exact goodB_toList h.2 x hx
  | .var _, _, _, hx | .const _, _, _, hx | .univ _, _, _, hx | .abort, _, _, hx | .tnil, _, _, hx
  | .pi .., _, _, hx | .sigma .., _, _, hx | .lam .., _, _, hx | .app .., _, _, hx | .pair .., _, _, hx
  | .fst _, _, _, hx | .snd _, _, _, hx | .path .., _, _, hx | .plam _, _, _, hx | .papp .., _, _, hx
  | .ipi _, _, _, hx | .split .., _, _, hx | .transp .., _, _, hx | .hcomp .., _, _, hx
  | .glue .., _, _, hx | .glueEl .., _, _, hx | .unglue .., _, _, hx | .data .., _, _, hx
  | .con .., _, _, hx | .elim .., _, _, hx => by simp [Tm.toList] at hx

mutual

theorem good_ty {Ψ Φ Γ t A} : HasTy0 S Ψ Φ Γ t A → goodB S Ψ t = true
  | @HasTy0.var _ Ψ Φ Γ x A h0 h1 => rfl
  | @HasTy0.conv _ Ψ Φ Γ t A B l h0 h1 => good_ty h0
  | @HasTy0.restrict _ Ψ Φ Φ' Γ t A h0 h1 h2 => good_ty h2
  | @HasTy0.const _ Ψ Φ Γ k t A h0 h1 => rfl
  | @HasTy0.univ _ Ψ Φ Γ l h0 h1 => rfl
  | @HasTy0.cumul _ Ψ Φ Γ A l h0 h1 => good_ty h1
  | @HasTy0.pi _ Ψ Φ Γ A B l h0 h1 => by
    simp only [goodB, Bool.and_eq_true]; exact ⟨good_ty h0, by simpa using good_ty h1⟩
  | @HasTy0.lam _ Ψ Φ Γ A B t l h0 h1 => by
    have := good_ty h0
    simp only [goodB, Bool.and_eq_true] at this ⊢; exact ⟨this.1, by simpa using good_ty h1⟩
  | @HasTy0.app _ Ψ Φ Γ A B f a h0 h1 => by
    simp only [goodB, Bool.and_eq_true]; exact ⟨good_ty h0, good_ty h1⟩
  | @HasTy0.sigma _ Ψ Φ Γ A B l h0 h1 => by
    simp only [goodB, Bool.and_eq_true]; exact ⟨good_ty h0, by simpa using good_ty h1⟩
  | @HasTy0.pair _ Ψ Φ Γ A B a b l h0 h1 h2 => by
    simp only [goodB, Bool.and_eq_true]; exact ⟨good_ty h1, good_ty h2⟩
  | @HasTy0.fst _ Ψ Φ Γ A B p h0 => by simp only [goodB]; exact good_ty h0
  | @HasTy0.snd _ Ψ Φ Γ A B p h0 => by simp only [goodB]; exact good_ty h0
  | @HasTy0.path _ Ψ Φ Γ A a b l h0 h1 h2 => by
    simp only [goodB, Bool.and_eq_true]
    exact ⟨⟨by simpa [Ctx.dshift] using good_ty h0, good_ty h1⟩, good_ty h2⟩
  | @HasTy0.plam _ Ψ Φ Γ A a b t l h0 h1 h2 h3 => by
    simp only [goodB]; simpa [Ctx.dshift] using good_ty h1
  | @HasTy0.papp _ Ψ Φ Γ A a b p r h0 h1 => by
    simp only [goodB, Bool.and_eq_true]; exact ⟨good_ty h0, Model.Canon.scopedB_of h1⟩
  | @HasTy0.ipi _ Ψ Φ Γ A l h0 h1 => by
    simp only [goodB]; simpa [Ctx.dshift] using good_ty h1
  | @HasTy0.ilam _ Ψ Φ Γ A t l h0 h1 => by
    simp only [goodB]; simpa [Ctx.dshift] using good_ty h1
  | @HasTy0.iapp _ Ψ Φ Γ A p r h0 h1 => by
    simp only [goodB, Bool.and_eq_true]; exact ⟨good_ty h0, Model.Canon.scopedB_of h1⟩
  | @HasTy0.split _ Ψ Φ Γ A φ ψ t u l h0 h1 h2 h3 h4 h5 h6 => by
    simp only [goodB, Bool.and_eq_true]
    exact ⟨⟨⟨Model.Canon.scopedB_of h0, good_ty h4⟩, Model.Canon.scopedB_of h1⟩, good_ty h5⟩
  | @HasTy0.abort _ Ψ Φ Γ A l h0 h1 => rfl
  | @HasTy0.transp _ Ψ Φ Γ A φ a l h0 h1 h2 h3 => by
    simp only [goodB, Bool.and_eq_true]
    exact ⟨⟨by simpa [Ctx.dshift] using good_ty h0, Model.Canon.scopedB_of h1⟩, good_ty h3⟩
  | @HasTy0.hcomp _ Ψ Φ Γ A φ u a l h0 h1 h2 h3 h4 => by
    simp only [goodB, Bool.and_eq_true]
    exact ⟨⟨⟨good_ty h0, Model.Canon.scopedB_of h1⟩, by simpa [Ctx.dshift] using good_ty h2⟩, good_ty h3⟩
  | @HasTy0.glue _ Ψ Φ Γ A φ T e l h0 h1 h2 h3 => by
    simp only [goodB, Bool.and_eq_true]
    exact ⟨⟨⟨good_ty h0, Model.Canon.scopedB_of h1⟩, good_ty h2⟩, good_ty h3⟩
  | @HasTy0.glueEl _ Ψ Φ Γ A φ T e t a l h0 h1 h2 h3 h4 => by
    have := good_ty h0
    simp only [goodB, Bool.and_eq_true] at this ⊢
    exact ⟨⟨⟨this.1.1.2, good_ty h1⟩, good_ty h2⟩, good_ty h3⟩
  | @HasTy0.unglue _ Ψ Φ Γ A φ T e g l h0 h1 h2 h3 => by
    have := good_ty h0
    simp only [goodB, Bool.and_eq_true] at this ⊢
    exact ⟨⟨this.1.1.2, good_ty h2⟩, good_ty h3⟩
  | @HasTy0.data _ Ψ Φ Γ d D ps h0 h1 h2 => by simp only [goodB]; exact good_tele h2
  | @HasTy0.con _ Ψ Φ Γ d D c C ps args rs h0 h1 h2 h3 h4 h5 h6 h7 => by
    simp only [goodB, Bool.and_eq_true, List.all_eq_true]
    refine ⟨⟨⟨good_tele h4, good_tele h5⟩, fun r hr => Model.Canon.scopedB_of (h7 r hr)⟩, ?_⟩
    simp [conOK, h0, h1, h6]
  | @HasTy0.elim _ Ψ Φ Γ d D ps P bs t m h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
    simp only [goodB, Bool.and_eq_true]
    refine ⟨⟨⟨good_tele h3, by simpa using good_ty h4⟩, ?_⟩, good_ty h9⟩
    rw [h5]
    refine goodB_ofList fun b hb => ?_
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hb
    obtain ⟨C, hC⟩ : ∃ C, D.ctors[c]? = some C :=
      ⟨D.ctors[c]'(by omega), List.getElem?_eq_getElem _⟩
    exact good_ty (h7 c C _ hC (List.getElem?_eq_getElem hc))

theorem good_tele {Ψ Φ Γ ts Δ prev} : HasTele0 S Ψ Φ Γ ts Δ prev → goodB S Ψ ts = true
  | @HasTele0.nil _ Ψ Φ Γ prev h0 => rfl
  | @HasTele0.cons _ Ψ Φ Γ a as A Δ prev h0 h1 => by
    simp only [goodB, Bool.and_eq_true]; exact ⟨good_ty h0, good_tele h1⟩

end

/-! ### The signature is good -/

theorem upRen_id : Tm.upRen id = id := by funext n; cases n <;> rfl

theorem goodB_ren_term (t : Tm) : ∀ (m : ℕ) (ρ : ℕ → ℕ), goodB S m (t.ren ρ id) = goodB S m t := by
  induction t with
  | var | const | univ | abort | tnil => intros; rfl
  | pi A B ihA ihB | sigma A B ihA ihB | lam A B ihA ihB | app A B ihA ihB | pair A B ihA ihB
    | tcons A B ihA ihB => intro m ρ; simp only [goodB, Tm.ren, ihA, ihB]
  | fst p ih | snd p ih | data _ p ih => intro m ρ; simp only [goodB, Tm.ren, ih]
  | plam t ih | ipi t ih => intro m ρ; simp only [goodB, Tm.ren, upRen_id, ih]
  | path A a b ihA iha ihb => intro m ρ; simp only [goodB, Tm.ren, upRen_id, ihA, iha, ihb]
  | papp p r ih => intro m ρ; simp only [goodB, Tm.ren, ih, I_ren_id]
  | split φ t ψ u iht ihu => intro m ρ; simp only [goodB, Tm.ren, iht, ihu, I_ren_id]
  | transp A φ a ihA iha => intro m ρ; simp only [goodB, Tm.ren, upRen_id, ihA, iha, I_ren_id]
  | hcomp A φ u a ihA ihu iha => intro m ρ; simp only [goodB, Tm.ren, upRen_id, ihA, ihu, iha, I_ren_id]
  | glue A φ T e ihA ihT ihe => intro m ρ; simp only [goodB, Tm.ren, ihA, ihT, ihe, I_ren_id]
  | glueEl φ e t a ihe iht iha => intro m ρ; simp only [goodB, Tm.ren, ihe, iht, iha, I_ren_id]
  | unglue φ e g ihe ihg => intro m ρ; simp only [goodB, Tm.ren, ihe, ihg, I_ren_id]
  | con d c ps args rs ihps iha =>
    intro m ρ; simp only [goodB, Tm.ren, ihps, iha, I_ren_id, List.map_id']
  | elim d ps P bs t ihps ihP ihbs iht => intro m ρ; simp only [goodB, Tm.ren, ihps, ihP, ihbs, iht]

section
variable (hW : WfSig S)
include hW

theorem good_defn {k : ℕ} {t A : Tm} (h : S[k]? = some (.defn t A)) (m : ℕ) : goodB S m t = true :=
  goodB_mono t (good_ty (Model.Canon.htr_of hW k ((hW.1 k t A h).2.2.2))) (Nat.zero_le m)

theorem good_point {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor} (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C)
    {k : ℕ} {A : Tm} (hA : C.args[k]? = some (.point A)) (m : ℕ) : goodB S m A = true := by
  have := ((hW.2 d D hD).2.2 c C hC).1 k A hA
  have h := good_ty (Model.Canon.htr_of hW d this.2.2.2.2)
  rw [goodB_ren_term] at h
  exact goodB_mono A h (Nat.zero_le m)

omit hW in
theorem good_paramVars (np n m : ℕ) : goodB S m (Ctor.paramVars np n) = true :=
  goodB_ofList fun t ht => by obtain ⟨p, -, rfl⟩ := List.mem_map.1 ht; rfl

theorem good_argTy {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor} (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C)
    (np k m : ℕ) : goodB S m (C.argTy d np k) = true := by
  unfold Ctor.argTy
  split
  · exact good_point hW hD hC (by assumption) m
  · exact good_paramVars np k m

omit hW in
mutual
theorem good_simple {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) {np c n : ℕ} {C : Ctor} {m N : ℕ} :
    ∀ {b : Tm}, Ctor.simpleB D.ctors d np c n C b = true → b.closedB N m = true → goodB S m b = true
  | .var _, _, _ => rfl
  | .con d' c' ps as rs, h, hc => by
    simp only [Ctor.simpleB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, -⟩, rfl⟩, h⟩ := h
    simp only [Tm.closedB, Bool.and_eq_true, List.all_eq_true] at hc
    split at h
    · rename_i C' hC'
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      simp only [goodB, Bool.and_eq_true, List.all_eq_true]
      exact ⟨⟨⟨good_paramVars _ _ _, good_simpleArgs hD h.2 hc.1.2⟩, hc.2⟩, by simp [conOK, hD, hC', h.1.2]⟩
    · simp at h
  | .const _, h, _ | .univ _, h, _ | .abort, h, _ | .tnil, h, _ | .pi .., h, _ | .sigma .., h, _
  | .lam .., h, _ | .app .., h, _ | .pair .., h, _ | .fst _, h, _ | .snd _, h, _ | .path .., h, _
  | .plam _, h, _ | .papp .., h, _ | .ipi _, h, _ | .split .., h, _ | .transp .., h, _ | .hcomp .., h, _
  | .glue .., h, _ | .glueEl .., h, _ | .unglue .., h, _ | .tcons .., h, _ | .data .., h, _
  | .elim .., h, _ => by simp [Ctor.simpleB] at h
theorem good_simpleArgs {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) {np c n : ℕ} {C C' : Ctor} {m k N : ℕ} :
    ∀ {as : Tm}, Ctor.simpleArgs D.ctors d np c n C C' k as = true → as.closedB N m = true → goodB S m as = true
  | .tcons a as, h, hc => by
    simp only [Ctor.simpleArgs, Bool.and_eq_true] at h
    simp only [Tm.closedB, Bool.and_eq_true] at hc
    simp only [goodB, Bool.and_eq_true]
    refine ⟨?_, good_simpleArgs hD h.2 hc.2⟩
    have h1 := h.1
    split at h1
    · exact good_simple hD h1 hc.1
    · split at h1
      · rfl
      · simp at h1
  | .tnil, _, _ => rfl
  | .var _, h, _ | .const _, h, _ | .univ _, h, _ | .abort, h, _ | .pi .., h, _ | .sigma .., h, _
  | .lam .., h, _ | .app .., h, _ | .pair .., h, _ | .fst _, h, _ | .snd _, h, _ | .path .., h, _
  | .plam _, h, _ | .papp .., h, _ | .ipi _, h, _ | .split .., h, _ | .transp .., h, _ | .hcomp .., h, _
  | .glue .., h, _ | .glueEl .., h, _ | .unglue .., h, _ | .data .., h, _ | .con .., h, _
  | .elim .., h, _ => by simp [Ctor.simpleArgs] at h
end

theorem good_bnd {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor} (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C)
    {k : ℕ} {ψ : I} {b : Tm} (hb : C.bnd[k]? = some (ψ, b)) : goodB S C.dims b = true := by
  have := ((hW.2 d D hD).2.2 c C hC).2.1 k ψ b hb
  exact good_simple hD this.2.2.1 this.2.1

end

/-! ### The contracta -/


theorem sc_bind2 {r : I} {m M : ℕ} (hr : r.scopedB M = true) (hm : m + 2 ≤ M) :
    ∀ i < m + 1, (Tm.bind2 r i).scopedB M = true
  | 0, _ => hr
  | i + 1, hi => by simp [Tm.bind2, I.scopedB]; omega

theorem sc_dinst {φ r : I} {m : ℕ} (hφ : φ.scopedB (m + 1) = true) (hr : r.scopedB m = true) :
    (φ.subst (I.inst0 r)).scopedB m = true := sc_subst hφ (sc_inst0 hr)

macro "good0" : tactic => `(tactic| repeat' (first
  | assumption | rfl | omega | exact id
  | (apply And.intro)
  | (simp only [goodB, Bool.and_eq_true, I.scopedB, decide_eq_true_eq])
  | apply goodB_shift | apply goodB_dshift | apply goodB_dinst | apply goodB_inst
  | apply sc_shift | apply sc_forall0
  | apply sc_dinst
  | (apply goodB_dsubst (m := _ + 1); apply sc_bind2)
  | (apply sc_bind2)
  | (apply goodB_dsubst (m := _ + 1))
  | (apply goodB_subst (m := _ + 1))
  | (apply goodB_subst (m := _))
  | (intro x; rcases x with _ | x <;> dsimp only)
  | (intro i hi; rcases i with _ | _ | i <;> simp [I.scopedB, Tm.bind2] <;> omega)))

theorem good_comp {C u u0 : Tm} {ψ : I} {m : ℕ} (hC : goodB S (m + 1) C = true) (hψ : ψ.scopedB m = true)
    (hu : goodB S (m + 1) u = true) (hu0 : goodB S m u0 = true) : goodB S m (Tm.comp C ψ u u0) = true := by
  simp only [Tm.comp]; good0

theorem good_hfill {A u u0 : Tm} {φ : I} {m : ℕ} (hA : goodB S m A = true) (hφ : φ.scopedB m = true)
    (hu : goodB S (m + 1) u = true) (hu0 : goodB S m u0 = true) : goodB S (m + 1) (Tm.hfill A φ u u0) = true := by
  simp only [Tm.hfill]; good0

theorem good_fill {C u u0 : Tm} {ψ : I} {m : ℕ} (hC : goodB S (m + 1) C = true) (hψ : ψ.scopedB m = true)
    (hu : goodB S (m + 1) u = true) (hu0 : goodB S m u0 = true) : goodB S (m + 1) (Tm.fill C ψ u u0) = true := by
  simp only [Tm.fill]; apply good_comp <;> good0

theorem good_transpFill {A a : Tm} {φ : I} {m : ℕ} (hA : goodB S (m + 1) A = true) (hφ : φ.scopedB m = true)
    (ha : goodB S m a = true) : goodB S (m + 1) (Tm.transpFill A φ a) = true := by
  simp only [Tm.transpFill]; good0

macro "good" : tactic => `(tactic| repeat' (first
  | assumption | rfl | omega | exact id
  | (apply And.intro)
  | (simp only [goodB, Bool.and_eq_true, I.scopedB, decide_eq_true_eq])
  | apply goodB_shift | apply goodB_dshift | apply goodB_dinst | apply goodB_inst
  | apply sc_shift | apply sc_forall0
  | apply good_comp | apply good_hfill | apply good_fill | apply good_transpFill
  | apply sc_dinst
  | (apply goodB_dsubst (m := _ + 1); apply sc_bind2)
  | (apply sc_bind2)
  | (apply goodB_dsubst (m := _ + 1))
  | (apply goodB_subst (m := _ + 1))
  | (apply goodB_subst (m := _))
  | (intro x; rcases x with _ | x <;> dsimp only)
  | (intro i hi; rcases i with _ | _ | i <;> simp [I.scopedB, Tm.bind2] <;> omega)))

theorem good_transpPi {A B a : Tm} {φ : I} {m : ℕ} (hA : goodB S (m + 1) A = true) (hB : goodB S (m + 1) B = true)
    (hφ : φ.scopedB m = true) (ha : goodB S m a = true) : goodB S m (Tm.transpPi A B φ a) = true := by
  simp only [Tm.transpPi]
  good


theorem good_transpSigma {A B a : Tm} {φ : I} {m : ℕ} (hA : goodB S (m + 1) A = true) (hB : goodB S (m + 1) B = true)
    (hφ : φ.scopedB m = true) (ha : goodB S m a = true) : goodB S m (Tm.transpSigma A B φ a) = true := by
  simp only [Tm.transpSigma]
  good

theorem good_transpPath {A x y a : Tm} {φ : I} {m : ℕ} (hA : goodB S (m + 2) A = true) (hx : goodB S (m + 1) x = true)
    (hy : goodB S (m + 1) y = true) (hφ : φ.scopedB m = true) (ha : goodB S m a = true) :
    goodB S m (Tm.transpPath A x y φ a) = true := by
  simp only [Tm.transpPath]; good
  done

theorem good_transpIPi {A a : Tm} {φ : I} {m : ℕ} (hA : goodB S (m + 2) A = true) (hφ : φ.scopedB m = true)
    (ha : goodB S m a = true) : goodB S m (Tm.transpIPi A φ a) = true := by
  simp only [Tm.transpIPi]; good
  done

theorem good_hcompIPi {A u a : Tm} {φ : I} {m : ℕ} (hA : goodB S (m + 1) A = true) (hφ : φ.scopedB m = true)
    (hu : goodB S (m + 1) u = true) (ha : goodB S m a = true) : goodB S m (Tm.hcompIPi A φ u a) = true := by
  simp only [Tm.hcompIPi]; good
  done

theorem good_hcompPi {A B u a : Tm} {φ : I} {m : ℕ} (hA : goodB S m A = true) (hB : goodB S m B = true)
    (hφ : φ.scopedB m = true) (hu : goodB S (m + 1) u = true) (ha : goodB S m a = true) :
    goodB S m (Tm.hcompPi A B φ u a) = true := by
  simp only [Tm.hcompPi]; good
  done

theorem good_hcompSigma {A B u a : Tm} {φ : I} {m : ℕ} (hA : goodB S m A = true) (hB : goodB S m B = true)
    (hφ : φ.scopedB m = true) (hu : goodB S (m + 1) u = true) (ha : goodB S m a = true) :
    goodB S m (Tm.hcompSigma A B φ u a) = true := by
  simp only [Tm.hcompSigma]; good
  done

theorem good_hcompPath {A x y u a : Tm} {φ : I} {m : ℕ} (hA : goodB S (m + 1) A = true) (hx : goodB S m x = true)
    (hy : goodB S m y = true) (hφ : φ.scopedB m = true) (hu : goodB S (m + 1) u = true) (ha : goodB S m a = true) :
    goodB S m (Tm.hcompPath A x y φ u a) = true := by
  simp only [Tm.hcompPath]; good
  done

theorem good_hcompGlue {A T e u a : Tm} {φ ψ : I} {m : ℕ} (hA : goodB S m A = true) (hφ : φ.scopedB m = true)
    (hT : goodB S m T = true) (he : goodB S m e = true) (hψ : ψ.scopedB m = true) (hu : goodB S (m + 1) u = true)
    (ha : goodB S m a = true) : goodB S m (Tm.hcompGlue A φ T e ψ u a) = true := by
  simp only [Tm.hcompGlue]; good
  done

theorem good_transpGlueWith {A T e a : Tm} {δ φ ψ : I} {m : ℕ} (hδ : δ.scopedB m = true) (hA : goodB S (m + 1) A = true)
    (hφ : φ.scopedB (m + 1) = true) (hT : goodB S (m + 1) T = true) (he : goodB S (m + 1) e = true)
    (hψ : ψ.scopedB m = true) (ha : goodB S m a = true) : goodB S m (Tm.transpGlueWith δ A φ T e ψ a) = true := by
  simp only [Tm.transpGlueWith, Tm.fiber, Tm.pathC]; good
  done

theorem good_hcompU {u a : Tm} {φ : I} {m : ℕ} (hφ : φ.scopedB m = true) (hu : goodB S (m + 1) u = true)
    (ha : goodB S m a = true) : goodB S m (Tm.hcompU φ u a) = true := by
  simp only [Tm.hcompU, Tm.lineEquiv, Tm.lineFun, Tm.idIsEquiv, Tm.isEquiv, Tm.isContr, Tm.fiber, Tm.pathC]; good
  done

/-! ### Lists and the contracta of inductive types -/

theorem good_getD {L : List Tm} {m : ℕ} (hL : ∀ x ∈ L, goodB S m x = true) {d : Tm} (hd : goodB S m d = true) (j : ℕ) :
    goodB S m (L.getD j d) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases h : L[j]? with
  | none => exact hd
  | some x => exact hL x (List.mem_of_getElem? h)

theorem good_substList {A : Tm} {L : List Tm} {m : ℕ} (hA : goodB S m A = true) (hL : ∀ x ∈ L, goodB S m x = true) :
    goodB S m (A.substList L) = true :=
  goodB_subst A hA (fun j => good_getD hL rfl j) fun i hi => by simp [I.scopedB, hi]

theorem good_apps {m : ℕ} : ∀ {L : List Tm} {f : Tm}, goodB S m f = true → (∀ x ∈ L, goodB S m x = true) →
    goodB S m (Tm.apps f L) = true
  | [], f, hf, _ => hf
  | a :: L, f, hf, hL => by
    simp only [Tm.apps, List.foldl_cons]
    exact good_apps (L := L) (by simp only [goodB, Bool.and_eq_true]; exact ⟨hf, hL a (List.mem_cons_self ..)⟩)
      fun x hx => hL x (List.mem_cons_of_mem _ hx)

theorem good_papps {m : ℕ} : ∀ {rs : List I} {f : Tm}, goodB S m f = true → (∀ r ∈ rs, r.scopedB m = true) →
    goodB S m (Tm.papps f rs) = true
  | [], f, hf, _ => hf
  | r :: rs, f, hf, hr => by
    simp only [Tm.papps, List.foldl_cons]
    exact good_papps (rs := rs) (by simp only [goodB, Bool.and_eq_true]; exact ⟨hf, hr r (List.mem_cons_self ..)⟩)
      fun x hx => hr x (List.mem_cons_of_mem _ hx)

theorem good_lams {m : ℕ} : ∀ {Ts : List Tm} {b : Tm}, (∀ x ∈ Ts, goodB S m x = true) → goodB S m b = true →
    goodB S m (Model.Canon.lams Ts b) = true
  | [], b, _, hb => hb
  | T :: Ts, b, hT, hb => by
    simp only [Model.Canon.lams, List.foldr_cons, goodB, Bool.and_eq_true]
    exact ⟨hT T (List.mem_cons_self ..), good_lams (Ts := Ts) (fun x hx => hT x (List.mem_cons_of_mem _ hx)) hb⟩

theorem good_transpTele (argTy : ℕ → Tm) {m : ℕ} (hA : ∀ k, goodB S (m + 1) (argTy k) = true) {psL : List Tm}
    (hps : ∀ x ∈ psL, goodB S (m + 1) x = true) {φ : I} (hφ : φ.scopedB m = true) :
    ∀ (as : List Tm) (k : ℕ) (fills : List Tm), (∀ x ∈ fills, goodB S (m + 1) x = true) →
      (∀ x ∈ as, goodB S m x = true) → ∀ x ∈ Tm.transpTele argTy psL φ k fills as, goodB S m x = true
  | [], _, _, _, _ => by simp [Tm.transpTele]
  | a :: as, k, fills, hf, ha => by
    have hL : goodB S (m + 1) ((argTy k).substList (fills ++ psL.reverse)) = true :=
      good_substList (hA k) fun x hx => by
        rcases List.mem_append.1 hx with h | h
        · exact hf x h
        · exact hps x (List.mem_reverse.1 h)
    have ha0 := ha a (List.mem_cons_self ..)
    intro x hx
    simp only [Tm.transpTele, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [goodB, Bool.and_eq_true]; exact ⟨⟨hL, hφ⟩, ha0⟩
    · refine good_transpTele argTy hA hps hφ as (k + 1) _ (fun y hy => ?_) (fun y hy => ha y (List.mem_cons_of_mem _ hy)) x hx
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact good_transpFill hL hφ ha0
      · exact hf y hy

theorem good_hcompTele (C : Ctor) (argTy : ℕ → Tm) {m : ℕ} (hA : ∀ k, goodB S (m + 1) (argTy k) = true) {dT : Tm}
    (hdT : goodB S m dT = true) {psL : List Tm} (hps : ∀ x ∈ psL, goodB S (m + 1) x = true) {φ : I}
    (hφ : φ.scopedB m = true) :
    ∀ (us as : List Tm) (k : ℕ) (fills : List Tm), (∀ x ∈ fills, goodB S (m + 1) x = true) →
      (∀ x ∈ us, goodB S (m + 1) x = true) → (∀ x ∈ as, goodB S m x = true) →
      ∀ x ∈ Tm.hcompTele C argTy dT psL φ k fills us as, goodB S m x = true
  | [], _, _, _, _, _, _ => by intro x hx; cases ‹List Tm› <;> simp [Tm.hcompTele] at hx
  | _ :: _, [], _, _, _, _, _ => by simp [Tm.hcompTele]
  | u :: us, a :: as, k, fills, hf, hu, ha => by
    have hL : goodB S (m + 1) ((argTy k).substList (fills ++ psL.reverse)) = true :=
      good_substList (hA k) fun x hx => by
        rcases List.mem_append.1 hx with h | h
        · exact hf x h
        · exact hps x (List.mem_reverse.1 h)
    have hu0 := hu u (List.mem_cons_self ..)
    have ha0 := ha a (List.mem_cons_self ..)
    have hus : ∀ y ∈ us, goodB S (m + 1) y = true := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    have has : ∀ y ∈ as, goodB S m y = true := fun y hy => ha y (List.mem_cons_of_mem _ hy)
    intro x hx
    simp only [Tm.hcompTele] at hx
    split at hx
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp only [goodB, Bool.and_eq_true]; exact ⟨⟨⟨hdT, hφ⟩, hu0⟩, ha0⟩
      · refine good_hcompTele C argTy hA hdT hps hφ us as (k + 1) _ (fun y hy => ?_) hus has x hx
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact good_hfill hdT hφ hu0 ha0
        · exact hf y hy
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact good_comp hL hφ hu0 ha0
      · refine good_hcompTele C argTy hA hdT hps hφ us as (k + 1) _ (fun y hy => ?_) hus has x hx
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact good_fill hL hφ hu0 ha0
        · exact hf y hy


theorem good_wkN {t : Tm} {m : ℕ} (h : goodB S m t = true) (k : ℕ) : goodB S m (t.wkN k 0) = true :=
  goodB_ren t h fun i hi => by simpa using hi

section
variable (hW : WfSig S)
include hW

theorem good_branchArgTy {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor} (hD : S[d]? = some (.data D))
    (hC : D.ctors[c]? = some C) {ps : Tm} {m : ℕ} (hps : goodB S m ps = true) (np k : ℕ) :
    goodB S m (DataDecl.branchArgTy d np C ps k) = true := by
  unfold DataDecl.branchArgTy
  refine good_substList (good_argTy hW hD hC np k m) fun x hx => ?_
  rcases List.mem_append.1 hx with h | h
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h; rfl
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    exact good_wkN (goodB_toList hps p (List.mem_reverse.1 hp)) k

omit hW in
theorem good_branchIhTy (C : Ctor) {P : Tm} {m : ℕ} (hP : goodB S m P = true) (s : ℕ) :
    goodB S m (DataDecl.branchIhTy C P s) = true :=
  goodB_subst P hP (fun x => by cases x <;> rfl) fun i hi => by simp [I.scopedB, hi]

theorem good_branchesOf {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) {ps P : Tm} {m : ℕ}
    (hps : goodB S m ps = true) (hP : goodB S m P = true) {body : ℕ → Ctor → Tm}
    (hb : ∀ c C, D.ctors[c]? = some C → goodB S m (body c C) = true) :
    goodB S m (Model.Canon.branchesOf D d ps P body) = true := by
  unfold Model.Canon.branchesOf
  refine goodB_ofList fun t ht => ?_
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem ht
  have hc2 : c < D.ctors.length := by simpa using hc
  simp only [List.getElem_mapIdx]
  have hc' : D.ctors[c]? = some D.ctors[c] := List.getElem?_eq_getElem hc2
  refine good_lams (fun x hx => ?_) (hb c _ hc')
  rcases List.mem_append.1 hx with h | h
  · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h; exact good_branchArgTy hW hD hc' hps _ k
  · obtain ⟨s, -, rfl⟩ := List.mem_map.1 h; exact good_branchIhTy _ hP s

theorem good_proj {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) {ps t : Tm} {m : ℕ}
    (hps : goodB S m ps = true) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) (j : ℕ) (ht : goodB S m t = true) :
    goodB S m (Model.Canon.proj d D ps c C j t) = true := by
  have hQ : goodB S m (Model.Canon.projQ d D ps c C j) = true := by
    unfold Model.Canon.projQ
    simp only [goodB, Bool.and_eq_true]
    refine ⟨⟨⟨hps, trivial⟩, good_branchesOf hW hD hps rfl fun c' C' _ => ?_⟩, trivial⟩
    unfold Model.Canon.projQBody
    split
    · refine good_substList (good_argTy hW hD hC _ _ _) fun x hx => ?_
      rcases List.mem_append.1 hx with h | h
      · obtain ⟨y, hy, rfl⟩ := List.mem_reverse.1 h |> List.mem_of_mem_take |> List.mem_map.1
        rfl
      · exact goodB_toList hps x (List.mem_reverse.1 h)
    · simp only [goodB, Bool.and_eq_true]; exact ⟨hps, hps⟩
  unfold Model.Canon.proj
  simp only [goodB, Bool.and_eq_true]
  refine ⟨⟨⟨hps, hQ⟩, good_branchesOf hW hD hps hQ fun c' C' _ => ?_⟩, ht⟩
  unfold Model.Canon.projBody
  split
  · rfl
  · simp only [goodB, Bool.and_eq_true]; exact ⟨hps, trivial⟩

theorem good_bndAt {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor} (hD : S[d]? = some (.data D))
    (hC : D.ctors[c]? = some C) {k : ℕ} {ψ : I} {b : Tm} (hb : C.bnd[k]? = some (ψ, b)) {ps args : List Tm}
    {rs : List I} {m : ℕ} (hps : ∀ x ∈ ps, goodB S m x = true) (hargs : ∀ x ∈ args, goodB S m x = true)
    (hrs : ∀ r ∈ rs, r.scopedB m = true) (hl : rs.length = C.dims) :
    goodB S m (Ctor.bndAt b ps args rs) = true := by
  unfold Ctor.bndAt
  refine goodB_subst b (good_bnd hW hD hC hb) (fun j => good_getD (fun x hx => ?_) rfl j) fun i hi => ?_
  · rcases List.mem_append.1 hx with h | h
    · exact hargs x (List.mem_reverse.1 h)
    · exact hps x (List.mem_reverse.1 h)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
    exact hrs _ (List.mem_reverse.1 (List.getElem_mem _))

end


section
variable (hW : WfSig S)
include hW

/-- Reduction preserves goodness. -/
theorem step_good (t : Tm) : ∀ {m : ℕ} {u : Tm}, goodB S m t = true → step S t = some u → goodB S m u := by
  induction t with
  | var | univ | abort | tnil | pi | sigma | lam | pair | path | plam | ipi | tcons | data =>
    intro m u _ hs; simp [step] at hs
  | const c =>
    intro m u _ hs
    simp only [step] at hs
    split at hs
    · cases hs; exact good_defn hW (by assumption) m
    · cases hs
  | app f a ihf iha =>
    intro m u hg hs
    simp only [goodB, Bool.and_eq_true] at hg
    by_cases hl : ∃ A t, f = .lam A t
    · obtain ⟨A, t, rfl⟩ := hl
      simp only [step, Option.some.injEq] at hs; subst hs
      simp only [goodB, Bool.and_eq_true] at hg
      exact goodB_inst hg.1.2 hg.2
    · rw [step_app_eq S f a (fun A t e => hl ⟨A, t, e⟩)] at hs
      obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.1 hs
      simp only [goodB, Bool.and_eq_true]; exact ⟨ihf hg.1 hf', hg.2⟩
  | fst p ih =>
    intro m u hg hs
    simp only [goodB] at hg
    by_cases hl : ∃ a b, p = .pair a b
    · obtain ⟨a, b, rfl⟩ := hl
      simp only [step, Option.some.injEq] at hs; subst hs
      simp only [goodB, Bool.and_eq_true] at hg; exact hg.1
    · rw [step_fst_eq S p (fun a b e => hl ⟨a, b, e⟩)] at hs
      obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.1 hs
      simp only [goodB]; exact ih hg hp'
  | snd p ih =>
    intro m u hg hs
    simp only [goodB] at hg
    by_cases hl : ∃ a b, p = .pair a b
    · obtain ⟨a, b, rfl⟩ := hl
      simp only [step, Option.some.injEq] at hs; subst hs
      simp only [goodB, Bool.and_eq_true] at hg; exact hg.2
    · rw [step_snd_eq S p (fun a b e => hl ⟨a, b, e⟩)] at hs
      obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.1 hs
      simp only [goodB]; exact ih hg hp'
  | papp p r ih =>
    intro m u hg hs
    simp only [goodB, Bool.and_eq_true] at hg
    by_cases hl : ∃ t, p = .plam t
    · obtain ⟨t, rfl⟩ := hl
      simp only [step, Option.some.injEq] at hs; subst hs
      simp only [goodB] at hg; exact goodB_dinst hg.1 hg.2
    · rw [step_papp_eq S p r (fun t e => hl ⟨t, e⟩)] at hs
      obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.1 hs
      simp only [goodB, Bool.and_eq_true]; exact ⟨ih hg.1 hp', hg.2⟩
  | split φ t ψ u' iht ihu =>
    intro m u hg hs
    simp only [goodB, Bool.and_eq_true] at hg
    simp only [step] at hs
    split_ifs at hs <;> cases hs
    · exact hg.1.1.2
    · exact hg.2
  | glue A φ T e =>
    intro m u hg hs
    simp only [goodB, Bool.and_eq_true] at hg
    simp only [step] at hs
    split_ifs at hs; cases hs; exact hg.1.2
  | glueEl φ e t a =>
    intro m u hg hs
    simp only [goodB, Bool.and_eq_true] at hg
    simp only [step] at hs
    split_ifs at hs; cases hs; exact hg.1.2
  | unglue φ e g ihe ihg =>
    intro m u hg hs
    simp only [goodB, Bool.and_eq_true] at hg
    simp only [step] at hs
    split_ifs at hs
    · cases hs; simp only [goodB, Bool.and_eq_true]; exact ⟨hg.1.2, hg.2⟩
    · revert hs
      generalize hgs : step S g = og
      rcases og with _ | g'
      · intro hs
        cases g <;> simp at hs
        subst hs; simp only [goodB, Bool.and_eq_true] at hg; exact hg.2.2
      · intro hs; cases hs
        simp only [goodB, Bool.and_eq_true]; exact ⟨hg.1, ihg hg.2 hgs⟩
  | con d c ps args rs =>
    intro m u hg hs
    simp only [goodB, Bool.and_eq_true, List.all_eq_true] at hg
    simp only [step] at hs
    split at hs
    · rename_i D hD
      split at hs
      · rename_i C hC
        obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hs
        obtain ⟨k, ψ, hk, -⟩ := firstBnd_spec hb
        have hl : rs.length = C.dims := by simpa [conOK, hD, hC] using hg.2
        exact good_bndAt hW hD hC hk (goodB_toList hg.1.1.1) (goodB_toList hg.1.1.2) hg.1.2 hl
      · cases hs
    · cases hs
  | elim d ps P bs t ihps ihP ihbs iht =>
    intro m u hg hs
    simp only [goodB, Bool.and_eq_true] at hg
    simp only [step] at hs
    split at hs
    · rename_i t' ht'
      cases hs; simp only [goodB, Bool.and_eq_true]; exact ⟨hg.1, iht hg.2 ht'⟩
    · split at hs
      · rename_i d' c qs args rs
        split_ifs at hs
        split at hs
        · rename_i D b hD hb
          split at hs
          · rename_i C hC
            cases hs
            have ht := hg.2
            simp only [goodB, Bool.and_eq_true, List.all_eq_true] at ht
            refine good_papps (good_apps (goodB_toList hg.1.2 b (List.mem_of_getElem? hb)) fun x hx => ?_) ht.1.2
            rcases List.mem_append.1 hx with h | h
            · exact goodB_toList ht.1.1.2 x h
            · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h
              simp only [goodB, Bool.and_eq_true]
              exact ⟨hg.1, good_getD (goodB_toList ht.1.1.2) rfl k⟩
          · cases hs
        · cases hs
      · rename_i d' qs φ u a
        split at hs
        · split_ifs at hs
          cases hs
          have ht := hg.2
          simp only [goodB, Bool.and_eq_true] at ht
          have hps1 : goodB S (m + 1) ps.dshift = true := goodB_dshift hg.1.1.1
          refine good_comp ?_ ht.1.1.2 ?_ ?_
          · refine goodB_subst P hg.1.1.2 (fun x => ?_) fun i hi => by simp [I.scopedB]; omega
            cases x
            · exact good_hfill (by simpa [goodB] using hg.1.1.1) ht.1.1.2 ht.1.2 ht.2
            · rfl
          · simp only [goodB, Bool.and_eq_true]
            exact ⟨⟨⟨hps1, goodB_dshift hg.1.1.2⟩, goodB_dshift hg.1.2⟩, ht.1.2⟩
          · simp only [goodB, Bool.and_eq_true]; exact ⟨hg.1, ht.2⟩
        · cases hs
      · cases hs
  | transp A φ a ihA iha =>
    intro m u hg hs
    simp only [goodB, Bool.and_eq_true] at hg
    obtain ⟨⟨hA, hφ⟩, ha⟩ := hg
    simp only [step] at hs
    split_ifs at hs with hent
    · cases hs; exact ha
    split at hs
    · rename_i A' hA'
      cases hs; simp only [goodB, Bool.and_eq_true]; exact ⟨⟨ihA hA hA', hφ⟩, ha⟩
    split at hs
    all_goals first | (cases hs; done) | skip
    · cases hs; exact ha
    · cases hs; simp only [goodB, Bool.and_eq_true] at hA; exact good_transpPi hA.1 hA.2 hφ ha
    · cases hs; simp only [goodB, Bool.and_eq_true] at hA; exact good_transpSigma hA.1 hA.2 hφ ha
    · cases hs; simp only [goodB, Bool.and_eq_true] at hA; exact good_transpPath hA.1.1 hA.1.2 hA.2 hφ ha
    · cases hs; simp only [goodB] at hA; exact good_transpIPi hA hφ ha
    · cases hs; simp only [goodB, Bool.and_eq_true] at hA
      exact good_transpGlueWith (sc_forall0 hA.1.1.2) hA.1.1.1 hA.1.1.2 hA.1.2 hA.2 hφ ha
    · rename_i _ d ps
      simp only [goodB] at hA
      split at hs
      · rename_i D hD
        split_ifs at hs with hp
        · cases hs; exact ha
        split at hs
        · rename_i a' ha'
          cases hs; simp only [goodB, Bool.and_eq_true]; exact ⟨⟨by simpa [goodB] using hA, hφ⟩, iha ha ha'⟩
        split at hs
        · rename_i d' c qs args rs
          split_ifs at hs with hd
          split at hs
          · rename_i C hC
            cases hs
            simp only [ne_eq, Decidable.not_not] at hd; subst hd
            simp only [goodB, Bool.and_eq_true, List.all_eq_true] at ha ⊢
            refine ⟨⟨⟨goodB_dinst hA rfl, goodB_ofList (good_transpTele _ (fun k => good_argTy hW hD hC _ k _)
              (goodB_toList hA) hφ _ 0 [] (by simp) (goodB_toList ha.1.1.2))⟩, ha.1.2⟩, ha.2⟩
          · cases hs
        · split at hs
          · cases hs
            simp only [goodB, Bool.and_eq_true] at ha ⊢
            obtain ⟨⟨⟨_, hψ⟩, hu0⟩, ha0⟩ := ha
            good
          · cases hs
        · cases hs
      · cases hs
  | hcomp A φ u0 a ihA ihu iha =>
    intro m u hg hs
    simp only [goodB, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨hA, hφ⟩, hu⟩, ha⟩ := hg
    simp only [step] at hs
    split_ifs at hs with hent
    · cases hs; exact goodB_dinst hu rfl
    split at hs
    · rename_i A' hA'
      cases hs; simp only [goodB, Bool.and_eq_true]; exact ⟨⟨⟨ihA hA hA', hφ⟩, hu⟩, ha⟩
    split at hs
    all_goals first | (cases hs; done) | skip
    · cases hs; exact good_hcompU hφ hu ha
    · cases hs; simp only [goodB, Bool.and_eq_true] at hA; exact good_hcompPi hA.1 hA.2 hφ hu ha
    · cases hs; simp only [goodB, Bool.and_eq_true] at hA; exact good_hcompSigma hA.1 hA.2 hφ hu ha
    · cases hs; simp only [goodB, Bool.and_eq_true] at hA; exact good_hcompPath hA.1.1 hA.1.2 hA.2 hφ hu ha
    · cases hs; simp only [goodB] at hA; exact good_hcompIPi hA hφ hu ha
    · cases hs; simp only [goodB, Bool.and_eq_true] at hA
      exact good_hcompGlue hA.1.1.1 hA.1.1.2 hA.1.2 hA.2 hφ hu ha
    · rename_i _ d ps
      simp only [goodB] at hA
      split at hs
      · rename_i D hD
        split_ifs at hs with hp
        split at hs
        · rename_i a' ha'
          cases hs; simp only [goodB, Bool.and_eq_true]; exact ⟨⟨⟨by simpa [goodB] using hA, hφ⟩, hu⟩, iha ha ha'⟩
        split at hs
        · rename_i d' c qs args
          split_ifs at hs with hd
          split at hs
          · rename_i C hC
            cases hs
            simp only [ne_eq, Decidable.not_not] at hd; subst hd
            simp only [goodB, Bool.and_eq_true, List.all_eq_true] at ha ⊢
            refine ⟨⟨⟨hA, goodB_ofList (good_hcompTele C _ (fun k => good_argTy hW hD hC _ k _)
              (by simpa [goodB] using hA) (goodB_toList (goodB_dshift hA)) hφ _ _ 0 [] (by simp)
              (fun x hx => ?_) (goodB_toList ha.1.1.2))⟩, ha.1.2⟩, ha.2⟩
            obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
            exact good_proj hW hD (goodB_dshift hA) hC j hu
          · cases hs
        · cases hs
      · cases hs

end

end Model.Whnf
