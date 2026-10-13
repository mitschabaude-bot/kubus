import KubusCore.Meta.PresupB

/-!
# Metatheory: iterated application through telescopes

Typing `Tm.apps` through a Π-telescope (`HasTele0` of the arguments) and `Tm.papps` through
iterated `(i : I) → _`.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-- The substitution of `substList`. -/
def slS (L : List Tm) : Nat → Tm := fun j => L.getD j (var (j - L.length))

theorem substList_eq (L : List Tm) (t : Tm) : t.substList L = t.subst (slS L) I.var := rfl

theorem substList_nil (t : Tm) : t.substList [] = t := by
  rw [substList_eq]; apply subst_id_of _ (fun _ => rfl); intro n; simp [slS]

theorem pi_substList (A B : Tm) (L : List Tm) :
    (pi A B).substList L = pi (A.substList L) (B.subst (up (slS L)) I.var) := rfl

theorem up_slS_inst (B a : Tm) (L : List Tm) :
    (B.subst (up (slS L)) I.var).inst a = B.substList (a :: L) := by
  simp only [Tm.inst, subst_subst, substList_eq]
  apply subst_congr
  · intro n; cases n with
    | zero => rfl
    | succ n =>
      simp only [up, shift_subst, slS]
      rw [subst_id_of (fun _ => rfl) (fun _ => rfl)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.length_cons]
      congr 2; omega
  · intro i; rfl

/-- Application through a Π-telescope. -/
theorem apps_tele {Ψ Φ Γ} : ∀ {as Δ prev}, HasTele0 S Ψ Φ Γ as Δ prev → ∀ {f base},
    HasTy0 S Ψ Φ Γ f ((Δ.foldr pi base).substList prev) →
    HasTy0 S Ψ Φ Γ (Tm.apps f as.toList) (base.substList (as.toList.reverse ++ prev))
  | _, _, _, .nil _, _, _, hf => hf
  | _, _, _, .cons (a := a) (as := as) (Δ := Δ) (prev := prev) ha hs, f, base, hf => by
    have h1 : HasTy0 S Ψ Φ Γ (app f a) ((Δ.foldr pi base).substList (a :: prev)) := by
      rw [← up_slS_inst]; exact HasTy0.app hf ha
    have := apps_tele hs h1
    simpa [Tm.toList, Tm.apps, List.foldl] using this

/-- `(i₁ … iₘ : I) → B`, as in `DataDecl.branchTy`. -/
def ipis (m : Nat) (B : Tm) : Tm := (List.range m).foldl (fun acc _ => Tm.ipi acc) B

theorem ipis_succ (m : Nat) (B : Tm) : ipis (m + 1) B = ipi (ipis m B) := by
  simp only [ipis, List.range_succ, List.foldl_append, List.foldl]

/-- Instantiate the interval variables `0, 1, …` by the reversed list `rs`, then continue with `τ`. -/
def consIs : List I → (Nat → I) → Nat → I
  | [], τ => τ
  | r :: rs, τ => consIs rs (consI r τ)

theorem consIs_eq : ∀ (rs : List I) (τ : Nat → I) (i : Nat),
    consIs rs τ i = rs.reverse.getD i (τ (i - rs.length))
  | [], τ, i => by simp [consIs]
  | r :: rs, τ, i => by
    rw [consIs, consIs_eq rs]
    simp only [List.reverse_cons, List.getD_eq_getElem?_getD, List.length_cons]
    by_cases h : i < rs.length
    · rw [List.getElem?_append_left (by simpa using h),
        List.getElem?_eq_getElem (by simpa using h)]; rfl
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_reverse]
      by_cases h' : i = rs.length
      · subst h'; simp [consI]
      · rw [show i - rs.length = (i - (rs.length + 1)) + 1 by omega]
        rw [List.getElem?_eq_none (by simp; omega)]; simp [consI]

theorem dup_dinst (t : Tm) (σ : Nat → Tm) (τ : Nat → I) (r : I) :
    (t.subst (dupS σ) (I.up τ)).dinst r = t.subst σ (consI r τ) := by
  simp only [Tm.dinst, Tm.dsubst, subst_subst]
  apply subst_congr
  · intro n; simp only [dupS]; rw [dshift_subst]; exact subst_id_of (fun _ => rfl) (fun _ => rfl) _
  · intro i; cases i with
    | zero => rfl
    | succ i => simp only [I.up, I.shift, I_ren_subst]; exact I_subst_var _

/-- Interval application through iterated `(i : I) → _`. -/
theorem papps_ipis {Ψ Φ Γ σ B} : ∀ (rs : List I) {g τ}, (∀ r ∈ rs, r.Scoped Ψ) →
    HasTy0 S Ψ Φ Γ g ((ipis rs.length B).subst σ τ) →
    HasTy0 S Ψ Φ Γ (Tm.papps g rs) (B.subst σ (consIs rs τ))
  | [], g, τ, _, hg => hg
  | r :: rs, g, τ, hrs, hg => by
    rw [List.length_cons, ipis_succ] at hg
    have h1 := HasTy0.iapp hg (hrs r (List.mem_cons_self ..))
    rw [dup_dinst] at h1
    exact papps_ipis rs (fun r' h => hrs r' (List.mem_cons_of_mem _ h)) h1

end KubusCore.Meta
