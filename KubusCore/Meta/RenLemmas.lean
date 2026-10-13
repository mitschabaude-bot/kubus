import KubusCore.Meta.RenDefs

/-!
# Metatheory: lemmas for the renaming theorem
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-! ## Restrictions of derivable judgments are scoped -/

theorem scoped_of_wf : ∀ {Γ : Ctx} {Ψ Φ}, Wf0 S Ψ Φ Γ → Φ.Scoped Ψ
  | [], _, _, .nil h => h
  | _ :: _, _, _, .cons h => scoped_of_wf (wf_of_ty h)

theorem scoped_of_ty {Ψ Φ Γ t A} (h : HasTy0 S Ψ Φ Γ t A) : Φ.Scoped Ψ := scoped_of_wf (wf_of_ty h)
theorem scoped_of_eq {Ψ Φ Γ t u A} (h : EqTm0 S Ψ Φ Γ t u A) : Φ.Scoped Ψ := scoped_of_wf (wf_of_eq h)

theorem scoped_unshift {r : I} {n : Nat} (h : r.shift.Scoped (n + 1)) : r.Scoped n := by
  induction r with
  | zero | one => trivial
  | var i => simp only [I.shift, I.ren, I.subst, I.Scoped] at h; show i < n; omega
  | neg r ih => exact ih h
  | and r s ihr ihs | or r s ihr ihs => exact ⟨ihr h.1, ihs h.2⟩

theorem scoped_cof_right {Φ φ : I} {n : Nat} (h : (cof Φ φ).Scoped n) : φ.Scoped n := h.2

theorem scoped_cof_shift_right {Φ φ : I} {n : Nat} (h : (cof Φ φ).shift.Scoped (n + 1)) : φ.Scoped n :=
  scoped_unshift h.2

/-! ## Renaming and the syntax of the rules -/

theorem rn_dup (ρ : Nat → Nat) : (fun n => (rS ρ n).dshift) = rS ρ := rfl

theorem rn_dshift (t : Tm) (ρ δ : Nat → Nat) :
    (t.dshift).subst (rS ρ) (rI (upRen δ)) = (t.subst (rS ρ) (rI δ)).dshift := by
  rw [dshift_subst, subst_dshift]; rfl

theorem rn_shift (t : Tm) (ρ δ : Nat → Nat) :
    (t.shift).subst (rS (upRen ρ)) (rI δ) = (t.subst (rS ρ) (rI δ)).shift := by
  rw [shift_subst, subst_shift]; rfl

theorem rn_Ishift (r : I) (δ : Nat → Nat) : r.shift.subst (rI (upRen δ)) = (r.subst (rI δ)).shift := by
  simp only [I.shift, I.ren, I_subst_subst]; rfl

theorem lit_subst (i : Nat) (d : Bool) (τ : Nat → I) : (I.lit i d).subst τ = match d with
    | true => τ i | false => .neg (τ i) := by
  cases d <;> rfl

theorem lit_rn (i : Nat) (d : Bool) (δ : Nat → Nat) : (I.lit i d).subst (rI δ) = I.lit (δ i) d := by
  cases d <;> rfl

theorem dset_rn {δ : Nat → Nat} (inj : ∀ i j, δ i = δ j → i = j) (t : Tm) (i : Nat) (d : Bool) (ρ : Nat → Nat) :
    (t.dset i (I.ofDir d)).subst (rS ρ) (rI δ) = (t.subst (rS ρ) (rI δ)).dset (δ i) (I.ofDir d) := by
  rw [face_dset_subst]
  simp only [Tm.dset, Tm.dsubst, subst_subst]
  apply subst_congr
  · intro n; rfl
  · intro j
    simp only [rI, I.subst]
    by_cases h : j = i
    · simp [h]
    · have : δ j ≠ δ i := fun e => h (inj _ _ e)
      simp [h, this]

theorem getD_map_abort (L : List Tm) (k : Nat) (σ : Nat → Tm) (τ : Nat → I) :
    (L.map (·.subst σ τ)).getD k .abort = (L.getD k .abort).subst σ τ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[k]? <;> rfl

theorem elimCon_subst {d : Nat} {C : Ctor} {ps P bs b args : Tm} {rs : List I} (hargs : IsList args)
    (σ : Nat → Tm) (τ : Nat → I) :
    (Tm.papps (Tm.apps b (args.toList ++ C.recPos.map fun k => elim d ps P bs (args.toList.getD k .abort))) rs).subst σ τ =
    Tm.papps (Tm.apps (b.subst σ τ) ((args.subst σ τ).toList ++ C.recPos.map fun k =>
      elim d (ps.subst σ τ) (P.subst (up σ) τ) (bs.subst σ τ) ((args.subst σ τ).toList.getD k .abort)))
      (rs.map (·.subst τ)) := by
  rw [papps_subst, apps_subst, toList_subst hargs, List.map_append, List.map_map]
  congr 3
  apply List.map_congr_left; intro k _
  simp only [Function.comp, Tm.subst, getD_map_abort]

theorem transpCon_subst {S : Sig} (hS : SigClosed S) {d : Nat} {D : DataDecl} {c : Nat} {C : Ctor}
    (hd : S[d]? = some (.data D)) (hc : D.ctors[c]? = some C) {ps args : Tm} {φ : I} {rs : List I}
    (hps : IsList ps) (hargs : IsList args) (hlen : ps.toList.length = D.params.length)
    (σ : Nat → Tm) (τ : Nat → I) :
    (con d c (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs).subst σ τ =
    con d c ((ps.subst (dupS σ) (I.up τ)).dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) (ps.subst (dupS σ) (I.up τ)).toList
        (φ.subst τ) 0 [] (args.subst σ τ).toList)) (rs.map (·.subst τ)) := by
  simp only [Tm.subst, dinst_subst, ofList_subst]
  rw [transpTele_subst σ τ (fun k => argTy_closed hS hd hc k) hlen φ args.toList 0 [] rfl,
    toList_subst hps, toList_subst hargs]
  rfl

end KubusCore.Meta
