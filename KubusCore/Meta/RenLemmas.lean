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

section
variable (σ : Nat → Tm) (τ : Nat → I)

theorem dshift_toList' {ps : Tm} (h : IsList ps) : ps.dshift.toList = ps.toList.map Tm.dshift := by
  rw [dshift_eq ps, toList_subst h]; congr 1; funext x; rw [dshift_eq]

theorem comp_subst (C : Tm) (ψ : I) (u u0 : Tm) :
    (comp C ψ u u0).subst σ τ =
      comp (C.subst (dupS σ) (I.up τ)) (ψ.subst τ) (u.subst (dupS σ) (I.up τ)) (u0.subst σ τ) := by
  simp only [comp]; scalc

theorem fill_subst (C : Tm) (ψ : I) (u u0 : Tm) :
    (fill C ψ u u0).subst (dupS σ) (I.up τ) =
      fill (C.subst (dupS σ) (I.up τ)) (ψ.subst τ) (u.subst (dupS σ) (I.up τ)) (u0.subst σ τ) := by
  simp only [fill, comp]; scalc

theorem hfill_subst (A : Tm) (φ : I) (u u0 : Tm) :
    (hfill A φ u u0).subst (dupS σ) (I.up τ) =
      hfill (A.subst σ τ) (φ.subst τ) (u.subst (dupS σ) (I.up τ)) (u0.subst σ τ) := by
  simp only [hfill]; scalc

theorem dshift_subst_dup (t : Tm) : t.dshift.subst (dupS σ) (I.up τ) = (t.subst σ τ).dshift := by
  scalc

theorem hcompTele_subst {C : Ctor} {argTy : Nat → Tm} {np : Nat}
    (hA : ∀ k, (argTy k).closedB (np + k) 0 = true) {dataT : Tm}
    {psL : List Tm} (hlen : psL.length = np) (φ : I) :
    ∀ (us as : List Tm) (k : Nat) (fills : List Tm), fills.length = k →
    (Tm.hcompTele C argTy dataT psL φ k fills us as).map (·.subst σ τ) =
      Tm.hcompTele C argTy (dataT.subst σ τ) (psL.map (·.subst (dupS σ) (I.up τ))) (φ.subst τ) k
        (fills.map (·.subst (dupS σ) (I.up τ))) (us.map (·.subst (dupS σ) (I.up τ))) (as.map (·.subst σ τ))
  | [], _, _, _, _ => by cases ‹List Tm› <;> rfl
  | _ :: _, [], _, _, _ => rfl
  | u :: us, a :: as, k, fills, hf => by
    have hL : ((argTy k).substList (fills ++ psL.reverse)).subst (dupS σ) (I.up τ) =
        (argTy k).substList (fills.map (·.subst (dupS σ) (I.up τ)) ++
          (psL.map (·.subst (dupS σ) (I.up τ))).reverse) := by
      rw [substList_subst (by simp [hf, hlen]; rw [Nat.add_comm]; exact hA k)]
      simp [List.map_append, List.map_reverse]
    simp only [Tm.hcompTele, List.map_cons]
    split
    · simp only [List.map_cons, Tm.subst]
      congr 1
      rw [hcompTele_subst hA hlen φ us as (k + 1) _ (by simp [hf])]
      simp only [List.map_cons, hfill_subst]
    · simp only [List.map_cons, comp_subst, hL]
      congr 1
      rw [hcompTele_subst hA hlen φ us as (k + 1) _ (by simp [hf])]
      simp only [List.map_cons, fill_subst, hL]

theorem hcompCon_subst {S : Sig} (hS : SigClosed S) {d : Nat} {D : DataDecl} {c : Nat} {C : Ctor}
    (hd : S[d]? = some (.data D)) (hc : D.ctors[c]? = some C) {ps uargs args : Tm} {φ : I}
    (hps : IsList ps) (huargs : IsList uargs) (hargs : IsList args) (hlen : ps.toList.length = D.params.length) :
    (con d c ps (Tm.ofList (Tm.hcompTele C (C.argTy d D.params.length) (data d ps) ps.dshift.toList φ 0 []
      uargs.toList args.toList)) []).subst σ τ =
    con d c (ps.subst σ τ) (Tm.ofList (Tm.hcompTele C (C.argTy d D.params.length) (data d (ps.subst σ τ))
      (ps.subst σ τ).dshift.toList (φ.subst τ) 0 [] (uargs.subst (dupS σ) (I.up τ)).toList
      (args.subst σ τ).toList)) [] := by
  have e : ps.dshift.toList.map (·.subst (dupS σ) (I.up τ)) = (ps.subst σ τ).dshift.toList := by
    rw [dshift_eq ps, dshift_eq (ps.subst σ τ), toList_subst hps, toList_subst (isList_subst hps _ _),
      toList_subst hps, List.map_map, List.map_map]
    apply List.map_congr_left; intro x _
    show (x.subst Tm.var _).subst (dupS σ) (I.up τ) = ((x.subst σ τ).subst Tm.var _)
    rw [← dshift_eq, ← dshift_eq]; exact dshift_subst_dup σ τ x
  have hl' : ps.dshift.toList.length = D.params.length := by
    rw [dshift_eq ps, toList_subst hps, List.length_map, hlen]
  simp only [Tm.subst, ofList_subst]
  rw [hcompTele_subst σ τ (fun k => argTy_closed hS hd hc k) hl' φ uargs.toList args.toList 0 [] rfl,
    toList_subst huargs, toList_subst hargs, e]
  rfl

end

end KubusCore.Meta
