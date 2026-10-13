import KubusCore.Meta.Closed

/-!
# Metatheory: substitution commutes with the derived operations

The contracta of the computation rules (`transpPi`, …, `hcompU`, `transpGlueWith`), the
defined types (`equiv`), and the instantiations used by the rules for inductive types commute
with substitution. The Kan contracta are handled by the tactic `scalc`, which normalizes both
sides to substitutions of the atomic parts and compares the substitutions pointwise.
-/

namespace KubusCore.Meta

open Tm

/-- Lift a term substitution under an interval binder. -/
abbrev dupS (σ : Nat → Tm) : Nat → Tm := fun n => (σ n).dshift

/-- Normalize both sides to substitutions of atomic subterms and compare pointwise. -/
macro "scalc" : tactic => `(tactic| (
  simp only [Tm.subst, I.subst, shift_eq, dshift_eq, I.shift, I_ren_eq, Tm.inst, Tm.dinst, Tm.dsubst,
    subst_subst, I_subst_subst, Tm.up, I.up, I.inst0, Tm.bind2, subst_var, I_subst_var, dupS];
  repeat' (first
    | rfl
    | (funext n; rcases n with _ | _ | _ | n <;>
        simp only [Tm.subst, I.subst, shift_eq, dshift_eq, I.shift, I_ren_eq, Tm.inst, Tm.dinst,
          Tm.dsubst, subst_subst, I_subst_subst, Tm.up, I.up, I.inst0, Tm.bind2, subst_var,
          I_subst_var, dupS])
    | congr 1)))

section
variable (σ : Nat → Tm) (τ : Nat → I)

theorem transpPi_subst (A B : Tm) (φ : I) (u0 : Tm) :
    (transpPi A B φ u0).subst σ τ =
      transpPi (A.subst (dupS σ) (I.up τ)) (B.subst (up (dupS σ)) (I.up τ)) (φ.subst τ) (u0.subst σ τ) := by
  simp only [transpPi]; scalc

theorem transpSigma_subst (A B : Tm) (φ : I) (u0 : Tm) :
    (transpSigma A B φ u0).subst σ τ =
      transpSigma (A.subst (dupS σ) (I.up τ)) (B.subst (up (dupS σ)) (I.up τ)) (φ.subst τ) (u0.subst σ τ) := by
  simp only [transpSigma, transpFill]; scalc

theorem transpPath_subst (A a b : Tm) (φ : I) (p0 : Tm) :
    (transpPath A a b φ p0).subst σ τ =
      transpPath (A.subst (dupS (dupS σ)) (I.up (I.up τ))) (a.subst (dupS σ) (I.up τ))
        (b.subst (dupS σ) (I.up τ)) (φ.subst τ) (p0.subst σ τ) := by
  simp only [transpPath, comp]; scalc

theorem transpIPi_subst (A : Tm) (φ : I) (u0 : Tm) :
    (transpIPi A φ u0).subst σ τ =
      transpIPi (A.subst (dupS (dupS σ)) (I.up (I.up τ))) (φ.subst τ) (u0.subst σ τ) := by
  simp only [transpIPi]; scalc

theorem hcompIPi_subst (A : Tm) (φ : I) (u u0 : Tm) :
    (hcompIPi A φ u u0).subst σ τ =
      hcompIPi (A.subst (dupS σ) (I.up τ)) (φ.subst τ) (u.subst (dupS σ) (I.up τ)) (u0.subst σ τ) := by
  simp only [hcompIPi]; scalc

theorem hcompPi_subst (A B : Tm) (φ : I) (u u0 : Tm) :
    (hcompPi A B φ u u0).subst σ τ =
      hcompPi (A.subst σ τ) (B.subst (up σ) τ) (φ.subst τ) (u.subst (dupS σ) (I.up τ)) (u0.subst σ τ) := by
  simp only [hcompPi]; scalc

theorem hcompSigma_subst (A B : Tm) (φ : I) (u u0 : Tm) :
    (hcompSigma A B φ u u0).subst σ τ =
      hcompSigma (A.subst σ τ) (B.subst (up σ) τ) (φ.subst τ) (u.subst (dupS σ) (I.up τ)) (u0.subst σ τ) := by
  simp only [hcompSigma, hfill, comp]; scalc

theorem hcompPath_subst (A a b : Tm) (φ : I) (u p0 : Tm) :
    (hcompPath A a b φ u p0).subst σ τ =
      hcompPath (A.subst (dupS σ) (I.up τ)) (a.subst σ τ) (b.subst σ τ) (φ.subst τ)
        (u.subst (dupS σ) (I.up τ)) (p0.subst σ τ) := by
  simp only [hcompPath]; scalc

theorem hcompGlue_subst (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u u0 : Tm) :
    (hcompGlue A φ T e ψ u u0).subst σ τ =
      hcompGlue (A.subst σ τ) (φ.subst τ) (T.subst σ τ) (e.subst σ τ) (ψ.subst τ)
        (u.subst (dupS σ) (I.up τ)) (u0.subst σ τ) := by
  simp only [hcompGlue, hfill]; scalc

theorem transpGlueWith_subst (δ : I) (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) :
    (transpGlueWith δ A φ T e ψ u0).subst σ τ =
      transpGlueWith (δ.subst τ) (A.subst (dupS σ) (I.up τ)) (φ.subst (I.up τ)) (T.subst (dupS σ) (I.up τ))
        (e.subst (dupS σ) (I.up τ)) (ψ.subst τ) (u0.subst σ τ) := by
  simp only [transpGlueWith, comp, fill, transpFill, fiber, pathC]; scalc

theorem hcompU_subst (φ : I) (u u0 : Tm) :
    (hcompU φ u u0).subst σ τ = hcompU (φ.subst τ) (u.subst (dupS σ) (I.up τ)) (u0.subst σ τ) := by
  simp only [hcompU, lineEquiv, lineFun, idIsEquiv, isEquiv, isContr, fiber, pathC]; scalc

theorem equiv_subst (T A : Tm) : (equiv T A).subst σ τ = equiv (T.subst σ τ) (A.subst σ τ) := by
  simp only [equiv, isEquiv, isContr, fiber, pathC, arrow]; scalc

theorem etaPi_subst (A f : Tm) :
    (lam A (app f.shift (var 0))).subst σ τ = lam (A.subst σ τ) (app (f.subst σ τ).shift (var 0)) := by
  scalc

theorem etaPath_subst (p : Tm) :
    (plam (papp p.dshift (.var 0))).subst σ τ = plam (papp (p.subst σ τ).dshift (.var 0)) := by
  scalc

theorem elimHcomp_subst (d : Nat) (ps P bs : Tm) (φ : I) (u a : Tm) :
    (comp (P.subst (fun | 0 => hfill (data d ps) φ u a | j + 1 => var j) (fun i => .var (i + 1))) φ
      (elim d ps.dshift P.dshift bs.dshift u) (elim d ps P bs a)).subst σ τ =
    comp ((P.subst (up σ) τ).subst
        (fun | 0 => hfill (data d (ps.subst σ τ)) (φ.subst τ) (u.subst (dupS σ) (I.up τ)) (a.subst σ τ)
             | j + 1 => var j) (fun i => .var (i + 1))) (φ.subst τ)
      (elim d (ps.subst σ τ).dshift (P.subst (up σ) τ).dshift (bs.subst σ τ).dshift (u.subst (dupS σ) (I.up τ)))
      (elim d (ps.subst σ τ) (P.subst (up σ) τ) (bs.subst σ τ) (a.subst σ τ)) := by
  simp only [comp, hfill]; scalc

theorem transpHcomp_subst (d : Nat) (ps : Tm) (φ ψ : I) (u a : Tm) :
    (hcomp (data d (ps.dinst .one)) ψ
      (transp ((data d ps).dsubst fun | 0 => .var 0 | n + 1 => .var (n + 2)) φ.shift u)
      (transp (data d ps) φ a)).subst σ τ =
    hcomp (data d ((ps.subst (dupS σ) (I.up τ)).dinst .one)) (ψ.subst τ)
      (transp ((data d (ps.subst (dupS σ) (I.up τ))).dsubst fun | 0 => .var 0 | n + 1 => .var (n + 2))
        (φ.subst τ).shift (u.subst (dupS σ) (I.up τ)))
      (transp (data d (ps.subst (dupS σ) (I.up τ))) (φ.subst τ) (a.subst σ τ)) := by
  scalc

theorem face_dset_subst (t : Tm) (i : Nat) (d : Bool) :
    (t.dset i (I.ofDir d)).subst σ τ =
      t.subst σ (fun j => if j = i then I.ofDir d else τ j) := by
  simp only [Tm.dset, Tm.dsubst, subst_subst]
  apply subst_congr
  · intro n; simp [Tm.subst]
  · intro j; by_cases h : j = i <;> simp [h, I.subst]; cases d <;> rfl

end

end KubusCore.Meta
