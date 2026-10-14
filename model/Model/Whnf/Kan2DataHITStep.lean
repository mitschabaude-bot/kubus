import Model.Whnf.Kan2DataHITHyp

/-!
# Transport at higher inductive types: reduction

Transport of a formal composition in a higher inductive type with parameters (`transpHcomp`): its
contractum `tHc` is the formal composition of the transports of the tube and of the base. `tRedF` is
the contractum of a transport whose base is in normal form (a constructor or a formal composition).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- The substitution skipping the interval variable `1`. -/
abbrev skipI : ℕ → I := fun | 0 => .var 0 | n + 1 => .var (n + 2)

/-- The contractum of `transpHcomp`. -/
def tHc (d : ℕ) (ps : Tm) (φ ψ : I) (u a : Tm) : Tm :=
  .hcomp (.data d (ps.dinst .one)) ψ (.transp ((Tm.data d ps).dsubst skipI) φ.shift u) (.transp (.data d ps) φ a)

/-- The contractum of a transport along `data d ps` of a normal form. -/
def tRedF (d : ℕ) (D : DataDecl) (ps : Tm) (φ : I) : Tm → Tm
  | .con _ c _ args rs => tConR d D c (D.ctors.getD c default) ps φ args.toList rs
  | .hcomp _ ψ u a => tHc d ps φ ψ u a
  | w => w

theorem tRedF_con (d : ℕ) (D : DataDecl) (ps : Tm) (φ : I) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C)
    (q : Tm) (X : List Tm) (rs : List I) :
    tRedF d D ps φ (.con d c q (Tm.ofList X) rs) = tConR d D c C ps φ X rs := by
  simp only [tRedF, toList_ofList]
  rw [List.getD_eq_getElem?_getD, hC]; rfl

theorem tRedF_hcomp (d : ℕ) (D : DataDecl) (ps : Tm) (φ : I) (qs : Tm) (ψ : I) (u a : Tm) :
    tRedF d D ps φ (.hcomp (.data d qs) ψ u a) = tHc d ps φ ψ u a := rfl

/-- The tube of the contractum of `transpHcomp` at a point. -/
theorem tHc_tube_pt (L : Tm) (φ : I) (u : Tm) (σ : ISub k' k) (r : I) (hr : r.Scoped k') :
    ((Tm.transp (L.dsubst skipI) φ.shift u).isub σ.up).dinst r =
      .transp (L.isub σ.up) (φ.subst σ.τ) ((u.isub σ.up).dinst r) := by
  rw [isub_up_dinst _ σ r hr, isub_up_dinst _ σ r hr]
  show Tm.transp ((L.dsubst skipI).isub (ISub.cons r hr σ).up) ((φ.shift).subst (ISub.cons r hr σ).τ)
    (u.isub (ISub.cons r hr σ)) = _
  rw [I_shift_cons]
  congr 1
  simp only [Tm.dsubst, Tm.isub, subst_subst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) L
  rcases i with _ | i
  · rfl
  · rfl

/-- The contractum of `transpHcomp`, restricted. -/
theorem tHc_isub (d : ℕ) (ps : Tm) (φ ψ : I) (u a : Tm) (κ : ISub k' k) :
    (tHc d ps φ ψ u a).isub κ = tHc d (ps.isub κ.up) (φ.subst κ.τ) (ψ.subst κ.τ) (u.isub κ.up) (a.isub κ) := by
  show Tm.hcomp (.data d ((ps.dinst .one).isub κ)) (ψ.subst κ.τ)
    (.transp (((Tm.data d ps).dsubst skipI).isub κ.up.up) ((φ.shift).subst κ.up.τ) (u.isub κ.up))
    (.transp ((Tm.data d ps).isub κ.up) (φ.subst κ.τ) (a.isub κ)) = _
  have e1 : ((Tm.data d ps).dsubst skipI).isub κ.up.up = ((Tm.data d ps).isub κ.up).dsubst skipI := by
    simp only [Tm.dsubst, Tm.isub, subst_subst]
    refine subst_congr (fun _ => rfl) (fun i => ?_) _
    rcases i with _ | i
    · rfl
    · show ((κ.τ i).shift).shift = ((κ.τ i).shift).subst skipI
      simp only [I.shift, I_ren_ren, I_ren_subst]
      rfl
  have e2 : (φ.shift).subst κ.up.τ = (φ.subst κ.τ).shift := I_shift_subst_up κ.τ φ
  rw [e1, e2, isub_dinst]
  rfl

section red
variable {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hp : D.params ≠ []) (hH : D.isHIT = true)
include hD hp hH

/-- `transpHcomp` as a step. -/
theorem step_transp_hcompH {ps qs u a : Tm} {φ ψ : I} (hn : ¬ I.Entails .one φ) (hnψ : ¬ I.Entails .one ψ) :
    step S (.transp (.data d ps) φ (.hcomp (.data d qs) ψ u a)) = some (tHc d ps φ ψ u a) := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  have hnψ' : I.entails .one ψ = false := by simpa [I.Entails] using hnψ
  simp [step, hn', hnψ', hD, hp, hH, tHc]
  rfl

end red

section eq
variable {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hp : D.params ≠ [])
  (hH : D.isHIT = true)
include hD hp hH

/-- `transpHcomp` as a judgmental equality. -/
theorem transpHcomp_eq {ps qs u a T : Tm} {φ ψ : I}
    (hb : HasTy S k .one [] (.hcomp (.data d (ps.dinst .zero)) ψ u a) (.data d (ps.dinst .zero)))
    (hty : HasTy S k .one [] (.transp (.data d ps) φ (.hcomp (.data d qs) ψ u a)) T) :
    EqTm S k .one [] (.transp (.data d ps) φ (.hcomp (.data d qs) ψ u a)) (tHc d ps φ ψ u a) T :=
  EqTm.transpHcomp hD hp hH hb hty

end eq

end

end Model.Whnf
