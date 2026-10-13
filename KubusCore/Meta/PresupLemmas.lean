import KubusCore.Meta.GenRedex

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem upDShift_dinst0 (A : Tm) : (A.ren id (upRen Nat.succ)).dinst (.var 0) = A := by
  simp only [Tm.dinst, Tm.dsubst, ren_eq_subst, subst_subst]
  exact subst_id_of (fun n => rfl) (fun i => by cases i <;> rfl) A

/-- Context conversion of the last variable. -/
theorem HasTy0.ctxConv (hS : SigClosed S) {Ψ Φ Γ A A' t T l} (h : HasTy0 S Ψ Φ (A :: Γ) t T)
    (hA' : HasTy0 S Ψ Φ Γ A' (Tm.univ l)) (he : EqTm0 S Ψ Φ Γ A' A (Tm.univ l)) :
    HasTy0 S Ψ Φ (A' :: Γ) t T := by
  have hσ := (tySub_id (wf_of_ty hA')).up hS (A := A) hA' (by rw [subst_var]; exact he)
  have := (sub_ty hS h).2.1 hσ
  rwa [up_var, subst_var, subst_var] at this

/-- Interval functionality of a line. -/
theorem HasTy0.dinst_congr (hS : SigClosed S) {Ψ Φ Γ A T r r'}
    (h : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A T) (hr : r.Scoped Ψ) (hr' : r'.Scoped Ψ) (he : I.Eq r r') :
    EqTm0 S Ψ Φ Γ (A.dinst r) (A.dinst r') (T.dinst r) := by
  have hw := wf_unshift hS (wf_of_ty h)
  have hE : EqSub S (Ψ + 1) Γ.dshift Ψ Φ Γ Tm.var (I.inst0 r) Tm.var (I.inst0 r') :=
    ⟨fun x B hx => by
      rw [lookup_dshift, Option.map_eq_some_iff] at hx
      obtain ⟨B0, hB0, rfl⟩ := hx
      have : B0.dshift.subst Tm.var (I.inst0 r) = B0 := dshift_dinst B0 r
      rw [this]; exact EqTm0.refl (HasTy0.var hw hB0),
     fun i _ => by
      cases i
      · exact he
      · exact I_eq_refl _⟩
  exact (sub_ty hS h).2.2 (tySub_inst0 hw hr) (tySub_inst0 hw hr') hE

theorem dset_eq_dsetI (t : Tm) (i : Nat) (d : Bool) : t.dset i (I.ofDir d) = t.subst Tm.var (dsetI i d) := rfl

/-- The right-hand side of the face rule is typed. -/
theorem HasTy0.face_typed (hS : SigClosed S) {Ψ Φ Γ t A i d} (hi : i < Ψ) (he : I.Entails Φ (I.lit i d))
    (hA : IsTyp S Ψ Φ Γ A) (h : HasTy0 S Ψ Φ Γ t A) : HasTy0 S Ψ Φ Γ (t.dset i (I.ofDir d)) A := by
  have hw := wf_of_ty h
  have hΦ := scoped_of_wf hw
  have he' : I.Entails Φ ((I.lit i d).subst I.var) := by rw [I_subst_var]; exact he
  have hf : FaceEq Ψ Φ I.var (fun j => if j = i then I.ofDir d else I.var j) := faceEq_lit he'
  have hσ : TySub S Ψ Φ Γ Ψ Φ Γ Tm.var (dsetI i d) :=
    { bound := fun j hj => by
        simp only [dsetI]; split
        · cases d <;> trivial
        · exact hj
      hscoped := hΦ
      ent := faceEq_ent hf hΦ (by rw [I_subst_var]; exact ent_refl _)
      wf := hw
      look := fun x B hx => by
        obtain ⟨l, hB⟩ := lookup_typed hS hw hx
        exact HasTy0.conv (HasTy0.var hw hx) (EqTm0.faceU hi he hB) }
  have := (sub_ty hS h).2.1 hσ
  rw [← dset_eq_dsetI, ← dset_eq_dsetI] at this
  rcases hA with ⟨l, hA⟩ | ⟨l, rfl⟩
  · exact HasTy0.conv this (EqTm0.symm (EqTm0.faceU hi he hA))
  · exact this

end KubusCore.Meta
