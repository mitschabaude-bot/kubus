import Model.Whnf.Valid2Data

/-!
# The eliminator of inductive types without path constructors

The binary counterpart of `Model/Canon/Elim.lean` (`RE_elim_DR`): eliminations of related elements
are related, by induction on the relation of the eliminated elements (`DR2`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

variable (hW : WfSig S)
include hW

/-- Application through a Π-telescope. -/
theorem RE2_apps : ∀ (as as' : List Tm) {Δ prev : List Tm} {f f' base : Tm}, as.length = Δ.length →
    as'.length = as.length → RE2 S k ((Δ.foldr Tm.pi base).substList prev) f f' →
    (∀ j (hj : j < as.length) (hj' : j < as'.length) (hjΔ : j < Δ.length),
      RE2 S k (Δ[j].substList ((as.take j).reverse ++ prev)) as[j] as'[j]) →
    RE2 S k (base.substList (as.reverse ++ prev)) (Tm.apps f as) (Tm.apps f' as')
  | [], [], [], prev, f, f', base, _, _, hf, _ => by simpa [Tm.apps] using hf
  | a :: as, a' :: as', A :: Δ, prev, f, f', base, hl, hl', hf, ha => by
    rw [List.foldr_cons, pi_substList] at hf
    have h1 := RE2_pi_elim hW hf (by simpa using ha 0 (by simp) (by simp) (by simp))
    rw [up_slS_inst] at h1
    have := RE2_apps as as' (by simpa using hl) (by simpa using hl') h1 (fun j hj hj' hjΔ => by
      have := ha (j + 1) (by simp; omega) (by simp; omega) (by simp; omega)
      simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using this)
    simpa [Tm.apps, List.foldl, List.reverse_cons, List.append_assoc] using this
  | [], _ :: _, _, _, _, _, _, _, hl', _, _ => by simp at hl'
  | _ :: _, [], _, _, _, _, _, _, hl', _, _ => by simp at hl'
  | [], [], _ :: _, _, _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, _, _, hl, _, _, _ => by simp at hl

/-- The induction hypotheses of a branch at a constructor's arguments. -/
abbrev ihsOf (d : ℕ) (C : Ctor) (ps P bs : Tm) (X : List Tm) : List Tm :=
  C.recPos.map fun j => Tm.elim d ps P bs (X.getD j .abort)

omit hW in
theorem apps_append (f : Tm) (X Y : List Tm) : Tm.apps (Tm.apps f X) Y = Tm.apps f (X ++ Y) := by
  simp only [Tm.apps, List.foldl_append]

/-- The branches of related eliminations, applied to related arguments and the related eliminations of
the recursive arguments, are related. -/
theorem elimCon_rel {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) {ps M bs ps' M' bs' b b' : Tm} (hpl : ps.toList.length = D.params.length)
    (hbr : RE2 S k (D.branchTy d c C ps M) b b') {X X' : List Tm} (hXl : X.length = C.args.length)
    (hX'l : X'.length = C.args.length)
    (hargs : ∀ i (hi : i < X.length) (hi' : i < X'.length), RE2 S k ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ ps.toList.reverse)) X[i] X'[i])
    (hih : ∀ j (hj : j ∈ C.recPos), RE2 S k (M.inst (X.getD j .abort))
      (.elim d ps M bs (X.getD j .abort)) (.elim d ps' M' bs' (X'.getD j .abort))) :
    RE2 S k (M.inst (.con d c ps (Tm.ofList X) []))
      (Tm.apps b (X ++ ihsOf d C ps M bs X)) (Tm.apps b' (X' ++ ihsOf d C ps' M' bs' X')) := by
  have hS := sigClosed_of_wfSig hW
  have hdims := (nonHIT_ctor hH hC).1
  rw [Meta.branchTy_eq, hdims] at hbr
  have hbr0 : RE2 S k ((((List.range C.args.length).map (DataDecl.branchArgTy d D.params.length C ps)).foldr Tm.pi
      (((List.range C.recPos.length).map (DataDecl.branchIhTy C M)).foldr Tm.pi
        (ipis 0 (DataDecl.branchBody d c C ps M)))).substList []) b b' := by rw [substList_nil]; exact hbr
  have h1 := RE2_apps hW X X' (by simp [hXl]) (by rw [hX'l, hXl]) hbr0 (fun j hj hj' hjΔ => by
    simp only [List.getElem_map, List.getElem_range, List.append_nil]
    rw [branchArgTy_substList hS hD hC hpl (by simp; omega)]
    exact hargs j hj hj')
  rw [List.append_nil] at h1
  have h2 := RE2_apps hW (ihsOf d C ps M bs X) (ihsOf d C ps' M' bs' X')
    (Δ := (List.range C.recPos.length).map (DataDecl.branchIhTy C M)) (by simp) (by simp) h1
    (fun s hs hs' hsΔ => by
      simp only [List.length_map, List.length_range] at hsΔ
      simp only [List.getElem_map, List.getElem_range]
      rw [branchIhTy_substList M hsΔ (by simp; omega) hXl]
      obtain ⟨hjn, hjr⟩ := mem_recPos (List.getElem_mem (l := C.recPos) hsΔ)
      have hgd : C.recPos.getD s 0 = C.recPos[s] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsΔ]; rfl
      simp only [ihsOf, List.getElem_map, hgd]
      exact hih _ (List.getElem_mem hsΔ))
  rw [substList_eq] at h2
  have hb := branchBody_inst (d := d) (c := c) (ps := ps) (P := M) (ihs := ihsOf d C ps M bs X) (args := X) (rs := [])
    (by simp) hXl (by simp [hdims])
  simp only [ipis, List.range_zero, List.foldl_nil] at h2
  rw [show (consIs [] I.var) = I.var from rfl] at hb
  rw [hb, apps_append, apps_append] at h2
  exact h2

end

end Model.Whnf
