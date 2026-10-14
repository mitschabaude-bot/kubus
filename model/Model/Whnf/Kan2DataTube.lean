import Model.Whnf.Kan2DataFill

/-!
# Tubes in inductive types without path constructors

Related tubes in an inductive type without path constructors are constructors on their faces
(`tubeCanon_of`), so the `hcompCon` step is sound for them (`hcompCon_sound`). Projections out of a
constructor reduce to its arguments (`red_proj`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

/-! ### Reduction of projections -/

theorem red_elim {d : ℕ} {ps P bs t t' : Tm} (h : Red S t t') : Red S (.elim d ps P bs t) (.elim d ps P bs t') := by
  induction h with
  | refl => exact .refl _
  | @step t0 t1 t2 hs _ ih => exact .step (by simp [step, hs]) ih

theorem red_apps {f f' : Tm} (h : Red S f f') : ∀ (vals : List Tm), Red S (Tm.apps f vals) (Tm.apps f' vals) := by
  intro vals
  induction vals generalizing f f' with
  | nil => exact h
  | cons v vals ih => exact ih (red_app v h)

/-- Iterated β-reduction of an abstraction. -/
theorem red_apps_lams {Ts vals : List Tm} (hl : vals.length = Ts.length) (b : Tm) :
    Red S (Tm.apps (lams Ts b) vals) (b.substList vals.reverse) := by
  have claim : ∀ k, k ≤ Ts.length → Red S (Tm.apps (lams Ts b) (vals.take k))
      ((lams (Ts.drop k) b).subst (slS ((vals.take k).reverse)) I.var) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [List.take_zero, List.reverse_nil, List.drop_zero, subst_slS_nil]
      exact .refl _
    | succ k ih =>
      intro hk
      have ih := ih (by omega)
      have hv : vals[k]? = some vals[k] := List.getElem?_eq_getElem (by omega)
      have hd : Ts.drop k = Ts[k] :: Ts.drop (k + 1) := List.drop_eq_getElem_cons (by omega)
      rw [hd] at ih
      change Red S _ (Tm.lam (Ts[k].subst _ I.var) ((lams (Ts.drop (k + 1)) b).subst (Tm.up _) I.var)) at ih
      have e1 := red_app vals[k] ih
      have et : (vals.take (k + 1)).reverse = vals[k] :: (vals.take k).reverse := by
        rw [List.take_add_one, hv]; simp
      have ea : Tm.apps (lams Ts b) (vals.take (k + 1)) = .app (Tm.apps (lams Ts b) (vals.take k)) vals[k] := by
        rw [List.take_add_one, hv]; simp only [Option.toList_some]; unfold Tm.apps; rw [List.foldl_append]; rfl
      rw [ea, et]
      refine e1.trans (.step (by simp [step]; rfl) ?_)
      rw [subst_up_inst, ← slS_cons]
      exact .refl _
  have := claim Ts.length (Nat.le_refl _)
  rw [List.drop_length, List.take_of_length_le (by omega)] at this
  simpa [lams, substList_eq] using this

section proj
variable {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
include hD hH

/-- The projections of an element which reduces to a constructor reduce to its arguments. -/
theorem red_proj {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {ps t qs : Tm} {Z : List Tm}
    (hZ : Z.length = C.args.length) (hr : Red S t (.con d c qs (Tm.ofList Z) [])) {j : ℕ} (hj : j < C.args.length) :
    Red S (proj d D ps c C j t) (Z[j]'(by omega)) := by
  unfold proj
  refine (red_elim hr).trans (Red.step (t' := Tm.apps (lams ((List.range C.args.length).map
      (DataDecl.branchArgTy d D.params.length C ps) ++
      (List.range C.recPos.length).map (DataDecl.branchIhTy C (projQ d D ps c C j))) (projBody d C ps c j c C))
      (Z ++ C.recPos.map fun k => Tm.elim d ps (projQ d D ps c C j)
        (branchesOf D d ps (projQ d D ps c C j) (projBody d C ps c j)) (Z.getD k .abort))) ?_ ?_)
  · have hb := branchesOf_get (body := projBody d C ps c j) (ps := ps) (P := projQ d D ps c C j) (d := d) hC
    simp [step, hD, hb, hC, toList_ofList, Tm.papps, (nonHIT_ctor hH hC).2, firstBnd]
  · refine (red_apps_lams (by simp [hZ]) _).trans ?_
    have hbody : projBody d C ps c j c C = .var (C.recPos.length + (C.args.length - 1 - j)) := by
      simp [projBody]
    rw [hbody, substList_eq]
    show Red S (slS _ _) _
    simp only [slS, List.reverse_append, List.length_map]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.length_reverse, List.length_map,
      show C.recPos.length + (C.args.length - 1 - j) - C.recPos.length = Z.length - 1 - j by omega,
      List.getElem?_reverse (by omega), show Z.length - 1 - (Z.length - 1 - j) = j by omega,
      List.getElem?_eq_getElem (by omega)]
    exact .refl _

end proj

/-! ### Constructors at given parameters -/

section con
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
include hW hD hH

/-- A term equal to a constructor of an inductive type without path constructors is that constructor
at the parameters of its type. -/
theorem con_retype {t A qs p : Tm} {c : ℕ} {C : Ctor} {Z : List Tm} {rs : List I} (hC : D.ctors[c]? = some C)
    (he : EqTm S k .one [] t (.con d c qs (Tm.ofList Z) rs) A) (hA : TyEq S k A (.data d p))
    (hpT : HasTy S k .one [] (.data d p) (.univ D.level)) :
    HasTele0 S k .one [] (Tm.ofList Z) (C.argTys d D.params.length) p.toList.reverse ∧
    EqTm S k .one [] t (.con d c p (Tm.ofList Z) []) (.data d p) ∧ rs = [] ∧ Z.length = C.args.length := by
  have hS := sigClosed_of_wfSig hW
  have hcon := spec_to_minimal hW ((HasTy.eqR he).tyConv hA)
  obtain ⟨D', C', hD', hC', hpL, -, htele, hrs, m, eq0⟩ := con_args hW hcon (spec_to_minimal hW hpT)
  rw [hD] at hD'; cases hD'; rw [hC] at hC'; cases hC'
  have hrs0 : rs = [] := List.eq_nil_of_length_eq_zero (by rw [hrs, (nonHIT_ctor hH hC).1])
  subst hrs0
  have hZl : Z.length = C.args.length := by
    have := tele_length htele; rwa [toList_ofList, argTys_length] at this
  obtain ⟨hT, hCt⟩ := wf_typed _ S rfl hW
  obtain ⟨hq, -, -⟩ := pre_eq hS hT hCt eq0
  obtain ⟨D1, hD1, hqt⟩ := gen_data_tele hq rfl
  rw [hD] at hD1; cases hD1
  obtain ⟨D2, hD2, hpt⟩ := gen_data_tele (spec_to_minimal hW hpT) rfl
  rw [hD] at hD2; cases hD2
  have eps : EqTele0 S k .one [] p qs D.params [] := EqTele0.dataInj hD hpt hqt (EqTm0.symm eq0)
  have hc0 : HasTy0 S k .one [] (.con d c p (Tm.ofList Z) []) (.data d p) :=
    HasTy0.con hD hC (tele_isList hpt) (spec_to_minimal hW hpT) hpt htele
      (by simp [(nonHIT_ctor hH hC).1]) (by simp)
  have ec := EqTm0.con hD hC hc0 hcon eps (EqTele0.refl htele) rfl
    (fun _ _ _ h => by simp at h)
  exact ⟨htele, ((he.tyConv hA).trans (minimal_to_spec_eq (EqTm0.symm ec))), rfl, hZl⟩

/-- A composition's tube which is related to itself in a restriction of a literal inductive type
without path constructors is a constructor on the composition's face. -/
theorem tubeCanon_of {K : ℕ} {P : Tm} {l : ℕ} (hP : HasTy S K .one [] (.data d P) (.univ l)) {k1 : ℕ}
    (ρ : ISub k1 K) {p u : Tm} {φ : I} (hTy : TyEq S k1 (.data d (P.isub ρ)) (.data d p))
    (hpT : HasTy S k1 .one [] (.data d p) (.univ D.level)) (htube : Tube2 S k1 (.data d (P.isub ρ)) φ u u) :
    TubeCanon S k1 d D p φ u := by
  have hdD := dataD_eq hW hD
  intro k' σ r hr hh
  have h1 := htube k' σ r r hr hr (I_eq_refl _) hh
  rw [show (Tm.data d (P.isub ρ)).isub σ = .data d (P.isub (ρ.comp σ)) by
    show Tm.data d ((P.isub ρ).isub σ) = _; rw [Tm.isub_isub]] at h1
  obtain ⟨-, hdr⟩ := (RE2_dataLit_iff hW hD hP (ρ.comp σ)).1 h1
  have hat := DR2.at_id hW (Θ := ΘK S D d K P) hdr
  have hTyσ : TyEq S k' (.data d (P.isub (ρ.comp σ))) (.data d (p.isub σ)) := by
    have := hTy.isub hW σ
    rwa [show (Tm.data d (P.isub ρ)).isub σ = .data d (P.isub (ρ.comp σ)) by
      show Tm.data d ((P.isub ρ).isub σ) = _; rw [Tm.isub_isub]] at this
  cases hat with
  | con hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt =>
    have hC' := hdD ▸ hC
    obtain ⟨hX, he, -, -⟩ := con_retype hW hD hH hC' ht.2 hTyσ (HasTy.isubS hW hpT σ)
    exact ⟨_, _, _, hC', hX, he⟩
  | hcomp _ _ _ hH' =>
    have : D.isHIT = true := by rw [← hdD]; exact hH'
    rw [hH] at this; cases this

/-- The `hcompCon` step is sound for a composition whose tube is a constructor on its face. -/
theorem hcompCon_sound {q u qs T : Tm} {φ : I} {c : ℕ} {C : Ctor} {X : List Tm} (hC : D.ctors[c]? = some C)
    (hty : HasTy S k .one [] (.hcomp (.data d q) φ u (.con d c qs (Tm.ofList X) [])) T)
    (hcan : TubeCanon S k d D q φ u) :
    EqTm S k .one [] (.hcomp (.data d q) φ u (.con d c qs (Tm.ofList X) []))
      (.con d c q (Tm.ofList (Tm.hcompTele C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ 0 []
        ((List.range C.args.length).map fun j => proj d D q.dshift c C j u) X)) []) T := by
  obtain ⟨l0, ⟨hdT, hφs, hut, hb, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  obtain ⟨D', hD', hPt⟩ := gen_data_tele hdT rfl
  rw [hD] at hD'; cases hD'
  have hpT : HasTy S k .one [] (.data d q) (.univ D.level) := minimal_to_spec (HasTy0.data hD (hW.2 d D hD).1 hPt)
  obtain ⟨hX, ebase, -, -⟩ := con_retype hW hD hH hC (EqTm.refl (minimal_to_spec hb)) (TyEq.refl _) hpT
  have hside' : EqTm S k (cof .one φ) [] (u.dinst .zero) (.con d c q (Tm.ofList X) []) (.data d q) :=
    (minimal_to_spec_eq hside).trans (EqTm.restrict (show (cof .one φ).Scoped k from ⟨trivial, hφs⟩)
      (ent_and_left _ _) ebase)
  obtain ⟨G1, G2, G3, -⟩ := hcompCon_premises hW hD hH hC hpT hφs hut hside' hX hcan
  have e := EqTm0.hcompCon (qs := qs) hD hH hC (tele_isList hPt) (args := Tm.ofList X) (by rw [toList_ofList])
    (uargs := Tm.ofList ((List.range C.args.length).map fun j => proj d D q.dshift c C j u))
    (by rw [toList_ofList]) hX G1 G2 G3 (spec_to_minimal hW hty)
  simp only [toList_ofList] at e
  exact minimal_to_spec_eq e

end con

end

end Model.Whnf
