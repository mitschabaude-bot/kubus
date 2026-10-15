import Model.Whnf.Valid2Elim
import Model.Whnf.Kan2DataHITCon

/-!
# The eliminator of higher inductive types: reduction and the constructor contracta

Eliminations of higher inductive types reduce, at a constructor normal form (where no boundary holds),
to the branch applied to the arguments, the eliminations of the recursive arguments and the interval
arguments (`step_elimConH`), and at a formal composition (whose face does not hold) to a composition in
the motive along the filler (`step_elimHcompH`). Related branches at related arguments give related
contracta (`elimCon_relH`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

section red
variable {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hD

/-- An elimination of a constructor where no boundary holds steps to the branch. -/
theorem step_elimConH {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {ps M bs qs b : Tm} {X : List Tm}
    {rs : List I} (hb : bs.toList[c]? = some b) (hn : firstBnd C.bnd rs = none) :
    step S (.elim d ps M bs (.con d c qs (Tm.ofList X) rs)) =
      some (Tm.papps (Tm.apps b (X ++ ihsOf d C ps M bs X)) rs) := by
  have h0 := step_con_none (S := S) hD hC qs (Tm.ofList X) hn
  simp only [step] at h0 ⊢
  rw [h0]
  simp [hD, hb, hC, toList_ofList, ihsOf]

/-- An elimination of a formal composition steps to the composition in the motive along the filler. -/
theorem step_elimHcompH (hH : D.isHIT = true) {ps M bs qs u a : Tm} {φ : I} (hn : ¬ I.Entails .one φ) :
    step S (.elim d ps M bs (.hcomp (.data d qs) φ u a)) =
      some (Tm.comp (M.subst (fun | 0 => Tm.hfill (.data d ps) φ u a | j + 1 => .var j) (fun i => .var (i + 1))) φ
        (.elim d ps.dshift M.dshift bs.dshift u) (.elim d ps M bs a)) := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  have h0 : step S (.hcomp (.data d qs) φ u a) = none := by
    simp [step, hn', hD, hH]
  simp only [step] at h0 ⊢
  rw [h0]
  simp only [hD, hH, and_self, if_true]
  congr 3

end red

variable (hW : WfSig S)
include hW

/-- Interval application through iterated `(i : I) → _`. -/
theorem RE2_papps : ∀ (rs rs' : List I) {f f' B : Tm} {σ : ℕ → Tm} {τ : ℕ → I}, IEqL rs rs' →
    (∀ r ∈ rs, r.Scoped k) → (∀ r ∈ rs', r.Scoped k) →
    RE2 S k ((ipis rs.length B).subst σ τ) f f' →
    RE2 S k (B.subst σ (consIs rs τ)) (Tm.papps f rs) (Tm.papps f' rs')
  | [], [], _, _, _, _, _, _, _, _, h => h
  | r :: rs, r' :: rs', f, f', B, σ, τ, he, hs, hs', h => by
    cases he with
    | cons e he =>
    rw [List.length_cons, ipis_succ] at h
    have h1 := RE2_ipi_elim hW (show RE2 S k (.ipi ((ipis rs.length B).subst (dupS σ) (I.up τ))) f f' from h)
      r r' (hs r (List.mem_cons_self ..)) (hs' r' (List.mem_cons_self ..)) e
    rw [dup_dinst] at h1
    exact RE2_papps rs rs' he (fun x hx => hs x (List.mem_cons_of_mem _ hx))
      (fun x hx => hs' x (List.mem_cons_of_mem _ hx)) h1
  | [], _ :: _, _, _, _, _, _, he, _, _, _ => by cases he
  | _ :: _, [], _, _, _, _, _, he, _, _, _ => by cases he

/-- The branches of related eliminations, applied to related arguments, the related eliminations of the
recursive arguments and `I.Eq`-equal interval arguments, are related. -/
theorem elimCon_relH {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) {ps M bs ps' M' bs' b b' : Tm} (hpl : ps.toList.length = D.params.length)
    (hbr : RE2 S k (D.branchTy d c C ps M) b b') {X X' : List Tm} (hXl : X.length = C.args.length)
    (hX'l : X'.length = C.args.length)
    (hargs : ∀ i (hi : i < X.length) (hi' : i < X'.length), RE2 S k ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ ps.toList.reverse)) X[i] X'[i])
    (hih : ∀ j, j ∈ C.recPos → RE2 S k (M.inst (X.getD j .abort))
      (.elim d ps M bs (X.getD j .abort)) (.elim d ps' M' bs' (X'.getD j .abort)))
    {rs rs' : List I} (hrl : rs.length = C.dims) (hrr : IEqL rs rs') (hrs : ∀ r ∈ rs, r.Scoped k)
    (hrs' : ∀ r ∈ rs', r.Scoped k) :
    RE2 S k (M.inst (.con d c ps (Tm.ofList X) rs))
      (Tm.papps (Tm.apps b (X ++ ihsOf d C ps M bs X)) rs) (Tm.papps (Tm.apps b' (X' ++ ihsOf d C ps' M' bs' X')) rs') := by
  have hS := sigClosed_of_wfSig hW
  rw [Meta.branchTy_eq] at hbr
  have hbr0 : RE2 S k ((((List.range C.args.length).map (DataDecl.branchArgTy d D.params.length C ps)).foldr Tm.pi
      (((List.range C.recPos.length).map (DataDecl.branchIhTy C M)).foldr Tm.pi
        (ipis C.dims (DataDecl.branchBody d c C ps M)))).substList []) b b' := by rw [substList_nil]; exact hbr
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
      simp only [hgd]
      exact hih _ (List.getElem_mem hsΔ))
  rw [substList_eq] at h2
  have h3 := RE2_papps hW rs rs' hrr hrs hrs' (by rw [hrl]; exact h2)
  have hb := branchBody_inst (d := d) (c := c) (ps := ps) (P := M) (ihs := ihsOf d C ps M bs X) (args := X) (rs := rs)
    (by simp) hXl hrl
  rw [hb, apps_append, apps_append] at h3
  exact h3

end

end Model.Whnf
