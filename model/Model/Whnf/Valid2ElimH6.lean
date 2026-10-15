import Model.Whnf.Valid2ElimH5

/-!
# Instantiation of higher inductive eliminator boundary equations

The branch boundary premise is closed with related constructor arguments, related induction
hypotheses, and equal interval arguments at a face where the boundary holds.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-- The term telescope of an eliminator branch, in application order. -/
def branchTele2 (d : ℕ) (D : DataDecl) (C : Ctor) (ps M : Tm) : List Tm :=
  (List.range C.args.length).map (DataDecl.branchArgTy d D.params.length C ps) ++
    (List.range C.recPos.length).map (DataDecl.branchIhTy C M)

theorem branchTele2_length (d : ℕ) (D : DataDecl) (C : Ctor) (ps M : Tm) :
    (branchTele2 d D C ps M).length = C.args.length + C.recPos.length := by
  simp [branchTele2]

theorem branchTy_tele2 (d c : ℕ) (D : DataDecl) (C : Ctor) (ps M : Tm) :
    D.branchTy d c C ps M = (branchTele2 d D C ps M).foldr Tm.pi
      (ipis C.dims (DataDecl.branchBody d c C ps M)) := by
  rw [Meta.branchTy_eq]
  exact (List.foldr_append ..).symm

theorem branchCtx_tele2 (d : ℕ) (D : DataDecl) (C : Ctor) (ps M : Tm) (Γ : Ctx) :
    D.branchCtx d C ps M Γ = ctxWkI C.dims ((branchTele2 d D C ps M).reverse ++ Γ) := by
  unfold DataDecl.branchCtx branchTele2
  rw [Ctx_ren_add_eq]
  simp only [List.reverse_append, List.map_reverse, List.append_assoc]

/-- A scoped constructor face ignores the outer interval substitution. -/
theorem cofAt_consIs2 {ψ : I} {rs : List I} (hψ : ψ.Scoped rs.length) (τ : ℕ → I) :
    ψ.subst (consIs rs τ) = Ctor.cofAt ψ rs := by
  apply subst_scoped_eq hψ
  intro i hi
  rw [consIs_eq]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simpa using hi)]
  rfl

variable (hW : WfSig S)
include hW

/-- The argument type in the branch telescope at its actual related argument prefix. -/
theorem branchArgTy_teleSub2 {d c : ℕ} {D : DataDecl} {C : Ctor}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C)
    {ps : Tm} (hps : IsList ps) (hlen : ps.toList.length = D.params.length)
    (X : List Tm) (γ : ℕ → Tm) (τ : ℕ → I) :
    (DataDecl.branchArgTy d D.params.length C ps X.length).subst (teleSub X γ) τ =
      (C.argTy d D.params.length X.length).substList (X.reverse ++ (ps.subst γ τ).toList.reverse) := by
  rw [← subst_upN_teleSub, branchArgTy_subst γ τ (Meta.argTy_closed (sigClosed_of_wfSig hW) hD hC X.length) hps hlen]
  exact branchArgTy_substList (sigClosed_of_wfSig hW) hD hC (by rw [toList_subst hps]; simpa using hlen)
    (by simp)

/-- The induction hypothesis type in the branch telescope at its actual argument prefix. -/
theorem branchIhTy_teleSub2 {C : Ctor} {s : ℕ} (hs : s < C.recPos.length) (M : Tm)
    (X Y : List Tm) (hX : X.length = C.args.length) (hY : Y.length = s)
    (γ : ℕ → Tm) (τ : ℕ → I) :
    (DataDecl.branchIhTy C M s).subst (teleSub (X ++ Y) γ) τ =
      (M.subst (Tm.up γ) τ).inst (X.getD (C.recPos.getD s 0) .abort) := by
  rw [← subst_upN_teleSub]
  have hlen : (X ++ Y).length = C.args.length + s := by simp [hX, hY]
  rw [hlen, branchIhTy_subst γ τ hs M, List.reverse_append]
  exact branchIhTy_substList _ hs (by simpa using hY) hX

/-- Related constructor arguments and induction hypotheses close the branch telescope. -/
theorem branchTele2_rel {d c : ℕ} {D : DataDecl} {C : Ctor}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C)
    {ps M : Tm} (hps : IsList ps) (hlen : ps.toList.length = D.params.length)
    (cσ : CSub2 S Ψ Φ Γ k) (X X' Y Y' : List Tm)
    (hX : X.length = C.args.length) (hX' : X'.length = C.args.length)
    (hY : Y.length = C.recPos.length) (hY' : Y'.length = C.recPos.length)
    (ha : ∀ j (hj : j < C.args.length), RE2 S k ((C.argTy d D.params.length j).substList
      ((X.take j).reverse ++ (cσ.L ps).toList.reverse)) (X.getD j .abort) (X'.getD j .abort))
    (hi : ∀ s (hs : s < C.recPos.length), RE2 S k ((M.subst (Tm.up cσ.γ) cσ.σ.τ).inst
      (X.getD (C.recPos.getD s 0) .abort)) (Y.getD s .abort) (Y'.getD s .abort)) :
    ∀ j (hj : j < (X ++ Y).length) (hj' : j < (X' ++ Y').length)
      (hjΔ : j < (branchTele2 d D C ps M).length),
      RE2 S k ((branchTele2 d D C ps M)[j].subst (teleSub ((X ++ Y).take j) cσ.γ) cσ.σ.τ)
        (X ++ Y)[j] (X' ++ Y')[j] := by
  intro j hj hj' hjΔ
  by_cases hjx : j < X.length
  · have hjx' : j < X'.length := by omega
    simp only [branchTele2] at hjΔ ⊢
    rw [List.getElem_append_left (by simp; omega), List.getElem_map, List.getElem_range,
      List.getElem_append_left hjx, List.getElem_append_left hjx', List.take_append_of_le_length hjx.le]
    have hBT := branchArgTy_teleSub2 hW hD hC hps hlen (X.take j) cσ.γ cσ.σ.τ
    have ht : (X.take j).length = j := by simp; omega
    rw [ht] at hBT
    rw [hBT]
    have hh := ha j (by omega)
    rwa [getD_eq_get' hjx, getD_eq_get' hjx'] at hh
  · obtain ⟨s, rfl⟩ : ∃ s, j = X.length + s := ⟨j - X.length, by omega⟩
    have hs : s < C.recPos.length := by simp only [List.length_append] at hj; omega
    simp only [branchTele2] at hjΔ ⊢
    rw [List.getElem_append_right (by simp; omega), List.getElem_map, List.getElem_range,
      List.getElem_append_right (by omega), List.getElem_append_right (by omega), List.take_length_add_append]
    simp only [List.length_map, List.length_range, ← hX, ← hX', Nat.add_sub_cancel_left]
    rw [branchIhTy_teleSub2 hW hs M X (Y.take s) hX (by simp; omega)]
    simp only [show X.length + s - X'.length = s by omega]
    have hh := hi s hs
    rwa [getD_eq_get' (show s < Y.length by omega), getD_eq_get' (show s < Y'.length by omega)] at hh

/-- A branch boundary equation at related arguments and induction hypotheses. -/
theorem valid_branchBnd_inst2 {d c : ℕ} {D : DataDecl} {C : Ctor} {ps M bs b e : Tm}
    (hbr : Valid2 S Ψ Φ Γ b b (D.branchTy d c C ps M))
    {ψ : I} (hbd : Valid2 S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps M Γ)
      (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps M))
    (cσ : CSub2 S Ψ Φ Γ k) (X X' Y Y' : List Tm)
    (hX : X.length = C.args.length) (hX' : X'.length = C.args.length)
    (hY : Y.length = C.recPos.length) (hY' : Y'.length = C.recPos.length)
    (ha : ∀ j (hj : j < (X ++ Y).length) (hj' : j < (X' ++ Y').length)
      (hjΔ : j < (branchTele2 d D C ps M).length),
      RE2 S k ((branchTele2 d D C ps M)[j].subst (teleSub ((X ++ Y).take j) cσ.γ) cσ.σ.τ)
        (X ++ Y)[j] (X' ++ Y')[j])
    (rs rs' : List I) (hrs : rs.length = C.dims) (he : IEqL rs rs')
    (hsc : ∀ r ∈ rs, r.Scoped k) (hsc' : ∀ r ∈ rs', r.Scoped k)
    (hh : I.Entails .one (ψ.subst (consIs rs cσ.σ.τ))) :
    RE2 S k ((M.subst (Tm.up cσ.γ) cσ.σ.τ).inst (.con d c (cσ.L ps) (Tm.ofList X) rs))
      (Tm.papps (Tm.apps (cσ.L b) (X ++ Y)) rs)
      ((D.bndElim C ps bs e).subst (teleSub (X' ++ Y') cσ.γ') (consIs rs' cσ.σ'.τ)) := by
  have hT : ∀ k (cσ : CSub2 S Ψ Φ Γ k),
      RT2 S k (cσ.L ((branchTele2 d D C ps M).foldr Tm.pi
        (ipis C.dims (DataDecl.branchBody d c C ps M))))
        (cσ.R ((branchTele2 d D C ps M).foldr Tm.pi
          (ipis C.dims (DataDecl.branchBody d c C ps M)))) := by
    intro k cσ
    rw [← branchTy_tele2]
    exact (hbr k cσ).1
  rw [branchCtx_tele2, ← hrs] at hbd
  have H := Valid2.foldPi_inst hW hT cσ (X ++ Y) (X' ++ Y')
    (by simp only [List.length_append, branchTele2_length, hX, hY])
    (by simp only [List.length_append, hX, hX', hY, hY']) ha rs rs' he hsc hsc' hh hbd
  have R := H.2
  rw [branchBody_inst2 d c C ps M X Y rs hX hY hrs, branchApp_inst2 C b X Y rs hX hY hrs] at R
  exact R

/-- Close a branch boundary using the actual eliminations of its recursive arguments. -/
theorem valid_branchBnd_rel2 {d c : ℕ} {D : DataDecl} {C : Ctor}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C)
    {ps M bs b e : Tm} (hps : IsList ps) (hlen : ps.toList.length = D.params.length)
    (hbr : Valid2 S Ψ Φ Γ b b (D.branchTy d c C ps M))
    {ψ : I} (hψ : ψ.Scoped C.dims)
    (hbd : Valid2 S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps M Γ)
      (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps M))
    (cσ : CSub2 S Ψ Φ Γ k) (X X' : List Tm)
    (hX : X.length = C.args.length) (hX' : X'.length = C.args.length)
    (ha : ∀ j (hj : j < C.args.length), RE2 S k ((C.argTy d D.params.length j).substList
      ((X.take j).reverse ++ (cσ.L ps).toList.reverse)) (X.getD j .abort) (X'.getD j .abort))
    (hi : ∀ j, j ∈ C.recPos → RE2 S k ((M.subst (Tm.up cσ.γ) cσ.σ.τ).inst (X.getD j .abort))
      (.elim d (cσ.L ps) (M.subst (Tm.up cσ.γ) cσ.σ.τ) (cσ.L bs) (X.getD j .abort))
      (.elim d (cσ.R ps) (M.subst (Tm.up cσ.γ') cσ.σ'.τ) (cσ.R bs) (X'.getD j .abort)))
    (rs rs' : List I) (hrs : rs.length = C.dims) (he : IEqL rs rs')
    (hsc : ∀ r ∈ rs, r.Scoped k) (hsc' : ∀ r ∈ rs', r.Scoped k)
    (hh : I.Entails .one (Ctor.cofAt ψ rs)) :
    RE2 S k ((M.subst (Tm.up cσ.γ) cσ.σ.τ).inst (.con d c (cσ.L ps) (Tm.ofList X) rs))
      (Tm.papps (Tm.apps (cσ.L b) (X ++ ihsOf d C (cσ.L ps) (M.subst (Tm.up cσ.γ) cσ.σ.τ) (cσ.L bs) X)) rs)
      ((D.bndElim C ps bs e).subst
        (teleSub (X' ++ ihsOf d C (cσ.R ps) (M.subst (Tm.up cσ.γ') cσ.σ'.τ) (cσ.R bs) X') cσ.γ')
        (consIs rs' cσ.σ'.τ)) := by
  let Y := ihsOf d C (cσ.L ps) (M.subst (Tm.up cσ.γ) cσ.σ.τ) (cσ.L bs) X
  let Y' := ihsOf d C (cσ.R ps) (M.subst (Tm.up cσ.γ') cσ.σ'.τ) (cσ.R bs) X'
  have hY : Y.length = C.recPos.length := by simp [Y, ihsOf]
  have hY' : Y'.length = C.recPos.length := by simp [Y', ihsOf]
  have hih : ∀ s (hs : s < C.recPos.length), RE2 S k ((M.subst (Tm.up cσ.γ) cσ.σ.τ).inst
      (X.getD (C.recPos.getD s 0) .abort)) (Y.getD s .abort) (Y'.getD s .abort) := by
    intro s hs
    have hg : C.recPos.getD s 0 = C.recPos[s] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]
      rfl
    simp only [Y, Y', ihsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hs,
      Option.map_some, Option.getD_some, hg]
    exact hi _ (List.getElem_mem hs)
  exact valid_branchBnd_inst2 hW hbr hbd cσ X X' Y Y' hX hX' hY hY'
    (branchTele2_rel hW hD hC hps hlen cσ X X' Y Y' hX hX' hY hY' ha hih)
    rs rs' hrs he hsc hsc' (by rw [cofAt_consIs2 (by rw [hrs]; exact hψ)]; exact hh)

end

end Model.Whnf
