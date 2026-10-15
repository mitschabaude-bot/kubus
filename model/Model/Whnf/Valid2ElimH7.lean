import Model.Whnf.Valid2ElimH6

/-!
# Closing the boundary interpreter of an eliminator

A boundary point closes to the constructor boundary substitution. Recursive variables close to
the corresponding induction hypotheses.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

/-- The point interpretation in a branch context closes to ordinary boundary instantiation. -/
theorem bndPoint_inst2 {C : Ctor} {ps a : Tm} (hps : IsList ps)
    (ha : a.closedB (ps.toList.length + C.args.length) C.dims = true)
    (X Y : List Tm) (rs : List I) (hX : X.length = C.args.length)
    (hY : Y.length = C.recPos.length) (hrs : rs.length = C.dims)
    (γ : ℕ → Tm) (τ : ℕ → I) :
    (DataDecl.bndPoint C ps a).subst (teleSub (X ++ Y) γ) (consIs rs τ) =
      Ctor.bndAt a (ps.subst γ τ).toList X rs := by
  unfold DataDecl.bndPoint Ctor.bndAt
  dsimp only
  rw [subst_subst]
  apply closed_subst_eq a _ _ _ _ _ _ ha
  · intro j hj
    by_cases hjn : j < C.args.length
    · rw [if_pos hjn]
      simp only [Tm.subst]
      rw [teleSub_lt (X ++ Y) γ (by simp only [List.length_append, hX, hY]; omega),
        List.getElem_reverse, List.getElem_append_left (by simp [hX, hY]; omega)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hX]; omega),
        List.getElem?_eq_getElem (by simp [hX]; omega)]
      simp only [Option.getD_some, List.getElem_reverse]
      congr 1
      simp only [List.length_append, hX, hY]
      omega
    · rw [if_neg hjn]
      have hlen : (X ++ Y).length = C.args.length + C.recPos.length := by simp [hX, hY]
      have hw := wkN_teleSub (ps.toList.reverse.getD (j - C.args.length) (.var 0)) (X ++ Y) rs γ τ
      rw [hlen, hrs] at hw
      rw [hw, toList_subst hps, ← List.map_reverse]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [List.getElem?_eq_getElem (by simp; omega), List.getElem?_append_right (by simp [hX]; omega)]
      simp only [List.length_reverse, Option.map_some, Option.getD_some]
      rw [List.getElem?_eq_getElem (by simp [hX]; omega)]
      simp only [Option.getD_some, List.getElem_map, hX]
  · intro i hi
    simp only [I_subst_var, I.subst, consIs_eq, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simp [hrs]; omega)]
    rfl

/-- A recursive boundary variable is interpreted by its induction hypothesis. -/
theorem bndElim_var_inst2 {D : DataDecl} {C : Ctor} {ps bs : Tm} {j s : ℕ}
    (hj : j < C.args.length) (hidx : C.recPos.idxOf? (C.args.length - 1 - j) = some s)
    (X Y : List Tm) (rs : List I) (hX : X.length = C.args.length)
    (hY : Y.length = C.recPos.length) (γ : ℕ → Tm) (τ : ℕ → I) :
    (D.bndElim C ps bs (.var j)).subst (teleSub (X ++ Y) γ) (consIs rs τ) = Y.getD s .abort := by
  obtain ⟨hs, hget, -⟩ := List.idxOf?_eq_some_iff.1 hidx
  simp only [DataDecl.bndElim, hidx, Tm.subst]
  rw [teleSub_lt (X ++ Y) γ (by simp [hX, hY]; omega), List.getElem_reverse,
    List.getElem_append_right (by simp [hX, hY]; omega)]
  rw [getD_eq_get' (show s < Y.length by omega)]
  congr 1
  simp only [List.length_append, hX, hY]
  omega

/-- A nested boundary constructor closes to its branch applied to boundary points and recursive hypotheses. -/
theorem bndElim_con_inst2 {D : DataDecl} {C C' : Ctor} {ps bs b qs as : Tm} {d c : ℕ} {ss : List I}
    (hC : D.ctors[c]? = some C') (hb : bs.toList[c]? = some b) (hps : IsList ps)
    (has : IsList as) (hal : as.toList.length = C'.args.length)
    (hacl : as.closedB (ps.toList.length + C.args.length) C.dims = true)
    (X Y : List Tm) (rs : List I) (hX : X.length = C.args.length)
    (hY : Y.length = C.recPos.length) (hrs : rs.length = C.dims)
    (γ : ℕ → Tm) (τ : ℕ → I) :
    (D.bndElim C ps bs (.con d c qs as ss)).subst (teleSub (X ++ Y) γ) (consIs rs τ) =
      Tm.papps (Tm.apps (b.subst γ τ)
        (as.toList.map (fun a => Ctor.bndAt a (ps.subst γ τ).toList X rs) ++
          C'.recPos.map (fun j => (D.bndElim C ps bs (as.toList.getD j .abort)).subst
            (teleSub (X ++ Y) γ) (consIs rs τ)))) (ss.map (·.subst (consIs rs τ))) := by
  have hEA : D.bndElimArgs C ps bs C' 0 as =
      C'.recPos.map (fun j => D.bndElim C ps bs (as.toList.getD j .abort)) := by
    conv => lhs; rw [has]
    rw [bndElimArgs_eqN, hal, ← recPos_eq_filter]
  have hL : (X ++ Y).length = C.args.length + C.recPos.length := by simp [hX, hY]
  have hP : (as.toList.map (DataDecl.bndPoint C ps)).map
      (fun t => t.subst (teleSub (X ++ Y) γ) (consIs rs τ)) =
      as.toList.map (fun a => Ctor.bndAt a (ps.subst γ τ).toList X rs) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    exact bndPoint_inst2 hps (closed_toList hacl _ ha) X Y rs hX hY hrs γ τ
  simp only [DataDecl.bndElim, hC, hb]
  rw [papps_subst, apps_subst, ← hL, ← hrs, wkN_teleSub, List.map_append, hP, hEA, List.map_map]
  rfl

/-- At actual induction hypotheses, a recursive boundary variable closes to elimination of that variable. -/
theorem bndElim_var_eq2 {D : DataDecl} {C : Ctor} {ps M bs : Tm} {d j : ℕ}
    (hj : j < C.args.length) (hr : C.isRec (C.args.length - 1 - j) = true)
    (X : List Tm) (rs : List I) (hX : X.length = C.args.length) (γ : ℕ → Tm) (τ : ℕ → I) :
    (D.bndElim C ps bs (.var j)).subst
      (teleSub (X ++ ihsOf d C (ps.subst γ τ) (M.subst (Tm.up γ) τ) (bs.subst γ τ) X) γ) (consIs rs τ) =
      .elim d (ps.subst γ τ) (M.subst (Tm.up γ) τ) (bs.subst γ τ)
        (Ctor.bndAt (.var j) (ps.subst γ τ).toList X rs) := by
  have hm : C.args.length - 1 - j ∈ C.recPos := by
    unfold Ctor.recPos
    exact List.mem_filter.2 ⟨List.mem_range.2 (by omega), hr⟩
  cases hidx : C.recPos.idxOf? (C.args.length - 1 - j) with
  | none => exact False.elim ((List.idxOf?_eq_none_iff.1 hidx) hm)
  | some s =>
    obtain ⟨hs, hg, -⟩ := List.idxOf?_eq_some_iff.1 hidx
    rw [bndElim_var_inst2 hj hidx X _ rs hX (by simp [ihsOf]) γ τ, bndAt_var rs (by omega)]
    simp only [ihsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hs,
      Option.map_some, Option.getD_some, hg, hX]

end

end Model.Whnf
