import Model.Whnf.Valid2ElimH8

/-!
# The closed boundary interpreter of a higher inductive eliminator

Recursive boundary leaves use the eliminations of the corresponding opaque constructor arguments.
Nested constructors use their branches, with ordinary boundary instances as point arguments.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

mutual
/-- The value of a simple boundary in the eliminator's constructor algebra. -/
def bndInterp2 (d : ℕ) (D : DataDecl) (C : Ctor) (ps M bs : Tm) (X : List Tm) (rs : List I) : Tm → Tm
  | .var j => .elim d ps M bs (X.getD (C.args.length - 1 - j) .abort)
  | .con _ c _ as ss =>
    match D.ctors[c]?, bs.toList[c]? with
    | some C', some b => Tm.papps (Tm.apps b
        (as.toList.map (fun a => Ctor.bndAt a ps.toList X rs) ++ bndInterpArgs2 d D C ps M bs X rs C' 0 as))
        (ss.map fun r => Ctor.cofAt r rs)
    | _, _ => .abort
  | _ => .abort

/-- The induction hypotheses of a nested boundary constructor. -/
def bndInterpArgs2 (d : ℕ) (D : DataDecl) (C : Ctor) (ps M bs : Tm) (X : List Tm) (rs : List I)
    (C' : Ctor) (k : ℕ) : Tm → List Tm
  | .tcons a as => (if C'.isRec k then [bndInterp2 d D C ps M bs X rs a] else []) ++
      bndInterpArgs2 d D C ps M bs X rs C' (k + 1) as
  | _ => []
end

/-- A recursive boundary leaf evaluates to its induction hypothesis. -/
theorem bndInterp2_var (d : ℕ) (D : DataDecl) (C : Ctor) (ps M bs : Tm) (X : List Tm) (rs : List I) (j : ℕ) :
    bndInterp2 d D C ps M bs X rs (.var j) = .elim d ps M bs (X.getD (C.args.length - 1 - j) .abort) := rfl

/-- A boundary constructor evaluates to its branch. -/
theorem bndInterp2_con {d c d' : ℕ} {D : DataDecl} {C C' : Ctor} {ps M bs b qs as : Tm} {X : List Tm}
    {rs ss : List I} (hC : D.ctors[c]? = some C') (hb : bs.toList[c]? = some b) :
    bndInterp2 d D C ps M bs X rs (.con d' c qs as ss) = Tm.papps (Tm.apps b
      (as.toList.map (fun a => Ctor.bndAt a ps.toList X rs) ++ bndInterpArgs2 d D C ps M bs X rs C' 0 as))
      (ss.map fun r => Ctor.cofAt r rs) := by
  simp only [bndInterp2, hC, hb]

/-- The recursive arguments of a boundary constructor, in declaration order. -/
theorem bndInterpArgs2_eqN (d : ℕ) (D : DataDecl) (C : Ctor) (ps M bs : Tm) (X : List Tm) (rs : List I) (C' : Ctor) :
    ∀ (L : List Tm) (k : ℕ), bndInterpArgs2 d D C ps M bs X rs C' k (Tm.ofList L) =
      ((List.range L.length).filter (fun j => C'.isRec (k + j))).map
        (fun j => bndInterp2 d D C ps M bs X rs (L.getD j .abort))
  | [], k => by simp [Tm.ofList, bndInterpArgs2]
  | a :: L, k => by
    simp only [Tm.ofList, bndInterpArgs2, bndInterpArgs2_eqN d D C ps M bs X rs C' L (k + 1)]
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
    have e : ((fun j => C'.isRec (k + j)) ∘ Nat.succ) = fun j => C'.isRec (k + 1 + j) := by
      funext j
      simp only [Function.comp]
      congr 1
      omega
    rw [e]
    by_cases hr : C'.isRec k = true
    · simp [hr, List.map_map, Function.comp_def, List.getD_cons_succ]
    · simp [hr, List.map_map, Function.comp_def, List.getD_cons_succ]

/-- The open branch boundary interpreter closes to the eliminator's constructor algebra. -/
theorem bndElim_interp_inst2 {d c : ℕ} {D : DataDecl} {C : Ctor} {ps M bs : Tm}
    (hps : IsList ps) (hpl : ps.toList.length = D.params.length) (hbs : IsList bs)
    (X : List Tm) (rs : List I) (hX : X.length = C.args.length) (hrs : rs.length = C.dims)
    (γ : ℕ → Tm) (τ : ℕ → I) :
    ∀ (N : ℕ) (e : Tm), sizeOf e < N → Ctor.simpleB D.ctors d D.params.length c C.args.length C e = true →
      e.closedB (ps.toList.length + C.args.length) C.dims = true →
      (D.bndElim C ps bs e).subst
        (teleSub (X ++ ihsOf d C (ps.subst γ τ) (M.subst (Tm.up γ) τ) (bs.subst γ τ) X) γ) (consIs rs τ) =
      bndInterp2 d D C (ps.subst γ τ) (M.subst (Tm.up γ) τ) (bs.subst γ τ) X rs e := by
  let Y := ihsOf d C (ps.subst γ τ) (M.subst (Tm.up γ) τ) (bs.subst γ τ) X
  have hY : Y.length = C.recPos.length := by simp [Y, ihsOf]
  intro N
  induction N with
  | zero => intro e hsz; omega
  | succ N ih =>
    intro e hsz hs hcl
    cases e
    case var j =>
      simp only [Ctor.simpleB, Bool.and_eq_true, decide_eq_true_eq] at hs
      rw [bndElim_var_eq2 hs.1 hs.2 X rs hX γ τ, bndInterp2_var, bndAt_var rs (by omega)]
      rw [hX]
    case con d' c' qs as ss =>
      obtain ⟨hdd, hcc, hqs, C', hC', hal, hrl, hsa, has⟩ := simpleB_con_inv hs
      subst d' qs
      obtain ⟨-, hacl, hss⟩ := closedB_con hcl
      have hBC : (bs.subst γ τ).toList[c']? = (bs.toList[c']?).map (fun b => b.subst γ τ) := by
        rw [toList_subst hbs, List.getElem?_map]
      cases hb : bs.toList[c']? with
      | none => simp only [DataDecl.bndElim, hC', hb, Tm.subst, bndInterp2, hBC, Option.map_none]
      | some b =>
        have hBC' : (bs.subst γ τ).toList[c']? = some (b.subst γ τ) := by rw [hBC, hb]; rfl
        have hBA : bndInterpArgs2 d D C (ps.subst γ τ) (M.subst (Tm.up γ) τ) (bs.subst γ τ) X rs C' 0 as =
            C'.recPos.map (fun j => bndInterp2 d D C (ps.subst γ τ) (M.subst (Tm.up γ) τ)
              (bs.subst γ τ) X rs (as.toList.getD j .abort)) := by
          conv => lhs; rw [has]
          rw [bndInterpArgs2_eqN, hal, ← recPos_eq_filter]
        have hrec : C'.recPos.map (fun j => (D.bndElim C ps bs (as.toList.getD j .abort)).subst
              (teleSub (X ++ Y) γ) (consIs rs τ)) =
            C'.recPos.map (fun j => bndInterp2 d D C (ps.subst γ τ) (M.subst (Tm.up γ) τ)
              (bs.subst γ τ) X rs (as.toList.getD j .abort)) := by
          apply List.map_congr_left
          intro j hj
          obtain ⟨hjn, hjr⟩ := mem_recPos hj
          have hjas : j < as.toList.length := by omega
          rw [getD_eq_get' hjas]
          have hs0 := (simpleArgs_get as 0 hsa j hjas).1 (by simpa using hjr)
          have hc0 := closed_toList hacl _ (List.getElem_mem hjas)
          have hsize := sizeOf_con_arg (d' := d) (c' := c') (ps0 := Ctor.paramVars D.params.length C.args.length)
            (rs0 := ss) (List.getElem_mem hjas)
          exact ih _ (by omega) hs0 hc0
        have hsr : ss.map (fun r => r.subst (consIs rs τ)) = ss.map (fun r => Ctor.cofAt r rs) := by
          apply List.map_congr_left
          intro r hr
          exact cofAt_consIs2 (by rw [hrs]; exact hss r hr) τ
        rw [bndElim_con_inst2 hC' hb hps has hal hacl X Y rs hX hY hrs γ τ,
          bndInterp2_con hC' hBC', hBA, hrec, hsr]
    all_goals simp [Ctor.simpleB] at hs

end

end Model.Whnf
