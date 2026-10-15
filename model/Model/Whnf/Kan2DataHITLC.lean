import Model.Whnf.Kan2DataHITBnd

/-!
# Transport of boundary terms: the point arguments of nested constructors

A point argument of a nested constructor `c'` of a boundary of `c` is an argument `X_i` of `c`. Its
transport along the argument line of `c'` (built from the fillers of the nested arguments) is related to
its transport along the argument line of `c` (`TC.nested_pt`): the lines are related at every point, by
the relation of the argument types of the nested constructors (`bndRel`, `HITHyp2.bndTy`) and by induction
along the arguments of `c'` (the recursive arguments do not occur in the argument types,
`argTy_point_congr`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

namespace TC

variable {d : ℕ} {D : DataDecl} {PL : Tm} {φ : I} {c : ℕ} {C : Ctor} {q : Tm} {X : List Tm}
  {rs : List I} (H : TC S k d D PL PL φ φ c C q q X X rs rs)
include H

/-- Point arguments of nested constructors, transported along the nested and the outer argument lines. -/
theorem nested_pt (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1)) {c' : ℕ} {C' : Ctor} {as0 : Tm} {rs0 : List I}
    (hC' : D.ctors[c']? = some C')
    (hs : Ctor.simpleB D.ctors d D.params.length c C.args.length C
      (.con d c' (Ctor.paramVars D.params.length C.args.length) as0 rs0) = true)
    (hBI : BI S d D c C rs (.con d c' (Ctor.paramVars D.params.length C.args.length) as0 rs0))
    (hty' : HasTy S k .one [] (.transp (.data d PL) φ (.con d c' q
      (Tm.ofList (as0.toList.map (Ctor.bndAt · q.toList X rs))) (rs0.map (·.subst (rsSub rs)))))
      (.data d (PL.dinst .one))) :
    ∀ j (hj : j < C'.args.length), C'.isRec j = false → ∀ x, as0.toList[j]? = some (.var x) →
      x < C.args.length →
      RE2 S k ((tl d D C' PL φ (as0.toList.map (Ctor.bndAt · q.toList X rs)) j).dinst .one)
        (.transp (tl d D C' PL φ (as0.toList.map (Ctor.bndAt · q.toList X rs)) j) φ
          ((as0.toList.map (Ctor.bndAt · q.toList X rs)).getD j .abort))
        (.transp (tl d D C PL φ X (C.args.length - 1 - x)) φ (X.getD (C.args.length - 1 - x) .abort)) ∧
      RT2 S k ((tl d D C' PL φ (as0.toList.map (Ctor.bndAt · q.toList X rs)) j).dinst .one)
        ((tl d D C PL φ X (C.args.length - 1 - x)).dinst .one) := by
  have hW := H.hW
  obtain ⟨-, -, -, C1, hC1, hal, -, hsa, -⟩ := simpleB_con_inv hs
  rw [hC'] at hC1; cases hC1
  set Z := as0.toList.map (Ctor.bndAt · q.toList X rs) with hZ
  obtain ⟨-, -, -, -, hXl, -, hPl, -, hPlen, -, hPc, -⟩ := H.basic
  have hZl : Z.length = C'.args.length := by simp [hZ, hal]
  have hlF := tF_length d D C PL φ X
  have hlF' := tF_length d D C' PL φ Z
  have tyB : ∀ {k4 : ℕ} {A B : Tm}, RT2 S k4 A B → TyEq S k4 A B := fun h => (Comp2_ty_base h).2.2.2.2.2
  have hPP1 : RT2 S (k + 1) (.data d PL) (.data d PL) := by
    have := H.hRLσ (ISub.id (k + 1)); rwa [isub_id_of_closed hPc] at this
  have hCR : ∀ c'' < c, CRSt S d D (k + 1) PL c'' := fun c'' _ => con_rel hW H.hD H.hPL hPP1 hH hyp c''
  -- the lines of the nested arguments, typed
  have hLt : ∀ j (hj : j < C'.args.length), HasTy S (k + 1) .one [] (tl d D C' PL φ Z j)
      (.univ (tcon_typing hW H.hD H.hp hC' hty' hj).choose) :=
    fun j hj => (tcon_typing hW H.hD H.hp hC' hty' hj).choose_spec.1
  have hXL' : ∀ j (hj : j < C'.args.length) {k4 : ℕ} (θ : ISub k4 (k + 1)),
      TyCode k4 (semK S k4 ((tl d D C' PL φ Z j).isub θ)) := fun j hj {_} θ =>
    tyCode_of_univ hW (HasTy.isubS hW (hLt j hj) θ)
  -- the point positions
  have hptpos : ∀ j (hj : j < C'.args.length), C'.isRec j = false → ∃ x, as0.toList[j]? = some (.var x) ∧
      x < C.args.length ∧ C.isRec (C.args.length - 1 - x) = false := by
    intro j hj hr
    obtain ⟨x, hx, hxn, hcr⟩ := (simpleArgs_get as0 0 hsa j (by omega)).2 (by simpa using hr)
    exact ⟨x, by rw [List.getElem?_eq_getElem (by omega), hx], hxn, hcr⟩
  have hZget : ∀ j (hj : j < C'.args.length) x, as0.toList[j]? = some (.var x) → x < C.args.length →
      Z.getD j .abort = X.getD (C.args.length - 1 - x) .abort := by
    intro j hj x hx hxn
    rw [hZ, List.getD_eq_getElem?_getD, List.getElem?_map, hx]
    simp only [Option.map_some, Option.getD_some]
    rw [bndAt_var rs (by omega), hXl]
  -- the invariant along the nested arguments
  let Inv : ℕ → Prop := fun j => ∀ (hj : j < C'.args.length), C'.isRec j = false → ∀ x,
    as0.toList[j]? = some (.var x) → x < C.args.length →
    (∀ k3 (σ : ISub k3 (k + 1)), RT2 S k3 ((tl d D C' PL φ Z j).isub σ)
      ((tl d D C PL φ X (C.args.length - 1 - x)).isub σ)) ∧
    (∀ k3 (σ σ' : ISub k3 (k + 1)), σ.tail = σ'.tail → I.Eq (σ.τ 0) (σ'.τ 0) →
      RE2 S k3 ((tl d D C' PL φ Z j).isub σ)
        ((Tm.transpFill (tl d D C' PL φ Z j) φ (Z.getD j .abort)).isub σ)
        ((Tm.transpFill (tl d D C PL φ X (C.args.length - 1 - x)) φ (X.getD (C.args.length - 1 - x) .abort)).isub σ')) ∧
    RE2 S k ((tl d D C' PL φ Z j).dinst .one) (.transp (tl d D C' PL φ Z j) φ (Z.getD j .abort))
        (.transp (tl d D C PL φ X (C.args.length - 1 - x)) φ (X.getD (C.args.length - 1 - x) .abort)) ∧
    RT2 S k ((tl d D C' PL φ Z j).dinst .one) ((tl d D C PL φ X (C.args.length - 1 - x)).dinst .one)
  have key : ∀ j, Inv j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ihj =>
    intro hj hr x hx hxn
    set i := C.args.length - 1 - x with hi_def
    have hi : i < C.args.length := by omega
    have hcr : C.isRec i = false := by
      obtain ⟨x', hx', -, hcr'⟩ := hptpos j hj hr
      rw [hx] at hx'; cases hx'; exact hcr'
    have Gi := H.good_all i hi
    have hZj := hZget j hj x hx hxn
    obtain ⟨lt, hLt', -, -, -, -⟩ := tcon_typing hW H.hD H.hp H.hC H.hty hi
    have hXLc : ∀ {k4 : ℕ} (θ : ISub k4 (k + 1)), TyCode k4 (semK S k4 ((tl d D C PL φ X i).isub θ)) := fun θ =>
      tyCode_of_univ hW (HasTy.isubS hW hLt' θ)
    -- the argument types of the nested constructor do not depend on its recursive arguments
    have congrV : ∀ l (hl : l < C'.args.length), C'.isRec l = false → ∀ (F V : List Tm) (R : List Tm),
        F.length = C'.args.length → V.length = C'.args.length → R.length = D.params.length →
        (∀ l' (h1 : l' < F.length) (h2 : l' < V.length), C'.isRec l' = false → F[l'] = V[l']) →
        (C'.argTy d D.params.length l).substList ((F.take l).reverse ++ R) =
          (C'.argTy d D.params.length l).substList ((V.take l).reverse ++ R) := by
      intro l hl hrl F V R hFl hVl hR hFV
      obtain ⟨A1, hA1⟩ := ctor_point hl hrl
      have eA : C'.argTy d D.params.length l = A1 := by simp [Ctor.argTy, hA1]
      rw [eA]
      exact argTy_point_congr hW H.hD hC' hA1 (by omega) (by omega) R hR (fun l' h1 h2 h => hFV l' h2 h1 h)
    -- (A) the nested line is related to the outer line at every point
    have LA : ∀ k3 (σ : ISub k3 (k + 1)), RT2 S k3 ((tl d D C' PL φ Z j).isub σ) ((tl d D C PL φ X i).isub σ) := by
      intro k3 σ
      obtain ⟨hcon, hYself⟩ := H.fill_inst σ
      have hPσ : HasTy S k3 .one [] (.data d (PL.isub σ)) (.univ D.level) := HasTy.isubS hW H.hPL σ
      have hPPσ := H.hRLσ σ
      have hPlσ : IsList (PL.isub σ) := isList_subst hPl _ _
      have hPlenσ : (PL.isub σ).toList.length = D.params.length := by
        show (PL.subst Tm.var σ.τ).toList.length = _; rw [toList_subst hPl]; simp [hPlen]
      set Y := (tF d D C PL φ X).map (·.isub σ) with hY
      have hYl : Y.length = C.args.length := by simp [hY, hlF]
      obtain ⟨hrel, -⟩ := hBI (PL.isub σ) Y σ.tail.τ hPσ hPPσ hYl hcon hYself
      simp only [bndRel, hC'] at hrel
      have hxj : as0.toList[j]'(by omega) = .var x := by
        rw [List.getElem?_eq_getElem (by omega)] at hx; exact Option.some.inj hx
      have T1 := (bndRelArgs_get as0 0 [] hrel j (by omega)).1 x hxj (by simpa using hr) hxn
      set W2 := as0.toList.map (Ctor.bndAt · (PL.isub σ).toList Y (rs.map (·.subst σ.tail.τ))) with hW2
      have hW2l : W2.length = C'.args.length := by simp [hW2, hal]
      rw [Nat.zero_add, List.append_nil, List.map_take] at T1
      set F := (tF d D C' PL φ Z).map (·.isub σ) with hF
      have hFl : F.length = C'.args.length := by simp [hF, hlF']
      set V := (List.range C'.args.length).map (fun l => if C'.isRec l then W2.getD l .abort else F.getD l .abort)
        with hV
      have hVl : V.length = C'.args.length := by simp [hV]
      have hVget : ∀ l (hl : l < C'.args.length), V.getD l .abort =
          if C'.isRec l then W2.getD l .abort else F.getD l .abort := by
        intro l hl
        rw [hV, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]; rfl
      have hFV : ∀ l' (h1 : l' < F.length) (h2 : l' < V.length), C'.isRec l' = false → F[l'] = V[l'] := by
        intro l' h1 h2 hr'
        have := hVget l' (by omega)
        rw [hr', if_neg (by simp), getD_eq_get' h2, getD_eq_get' h1] at this
        exact this.symm
      have T2 := argTy_rt2' hW H.hD hPσ hPPσ hPPσ hC' hj (A := V.take j) (B := W2.take j) (by simp; omega)
        (by simp; omega) (fun l hl => by
          rw [List.take_take, Nat.min_eq_left hl.le, getD_take_lt hl, getD_take_lt hl, hVget l (by omega)]
          cases hrl : C'.isRec l
          · obtain ⟨xl, hxl, hxln, -⟩ := hptpos l (by omega) hrl
            have IH := (ihj l hl (by omega) hrl xl hxl hxln).2.1 k3 σ σ rfl (I_eq_refl _)
            rw [if_neg (by simp)]
            rw [← congrV l (by omega) hrl F V _ hFl hVl (by simp [hPlenσ]) hFV,
              ← tl_isub hW H.hD hC' hPl φ Z (by omega) σ]
            have e1 : F.getD l .abort = (Tm.transpFill (tl d D C' PL φ Z l) φ (Z.getD l .abort)).isub σ := by
              rw [hF, getD_map_isub' (by omega), tF_getD d D C' PL φ Z (by omega)]
            have e2 : W2.getD l .abort = (Tm.transpFill (tl d D C PL φ X (C.args.length - 1 - xl)) φ
                (X.getD (C.args.length - 1 - xl) .abort)).isub σ := by
              rw [hW2, List.getD_eq_getElem?_getD, List.getElem?_map, hxl]
              simp only [Option.map_some, Option.getD_some]
              rw [bndAt_var _ (by omega), hYl, hY, getD_map_isub' (by omega), tF_getD d D C PL φ X (by omega)]
            rw [e1, e2]
            exact IH
          · rw [if_pos rfl, argTy_rec_inst hrl hPlσ hPlenσ (by simp; omega)]
            have hal' : l < as0.toList.length := by omega
            obtain ⟨hrel_l, hty_l⟩ := BI_sub hW H.hD H.hC hs hBI hC' hal' hrl (PL.isub σ) Y σ.tail.τ hPσ hPPσ hYl
              hcon hYself
            have hsl := (simpleArgs_get as0 0 hsa l hal').1 (by simpa using hrl)
            have e2 : W2.getD l .abort = Ctor.bndAt as0.toList[l] (PL.isub σ).toList Y (rs.map (·.subst σ.tail.τ)) := by
              rw [hW2, getD_eq_get' (by simp; omega), List.getElem_map]
            rw [e2]
            exact bnd_rel hW H.hD H.hPL hPP1 hCR H.hC (sizeOf as0.toList[l] + 1) _ (by omega) hsl σ hPlenσ hPlenσ
              hYl hYl (forall2_ieq_refl _) hYself hrel_l hty_l hty_l)
      have hTc : TyCode k3 (semK S k3 ((C.argTy d D.params.length i).substList ((Y.take i).reverse ++
          (PL.isub σ).toList.reverse))) := by
        rw [hY, ← tl_isub hW H.hD H.hC hPl φ X hi.le]; exact hXLc σ
      have e1 := tl_isub hW H.hD hC' hPl φ Z hj.le σ
      rw [congrV j hj hr _ V _ hFl hVl (by simp [hPlenσ]) hFV] at e1
      rw [e1, tl_isub hW H.hD H.hC hPl φ X hi.le σ]
      have hTV : TyCode k3 (semK S k3 ((C'.argTy d D.params.length j).substList ((V.take j).reverse ++
          (PL.isub σ).toList.reverse))) := by
        rw [← e1]; exact hXL' j hj σ
      exact RT2.trans hW hTV T2 (RT2.symm hW hTc T1)
    have hcj : (tl d D C PL φ X i).closedB 0 (k + 1) = true := closed_ty (spec_to_minimal hW hLt')
    have hcj' : (tl d D C' PL φ Z j).closedB 0 (k + 1) = true := closed_ty (spec_to_minimal hW (hLt j hj))
    obtain ⟨-, -, Gi3, Gi4, Gi5, -, -, -⟩ := Gi
    -- the lines at related points
    have hR : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
        RT2 S k3 ((tl d D C' PL φ Z j).isub (ISub.cons y hy τ)) ((tl d D C PL φ X i).isub (ISub.cons y' hy' τ)) :=
      fun k3 τ y y' hy hy' hE => RT2.trans hW (hXL' j hj _) (LA k3 _) (Gi3 k3 τ y y' hy hy' hE)
    have hRL : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
        RT2 S k3 ((tl d D C' PL φ Z j).isub (ISub.cons y hy τ)) ((tl d D C' PL φ Z j).isub (ISub.cons y' hy' τ)) :=
      fun k3 τ y y' hy hy' hE => RT2.trans hW (hXL' j hj _) (hR k3 τ y y' hy hy' hE)
        (RT2.symm hW (hXL' j hj _) (LA k3 (ISub.cons y' hy' τ)))
    have hLC : LineConst S k (tl d D C' PL φ Z j) φ := by
      intro k3 τ r hr hh
      exact RT2.trans hW (hXL' j hj _) (LA k3 _) (RT2.trans hW (hXLc _) (Gi4 k3 τ r hr hh)
        (RT2.symm hW (hXL' j hj _) (LA k3 (ISub.cons .zero trivial τ))))
    have hT : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped (k3 + 1)) (hy' : y'.Scoped (k3 + 1)), I.Eq y y' →
        I.Eq (y.subst (ISub.cons .zero trivial (ISub.id k3)).τ) .zero →
        KanT2At S k3 ((tl d D C' PL φ Z j).isub (ISub.cons y hy τ.up.tail))
          ((tl d D C PL φ X i).isub (ISub.cons y' hy' τ.up.tail)) ((X.getD i .abort).isub τ)
          ((X.getD i .abort).isub τ) := by
      intro k3 τ y y' hy hy' hE _
      obtain ⟨-, hYself'⟩ := H.fill_inst (ISub.cons y' hy' τ.up.tail)
      have hAl : (((tF d D C PL φ X).map (·.isub (ISub.cons y' hy' τ.up.tail))).take i).length = i := by
        simp; omega
      have hL2 : RT2 S (k3 + 1) ((tl d D C PL φ X i).isub (ISub.cons y' hy' τ.up.tail))
          ((tl d D C' PL φ Z j).isub (ISub.cons y hy τ.up.tail)) :=
        RT2.trans hW (hXLc _) (Gi3 (k3 + 1) τ.up.tail y' y hy' hy (I_eq_symm hE))
          (RT2.symm hW (hXL' j hj _) (LA (k3 + 1) _))
      rw [tl_isub hW H.hD H.hC hPl φ X hi.le] at hL2
      have K0 := argLine_kanT2 hW H.hD (HasTy.isubS hW H.hPL (ISub.cons y' hy' τ.up.tail))
        (H.hRLσ _)  H.hC (A := ((tF d D C PL φ X).map (·.isub (ISub.cons y' hy' τ.up.tail))).take i)
        (by rw [hAl]; exact hi) (by rw [hAl]; exact hcr) (fun l hl => by
          rw [hAl] at hl
          rw [List.take_take, Nat.min_eq_left hl.le, getD_take_lt hl]
          exact hYself' l (by omega)) (by rw [hAl]; exact hL2)
      rw [hAl] at K0
      have K : KanT2 S k3 ((tl d D C PL φ X i).isub (ISub.cons y' hy' τ.up.tail))
          ((tl d D C' PL φ Z j).isub (ISub.cons y hy τ.up.tail)) := by
        rw [tl_isub hW H.hD H.hC hPl φ X hi.le]; exact K0
      exact KanT2.at (KanT2.flip hW K) _ _
    obtain ⟨-, -, htyO', htyF', htyX', -⟩ := tcon_typing hW H.hD H.hp hC' hty' hj
    obtain ⟨-, -, htyO, htyF, htyX, -⟩ := tcon_typing hW H.hD H.hp H.hC H.hty hi
    rw [hZj] at htyO' htyF' htyX'
    have r0 := LA k (ISub.cons .zero trivial (ISub.id k))
    have r1 := LA k (ISub.cons .one trivial (ISub.id k))
    rw [isub_cons_id_of_closed hcj', isub_cons_id_of_closed hcj] at r0 r1
    have hX0 : TyCode k (semK S k ((tl d D C' PL φ Z j).dinst .zero)) := tyCode_of_ty hW htyX'
    have hX1 : TyCode k (semK S k ((tl d D C' PL φ Z j).dinst .one)) := tyCode_of_ty hW htyO'
    have hXc0 : TyCode k (semK S k ((tl d D C PL φ X i).dinst .zero)) := tyCode_of_ty hW htyX
    have ha : RE2 S k ((tl d D C' PL φ Z j).dinst .zero) (X.getD i .abort) (X.getD i .abort) :=
      RE2.conv hW (RT2.symm hW hX0 r0) (RE2.conv hW Gi5 (H.args0_self i hi))
    have LB := tfill_rel hW (hLt j hj) H.hφs H.h12 H.h21 hR hRL hLC hT htyF' htyF ha
    have K0 := hT k (ISub.id k) (.var 0) (.var 0) (show 0 < k + 1 by omega) (show 0 < k + 1 by omega)
      (I_eq_refl _) (I_eq_refl _)
    rw [ISub.cons_var0_up_tail, isub_up_id_of_closed hcj', isub_up_id_of_closed hcj,
      isub_id_of_closed (closed_of_ty hW htyX)] at K0
    have r2 := LA (k + 1) (ISub.id k).up
    rw [isub_up_id_of_closed hcj', isub_up_id_of_closed hcj] at r2
    have htyO'' := htyO.tyConv (TyEq.symm (Comp2_ty_base r1).2.2.2.2.2)
    have LC' := K0 hR φ φ hLC htyO' htyO'' (eqTm_transp_of hW htyO' htyO'' (Comp2_ty_base r2).2.2.2.2.2 H.h12 H.h21
      (RE2.typed ha).2.2) H.h12 H.h21 ha
    rw [hZj]
    exact ⟨LA, LB, LC', r1⟩
  intro j hj hr x hx hxn
  obtain ⟨-, -, h3, h4⟩ := key j hj hr x hx hxn
  exact ⟨h3, h4⟩

end TC

end

end Model.Whnf
