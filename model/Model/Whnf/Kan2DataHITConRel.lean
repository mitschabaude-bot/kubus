import Model.Whnf.Kan2DataHITCon
import Model.Canon.CanonForm

/-!
# Constructors of higher inductive types with related arguments are related

At a literal higher inductive type, two constructors (with any parameter annotations) whose arguments are
related and whose interval arguments are `I.Eq`-equal are related (`con_rel`), given the hypotheses
`HITHyp2` (the boundaries of constructors, and the argument types of their nested constructors). By
induction on the constructor: where a boundary holds, the constructors reduce to boundary terms, which are
related by induction on the (simple) boundary term (`bnd_rel`), using the relation of the earlier
constructors.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

theorem isub_conT (d c : ℕ) (q : Tm) (X : List Tm) (rs : List I) (σ : ISub k' k) :
    (Tm.con d c q (Tm.ofList X) rs).isub σ = .con d c (q.isub σ) (Tm.ofList (X.map (·.isub σ))) (rs.map (·.subst σ.τ)) := by
  show Tm.con d c (q.isub σ) ((Tm.ofList X).isub σ) (rs.map (·.subst σ.τ)) = _
  rw [ofList_isub]

/-- A list of arguments of a nested constructor of a simple boundary is a list. -/
theorem simpleArgs_isList {ctors : List Ctor} {d np c n : ℕ} {C C' : Ctor} :
    ∀ (as : Tm) (k : ℕ), Ctor.simpleArgs ctors d np c n C C' k as = true → as = Tm.ofList as.toList
  | .tcons a as, k, h => by
    simp only [Ctor.simpleArgs, Bool.and_eq_true] at h
    simp only [Tm.toList, Tm.ofList]
    rw [← simpleArgs_isList as (k + 1) h.2]
  | .tnil, _, _ => rfl
  | .var _, _, h | .const _, _, h | .univ _, _, h | .pi _ _, _, h | .lam _ _, _, h
  | .app _ _, _, h | .sigma _ _, _, h | .pair _ _, _, h | .fst _, _, h
  | .snd _, _, h | .path _ _ _, _, h | .plam _, _, h | .papp _ _, _, h
  | .ipi _, _, h | .split _ _ _ _, _, h | .abort, _, h | .transp _ _ _, _, h
  | .hcomp _ _ _ _, _, h | .glue _ _ _ _, _, h | .glueEl _ _ _ _, _, h
  | .unglue _ _ _, _, h | .data _ _, _, h | .con _ _ _ _ _, _, h
  | .elim _ _ _ _ _, _, h => by simp [Ctor.simpleArgs] at h

theorem argTys_get {C : Ctor} {d np i : ℕ} (hi : i < C.args.length) :
    (C.argTys d np)[i]? = some (C.argTy d np i) := by
  simp [Ctor.argTys, List.getElem?_map, List.getElem?_range hi]

theorem ctor_point {C : Ctor} {i : ℕ} (hi : i < C.args.length) (hr : C.isRec i = false) :
    ∃ A0, C.args[i]? = some (.point A0) := by
  cases h : C.args[i]? with
  | none => rw [List.getElem?_eq_none_iff] at h; omega
  | some a => cases a with
    | point A0 => exact ⟨A0, rfl⟩
    | recur => simp [Ctor.isRec, h] at hr

/-- A nested constructor of a simple boundary. -/
theorem simpleB_con_inv {ctors : List Ctor} {d np c n : ℕ} {C : Ctor} {d' c' : ℕ} {ps0 as0 : Tm} {rs0 : List I}
    (h : Ctor.simpleB ctors d np c n C (.con d' c' ps0 as0 rs0) = true) :
    d' = d ∧ c' < c ∧ ps0 = Ctor.paramVars np n ∧ ∃ C', ctors[c']? = some C' ∧ as0.toList.length = C'.args.length ∧
      rs0.length = C'.dims ∧ Ctor.simpleArgs ctors d np c n C C' 0 as0 = true ∧ as0 = Tm.ofList as0.toList := by
  simp only [Ctor.simpleB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hdd, hcc⟩, hps⟩, hm⟩ := h
  refine ⟨hdd, hcc, hps, ?_⟩
  cases hC' : ctors[c']? with
  | none => rw [hC'] at hm; cases hm
  | some C' =>
    rw [hC'] at hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨hal, hrl⟩, hsa⟩ := hm
    exact ⟨C', rfl, hal, hrl, hsa, simpleArgs_isList as0 0 hsa⟩

/-- The statement of `con_rel` for constructor `c`. -/
def CRSt (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P : Tm) (c : ℕ) : Prop :=
  ∀ {k3 : ℕ} (ρ' : ISub k3 K) {C : Ctor} {q q' : Tm} {X X' : List Tm} {rs rs' : List I},
    D.ctors[c]? = some C →
    HasTy S k3 .one [] (.con d c q (Tm.ofList X) rs) (.data d (P.isub ρ')) →
    HasTy S k3 .one [] (.con d c q' (Tm.ofList X') rs') (.data d (P.isub ρ')) →
    List.Forall₂ I.Eq rs rs' →
    (∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ (P.isub ρ').toList.reverse)) (X.getD i .abort) (X'.getD i .abort)) →
    RE2 S k3 (.data d (P.isub ρ')) (.con d c q (Tm.ofList X) rs) (.con d c q' (Tm.ofList X') rs')

section lit
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
  {K : ℕ} {P : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (hPP : RT2 S K (.data d P) (.data d P))
include hW hD hP hPP

/-- The argument clause of a literal inductive type at a restriction, for its own parameters. -/
theorem argRelH_litH {k3 : ℕ} (ρ' : ISub k3 K) :
    ∀ ps, RedT S k3 (.data d (P.isub ρ')) (.data d ps) →
      argRelH (ΘK S D d K P) (Hom.id K) S k3 ρ'.hom ps ps := by
  intro ps h
  obtain rfl := redT_data_eq (Θ := ΘK S D d K P) h
  exact (dataLit_rel hW hD hP hPP ρ').2.2.1

/-- The argument types at related argument prefixes of a literal inductive type are related. -/
theorem dataLit_argTy2H {k3 : ℕ} (ρ' : ISub k3 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {Z Z' : List Tm}
    (hl' : Z'.length = Z.length)
    (hrec : ∀ i (hi : i < Z.length) (hi' : i < Z'.length), C.isRec i = true →
      DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k3 ρ'.hom
        (.data d (P.isub ρ')) Z[i] Z'[i])
    (hpt : ∀ i (hi : i < Z.length) (hi' : i < Z'.length), C.isRec i = false →
      dataP2 S (ΘK S D d K P) (Hom.id K) k3 ρ'.hom c i ((Z.take i).map (semK S k3))
        ((C.argTy d (dataD S d).params.length i).substList ((Z.take i).reverse ++ (P.isub ρ').toList.reverse))
        Z[i] Z'[i])
    (hr : Z.length < C.args.length) (hrr : C.isRec Z.length = false) :
    (Comp2 S (tyLook (shapeV ((ΘK S D d K P).restr ((Hom.id K).comp ρ'.hom))) c Z.length (Z.map (semK S k3)))
      k3 k3 (Hom.id k3)).ty
      ((C.argTy d (dataD S d).params.length Z.length).substList (Z.reverse ++ (P.isub ρ').toList.reverse))
      ((C.argTy d (dataD S d).params.length Z.length).substList (Z'.reverse ++ (P.isub ρ').toList.reverse)) := by
  have hdD := dataD_eq hW hD
  obtain ⟨-, -, hR, -, -, -, -⟩ := dataLit_rel hW hD hP hPP ρ'
  have hpc : (P.isub ρ').closedB 0 k3 = true := by
    have := closed_of_ty hW (HasTy.isubS hW hP ρ'); simpa [Tm.closedB] using this
  have hC' : (dataD S (ΘK S D d K P).idx).ctors[c]? = some C := by
    show (dataD S d).ctors[c]? = some C; rw [hdD]; exact hC
  exact argRelH_id (Hom.id K) hR hpc hpc hC' hr hl' hrr hrec hpt

/-- A constructor where no boundary holds, related at one stage to an element whose normal form is the
same constructor, from the relations of their arguments. -/
theorem DR2At_conH_of {k3 : ℕ} (ρ' : ISub k3 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {q qs' t : Tm}
    {Y Z : List Tm} {rs rs' : List I} (hYl : Y.length = C.args.length) (hZl : Z.length = C.args.length)
    (hcT : HasTy S k3 .one [] (.con d c q (Tm.ofList Y) rs) (.data d (P.isub ρ')))
    (hnb : firstBnd C.bnd rs = none)
    (ht : RedE S k3 (.data d (P.isub ρ')) t (.con d c qs' (Tm.ofList Z) rs'))
    (he : EqTm S k3 .one [] (.con d c q (Tm.ofList Y) rs) t (.data d (P.isub ρ')))
    (hrs : rs.length = C.dims) (hrs' : rs'.length = C.dims)
    (hreq : ∀ (i : ℕ) (r r' : I), rs[i]? = some r → rs'[i]? = some r' → I.Eq r r')
    (hsc : ∀ r ∈ rs, r.Scoped k3) (hsc' : ∀ r ∈ rs', r.Scoped k3)
    (hargs : ∀ i (hi : i < Y.length) (hi' : i < Z.length),
      (C.isRec i = true → RE2 S k3 (.data d (P.isub ρ')) Y[i] Z[i]) ∧
      (C.isRec i = false →
        RT2 S k3 ((C.argTy d D.params.length i).substList ((Y.take i).reverse ++ (P.isub ρ').toList.reverse))
          ((C.argTy d D.params.length i).substList ((Z.take i).reverse ++ (P.isub ρ').toList.reverse)) →
        RE2 S k3 ((C.argTy d D.params.length i).substList ((Y.take i).reverse ++ (P.isub ρ').toList.reverse))
          Y[i] Z[i])) :
    DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k3 ρ'.hom
      (.data d (P.isub ρ')) (.con d c q (Tm.ofList Y) rs) t := by
  have hdD := dataD_eq hW hD
  have hC' : (dataD S d).ctors[c]? = some C := by rw [hdD]; exact hC
  have hpl := (dataLit_rel hW hD hP hPP ρ').2.2.2.2.2.1
  let Good : ℕ → Prop := fun j =>
    (∀ i (hi : i < Y.length) (hi' : i < Z.length), i < j → C.isRec i = true →
      DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k3 ρ'.hom
        (.data d (P.isub ρ')) Y[i] Z[i]) ∧
    (∀ i (hi : i < Y.length) (hi' : i < Z.length), i < j → C.isRec i = false →
      dataP2 S (ΘK S D d K P) (Hom.id K) k3 ρ'.hom c i ((Y.take i).map (semK S k3))
        ((C.argTy d (dataD S d).params.length i).substList ((Y.take i).reverse ++ (P.isub ρ').toList.reverse))
        Y[i] Z[i])
  have key : ∀ j, j ≤ C.args.length → Good j := by
    intro j
    induction j with
    | zero => intro _; exact ⟨fun i _ _ h => absurd h (Nat.not_lt_zero _), fun i _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ j ih =>
      intro hj
      obtain ⟨g1, g2⟩ := ih (by omega)
      refine ⟨fun i hi hi' hij hri => ?_, fun i hi hi' hij hri => ?_⟩
      · by_cases hlt : i < j
        · exact g1 i hi hi' hlt hri
        obtain rfl : i = j := by omega
        exact ((RE2_dataLit_iff hW hD hP ρ').1 ((hargs i hi hi').1 hri)).2
      · by_cases hlt : i < j
        · exact g2 i hi hi' hlt hri
        obtain rfl : i = j := by omega
        have hli : (Y.take i).length = i := by simp; omega
        have hty := dataLit_argTy2H hW hD hP hPP ρ' hC (Z := Y.take i) (Z' := Z.take i)
          (by simp; omega)
          (fun i' h1 h2 hri' => by
            simp only [List.getElem_take]; exact g1 i' (by simp at h1; omega) (by simp at h2; omega)
              (by simp at h1; omega) hri')
          (fun i' h1 h2 hri' => by
            simp only [List.getElem_take, List.take_take]
            rw [Nat.min_eq_left (by simp at h1; omega)]
            exact g2 i' (by simp at h1; omega) (by simp at h2; omega) (by simp at h1; omega) hri')
          (by rw [hli]; omega) (by rw [hli]; exact hri)
        rw [hli] at hty
        have hRT := Comp2_ty_RT2 hty
        rw [hdD] at hRT
        have hre := (hargs i hi hi').2 hri (by simpa using hRT)
        have hb := Comp2_ty_base hty
        unfold dataP2
        rw [hdD]
        rw [hdD] at hb
        exact (Comp2_el_iff hb.1 hb.2.2.2.1).2 (by simpa using hre)
  obtain ⟨g1, g2⟩ := key C.args.length (Nat.le_refl _)
  refine .con (dataMem_lit hW hD hP ρ' hcT) (dataMem_lit hW hD hP ρ' (HasTy.eqR he)) he hC'
    ⟨redW_self (step_data d _), TyEq.refl _⟩ hpl ⟨redW_self (step_con_none hD hC _ _ hnb), EqTm.refl hcT⟩ ht
    hrs hrs' hreq hsc hsc' hYl hZl (fun i hi hi' hri => g1 i hi hi' (by omega) hri)
    (fun i hi hi' hri => g2 i hi hi' (by omega) hri)

/-- Arguments related to arguments are related to themselves, at their own argument types. -/
theorem args_self {k3 : ℕ} (ρ' : ISub k3 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {X X' : List Tm}
    (hXl : X.length = C.args.length) (hX'l : X'.length = C.args.length)
    (hargs : ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ (P.isub ρ').toList.reverse)) (X.getD i .abort) (X'.getD i .abort)) :
    ∀ i (hi : i < C.args.length),
      RT2 S k3 ((C.argTy d D.params.length i).substList ((X.take i).reverse ++ (P.isub ρ').toList.reverse))
        ((C.argTy d D.params.length i).substList ((X'.take i).reverse ++ (P.isub ρ').toList.reverse)) ∧
      RE2 S k3 ((C.argTy d D.params.length i).substList ((X.take i).reverse ++ (P.isub ρ').toList.reverse))
        (X.getD i .abort) (X.getD i .abort) ∧
      RE2 S k3 ((C.argTy d D.params.length i).substList ((X'.take i).reverse ++ (P.isub ρ').toList.reverse))
        (X'.getD i .abort) (X'.getD i .abort) := by
  have hPρ : HasTy S k3 .one [] (.data d (P.isub ρ')) (.univ D.level) := HasTy.isubS hW hP ρ'
  have hPPρ : RT2 S k3 (.data d (P.isub ρ')) (.data d (P.isub ρ')) := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ'
  intro i hi
  have T := argTy_rt2' hW hD hPρ hPPρ hPPρ hC hi (A := X.take i) (B := X'.take i) (by simp; omega) (by simp; omega)
    (fun l hl => by
      rw [List.take_take, Nat.min_eq_left hl.le, getD_take_lt hl, getD_take_lt hl]
      exact hargs l (by omega))
  have r := hargs i hi
  exact ⟨T, RE2.trans hW T r (RE2.symm hW T r), RE2.conv hW T (RE2.trans hW T (RE2.symm hW T r) r)⟩

/-- Boundary terms at related arguments are related, given the relation of the earlier constructors. -/
theorem bnd_rel {c : ℕ} (ih : ∀ c' < c, CRSt S d D K P c') {C : Ctor} (hC : D.ctors[c]? = some C) :
    ∀ (N : ℕ) (a : Tm), sizeOf a < N → Ctor.simpleB D.ctors d D.params.length c C.args.length C a = true →
    ∀ {k3 : ℕ} (ρ' : ISub k3 K) {ps ps' X X' : List Tm} {rs rs' : List I},
    ps.length = D.params.length → ps'.length = D.params.length →
    X.length = C.args.length → X'.length = C.args.length → List.Forall₂ I.Eq rs rs' →
    (∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ (P.isub ρ').toList.reverse)) (X.getD i .abort) (X'.getD i .abort)) →
    bndRel S k3 d D.params.length C.args.length C D.ctors (P.isub ρ') (P.isub ρ') X X rs a →
    HasTy S k3 .one [] (Ctor.bndAt a ps X rs) (.data d (P.isub ρ')) →
    HasTy S k3 .one [] (Ctor.bndAt a ps' X' rs') (.data d (P.isub ρ')) →
    RE2 S k3 (.data d (P.isub ρ')) (Ctor.bndAt a ps X rs) (Ctor.bndAt a ps' X' rs') := by
  intro N
  induction N with
  | zero => intro a h; omega
  | succ N ihN =>
  intro a hsz hs k3 ρ' ps ps' X X' rs rs' hpl hpl' hXl hX'l hrs hargs hrel ht ht'
  have hPρ : HasTy S k3 .one [] (.data d (P.isub ρ')) (.univ D.level) := HasTy.isubS hW hP ρ'
  have hPl := (dataLit_rel hW hD hP hPP ρ').2.2.2.2.2.1
  have hplen : (P.isub ρ').toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl hPρ⟩ : IsTyK S k3 (.data d (P.isub ρ'))); rwa [dataD_eq hW hD] at this
  cases a
  case var x =>
    simp only [Ctor.simpleB, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨hx, hr⟩ := hs
    rw [bndAt_var rs (show x < X.length by omega), bndAt_var rs' (show x < X'.length by omega)]
    have h := hargs (C.args.length - 1 - x) (by omega)
    rw [argTy_rec_inst hr hPl hplen (by simp; omega)] at h
    rw [hXl, hX'l]; exact h
  case con d' c' ps0 as0 rs0 =>
    simp only [Ctor.simpleB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
    obtain ⟨⟨⟨hdd, hcc⟩, rfl⟩, hm⟩ := hs
    subst d'
    cases hC' : D.ctors[c']? with
    | none => rw [hC'] at hm; cases hm
    | some C' =>
    rw [hC'] at hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨hal, -⟩, hsa⟩ := hm
    simp only [bndRel, hC'] at hrel
    have hasL : as0 = Tm.ofList as0.toList := simpleArgs_isList as0 0 hsa
    have eB : ∀ (qs Y : List Tm) (rY : List I), qs.length = D.params.length → Y.length = C.args.length →
        Ctor.bndAt (.con d c' (Ctor.paramVars D.params.length C.args.length) as0 rs0) qs Y rY =
          .con d c' (Tm.ofList qs) (Tm.ofList (as0.toList.map (Ctor.bndAt · qs Y rY)))
            (rs0.map (·.subst (rsSub rY))) := by
      intro qs Y rY h1 h2
      rw [bndAt_con, bndAt_paramVars rY h1 h2, show Ctor.bndAt as0 qs Y rY =
        Tm.ofList (as0.toList.map (Ctor.bndAt · qs Y rY)) from by conv_lhs => rw [hasL]
                                                                  exact bndAt_ofList _ _ _ _]
    rw [eB ps X rs hpl hXl] at ht ⊢
    rw [eB ps' X' rs' hpl' hX'l] at ht' ⊢
    refine ih c' hcc ρ' hC' ht ht' (forall2_map_subst rs0 hrs) fun i hi => ?_
    have hai : i < as0.toList.length := by omega
    obtain ⟨hsr, hsp⟩ := simpleArgs_get as0 0 hsa i hai
    obtain ⟨hrp, hrr⟩ := bndRelArgs_get as0 0 [] hrel i hai
    simp only [Nat.zero_add, List.append_nil] at hsr hsp hrp hrr
    have eZ : ∀ (qs Y : List Tm) (rY : List I), (as0.toList.map (Ctor.bndAt · qs Y rY)).getD i .abort =
        Ctor.bndAt as0.toList[i] qs Y rY := by
      intro qs Y rY
      rw [getD_eq_get' (by simpa using hai), List.getElem_map]
    cases hri : C'.isRec i
    · obtain ⟨x, hx, hxn, hcr⟩ := hsp hri
      obtain ⟨A0, hA0⟩ := ctor_point hi hri
      have T := hrp x hx hri hxn
      have hpt : ∀ (qs Y : List Tm) (rY : List I) (qs' Y' : List Tm) (rY' : List I), Y.length = C.args.length →
          Y' = Y → ∀ i' (h1 : i' < (as0.toList.map (Ctor.bndAt · qs Y rY)).length)
          (h2 : i' < (as0.toList.map (Ctor.bndAt · qs' Y' rY')).length), C'.isRec i' = false →
          (as0.toList.map (Ctor.bndAt · qs' Y' rY'))[i'] = (as0.toList.map (Ctor.bndAt · qs Y rY))[i'] := by
        intro qs Y rY qs' Y' rY' hYl hYY i' h1 h2 hr'
        subst hYY
        obtain ⟨x', hx', hxn'⟩ := (simpleArgs_get as0 0 hsa i' (by simpa using h1)).2 (by simpa using hr')
        simp only [List.getElem_map, hx']
        rw [bndAt_var rY (by omega), bndAt_var rY' (by omega)]
      have ec := argTy_point_congr hW hD hC' hA0 (args := as0.toList.map (Ctor.bndAt · (P.isub ρ').toList X rs))
        (args' := as0.toList.map (Ctor.bndAt · ps X rs)) (by simp; omega) (by simp; omega)
        (P.isub ρ').toList.reverse (by simp [hplen]) (hpt _ X rs _ X rs hXl rfl)
      have eA : C'.argTy d D.params.length i = A0 := by simp [Ctor.argTy, hA0]
      rw [eA] at T ⊢
      rw [ec, ← List.map_take]
      rw [eZ, eZ, hx, bndAt_var rs (show x < X.length by omega), bndAt_var rs' (show x < X'.length by omega),
        hXl, hX'l]
      exact RE2.conv hW T (hargs _ (by omega))
    · rw [argTy_rec_inst hri hPl hplen (by simp; omega), eZ, eZ]
      have htZ : ∀ {qs Y : List Tm} {rY : List I} {q0 : Tm},
          HasTy S k3 .one [] (.con d c' q0 (Tm.ofList (as0.toList.map (Ctor.bndAt · qs Y rY)))
            (rs0.map (·.subst (rsSub rY)))) (.data d (P.isub ρ')) →
          HasTy S k3 .one [] (Ctor.bndAt as0.toList[i] qs Y rY) (.data d (P.isub ρ')) := by
        intro qs Y rY q0 h
        obtain ⟨htele, -⟩ := con_inv hW hD hC' h hPρ
        have g := HasTele0.get htele (k := i) (a := Ctor.bndAt as0.toList[i] qs Y rY)
          (by rw [toList_ofList, List.getElem?_map, List.getElem?_eq_getElem hai]; rfl) (argTys_get hi)
        rw [argTy_rec_inst hri hPl hplen (by simp [toList_ofList]; omega)] at g
        exact minimal_to_spec g
      exact ihN as0.toList[i] (by have := sizeOf_con_arg (d' := d) (c' := c') (ps0 := Ctor.paramVars
          D.params.length C.args.length) (rs0 := rs0) (List.getElem_mem hai); omega) (hsr hri) ρ' hpl hpl' hXl hX'l
        hrs hargs (hrr hri) (htZ ht) (htZ ht')
  all_goals simp [Ctor.simpleB] at hs

/-- Related arguments, restricted. -/
theorem args_restr {k3 : ℕ} (ρ' : ISub k3 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {X X' : List Tm}
    (hXl : X.length = C.args.length) (hX'l : X'.length = C.args.length)
    (hargs : ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ (P.isub ρ').toList.reverse)) (X.getD i .abort) (X'.getD i .abort))
    {k4 : ℕ} (κ : ISub k4 k3) :
    ∀ i (hi : i < C.args.length), RE2 S k4 ((C.argTy d D.params.length i).substList
      (((X.map (·.isub κ)).take i).reverse ++ (P.isub (ρ'.comp κ)).toList.reverse))
      ((X.map (·.isub κ)).getD i .abort) ((X'.map (·.isub κ)).getD i .abort) := by
  have hPl := (dataLit_rel hW hD hP hPP ρ').2.2.2.2.2.1
  intro i hi
  have := RE2.isub hW (hargs i hi) κ
  rw [argTy_isub (sigClosed_of_wfSig hW) hD hC i X hPl κ, Tm.isub_isub] at this
  rwa [getD_map_isub' (by omega) κ, getD_map_isub' (by omega) κ]

omit hW hD hP hPP in
/-- A boundary term at list parameters, restricted. -/
theorem bndAt_isubL {b q : Tm} {X : List Tm} {rs : List I} (hq : q = Tm.ofList q.toList)
    (hb : b.closedB (q.toList.length + X.length) rs.length = true) (κ : ISub k' k) :
    (Ctor.bndAt b q.toList X rs).isub κ = Ctor.bndAt b (q.isub κ).toList (X.map (·.isub κ)) (rs.map (·.subst κ.τ)) := by
  rw [bndAt_isub hb κ, toList_isub hq κ]

section rel
variable (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1))
include hH hyp

/-- Constructors with related arguments are related at each stage, given the relation of the earlier
constructors. -/
theorem con_at {c : ℕ} (ih : ∀ c' < c, CRSt S d D K P c') {k3 : ℕ} (ρ' : ISub k3 K) {C : Ctor} {q q' : Tm}
    {X X' : List Tm} {rs rs' : List I} (hC : D.ctors[c]? = some C)
    (ht : HasTy S k3 .one [] (.con d c q (Tm.ofList X) rs) (.data d (P.isub ρ')))
    (ht' : HasTy S k3 .one [] (.con d c q' (Tm.ofList X') rs') (.data d (P.isub ρ')))
    (hrs : List.Forall₂ I.Eq rs rs')
    (hargs : ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ (P.isub ρ').toList.reverse)) (X.getD i .abort) (X'.getD i .abort)) :
    DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k3 ρ'.hom
      (.data d (P.isub ρ')) (.con d c q (Tm.ofList X) rs) (.con d c q' (Tm.ofList X') rs') := by
  have hPρ : HasTy S k3 .one [] (.data d (P.isub ρ')) (.univ D.level) := HasTy.isubS hW hP ρ'
  have hPPρ : RT2 S k3 (.data d (P.isub ρ')) (.data d (P.isub ρ')) := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ'
  have hPl := (dataLit_rel hW hD hP hPP ρ').2.2.2.2.2.1
  have hplen : (P.isub ρ').toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl hPρ⟩ : IsTyK S k3 (.data d (P.isub ρ'))); rwa [dataD_eq hW hD] at this
  have CI := con_inv hW hD hC ht hPρ
  have CI' := con_inv hW hD hC ht' hPρ
  have hrsl := CI.2.2.2.1
  have hsc := CI.2.2.2.2.1
  have hXl := CI.2.2.2.2.2.1
  have hcP := CI.2.2.2.2.2.2.1
  have hqL := CI.2.2.2.2.2.2.2.2.1
  have hql := CI.2.2.2.2.2.2.2.2.2
  have hrsl' := CI'.2.2.2.1
  have hsc' := CI'.2.2.2.2.1
  have hX'l := CI'.2.2.2.2.2.1
  have hqL' := CI'.2.2.2.2.2.2.2.2.1
  have hql' := CI'.2.2.2.2.2.2.2.2.2
  have he : EqTm S k3 .one [] (.con d c q (Tm.ofList X) rs) (.con d c q' (Tm.ofList X') rs') (.data d (P.isub ρ')) :=
    con_eqTm hW hD hC hPρ ht ht' hrs fun i hi => (RE2.typed (hargs i hi)).2.2
  have hself := args_self hW hD hP hPP ρ' hC hXl hX'l hargs
  cases hf : firstBnd C.bnd rs with
  | none =>
    have hf' : firstBnd C.bnd rs' = none := by rw [← firstBnd_eq hrs]; exact hf
    refine DR2At_conH_of hW hD hP hPP ρ' hC hXl hX'l ht hf ⟨redW_self (step_con_none hD hC _ _ hf'), EqTm.refl ht'⟩
      he hrsl hrsl' (ieq_of_forall2 hrs).2 hsc hsc' fun i hi hi' => ⟨fun hri => ?_, fun hri _ => ?_⟩
    · have h := hargs i (by omega)
      rw [argTy_rec_inst hri hPl hplen (by simp; omega), getD_eq_get' hi, getD_eq_get' hi'] at h
      exact h
    · have h := hargs i (by omega)
      rwa [getD_eq_get' hi, getD_eq_get' hi'] at h
  | some b =>
    have hf' : firstBnd C.bnd rs' = some b := by rw [← firstBnd_eq hrs]; exact hf
    obtain ⟨kb, ψ, hb, hent⟩ := firstBnd_spec hf
    obtain ⟨-, -, hsimple, -⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 kb ψ b hb
    obtain ⟨kb', ψ', hb', hent'⟩ := firstBnd_spec hf'
    have e1 : EqTm S k3 .one [] (.con d c q (Tm.ofList X) rs) (Ctor.bndAt b q.toList X rs) (.data d (P.isub ρ')) := by
      have := EqTm.conBnd hD hC hb hent hqL (by rw [toList_ofList]) ht
      rwa [toList_ofList] at this
    have e1' : EqTm S k3 .one [] (.con d c q' (Tm.ofList X') rs') (Ctor.bndAt b q'.toList X' rs')
        (.data d (P.isub ρ')) := by
      have := EqTm.conBnd hD hC hb' hent' hqL' (by rw [toList_ofList]) ht'
      rwa [toList_ofList] at this
    have hrel := hyp.bndTy (by omega) hD hH hC hb hent hPρ hPPρ hXl hcP (fun i hi => (hself i hi).2.1)
    have R := bnd_rel hW hD hP hPP ih hC (sizeOf b + 1) b (by omega) hsimple ρ' hql hql' hXl hX'l hrs hargs hrel
      (HasTy.eqR e1) (HasTy.eqR e1')
    have at0 := DR2.at_id hW (Θ := ΘK S D d K P) ((RE2_dataLit_iff hW hD hP ρ').1 R).2
    have s1 : step S (.con d c q (Tm.ofList X) rs) = some (Ctor.bndAt b q.toList X rs) := by
      rw [step_con_some hD hC _ _ hf, toList_ofList]
    have s1' : step S (.con d c q' (Tm.ofList X') rs') = some (Ctor.bndAt b q'.toList X' rs') := by
      rw [step_con_some hD hC _ _ hf', toList_ofList]
    exact DR2At.expandL hW (DR2At.expandR hW at0 (.step s1' (.refl _)) e1') (.step s1 (.refl _)) e1

/-- The coherence of a constructor: its normal form, restricted, is related to its restriction. -/
theorem con_coh0 {c : ℕ} (ih : ∀ c' < c, CRSt S d D K P c') {k3 : ℕ} (ρ' : ISub k3 K) {C : Ctor} {q : Tm}
    {X : List Tm} {rs : List I} (hC : D.ctors[c]? = some C)
    (ht : HasTy S k3 .one [] (.con d c q (Tm.ofList X) rs) (.data d (P.isub ρ')))
    (hargs : ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ (P.isub ρ').toList.reverse)) (X.getD i .abort) (X.getD i .abort))
    {w : Tm} (hw : RedW S (.con d c q (Tm.ofList X) rs) w) {k5 : ℕ} (κ : ISub k5 k3) :
    DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k5
      (ρ'.comp κ).hom (.data d (P.isub (ρ'.comp κ))) (w.isub κ) ((Tm.con d c q (Tm.ofList X) rs).isub κ) := by
  have eP : ∀ {k4 : ℕ} (σ : ISub k4 k3), (Tm.data d (P.isub ρ')).isub σ = .data d (P.isub (ρ'.comp σ)) := by
    intro k4 σ; show Tm.data d ((P.isub ρ').isub σ) = _; rw [Tm.isub_isub]
  have hPρ : HasTy S k3 .one [] (.data d (P.isub ρ')) (.univ D.level) := HasTy.isubS hW hP ρ'
  have hPPρ : RT2 S k3 (.data d (P.isub ρ')) (.data d (P.isub ρ')) := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ'
  have hPκT : HasTy S k5 .one [] (.data d (P.isub (ρ'.comp κ))) (.univ D.level) := HasTy.isubS hW hP (ρ'.comp κ)
  have hPPκ : RT2 S k5 (.data d (P.isub (ρ'.comp κ))) (.data d (P.isub (ρ'.comp κ))) :=
    RT2.isub hW (tyCode_of_univ hW hP) hPP (ρ'.comp κ)
  have hPlκ := (dataLit_rel hW hD hP hPP (ρ'.comp κ)).2.2.2.2.2.1
  have hplenκ : (P.isub (ρ'.comp κ)).toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl hPκT⟩ : IsTyK S k5 (.data d (P.isub (ρ'.comp κ)))); rwa [dataD_eq hW hD] at this
  have CI := con_inv hW hD hC ht hPρ
  have hrsl := CI.2.2.2.1
  have hXl := CI.2.2.2.2.2.1
  have hqL := CI.2.2.2.2.2.2.2.2.1
  have hql := CI.2.2.2.2.2.2.2.2.2
  have htκ := HasTy.isubS hW ht κ
  rw [isub_conT, eP] at htκ
  have CIκ := con_inv hW hD hC htκ hPκT
  have hXκl := CIκ.2.2.2.2.2.1
  have hcPκ := CIκ.2.2.2.2.2.2.1
  have hqLκ := CIκ.2.2.2.2.2.2.2.2.1
  have hqlκ := CIκ.2.2.2.2.2.2.2.2.2
  have argsκ := args_restr hW hD hP hPP ρ' hC hXl hXl hargs κ
  cases hf : firstBnd C.bnd rs with
  | none =>
    obtain rfl := RedW.unique hw (redW_self (step_con_none hD hC _ _ hf))
    rw [isub_conT]
    exact con_at hW hD hP hPP hH hyp ih (ρ'.comp κ) hC htκ htκ (forall2_ieq_refl _) argsκ
  | some b =>
    obtain ⟨kb, ψ, hb, hent⟩ := firstBnd_spec hf
    obtain ⟨hψs, hbc, hsimple, -⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 kb ψ b hb
    have e1 : EqTm S k3 .one [] (.con d c q (Tm.ofList X) rs) (Ctor.bndAt b q.toList X rs) (.data d (P.isub ρ')) := by
      have := EqTm.conBnd hD hC hb hent hqL (by rw [toList_ofList]) ht
      rwa [toList_ofList] at this
    have s1 : step S (.con d c q (Tm.ofList X) rs) = some (Ctor.bndAt b q.toList X rs) := by
      rw [step_con_some hD hC _ _ hf, toList_ofList]
    have hwB := red_redW (.step s1 (.refl _)) hw
    have hrel := hyp.bndTy (by omega) hD hH hC hb hent hPρ hPPρ hXl CI.2.2.2.2.2.2.1 hargs
    have RBB := bnd_rel hW hD hP hPP ih hC (sizeOf b + 1) b (by omega) hsimple ρ' hql hql hXl hXl
      (forall2_ieq_refl _) hargs hrel (HasTy.eqR e1) (HasTy.eqR e1)
    have hBc := closed_of_ty hW (HasTy.eqR e1)
    obtain ⟨-, hdB⟩ := (RE2_dataLit_iff hW hD hP ρ').1 RBB
    have h2 : DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k5
        (ρ'.comp κ).hom (.data d (P.isub (ρ'.comp κ))) (w.isub κ) ((Ctor.bndAt b q.toList X rs).isub κ) := by
      cases hdB with
      | intro _ _ hc _ =>
        have := hc k3 (ISub.id k3) w (by rw [isub_id_of_closed hBc]; exact hwB) k5 κ
        rwa [ISub.id_comp, eP, ← ISub.hom_comp] at this
    have hbc' : b.closedB (q.toList.length + X.length) rs.length = true := by rw [hql, hXl, hrsl]; exact hbc
    rw [bndAt_isubL hqL hbc' κ] at h2
    -- the boundaries at the restriction
    have hsc : ∀ p ∈ C.bnd, p.1.Scoped rs.length := by
      intro p hp
      obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
      obtain ⟨h0, -⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 i p.1 p.2 (by rw [List.getElem?_eq_getElem hi, hpi])
      rw [hrsl]; exact h0
    obtain ⟨b'', hf''⟩ := firstBnd_isSome_subst hf hsc κ.τ
    obtain ⟨kb'', ψ'', hb'', hent''⟩ := firstBnd_spec hf''
    obtain ⟨-, -, hsimple'', -⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 kb'' ψ'' b'' hb''
    have hentκ : I.Entails .one (Ctor.cofAt ψ (rs.map (·.subst κ.τ))) := by
      rw [← cofAt_subst κ.τ (by rw [hrsl]; exact hψs)]; exact ent_one_subst hent κ.τ
    have eqb : ∀ {kb0 : ℕ} {ψ0 : I} {b0 : Tm}, C.bnd[kb0]? = some (ψ0, b0) →
        I.Entails .one (Ctor.cofAt ψ0 (rs.map (·.subst κ.τ))) → ∀ {q0 : Tm}, q0 = Tm.ofList q0.toList →
        HasTy S k5 .one [] (.con d c q0 (Tm.ofList (X.map (·.isub κ))) (rs.map (·.subst κ.τ)))
          (.data d (P.isub (ρ'.comp κ))) →
        EqTm S k5 .one [] (.con d c q0 (Tm.ofList (X.map (·.isub κ))) (rs.map (·.subst κ.τ)))
          (Ctor.bndAt b0 q0.toList (X.map (·.isub κ)) (rs.map (·.subst κ.τ))) (.data d (P.isub (ρ'.comp κ))) := by
      intro kb0 ψ0 b0 hb0 hent0 q0 hq0 h0
      have := EqTm.conBnd hD hC hb0 hent0 hq0 (by rw [toList_ofList]) h0
      rwa [toList_ofList] at this
    have e_qb := eqb hb hentκ hqLκ htκ
    have e_qb'' := eqb hb'' hent'' hqLκ htκ
    have e_Pb := eqb hb hentκ hPlκ hcPκ
    have e_Pb'' := eqb hb'' hent'' hPlκ hcPκ
    have hrelκ := hyp.bndTy (by omega) hD hH hC hb hentκ hPκT hPPκ hXκl hcPκ argsκ
    have hrelκ'' := hyp.bndTy (by omega) hD hH hC hb'' hent'' hPκT hPPκ hXκl hcPκ argsκ
    have R1 := bnd_rel hW hD hP hPP ih hC (sizeOf b + 1) b (by omega) hsimple (ρ'.comp κ) hqlκ hplenκ hXκl hXκl
      (forall2_ieq_refl _) argsκ hrelκ (HasTy.eqR e_qb) (HasTy.eqR e_Pb)
    have R2 := hyp.conBnd (by omega) hD hH hC hb hentκ hPκT hPPκ hXκl hcPκ argsκ
    have R3 := hyp.conBnd (by omega) hD hH hC hb'' hent'' hPκT hPPκ hXκl hcPκ argsκ
    have R4 := bnd_rel hW hD hP hPP ih hC (sizeOf b'' + 1) b'' (by omega) hsimple'' (ρ'.comp κ) hplenκ hqlκ hXκl hXκl
      (forall2_ieq_refl _) argsκ hrelκ'' (HasTy.eqR e_Pb'') (HasTy.eqR e_qb'')
    have R := RE2.trans hW hPPκ R1 (RE2.trans hW hPPκ (RE2.symm hW hPPκ R2) (RE2.trans hW hPPκ R3 R4))
    have at1 := DR2.at_id hW (Θ := ΘK S D d K P) ((RE2_dataLit_iff hW hD hP (ρ'.comp κ)).1 R).2
    have tr := DR2At_trans hW (Hom.id K) (perP_ΘK hW hD hP) h2 at1 (argRelH_litH hW hD hP hPP (ρ'.comp κ))
    have s'' : step S (.con d c (q.isub κ) (Tm.ofList (X.map (·.isub κ))) (rs.map (·.subst κ.τ))) =
        some (Ctor.bndAt b'' (q.isub κ).toList (X.map (·.isub κ)) (rs.map (·.subst κ.τ))) := by
      rw [step_con_some hD hC _ _ hf'', toList_ofList]
    rw [isub_conT]
    exact DR2At.expandR hW tr (.step s'' (.refl _)) e_qb''

/-- Constructors of a literal higher inductive type with related arguments and `I.Eq`-equal interval
arguments are related (with any parameter annotations). -/
theorem con_rel : ∀ c, CRSt S d D K P c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro k3 ρ' C q q' X X' rs rs' hC ht ht' hrs hargs
  have eP : ∀ {k4 : ℕ} (σ : ISub k4 k3), (Tm.data d (P.isub ρ')).isub σ = .data d (P.isub (ρ'.comp σ)) := by
    intro k4 σ; show Tm.data d ((P.isub ρ').isub σ) = _; rw [Tm.isub_isub]
  have hPρ : HasTy S k3 .one [] (.data d (P.isub ρ')) (.univ D.level) := HasTy.isubS hW hP ρ'
  have hXl := (con_inv hW hD hC ht hPρ).2.2.2.2.2.1
  have hX'l := (con_inv hW hD hC ht' hPρ).2.2.2.2.2.1
  have he : EqTm S k3 .one [] (.con d c q (Tm.ofList X) rs) (.con d c q' (Tm.ofList X') rs') (.data d (P.isub ρ')) :=
    con_eqTm hW hD hC hPρ ht ht' hrs fun i hi => (RE2.typed (hargs i hi)).2.2
  have hself := args_self hW hD hP hPP ρ' hC hXl hX'l hargs
  have coh : ∀ {q0 : Tm} {X0 : List Tm} {rs0 : List I},
      HasTy S k3 .one [] (.con d c q0 (Tm.ofList X0) rs0) (.data d (P.isub ρ')) →
      (∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
        ((X0.take i).reverse ++ (P.isub ρ').toList.reverse)) (X0.getD i .abort) (X0.getD i .abort)) →
      ∀ k4 (σ : ISub k4 k3) w, RedW S ((Tm.con d c q0 (Tm.ofList X0) rs0).isub σ) w → ∀ k5 (κ : ISub k5 k4),
      DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k5
        (ρ'.hom.comp (σ.comp κ).hom) ((Tm.data d (P.isub ρ')).isub (σ.comp κ)) (w.isub κ)
        ((Tm.con d c q0 (Tm.ofList X0) rs0).isub (σ.comp κ)) := by
    intro q0 X0 rs0 h0 hX0 k4 σ w hw k5 κ
    have hX0l := (con_inv hW hD hC h0 hPρ).2.2.2.2.2.1
    have h0σ := HasTy.isubS hW h0 σ
    rw [isub_conT, eP] at h0σ
    rw [isub_conT] at hw
    have := con_coh0 hW hD hP hPP hH hyp ih (ρ'.comp σ) hC h0σ (args_restr hW hD hP hPP ρ' hC hX0l hX0l hX0 σ) hw κ
    have e1 : (Tm.con d c q0 (Tm.ofList X0) rs0).isub (σ.comp κ) =
        (Tm.con d c (q0.isub σ) (Tm.ofList (X0.map (·.isub σ))) (rs0.map (·.subst σ.τ))).isub κ := by
      rw [← isub_conT, Tm.isub_isub]
    have e2 : (Tm.data d (P.isub ρ')).isub (σ.comp κ) = Tm.data d (P.isub ((ρ'.comp σ).comp κ)) := by
      rw [eP, ISub.comp_assoc]
    rw [e1, e2, ← ISub.hom_comp, ← ISub.comp_assoc]
    exact this
  refine (RE2_dataLit_iff hW hD hP ρ').2 ⟨⟨ht, ht', he⟩, .intro he (fun k4 κ => ?_)
    (coh ht fun i hi => (hself i hi).2.1) (coh ht' fun i hi => ?_)⟩
  · have htκ := HasTy.isubS hW ht κ
    have ht'κ := HasTy.isubS hW ht' κ
    rw [isub_conT, eP] at htκ ht'κ
    rw [eP, isub_conT, isub_conT, ← ISub.hom_comp]
    exact con_at hW hD hP hPP hH hyp ih (ρ'.comp κ) hC htκ ht'κ (forall2_ieq_map hrs κ.τ)
      (args_restr hW hD hP hPP ρ' hC hXl hX'l hargs κ)
  · exact (hself i hi).2.2


/-- The arguments of a nested constructor of a boundary, at related arguments, are related. -/
theorem nested_args {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {c' : ℕ} {C' : Ctor} {as0 : Tm} {rs0 : List I}
    (hs : Ctor.simpleB D.ctors d D.params.length c C.args.length C
      (.con d c' (Ctor.paramVars D.params.length C.args.length) as0 rs0) = true)
    (hC' : D.ctors[c']? = some C') {k3 : ℕ} (ρ' : ISub k3 K) {ps ps' X X' : List Tm} {rs rs' : List I}
    (hpl : ps.length = D.params.length) (hpl' : ps'.length = D.params.length)
    (hXl : X.length = C.args.length) (hX'l : X'.length = C.args.length) (hrs : List.Forall₂ I.Eq rs rs')
    (hargs : ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ (P.isub ρ').toList.reverse)) (X.getD i .abort) (X'.getD i .abort))
    (hrel : bndRel S k3 d D.params.length C.args.length C D.ctors (P.isub ρ') (P.isub ρ') X X rs
      (.con d c' (Ctor.paramVars D.params.length C.args.length) as0 rs0))
    (ht : HasTy S k3 .one [] (.con d c' (Tm.ofList ps) (Tm.ofList (as0.toList.map (Ctor.bndAt · ps X rs)))
      (rs0.map (·.subst (rsSub rs)))) (.data d (P.isub ρ')))
    (ht' : HasTy S k3 .one [] (.con d c' (Tm.ofList ps') (Tm.ofList (as0.toList.map (Ctor.bndAt · ps' X' rs')))
      (rs0.map (·.subst (rsSub rs')))) (.data d (P.isub ρ'))) :
    ∀ i (hi : i < C'.args.length), RE2 S k3 ((C'.argTy d D.params.length i).substList
      (((as0.toList.map (Ctor.bndAt · ps X rs)).take i).reverse ++ (P.isub ρ').toList.reverse))
      ((as0.toList.map (Ctor.bndAt · ps X rs)).getD i .abort) ((as0.toList.map (Ctor.bndAt · ps' X' rs')).getD i .abort) := by
  have hPρ : HasTy S k3 .one [] (.data d (P.isub ρ')) (.univ D.level) := HasTy.isubS hW hP ρ'
  have hPl := (dataLit_rel hW hD hP hPP ρ').2.2.2.2.2.1
  have hplen : (P.isub ρ').toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl hPρ⟩ : IsTyK S k3 (.data d (P.isub ρ'))); rwa [dataD_eq hW hD] at this
  obtain ⟨-, -, -, C1, hC1, hal, -, hsa, -⟩ := simpleB_con_inv hs
  rw [hC'] at hC1; cases hC1
  simp only [bndRel, hC'] at hrel
  intro i hi
  have hai : i < as0.toList.length := by omega
  obtain ⟨hsr, hsp⟩ := simpleArgs_get as0 0 hsa i hai
  obtain ⟨hrp, hrr⟩ := bndRelArgs_get as0 0 [] hrel i hai
  simp only [Nat.zero_add, List.append_nil] at hsr hsp hrp hrr
  have eZ : ∀ (qs Y : List Tm) (rY : List I), (as0.toList.map (Ctor.bndAt · qs Y rY)).getD i .abort =
      Ctor.bndAt as0.toList[i] qs Y rY := by
    intro qs Y rY
    rw [getD_eq_get' (by simpa using hai), List.getElem_map]
  cases hri : C'.isRec i
  · obtain ⟨x, hx, hxn, hcr⟩ := hsp hri
    obtain ⟨A0, hA0⟩ := ctor_point hi hri
    have T := hrp x hx hri hxn
    have hpt : ∀ (qs Y : List Tm) (rY : List I) (qs' : List Tm) (rY' : List I), Y.length = C.args.length →
        ∀ i' (h1 : i' < (as0.toList.map (Ctor.bndAt · qs Y rY)).length)
        (h2 : i' < (as0.toList.map (Ctor.bndAt · qs' Y rY')).length), C'.isRec i' = false →
        (as0.toList.map (Ctor.bndAt · qs' Y rY'))[i'] = (as0.toList.map (Ctor.bndAt · qs Y rY))[i'] := by
      intro qs Y rY qs' rY' hYl i' h1 h2 hr'
      obtain ⟨x', hx', hxn'⟩ := (simpleArgs_get as0 0 hsa i' (by simpa using h1)).2 (by simpa using hr')
      simp only [List.getElem_map, hx']
      rw [bndAt_var rY (by omega), bndAt_var rY' (by omega)]
    have ec := argTy_point_congr hW hD hC' hA0 (args := as0.toList.map (Ctor.bndAt · (P.isub ρ').toList X rs))
      (args' := as0.toList.map (Ctor.bndAt · ps X rs)) (by simp; omega) (by simp; omega)
      (P.isub ρ').toList.reverse (by simp [hplen]) (hpt _ X rs _ rs hXl)
    have eA : C'.argTy d D.params.length i = A0 := by simp [Ctor.argTy, hA0]
    rw [eA] at T ⊢
    rw [ec, ← List.map_take]
    rw [eZ, eZ, hx, bndAt_var rs (show x < X.length by omega), bndAt_var rs' (show x < X'.length by omega),
      hXl, hX'l]
    exact RE2.conv hW T (hargs _ (by omega))
  · rw [argTy_rec_inst hri hPl hplen (by simp; omega), eZ, eZ]
    have htZ : ∀ {qs Y : List Tm} {rY : List I} {q0 : Tm},
        HasTy S k3 .one [] (.con d c' q0 (Tm.ofList (as0.toList.map (Ctor.bndAt · qs Y rY)))
          (rs0.map (·.subst (rsSub rY)))) (.data d (P.isub ρ')) →
        HasTy S k3 .one [] (Ctor.bndAt as0.toList[i] qs Y rY) (.data d (P.isub ρ')) := by
      intro qs Y rY q0 h
      obtain ⟨htele, -⟩ := con_inv hW hD hC' h hPρ
      have g := HasTele0.get htele (k := i) (a := Ctor.bndAt as0.toList[i] qs Y rY)
        (by rw [toList_ofList, List.getElem?_map, List.getElem?_eq_getElem hai]; rfl) (argTys_get hi)
      rw [argTy_rec_inst hri hPl hplen (by simp [toList_ofList]; omega)] at g
      exact minimal_to_spec g
    exact bnd_rel hW hD hP hPP (fun c'' _ => con_rel hW hD hP hPP hH hyp c'') hC (sizeOf as0.toList[i] + 1) _
      (by omega) (hsr hri) ρ' hpl hpl' hXl hX'l hrs hargs (hrr hri) (htZ ht) (htZ ht')

end rel


end lit

end

end Model.Whnf
