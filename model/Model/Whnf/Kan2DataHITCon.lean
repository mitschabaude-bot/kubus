import Model.Whnf.Kan2DataHITRel
import Model.Whnf.Near

/-!
# Constructors of higher inductive types: syntax and typing

Reduction of constructors at their boundaries, the boundary terms at parameters, arguments and
interval arguments (`Ctor.bndAt`) and their restrictions, and the retyping of constructors to the
parameters of their type.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- `I.Eq`-equal interval arguments, from their pointwise statement. -/
theorem forall2_ieq {rs rs' : List I} (hl : rs.length = rs'.length)
    (h : ∀ (i : ℕ) (r r' : I), rs[i]? = some r → rs'[i]? = some r' → I.Eq r r') : List.Forall₂ I.Eq rs rs' := by
  induction rs generalizing rs' with
  | nil => cases rs' with
    | nil => exact .nil
    | cons _ _ => simp at hl
  | cons r rs ih => cases rs' with
    | nil => simp at hl
    | cons r' rs' =>
      exact .cons (h 0 r r' rfl rfl) (ih (by simpa using hl) fun i x x' hx hx' => h (i + 1) x x' hx hx')

theorem ieq_of_forall2 {rs rs' : List I} (h : List.Forall₂ I.Eq rs rs') :
    rs.length = rs'.length ∧ ∀ (i : ℕ) (r r' : I), rs[i]? = some r → rs'[i]? = some r' → I.Eq r r' := by
  induction h with
  | nil => exact ⟨rfl, fun i r r' h _ => by simp at h⟩
  | cons h1 _ ih =>
    refine ⟨by simp [ih.1], fun i r r' hr hr' => ?_⟩
    cases i with
    | zero => simp at hr hr'; subst hr hr'; exact h1
    | succ i => exact ih.2 i r r' (by simpa using hr) (by simpa using hr')

/-- The interval substitution of the interval arguments. -/
abbrev rsSub (rs : List I) : ℕ → I := fun i => rs.reverse.getD i (.var i)

theorem rsSub_ieq {rs rs' : List I} (h : List.Forall₂ I.Eq rs rs') (i : ℕ) : I.Eq (rsSub rs i) (rsSub rs' i) :=
  ieqL_getD (ieqL_reverse h) _ i

/-- The interval arguments of a nested constructor, at related interval arguments. -/
theorem forall2_map_subst (rs0 : List I) {rs rs' : List I} (h : List.Forall₂ I.Eq rs rs') :
    List.Forall₂ I.Eq (rs0.map (·.subst (rsSub rs))) (rs0.map (·.subst (rsSub rs'))) := by
  induction rs0 with
  | nil => exact .nil
  | cons r rs0 ih => exact .cons (I_eq_subst_congr (rsSub_ieq h) r) ih

theorem forall2_ieq_map {rs rs' : List I} (h : List.Forall₂ I.Eq rs rs') (τ : ℕ → I) :
    List.Forall₂ I.Eq (rs.map (·.subst τ)) (rs'.map (·.subst τ)) := by
  induction h with
  | nil => exact .nil
  | cons h1 _ ih => exact .cons (I_eq_subst h1 τ) ih

theorem forall2_ieq_refl (rs : List I) : List.Forall₂ I.Eq rs rs := by
  induction rs with
  | nil => exact .nil
  | cons r rs ih => exact .cons (I_eq_refl r) ih

theorem forall2_ieq_symm {rs rs' : List I} (h : List.Forall₂ I.Eq rs rs') : List.Forall₂ I.Eq rs' rs := by
  induction h with
  | nil => exact .nil
  | cons h1 _ ih => exact .cons (I_eq_symm h1) ih

/-- The first boundary that holds is not affected by `I.Eq`-equal interval arguments. -/
theorem firstBnd_eq {bnd : List (I × Tm)} {rs rs' : List I} (h : List.Forall₂ I.Eq rs rs') :
    firstBnd bnd rs = firstBnd bnd rs' := firstBnd_near bnd h

theorem firstBnd_none {bnd : List (I × Tm)} {rs : List I} (h : firstBnd bnd rs = none) {kb : ℕ} {ψ : I} {b : Tm}
    (hb : bnd[kb]? = some (ψ, b)) : ¬ I.Entails .one (Ctor.cofAt ψ rs) := by
  intro hent
  unfold firstBnd at h
  split at h
  · cases h
  · rename_i hn
    have hm : (ψ, b) ∈ bnd := List.mem_of_getElem? hb
    have := List.find?_eq_none.1 hn (ψ, b) hm
    exact this (by simpa using hent)

/-- Boundaries that hold keep holding at restrictions. -/
theorem firstBnd_isSome_subst {bnd : List (I × Tm)} {rs : List I} {b : Tm} (h : firstBnd bnd rs = some b)
    (hsc : ∀ p ∈ bnd, p.1.Scoped rs.length) (τ : ℕ → I) :
    ∃ b', firstBnd bnd (rs.map (·.subst τ)) = some b' := by
  obtain ⟨kb, ψ, hb, hent⟩ := firstBnd_spec h
  cases hf : firstBnd bnd (rs.map (·.subst τ)) with
  | some b' => exact ⟨b', rfl⟩
  | none =>
    exfalso
    have hψ := hsc (ψ, b) (List.mem_of_getElem? hb)
    refine firstBnd_none hf hb ?_
    rw [← cofAt_subst τ hψ]
    exact ent_one_subst hent τ

section red
variable {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hD

/-- A constructor where no boundary holds is a weak-head normal form. -/
theorem step_con_none {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) (ps args : Tm) {rs : List I}
    (h : firstBnd C.bnd rs = none) : step S (.con d c ps args rs) = none := by
  simp [step, hD, hC, h]

/-- A constructor where a boundary holds reduces to the first such boundary. -/
theorem step_con_some {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) (ps args : Tm) {rs : List I} {b : Tm}
    (h : firstBnd C.bnd rs = some b) :
    step S (.con d c ps args rs) = some (Ctor.bndAt b ps.toList args.toList rs) := by
  simp [step, hD, hC, h]

end red

/-! ### Boundary terms -/

theorem bndAt_var {x : ℕ} {ps args : List Tm} (rs : List I) (hx : x < args.length) :
    Ctor.bndAt (.var x) ps args rs = args.getD (args.length - 1 - x) .abort := by
  simp only [Ctor.bndAt, Tm.subst, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_reverse hx,
    List.getElem?_eq_getElem (by omega)]
  simp

theorem bndAt_con (d' c' : ℕ) (ps0 as0 : Tm) (rs0 : List I) (ps args : List Tm) (rs : List I) :
    Ctor.bndAt (.con d' c' ps0 as0 rs0) ps args rs =
      .con d' c' (Ctor.bndAt ps0 ps args rs) (Ctor.bndAt as0 ps args rs) (rs0.map (·.subst (rsSub rs))) := by
  simp only [Ctor.bndAt, Tm.subst]

theorem bndAt_tcons (a as0 : Tm) (ps args : List Tm) (rs : List I) :
    Ctor.bndAt (.tcons a as0) ps args rs = .tcons (Ctor.bndAt a ps args rs) (Ctor.bndAt as0 ps args rs) := by
  simp only [Ctor.bndAt, Tm.subst]

theorem bndAt_ofList (L : List Tm) (ps args : List Tm) (rs : List I) :
    Ctor.bndAt (Tm.ofList L) ps args rs = Tm.ofList (L.map fun a => Ctor.bndAt a ps args rs) := by
  induction L with
  | nil => simp [Tm.ofList, Ctor.bndAt, Tm.subst]
  | cons a L ih => simp only [Tm.ofList, List.map_cons]; rw [bndAt_tcons, ih]

theorem bndAt_paramVars {ps args : List Tm} (rs : List I) {np n : ℕ} (hp : ps.length = np) (hn : args.length = n) :
    Ctor.bndAt (Ctor.paramVars np n) ps args rs = Tm.ofList ps := by
  subst hp hn
  rw [Ctor.paramVars, bndAt_ofList, List.map_map]
  congr 1
  apply List.ext_getElem (by simp)
  intro p h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, Ctor.bndAt, Tm.subst,
    List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega), List.getElem?_reverse (by simp; omega)]
  simp only [List.length_reverse]
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  congr 1; omega

/-- A boundary term, restricted. -/
theorem bndAt_isub {b : Tm} {ps args : List Tm} {rs : List I}
    (hb : b.closedB (ps.length + args.length) rs.length = true) (σ : ISub k' k) :
    (Ctor.bndAt b ps args rs).isub σ =
      Ctor.bndAt b (ps.map (·.isub σ)) (args.map (·.isub σ)) (rs.map (·.subst σ.τ)) :=
  bndAt_subst _ _ hb

/-! ### Typing of constructors -/

section typing
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hW hD

/-- Inverting the typing of a constructor at a literal inductive type, and retyping it to the
parameters of the type. -/
theorem con_inv {P1 q : Tm} {c : ℕ} {C : Ctor} {X : List Tm} {rs : List I} (hC : D.ctors[c]? = some C)
    (h : HasTy S k .one [] (.con d c q (Tm.ofList X) rs) (.data d P1))
    (hP1 : HasTy S k .one [] (.data d P1) (.univ D.level)) :
    HasTele0 S k .one [] (Tm.ofList X) (C.argTys d D.params.length) P1.toList.reverse ∧
    HasTele0 S k .one [] P1 D.params [] ∧ IsList P1 ∧
    rs.length = C.dims ∧ (∀ r ∈ rs, r.Scoped k) ∧ X.length = C.args.length ∧
    HasTy S k .one [] (.con d c P1 (Tm.ofList X) rs) (.data d P1) ∧
    EqTm S k .one [] (.con d c q (Tm.ofList X) rs) (.con d c P1 (Tm.ofList X) rs) (.data d P1) ∧
    q = Tm.ofList q.toList ∧ q.toList.length = D.params.length := by
  have hcon := spec_to_minimal hW h
  obtain ⟨⟨-, D0, C0, hD0, hC0, hqL, -, hqt0, -, -, hsc⟩, -⟩ := gen_conF hcon rfl
  rw [hD] at hD0; cases hD0; rw [hC] at hC0; cases hC0
  obtain ⟨D', C', hD', hC', hpL, -, htele, hrs, m, eq0⟩ := con_args hW hcon (spec_to_minimal hW hP1)
  rw [hD] at hD'; cases hD'; rw [hC] at hC'; cases hC'
  have hXl : X.length = C.args.length := by
    have := Meta.tele_length htele; rwa [toList_ofList, argTys_length] at this
  obtain ⟨hT, hCt⟩ := wf_typed _ S rfl hW
  obtain ⟨hq, -, -⟩ := pre_eq (sigClosed_of_wfSig hW) hT hCt eq0
  obtain ⟨D1, hD1, hqt⟩ := gen_data_tele hq rfl
  rw [hD] at hD1; cases hD1
  obtain ⟨D2, hD2, hpt⟩ := gen_data_tele (spec_to_minimal hW hP1) rfl
  rw [hD] at hD2; cases hD2
  have eps : EqTele0 S k .one [] P1 q D.params [] := EqTele0.dataInj hD hpt hqt (EqTm0.symm eq0)
  have hc0 : HasTy0 S k .one [] (.con d c P1 (Tm.ofList X) rs) (.data d P1) :=
    HasTy0.con hD hC (tele_isList hpt) (spec_to_minimal hW hP1) hpt htele hrs hsc
  have ec := EqTm0.con hD hC hc0 hcon eps (EqTele0.refl htele) rfl (fun i r r' h1 h2 => by
    rw [h1] at h2; cases h2; exact I_eq_refl _)
  exact ⟨htele, hpt, hpL, hrs, hsc, hXl, minimal_to_spec hc0, minimal_to_spec_eq (EqTm0.symm ec), hqL,
    by simpa using Meta.tele_length hqt0⟩

/-- Constructors with judgmentally equal arguments and `I.Eq`-equal interval arguments are judgmentally
equal. -/
theorem con_eqTm {P1 q q' : Tm} {c : ℕ} {C : Ctor} {X X' : List Tm} {rs rs' : List I} (hC : D.ctors[c]? = some C)
    (hP1 : HasTy S k .one [] (.data d P1) (.univ D.level))
    (h : HasTy S k .one [] (.con d c q (Tm.ofList X) rs) (.data d P1))
    (h' : HasTy S k .one [] (.con d c q' (Tm.ofList X') rs') (.data d P1))
    (hrs : List.Forall₂ I.Eq rs rs')
    (hargs : ∀ i (hi : i < C.args.length), EqTm S k .one [] (X.getD i .abort) (X'.getD i .abort)
      ((C.argTy d D.params.length i).substList ((X.take i).reverse ++ P1.toList.reverse))) :
    EqTm S k .one [] (.con d c q (Tm.ofList X) rs) (.con d c q' (Tm.ofList X') rs') (.data d P1) := by
  obtain ⟨htele, hpt, -, -, -, hXl, hc1, e1, -⟩ := con_inv hW hD hC h hP1
  obtain ⟨-, -, -, -, -, hX'l, hc1', e1', -⟩ := con_inv hW hD hC h' hP1
  have hw := wf_of_ty (spec_to_minimal hW hP1)
  have eX : EqTele0 S k .one [] (Tm.ofList X) (Tm.ofList X') (C.argTys d D.params.length) P1.toList.reverse := by
    refine EqTele0.ofList_of' hw X X' _ _ (by simp [argTys_length, hXl]) (by simp [argTys_length, hX'l])
      fun i a a' A ha ha' hA => ?_
    have hi : i < C.args.length := by
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 ha; omega
    have eA : A = C.argTy d D.params.length i := by
      simp [Ctor.argTys, List.getElem?_map, List.getElem?_range hi] at hA; exact hA.symm
    subst eA
    have := spec_to_minimal_eq hW (hargs i hi)
    rw [List.getD_eq_getElem?_getD, ha, List.getD_eq_getElem?_getD, ha'] at this
    exact this
  have ec := EqTm0.con hD hC (spec_to_minimal hW hc1) (spec_to_minimal hW hc1') (EqTele0.refl hpt) eX
    (ieq_of_forall2 hrs).1 (ieq_of_forall2 hrs).2
  exact e1.trans ((minimal_to_spec_eq ec).trans e1'.symm)

end typing

/-! ### Simple boundaries, along the arguments of nested constructors -/

theorem sizeOf_toList_lt : ∀ (t x : Tm), x ∈ t.toList → sizeOf x < sizeOf t
  | .tcons a as, x, h => by
    simp only [Tm.toList, List.mem_cons] at h
    rcases h with rfl | h
    · simp; omega
    · have := sizeOf_toList_lt as x h; simp; omega
  | .var _, _, h | .const _, _, h | .univ _, _, h | .pi _ _, _, h | .lam _ _, _, h | .app _ _, _, h
  | .sigma _ _, _, h | .pair _ _, _, h | .fst _, _, h | .snd _, _, h | .path _ _ _, _, h | .plam _, _, h
  | .papp _ _, _, h | .ipi _, _, h | .split _ _ _ _, _, h | .abort, _, h | .transp _ _ _, _, h
  | .hcomp _ _ _ _, _, h | .glue _ _ _ _, _, h | .glueEl _ _ _ _, _, h | .unglue _ _ _, _, h
  | .tnil, _, h | .data _ _, _, h | .con _ _ _ _ _, _, h | .elim _ _ _ _ _, _, h => by simp [Tm.toList] at h

theorem sizeOf_con_arg {d' c' : ℕ} {ps0 as0 : Tm} {rs0 : List I} {x : Tm} (h : x ∈ as0.toList) :
    sizeOf x < sizeOf (Tm.con d' c' ps0 as0 rs0) := by
  have := sizeOf_toList_lt as0 x h; simp; omega

/-- The arguments of a nested constructor of a simple boundary. -/
theorem simpleArgs_get {ctors : List Ctor} {d np c n : ℕ} {C C' : Ctor} :
    ∀ (as : Tm) (k : ℕ), Ctor.simpleArgs ctors d np c n C C' k as = true → ∀ j (hj : j < as.toList.length),
      (C'.isRec (k + j) = true → Ctor.simpleB ctors d np c n C as.toList[j] = true) ∧
      (C'.isRec (k + j) = false → ∃ x, as.toList[j] = .var x ∧ x < n ∧ C.isRec (n - 1 - x) = false)
  | .tcons a as, k, h, j, hj => by
    simp only [Ctor.simpleArgs, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases j with
    | zero =>
      simp only [Tm.toList, List.getElem_cons_zero, Nat.add_zero]
      refine ⟨fun hr => by rw [hr] at h1; simpa using h1, fun hr => ?_⟩
      rw [hr] at h1
      simp only [Bool.false_eq_true, ↓reduceIte] at h1
      split at h1
      · rename_i x
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
        exact ⟨x, rfl, h1.1, h1.2⟩
      · cases h1
    | succ j =>
      simp only [Tm.toList, List.getElem_cons_succ]
      have := simpleArgs_get as (k + 1) h2 j (by simp [Tm.toList] at hj; omega)
      rw [show k + 1 + j = k + (j + 1) by omega] at this
      exact this
  | .tnil, _, _, j, hj => by simp [Tm.toList] at hj
  | .var _, _, h, _, _ | .const _, _, h, _, _ | .univ _, _, h, _, _ | .pi _ _, _, h, _, _ | .lam _ _, _, h, _, _
  | .app _ _, _, h, _, _ | .sigma _ _, _, h, _, _ | .pair _ _, _, h, _, _ | .fst _, _, h, _, _
  | .snd _, _, h, _, _ | .path _ _ _, _, h, _, _ | .plam _, _, h, _, _ | .papp _ _, _, h, _, _
  | .ipi _, _, h, _, _ | .split _ _ _ _, _, h, _, _ | .abort, _, h, _, _ | .transp _ _ _, _, h, _, _
  | .hcomp _ _ _ _, _, h, _, _ | .glue _ _ _ _, _, h, _, _ | .glueEl _ _ _ _, _, h, _, _
  | .unglue _ _ _, _, h, _, _ | .data _ _, _, h, _, _ | .con _ _ _ _ _, _, h, _, _
  | .elim _ _ _ _ _, _, h, _, _ => by simp [Ctor.simpleArgs] at h

/-- The relations of the argument types of a nested constructor, along its arguments. -/
theorem bndRelArgs_get {S : Sig} {k d np n : ℕ} {C : Ctor} {ctors : List Ctor} {P1 Q1 : Tm} {Y Y' : List Tm}
    {rs : List I} {C' : Ctor} :
    ∀ (as : Tm) (j : ℕ) (prev : List Tm), bndRelArgs S k d np n C ctors P1 Q1 Y Y' rs C' j prev as →
      ∀ i (hi : i < as.toList.length),
      (∀ x, as.toList[i] = .var x → C'.isRec (j + i) = false → x < n →
        RT2 S k ((C.argTy d np (n - 1 - x)).substList ((Y.take (n - 1 - x)).reverse ++ P1.toList.reverse))
          ((C'.argTy d np (j + i)).substList
            (((as.toList.take i).map (Ctor.bndAt · Q1.toList Y' rs)).reverse ++ prev ++ Q1.toList.reverse))) ∧
      (C'.isRec (j + i) = true → bndRel S k d np n C ctors P1 Q1 Y Y' rs as.toList[i])
  | .tcons a as, j, prev, h, i, hi => by
    simp only [bndRelArgs] at h
    obtain ⟨h1, h2, h3⟩ := h
    cases i with
    | zero =>
      simp only [Tm.toList, List.getElem_cons_zero, Nat.add_zero, List.take_zero, List.map_nil,
        List.reverse_nil, List.nil_append]
      exact ⟨h1, h2⟩
    | succ i =>
      have := bndRelArgs_get as (j + 1) _ h3 i (by simp [Tm.toList] at hi; omega)
      simp only [Tm.toList, List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.reverse_cons,
        List.append_assoc, List.singleton_append]
      rw [show j + (i + 1) = j + 1 + i by omega]
      simpa only [List.append_assoc, List.cons_append] using this
  | .tnil, _, _, _, i, hi => by simp [Tm.toList] at hi
  | .var _, _, _, _, i, hi | .const _, _, _, _, i, hi | .univ _, _, _, _, i, hi | .pi _ _, _, _, _, i, hi
  | .lam _ _, _, _, _, i, hi | .app _ _, _, _, _, i, hi | .sigma _ _, _, _, _, i, hi
  | .pair _ _, _, _, _, i, hi | .fst _, _, _, _, i, hi | .snd _, _, _, _, i, hi
  | .path _ _ _, _, _, _, i, hi | .plam _, _, _, _, i, hi | .papp _ _, _, _, _, i, hi | .ipi _, _, _, _, i, hi
  | .split _ _ _ _, _, _, _, i, hi | .abort, _, _, _, i, hi | .transp _ _ _, _, _, _, i, hi
  | .hcomp _ _ _ _, _, _, _, i, hi | .glue _ _ _ _, _, _, _, i, hi | .glueEl _ _ _ _, _, _, _, i, hi
  | .unglue _ _ _, _, _, _, i, hi | .data _ _, _, _, _, i, hi | .con _ _ _ _ _, _, _, _, i, hi
  | .elim _ _ _ _ _, _, _, _, i, hi => by simp [Tm.toList] at hi

end

end Model.Whnf
