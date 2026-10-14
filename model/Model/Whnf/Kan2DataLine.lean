import Model.Whnf.Kan2DataFace
import Model.Whnf.Kan2DataFillH

/-!
# Argument types of literal inductive types at related prefixes

The argument types of a constructor at related prefixes of arguments and related parameters are
related at the code of the inductive type (`argTy_code_rel`), for any parameter lists related to
those of a literal inductive type `data d P`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

section lit
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
  {K : ℕ} {P : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (hPP : RT2 S K (.data d P) (.data d P))
include hW hD hP

/-- Related elements of a type whose code is a restriction of that of a literal inductive type. -/
theorem RE2_dataT_iff {k3 : ℕ} (g : Hom k3 K) {T x y : Tm}
    (hsem : semK S k3 T = res g (dataC (ΘK S D d K P))) :
    RE2 S k3 T x y ↔ EB S k3 T x y ∧
      DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k3 g T x y := by
  unfold RE2
  rw [hsem, Comp2_res (show dataC (ΘK S D d K P) ≠ ∅ from mkKV_ne_empty _), Hom.comp_id, Comp2_dataC]
  simp only [show (ΘK S D d K P).idx = d from rfl]
  constructor
  · rintro ⟨hE, -, -, hdr⟩
    refine ⟨hE, ?_⟩
    have := DR2.unbase (Θ := ΘK S D d K P) (Hom.id K) (h := g) (g := Hom.id k3)
      (by rw [Hom.id_comp]; exact hdr)
    rwa [Hom.comp_id] at this
  · rintro ⟨hE, hdr⟩
    refine ⟨hE, ?_, hE, ?_⟩
    · have := mem_of_ty hW hE.1
      rwa [hsem] at this
    · have := DR2.rebase (Hom.id K) hdr g (Hom.id k3) (Hom.comp_id _).symm
      rwa [Hom.id_comp] at this

/-- The code of a restriction of a literal inductive type related to `data d P`. -/
theorem semK_dataQ {Q : Tm} (hQ : RT2 S K (.data d P) (.data d Q)) (σ : ISub k' K) :
    semK S k' (.data d (Q.isub σ)) = res σ.hom (dataC (ΘK S D d K P)) := by
  have hQT : IsTyK S K (.data d Q) := (Comp2_ty_base hQ).2.2.1
  rw [show Tm.data d (Q.isub σ) = (Tm.data d Q).isub σ from rfl, semK_isubTy hW hQT σ, RT2.semK_eq hW hQ,
    semK_dataT hW hD hP]

include hH

/-- The argument types at related prefixes of arguments and related parameters are related at the
code of the inductive type. -/
theorem argTy_code_rel {k3 : ℕ} (ρ3 : ISub k3 K) {R R' : Tm}
    (hRR' : argRelH (ΘK S D d K P) (Hom.id K) S k3 ρ3.hom R R')
    (hRsem : semK S k3 (.data d R) = res ρ3.hom (dataC (ΘK S D d K P)))
    (hRc : R.closedB 0 k3 = true) (hR'c : R'.closedB 0 k3 = true)
    {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {A A' : List Tm} (hl' : A'.length = A.length)
    (hrec : ∀ i (hi : i < A.length) (hi' : i < A'.length), C.isRec i = true → RE2 S k3 (.data d R) A[i] A'[i])
    (hpt : ∀ i (hi : i < A.length) (hi' : i < A'.length), C.isRec i = false →
      RE2 S k3 ((C.argTy d D.params.length i).substList ((A.take i).reverse ++ R.toList.reverse)) A[i] A'[i])
    (hr : A.length < C.args.length) (hrr : C.isRec A.length = false) :
    (Comp2 S (tyLook (shapeV ((ΘK S D d K P).restr ((Hom.id K).comp ρ3.hom))) c A.length (A.map (semK S k3)))
      k3 k3 (Hom.id k3)).ty
      ((C.argTy d D.params.length A.length).substList (A.reverse ++ R.toList.reverse))
      ((C.argTy d D.params.length A.length).substList (A'.reverse ++ R'.toList.reverse)) := by
  have hdD := dataD_eq hW hD
  have hC' : (dataD S (ΘK S D d K P).idx).ctors[c]? = some C := by
    show (dataD S d).ctors[c]? = some C; rw [hdD]; exact hC
  -- the relations of the prefix, at the code, by induction along it
  let Good : ℕ → Prop := fun j =>
    (∀ i (hi : i < A.length) (hi' : i < A'.length), i < j → C.isRec i = true →
      DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k3
        ρ3.hom (.data d R) A[i] A'[i]) ∧
    (∀ i (hi : i < A.length) (hi' : i < A'.length), i < j → C.isRec i = false →
      dataP2 S (ΘK S D d K P) (Hom.id K) k3 ρ3.hom c i ((A.take i).map (semK S k3))
        ((C.argTy d (dataD S d).params.length i).substList ((A.take i).reverse ++ R.toList.reverse))
        A[i] A'[i])
  have key : ∀ j, j ≤ A.length → Good j := by
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
        exact ((RE2_dataT_iff hW hD hP ρ3.hom hRsem).1 (hrec i hi hi' hri)).2
      · by_cases hlt : i < j
        · exact g2 i hi hi' hlt hri
        obtain rfl : i = j := by omega
        have hli : (A.take i).length = i := by simp; omega
        have hty := argRelH_id (Hom.id K) hRR' hRc hR'c hC' (args := A.take i) (args' := A'.take i)
          (by rw [hli]; omega) (by simp; omega) (by rw [hli]; exact hri)
          (fun i' h1 h2 hri' => by
            simp only [List.getElem_take]; exact g1 i' (by simp at h1; omega) (by simp at h2; omega)
              (by simp at h1; omega) hri')
          (fun i' h1 h2 hri' => by
            simp only [List.getElem_take, List.take_take]
            rw [Nat.min_eq_left (by simp at h1; omega)]
            exact g2 i' (by simp at h1; omega) (by simp at h2; omega) (by simp at h1; omega) hri')
        rw [hli] at hty
        have hb := Comp2_ty_base hty
        unfold dataP2
        simp only [show (ΘK S D d K P).idx = d from rfl, hdD] at hb ⊢
        exact (Comp2_el_iff hb.1 hb.2.2.2.1).2 (by simpa using hpt i hi hi' hri)
  obtain ⟨g1, g2⟩ := key A.length (Nat.le_refl _)
  have := argRelH_id (Hom.id K) hRR' hRc hR'c hC' (args := A) (args' := A') hr hl' hrr
    (fun i hi hi' hri => g1 i hi hi' hi hri) (fun i hi hi' hri => g2 i hi hi' hi hri)
  simpa only [show (ΘK S D d K P).idx = d from rfl, hdD] using this

omit hH in
/-- Parameters related to those of a literal inductive type are related to each other. -/
theorem argRelH_QQ {Q Q' : Tm} (hQ : RT2 S K (.data d P) (.data d Q)) (hQ' : RT2 S K (.data d P) (.data d Q'))
    (σ : ISub k' K) : argRelH (ΘK S D d K P) (Hom.id K) S k' σ.hom (Q.isub σ) (Q'.isub σ) := by
  obtain ⟨-, rQP, dP, dQ, -, hPl, hQl⟩ := dataLit_rel hW hD hP hQ σ
  obtain ⟨rPQ', -, -, -, -, -, -⟩ := dataLit_rel hW hD hP hQ' σ
  have hQT : IsTyK S k' (.data d (Q.isub σ)) := ((Comp2_ty_base hQ).2.2.1).isub hW σ
  have hPT : IsTyK S k' (.data d (P.isub σ)) := ((Comp2_ty_base hQ).2.1).isub hW σ
  have hQ'T : IsTyK S k' (.data d (Q'.isub σ)) := ((Comp2_ty_base hQ').2.2.1).isub hW σ
  have hdd : TyEq S k' (.data d (Q.isub σ)) (.data d (P.isub σ)) :=
    ((Comp2_ty_base hQ).2.2.2.2.2.isub hW σ).symm
  exact argRelH_comp hW (Hom.id K) (perP_ΘK hW hD hP) rQP dQ dP rPQ' hQT hPT hQ'T hPl hdd

include hH hPP in
/-- The projections of related elements of a literal inductive type, at parameters related to its
own, are related, at the argument types instantiated by the projections. -/
theorem projs_rel {Q Q' : Tm} (hQ : RT2 S K (.data d P) (.data d Q)) (hQ' : RT2 S K (.data d P) (.data d Q'))
    {k3 : ℕ} (ρ3 : ISub k3 K) {x x' : Tm} (hx : RE2 S k3 (.data d (P.isub ρ3)) x x')
    {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {qsZ : Tm} {Z : List Tm}
    (hw : RedW S x (.con d c qsZ (Tm.ofList Z) [])) {j : ℕ} (hj : j < C.args.length) :
    RE2 S k3 ((C.argTy d D.params.length j).substList
        ((((List.range C.args.length).map fun i => proj d D (Q.isub ρ3) c C i x).take j).reverse ++
          (Q.isub ρ3).toList.reverse))
      (proj d D (Q.isub ρ3) c C j x) (proj d D (Q'.isub ρ3) c C j x') ∧
    RE2 S k3 ((C.argTy d D.params.length j).substList
        ((((List.range C.args.length).map fun i => proj d D (Q.isub ρ3) c C i x).take j).reverse ++
          (Q.isub ρ3).toList.reverse))
      (proj d D (Q.isub ρ3) c C j x) (Z.getD j .abort) ∧
    RT2 S k3 ((C.argTy d D.params.length j).substList ((Z.take j).reverse ++ (P.isub ρ3).toList.reverse))
      ((C.argTy d D.params.length j).substList
        ((((List.range C.args.length).map fun i => proj d D (Q.isub ρ3) c C i x).take j).reverse ++
          (Q.isub ρ3).toList.reverse)) := by
  have hdD := dataD_eq hW hD
  have hTP : IsTyK S k3 (.data d (P.isub ρ3)) := ⟨_, .inl (HasTy.isubS hW hP ρ3)⟩
  have lvl : ∀ {R : Tm}, IsTyK S k3 (.data d R) → HasTy S k3 .one [] (.data d R) (.univ D.level) := by
    intro R hR
    obtain ⟨l, hR | hR⟩ := hR
    · obtain ⟨D', hD', hpt⟩ := gen_data_tele (spec_to_minimal hW hR) rfl
      rw [hD] at hD'; cases hD'
      exact minimal_to_spec (HasTy0.data hD (hW.2 d D hD).1 hpt)
    · cases hR
  have hQT : IsTyK S k3 (.data d (Q.isub ρ3)) := ((Comp2_ty_base hQ).2.2.1).isub hW ρ3
  have hQ'T : IsTyK S k3 (.data d (Q'.isub ρ3)) := ((Comp2_ty_base hQ').2.2.1).isub hW ρ3
  have hTQ : TyEq S k3 (.data d (P.isub ρ3)) (.data d (Q.isub ρ3)) := (Comp2_ty_base hQ).2.2.2.2.2.isub hW ρ3
  have hTQ' : TyEq S k3 (.data d (P.isub ρ3)) (.data d (Q'.isub ρ3)) := (Comp2_ty_base hQ').2.2.2.2.2.isub hW ρ3
  have hXP : TyCode K (semK S K (.data d P)) := tyCode_of_univ hW hP
  have hPρ := RT2.isub hW hXP hPP ρ3
  obtain ⟨c0, C0, qs0, Z0, qs0', Z', hC0, hZ0l, hZ'l, ht, ht', hrecZ, hptZ⟩ := dataLit_args hW hD hH hP hPP ρ3 hx
  have e := RedW.unique ht.1 hw
  simp only [Tm.con.injEq] at e
  obtain ⟨-, hc0, -, ea, -⟩ := e
  have hc0' := hc0.symm
  subst hc0'
  have ea' := congrArg Tm.toList ea
  simp only [toList_ofList] at ea'
  subst ea'
  rw [hC] at hC0; cases hC0
  have hxx' := RE2.trans hW hPρ (RE2.symm hW hPρ hx) hx
  have hPl := (dataLit_rel hW hD hP hPP ρ3).2.2.2.2.2.1
  have hplen : (P.isub ρ3).toList.length = D.params.length := by
    have := data_len_of hW hTP; rwa [hdD] at this
  set pr := (List.range C.args.length).map fun i => proj d D (Q.isub ρ3) c C i x with hpr
  have hprl : pr.length = C.args.length := by simp [pr]
  have hprget : ∀ i (hi : i < pr.length), pr[i] = proj d D (Q.isub ρ3) c C i x := by intro i hi; simp [pr]
  -- the projections against the arguments of the normal forms
  have PZ := fun {i : ℕ} (hi : i < C.args.length) => proj_rel hW hD hH hP hPP ρ3 hx hC hw hTQ (lvl hQT) hi
  have PZ' := fun {i : ℕ} (hi : i < C.args.length) => proj_rel hW hD hH hP hPP ρ3 hxx' hC ht'.1 hTQ' (lvl hQ'T) hi
  have hgetZ : ∀ i (hi : i < Z0.length), Z0.getD i .abort = Z0[i] := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have hgetZ' : ∀ i (hi : i < Z'.length), Z'.getD i .abort = Z'[i] := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  -- the argument types along the normal forms
  have ZZ' : ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((Z0.take i).reverse ++ (P.isub ρ3).toList.reverse)) (Z0.getD i .abort) (Z'.getD i .abort) := by
    intro i hi
    rw [hgetZ i (by omega), hgetZ' i (by omega)]
    cases hri : C.isRec i
    · exact hptZ i (by omega) (by omega) hri
    · rw [argTy_rec_inst hri hPl hplen (by simp; omega)]; exact hrecZ i (by omega) (by omega) hri
  have pc := (dataLit_rel hW hD hP hPP ρ3).2.2.1
  have hpc : (P.isub ρ3).closedB 0 k3 = true := by
    have := closed_of_isTyK hW hTP; simpa [Tm.closedB] using this
  have hsemP := semK_dataLit hW hD hP ρ3
  -- the argument types at the arguments of the two normal forms
  have TZZ' : ∀ j (hj : j < C.args.length), RT2 S k3
      ((C.argTy d D.params.length j).substList ((Z0.take j).reverse ++ (P.isub ρ3).toList.reverse))
      ((C.argTy d D.params.length j).substList ((Z'.take j).reverse ++ (P.isub ρ3).toList.reverse)) := by
    intro j hj
    cases hrj : C.isRec j
    · have := argTy_code_rel hW hD hH hP ρ3 pc hsemP hpc hpc hC (A := Z0.take j) (A' := Z'.take j)
        (by simp; omega) (fun i h1 h2 hri => by
          have hij : i < j := by simp at h1; omega
          have := ZZ' i (by omega)
          rw [argTy_rec_inst hri hPl hplen (by simp; omega), hgetZ i (by omega),
            hgetZ' i (by omega)] at this
          simpa using this)
        (fun i h1 h2 hri => by
          have hij : i < j := by simp at h1; omega
          have := ZZ' i (by omega)
          rw [hgetZ i (by omega), hgetZ' i (by omega)] at this
          simpa [List.take_take, Nat.min_eq_left (show i ≤ j by omega)] using this)
        (by simp; omega) (by simp; rw [Nat.min_eq_left (by omega)]; exact hrj)
      have hl : (Z0.take j).length = j := by simp; omega
      rw [hl] at this
      exact Comp2_ty_RT2 this
    · rw [argTy_rec_inst hrj hPl hplen (by simp; omega), argTy_rec_inst hrj hPl hplen (by simp; omega)]
      exact hPρ
  -- the argument types at the arguments and at the projections
  obtain ⟨rPQ, -, -, -, -, -, hQl⟩ := dataLit_rel hW hD hP hQ ρ3
  have hqc : (Q.isub ρ3).closedB 0 k3 = true := by
    have := closed_of_isTyK hW hQT; simpa [Tm.closedB] using this
  have hQlen : (Q.isub ρ3).toList.length = D.params.length := by
    have := data_len_of hW hQT; rwa [hdD] at this
  have TT : ∀ j (hj : j < C.args.length), RT2 S k3
      ((C.argTy d D.params.length j).substList ((Z0.take j).reverse ++ (P.isub ρ3).toList.reverse))
      ((C.argTy d D.params.length j).substList ((pr.take j).reverse ++ (Q.isub ρ3).toList.reverse)) := by
    intro j hj
    cases hrj : C.isRec j
    · have := argTy_code_rel hW hD hH hP ρ3 rPQ hsemP hpc hqc hC (A := Z0.take j) (A' := pr.take j)
        (by simp; omega) (fun i h1 h2 hri => by
          have hij : i < j := by simp at h1; omega
          have := (PZ (i := i) (by omega))
          rw [argTy_rec_inst hri hPl hplen (by simp; omega)] at this
          simp only [List.getElem_take]
          rw [hprget i (by omega), ← hgetZ i (by omega)]
          exact RE2.symm hW hPρ this)
        (fun i h1 h2 hri => by
          have hij : i < j := by simp at h1; omega
          have := (PZ (i := i) (by omega))
          simp only [List.getElem_take, List.take_take, Nat.min_eq_left (show i ≤ j by omega)]
          rw [hprget i (by omega), ← hgetZ i (by omega)]
          exact RE2.symm hW (RT2.refl hW (RE2.tyCode hW this) (TZZ' i (by omega))) this)
        (by simp; omega) (by simp; rw [Nat.min_eq_left (by omega)]; exact hrj)
      have hl : (Z0.take j).length = j := by simp; omega
      rw [hl] at this
      exact Comp2_ty_RT2 this
    · rw [argTy_rec_inst hrj hPl hplen (by simp; omega), argTy_rec_inst hrj hQl hQlen (by simp; omega)]
      exact RT2.isub hW hXP hQ ρ3
  have hXZ : TyCode k3 (semK S k3 ((C.argTy d D.params.length j).substList
      ((Z0.take j).reverse ++ (P.isub ρ3).toList.reverse))) := RE2.tyCode hW (PZ hj)
  have hZZ := RT2.refl hW hXZ (TT j hj)
  have a1 := PZ hj
  have a2 := ZZ' j hj
  have a3 := RE2.conv' hW (TZZ' j hj) (RE2.symm hW (RT2.refl' hW hXZ (TZZ' j hj)) (PZ' hj)) hXZ
  rw [show proj d D (Q'.isub ρ3) c C j x' = proj d D (Q'.isub ρ3) c C j x' from rfl] at a3
  exact ⟨RE2.conv hW (TT j hj) (RE2.trans hW hZZ a1 (RE2.trans hW hZZ a2 a3)), RE2.conv hW (TT j hj) a1, TT j hj⟩

include hH hPP in
/-- The argument types at componentwise related prefixes and parameters related to those of a
literal inductive type are related. -/
theorem argTy_rt2 {Q1 Q2 : Tm} (hQ1 : RT2 S K (.data d P) (.data d Q1)) (hQ2 : RT2 S K (.data d P) (.data d Q2))
    {k3 : ℕ} (ρ3 : ISub k3 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {j : ℕ} (hj : j < C.args.length)
    {A B : List Tm} (hAl : A.length = j) (hBl : B.length = j)
    (hrel : ∀ i (hi : i < j), (C.isRec i = true → RE2 S k3 (.data d (Q1.isub ρ3)) (A.getD i .abort) (B.getD i .abort)) ∧
      (C.isRec i = false → RE2 S k3 ((C.argTy d D.params.length i).substList ((A.take i).reverse ++
        (Q1.isub ρ3).toList.reverse)) (A.getD i .abort) (B.getD i .abort))) :
    RT2 S k3 ((C.argTy d D.params.length j).substList (A.reverse ++ (Q1.isub ρ3).toList.reverse))
      ((C.argTy d D.params.length j).substList (B.reverse ++ (Q2.isub ρ3).toList.reverse)) := by
  have hdD := dataD_eq hW hD
  have hQ1T : IsTyK S k3 (.data d (Q1.isub ρ3)) := ((Comp2_ty_base hQ1).2.2.1).isub hW ρ3
  have hQ2T : IsTyK S k3 (.data d (Q2.isub ρ3)) := ((Comp2_ty_base hQ2).2.2.1).isub hW ρ3
  have hXP : TyCode K (semK S K (.data d P)) := tyCode_of_univ hW hP
  have hgetA : ∀ i (hi : i < A.length), A.getD i .abort = A[i] := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have hgetB : ∀ i (hi : i < B.length), B.getD i .abort = B[i] := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  cases hrj : C.isRec j
  · have hc1 : (Q1.isub ρ3).closedB 0 k3 = true := by
      have := closed_of_isTyK hW hQ1T; simpa [Tm.closedB] using this
    have hc2 : (Q2.isub ρ3).closedB 0 k3 = true := by
      have := closed_of_isTyK hW hQ2T; simpa [Tm.closedB] using this
    have := argTy_code_rel hW hD hH hP ρ3 (argRelH_QQ hW hD hP hQ1 hQ2 ρ3) (semK_dataQ hW hD hP hQ1 ρ3) hc1 hc2 hC
      (A := A) (A' := B) (by omega)
      (fun i hi hi' hri => by rw [← hgetA i hi, ← hgetB i hi']; exact (hrel i (by omega)).1 hri)
      (fun i hi hi' hri => by rw [← hgetA i hi, ← hgetB i hi']; exact (hrel i (by omega)).2 hri)
      (by omega) (by rw [hAl]; exact hrj)
    rw [hAl] at this
    exact Comp2_ty_RT2 this
  · have hl1 := (dataLit_rel hW hD hP hQ1 ρ3).2.2.2.2.2.2
    have hl2 := (dataLit_rel hW hD hP hQ2 ρ3).2.2.2.2.2.2
    have hlen1 : (Q1.isub ρ3).toList.length = D.params.length := by
      have := data_len_of hW hQ1T; rwa [hdD] at this
    have hlen2 : (Q2.isub ρ3).toList.length = D.params.length := by
      have := data_len_of hW hQ2T; rwa [hdD] at this
    rw [argTy_rec_inst hrj hl1 hlen1 (by simp; omega), argTy_rec_inst hrj hl2 hlen2 (by simp; omega)]
    have h1 := RT2.isub hW hXP hQ1 ρ3
    have h2 := RT2.isub hW hXP hQ2 ρ3
    exact RT2.trans hW (RT2.tyCode_r hW h1 (hXP.res _ |> fun h => by
      rw [semK_isubTy hW (Comp2_ty_base hQ1).2.1 ρ3]; exact h)) (RT2.symm hW (by
      rw [semK_isubTy hW (Comp2_ty_base hQ1).2.1 ρ3]; exact hXP.res _) h1) h2

include hH hPP in
/-- The normal forms of related elements of a literal inductive type, with their arguments related at
the argument types. -/
theorem dataLit_argsU {k3 : ℕ} (ρ3 : ISub k3 K) {x x' : Tm} (hx : RE2 S k3 (.data d (P.isub ρ3)) x x') :
    ∃ c C qs Z qs' Z', D.ctors[c]? = some C ∧ Z.length = C.args.length ∧ Z'.length = C.args.length ∧
      RedE S k3 (.data d (P.isub ρ3)) x (.con d c qs (Tm.ofList Z) []) ∧
      RedE S k3 (.data d (P.isub ρ3)) x' (.con d c qs' (Tm.ofList Z') []) ∧
      ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
        ((Z.take i).reverse ++ (P.isub ρ3).toList.reverse)) (Z.getD i .abort) (Z'.getD i .abort) := by
  have hdD := dataD_eq hW hD
  have hTP : IsTyK S k3 (.data d (P.isub ρ3)) := ⟨_, .inl (HasTy.isubS hW hP ρ3)⟩
  have hPl := (dataLit_rel hW hD hP hPP ρ3).2.2.2.2.2.1
  have hplen : (P.isub ρ3).toList.length = D.params.length := by
    have := data_len_of hW hTP; rwa [hdD] at this
  obtain ⟨c, C, qs, Z, qs', Z', hC, hZl, hZ'l, ht, ht', hrecZ, hptZ⟩ := dataLit_args hW hD hH hP hPP ρ3 hx
  refine ⟨c, C, qs, Z, qs', Z', hC, hZl, hZ'l, ht, ht', fun i hi => ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some]
  cases hri : C.isRec i
  · exact hptZ i (by omega) (by omega) hri
  · rw [argTy_rec_inst hri hPl hplen (by simp; omega)]; exact hrecZ i (by omega) (by omega) hri

end lit

end

end Model.Whnf
