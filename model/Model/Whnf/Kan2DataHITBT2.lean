import Model.Whnf.Kan2DataHITBT1

/-!
# Transport of boundary terms: the data of a nested constructor

`BTa c C a`: transport of the instances of a subterm `a` of a boundary of constructor `c` along any line
(at self-related data `TC`) is related to the instance at the transported arguments. Given it for the
recursive arguments of a nested constructor `c'` of the boundary, the transport of `c'` (at the instances
of its arguments) has the data `TC` (`TC.mkNested`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- Transport of the instances of a subterm `a` of a boundary of constructor `c`. -/
def BTa (S : Sig) (d : ℕ) (D : DataDecl) (c : ℕ) (C : Ctor) (a : Tm) : Prop :=
  ∀ {k : ℕ} {PL : Tm} {φ : I} {q : Tm} {X : List Tm} {rs : List I},
    TC S k d D PL PL φ φ c C q q X X rs rs → BI S d D c C rs a →
    HasTy S k .one [] (.transp (.data d PL) φ (Ctor.bndAt a q.toList X rs)) (.data d (PL.dinst .one)) →
    RE2 S k (.data d (PL.dinst .one)) (.transp (.data d PL) φ (Ctor.bndAt a q.toList X rs))
      (Ctor.bndAt a (PL.dinst .one).toList (tOuts d D C PL φ X) rs)

/-- A line constant on a face, at a related line and an equivalent face. -/
theorem LineConst.transfer (hW : WfSig S) {A A' : Tm} {φ φ' : I} {l l' : ℕ}
    (hA : HasTy S (k + 1) .one [] A (.univ l)) (hA' : HasTy S (k + 1) .one [] A' (.univ l'))
    (hφs : φ.Scoped k) (hφs' : φ'.Scoped k) (h21 : I.Entails φ' φ)
    (hLC : LineConst S k A φ) (hLR : LineRob S k A A') : LineConst S k A' φ' := by
  have hXA : ∀ {k3 : ℕ} (θ : ISub k3 (k + 1)), TyCode k3 (semK S k3 (A.isub θ)) := fun θ =>
    tyCode_of_univ hW (HasTy.isubS hW hA θ)
  have hXA' : ∀ {k3 : ℕ} (θ : ISub k3 (k + 1)), TyCode k3 (semK S k3 (A'.isub θ)) := fun θ =>
    tyCode_of_univ hW (HasTy.isubS hW hA' θ)
  intro k3 τ r hr hh
  have hφ : (ival (idEnv k3) (φ.subst τ.τ)).holds :=
    (holds_iff_entails (I.scoped_subst hφs τ.sc)).2
      (ent_trans ((holds_iff_entails (I.scoped_subst hφs' τ.sc)).1 hh) (ent_subst h21 _))
  have r1 := RT2.symm hW (hXA _) (hLR k3 τ r r hr hr (I_eq_refl _))
  exact RT2.trans hW (hXA' _) r1 (RT2.trans hW (hXA _) (hLC k3 τ r hr hφ) (hLR k3 τ .zero .zero trivial trivial
    (I_eq_refl _)))

namespace TC

variable {d : ℕ} {D : DataDecl} {PL : Tm} {φ : I} {c : ℕ} {C : Ctor} {q : Tm} {X : List Tm} {rs : List I}

/-- The end of the line. -/
theorem end_data {QL : Tm} {φ' : I} {q' : Tm} {X' : List Tm} {rs' : List I}
    (H : TC S k d D PL QL φ φ' c C q q' X X' rs rs') :
    HasTy S k .one [] (.data d (PL.dinst .one)) (.univ D.level) ∧
    RT2 S k (.data d (PL.dinst .one)) (.data d (PL.dinst .one)) ∧ IsList (PL.dinst .one) ∧
    (PL.dinst .one).toList.length = D.params.length ∧ (PL.dinst .one).closedB 0 k = true := by
  have hW := H.hW
  obtain ⟨-, -, -, -, -, -, hPl, -, hPlen, -, hPc, -⟩ := H.basic
  have hP1 : PL.isub (ISub.cons .one trivial (ISub.id k)) = PL.dinst .one := isub_cons_id_of_closed hPc .one trivial
  have hd1 : HasTy S k .one [] (.data d (PL.dinst .one)) (.univ D.level) := by
    have := HasTy.isubS hW H.hPL (ISub.cons .one trivial (ISub.id k)); rwa [show (Tm.data d PL).isub
      (ISub.cons .one trivial (ISub.id k)) = .data d (PL.isub (ISub.cons .one trivial (ISub.id k))) from rfl, hP1] at this
  have s1 := H.hRLσ (ISub.cons .one trivial (ISub.id k))
  rw [hP1] at s1
  refine ⟨hd1, s1, isList_subst hPl _ _, ?_, data_closed hW H.hD hd1⟩
  rw [show PL.dinst .one = PL.subst Tm.var (I.inst0 .one) from rfl, toList_subst hPl]; simp [hPlen]

/-- The data of the transport of a nested constructor of a boundary, at the instances of its arguments. -/
theorem mkNested (H : TC S k d D PL PL φ φ c C q q X X rs rs) (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1))
    {c' : ℕ} {C' : Ctor} {as0 : Tm} {rs0 : List I} (hC' : D.ctors[c']? = some C')
    (hs : Ctor.simpleB D.ctors d D.params.length c C.args.length C
      (.con d c' (Ctor.paramVars D.params.length C.args.length) as0 rs0) = true)
    (hcl : (Tm.con d c' (Ctor.paramVars D.params.length C.args.length) as0 rs0).closedB
      (D.params.length + C.args.length) C.dims = true)
    (hBI : BI S d D c C rs (.con d c' (Ctor.paramVars D.params.length C.args.length) as0 rs0))
    (hty' : HasTy S k .one [] (.transp (.data d PL) φ (.con d c' q
      (Tm.ofList (as0.toList.map (Ctor.bndAt · q.toList X rs))) (rs0.map (·.subst (rsSub rs)))))
      (.data d (PL.dinst .one)))
    (hrecIH : ∀ l (hl : l < as0.toList.length), C'.isRec l = true → BTa S d D c C as0.toList[l]) :
    TC S k d D PL PL φ φ c' C' q q (as0.toList.map (Ctor.bndAt · q.toList X rs))
      (as0.toList.map (Ctor.bndAt · q.toList X rs)) (rs0.map (·.subst (rsSub rs))) (rs0.map (·.subst (rsSub rs))) := by
  have hW := H.hW
  obtain ⟨-, -, -, C1, hC1, hal, -, hsa, -⟩ := simpleB_con_inv hs
  rw [hC'] at hC1; cases hC1
  obtain ⟨-, -, -, -, hXl, -, hPl, -, hPlen, -, hPc, -⟩ := H.basic
  have tyB : ∀ {k4 : ℕ} {A B : Tm}, RT2 S k4 A B → TyEq S k4 A B := fun h => (Comp2_ty_base h).2.2.2.2.2
  have hP0 : PL.isub (ISub.cons .zero trivial (ISub.id k)) = PL.dinst .zero := isub_cons_id_of_closed hPc .zero trivial
  have hd0 : HasTy S k .one [] (.data d (PL.dinst .zero)) (.univ D.level) := by
    have := HasTy.isubS hW H.hPL (ISub.cons .zero trivial (ISub.id k)); rwa [show (Tm.data d PL).isub
      (ISub.cons .zero trivial (ISub.id k)) = .data d (PL.isub (ISub.cons .zero trivial (ISub.id k))) from rfl, hP0] at this
  have s0 := H.hRL k (ISub.id k) .zero .zero trivial trivial (I_eq_refl _)
  rw [hP0] at s0
  have hc0 : (PL.dinst .zero).closedB 0 k = true := data_closed hW H.hD hd0
  obtain ⟨-, ⟨-, -, -, hb0⟩, -⟩ := gen_transpF (spec_to_minimal hW H.hty) rfl
  have hcb : HasTy S k .one [] (.con d c q (Tm.ofList X) rs) (.data d (PL.dinst .zero)) := minimal_to_spec hb0
  have CI := con_inv hW H.hD H.hC hcb hd0
  have hrsl := CI.2.2.2.1
  have hcP0 := CI.2.2.2.2.2.2.1
  have hqL := CI.2.2.2.2.2.2.2.2.1
  have hql := CI.2.2.2.2.2.2.2.2.2
  have hXs := H.args0_self
  -- the nested arguments at the start of the line
  have hargs0 : ∀ i (hi : i < C'.args.length), RE2 S k ((C'.argTy d D.params.length i).substList
      (((as0.toList.map (Ctor.bndAt · q.toList X rs)).take i).reverse ++ (PL.dinst .zero).toList.reverse))
      ((as0.toList.map (Ctor.bndAt · q.toList X rs)).getD i .abort)
      ((as0.toList.map (Ctor.bndAt · q.toList X rs)).getD i .abort) := by
    obtain ⟨hrel0, -⟩ := hBI (PL.dinst .zero) X I.var hd0 s0 hXl (by rw [map_subst_var]; exact hcP0) hXs
    rw [map_subst_var] at hrel0
    have htZ : HasTy S k .one [] (.con d c' (Tm.ofList q.toList) (Tm.ofList (as0.toList.map (Ctor.bndAt · q.toList X rs)))
        (rs0.map (·.subst (rsSub rs)))) (.data d (PL.dinst .zero)) := by
      obtain ⟨-, ⟨-, -, -, hb'⟩, -⟩ := gen_transpF (spec_to_minimal hW hty') rfl
      rw [← hqL]; exact minimal_to_spec hb'
    have := nested_args hW H.hD hd0 s0 hH hyp H.hC hs hC' (ISub.id k) (ps := q.toList) (ps' := q.toList) hql hql
      hXl hXl (forall2_ieq_refl _) (by rw [isub_id_of_closed hc0]; exact hXs)
      (by rw [isub_id_of_closed hc0]; exact hrel0) (by rw [isub_id_of_closed hc0]; exact htZ)
      (by rw [isub_id_of_closed hc0]; exact htZ)
    intro i hi
    have h := this i hi
    rwa [isub_id_of_closed hc0] at h
  refine ⟨hW, H.hD, H.hp, hC', H.hPL, H.hR, H.hRL, H.hφs, H.h12, H.h21, H.hLC, hty', hty', EqTm.refl hty',
    hargs0, ?_, conR_hit hW H.hD hH hyp hC' H.hPL H.hRL (forall2_ieq_refl _)⟩
  intro l hl hrl k3 τ y y' hy hy' hE hy0 hLR ψ ψ' hLCy htyA htyA' heqA h12' h21' hbase
  have hlZ : l < as0.toList.length := by omega
  -- the recursive argument at the restriction
  have hcl' : ∀ x ∈ as0.toList, x.closedB (D.params.length + C.args.length) C.dims = true := by
    simp only [Tm.closedB, Bool.and_eq_true] at hcl
    exact closedB_toList hcl.1.2
  have eZ : ((as0.toList.map (Ctor.bndAt · q.toList X rs)).getD l .abort).isub τ =
      Ctor.bndAt as0.toList[l] (q.isub τ).toList (X.map (·.isub τ)) (rs.map (·.subst τ.τ)) := by
    rw [getD_eq_get' (by simp; omega), List.getElem_map]
    exact bndAt_isubL hqL (by rw [hql, hXl, hrsl]; exact hcl' _ (List.getElem_mem hlZ)) τ
  rw [eZ] at htyA htyA' ⊢
  obtain ⟨-, ⟨hLy, hψs, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW htyA) rfl
  obtain ⟨-, ⟨hLy', hψs', -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW htyA') rfl
  have hLyT : HasTy S (k3 + 1) .one [] (.data d (PL.isub (ISub.cons y hy τ.up.tail))) (.univ D.level) :=
    HasTy.isubS hW H.hPL _
  have hLy'T : HasTy S (k3 + 1) .one [] (.data d (PL.isub (ISub.cons y' hy' τ.up.tail))) (.univ D.level) :=
    HasTy.isubS hW H.hPL _
  have hcLy : (Tm.data d (PL.isub (ISub.cons y hy τ.up.tail))).closedB 0 (k3 + 1) = true := closed_of_ty hW hLyT
  have hcLy' : (Tm.data d (PL.isub (ISub.cons y' hy' τ.up.tail))).closedB 0 (k3 + 1) = true := closed_of_ty hW hLy'T
  -- the base constructor at the starts of the lines
  have hcτ := HasTy.isubS hW hcb τ
  rw [isub_conT, show (Tm.data d (PL.dinst .zero)).isub τ = .data d (PL.isub (ISub.cons .zero trivial τ)) by
    show Tm.data d ((PL.dinst .zero).isub τ) = _; rw [start_isub]] at hcτ
  have hy'0 : I.Eq (y'.subst (ISub.cons .zero trivial (ISub.id k3)).τ) .zero :=
    I_eq_trans (I_eq_subst (I_eq_symm hE) _) hy0
  have hcy : ∀ (z : I) (hz : z.Scoped (k3 + 1)), I.Eq (z.subst (ISub.cons .zero trivial (ISub.id k3)).τ) .zero →
      HasTy S k3 .one [] (.con d c (q.isub τ) (Tm.ofList (X.map (·.isub τ))) (rs.map (·.subst τ.τ)))
        ((Tm.data d (PL.isub (ISub.cons z hz τ.up.tail))).dinst .zero) := by
    intro z hz hz0
    show HasTy S k3 .one [] _ (.data d ((PL.isub (ISub.cons z hz τ.up.tail)).dinst .zero))
    rw [H.line_pt τ z hz .zero trivial]
    exact hcτ.tyConv (tyB (H.hRL k3 τ .zero _ trivial _ (I_eq_symm hz0)))
  have e1 : RT2 S k3 ((Tm.data d (PL.isub (ISub.cons y hy τ.up.tail))).dinst .one)
      ((Tm.data d (PL.isub (ISub.cons y' hy' τ.up.tail))).dinst .one) := by
    have : RT2 S k3 ((Tm.data d (PL.isub (ISub.cons y hy τ.up.tail))).isub (ISub.cons .one trivial (ISub.id k3)))
        ((Tm.data d (PL.isub (ISub.cons y' hy' τ.up.tail))).isub (ISub.cons .one trivial (ISub.id k3))) :=
      hLR k3 (ISub.id k3) .one .one trivial trivial (I_eq_refl _)
    rwa [isub_cons_id_of_closed hcLy, isub_cons_id_of_closed hcLy'] at this
  have hX1 : TyCode k3 (semK S k3 ((Tm.data d (PL.isub (ISub.cons y hy τ.up.tail))).dinst .one)) :=
    tyCode_of_ty hW htyA
  have hA2 := htyA'.tyConv (tyB e1)
  have hcon1 := transp_retarget hW htyA (hcy y hy hy0)
  have hcon2 := transp_retarget hW hA2 (hcy y' hy' hy'0)
  have hLC2 := LineConst.transfer hW hLyT hLy'T hψs hψs' h21' hLCy hLR
  have H1 := H.restrLine hH hyp (forall2_ieq_refl rs) τ y y hy hy (I_eq_refl _) hy0 hψs (ent_refl _) (ent_refl _)
    hLCy hcon1 hcon1 (EqTm.refl hcon1)
  have H2 := H.restrLine hH hyp (forall2_ieq_refl rs) τ y' y' hy' hy' (I_eq_refl _) hy'0 hψs' (ent_refl _) (ent_refl _)
    hLC2 hcon2 hcon2 (EqTm.refl hcon2)
  have hcon2' := hcon2.tyConv (TyEq.symm (tyB e1))
  have eL : TyEq S (k3 + 1) (.data d (PL.isub (ISub.cons y hy τ.up.tail))) (.data d (PL.isub (ISub.cons y' hy' τ.up.tail))) := by
    have : RT2 S (k3 + 1) ((Tm.data d (PL.isub (ISub.cons y hy τ.up.tail))).isub
        (ISub.cons (.var 0) (show 0 < k3 + 1 by omega) (ISub.id k3).up.tail))
        ((Tm.data d (PL.isub (ISub.cons y' hy' τ.up.tail))).isub
        (ISub.cons (.var 0) (show 0 < k3 + 1 by omega) (ISub.id k3).up.tail)) :=
      hLR (k3 + 1) (ISub.id k3).up.tail (.var 0) (.var 0) (show 0 < k3 + 1 by omega) (show 0 < k3 + 1 by omega)
        (I_eq_refl _)
    rw [ISub.cons_var0_up_tail, isub_up_id_of_closed hcLy, isub_up_id_of_closed hcLy'] at this
    exact tyB this
  have H12 := H.restrLine hH hyp (forall2_ieq_refl rs) τ y y' hy hy' hE hy0 hψs h12' h21' hLCy hcon1 hcon2'
    (eqTm_transp_of hW hcon1 hcon2' eL h12' h21' (EqTm.refl (hcy y hy hy0)))
  have BIl : BI S d D c C (rs.map (·.subst τ.τ)) as0.toList[l] := BI_isub (BI_sub hW H.hD H.hC hs hBI hC' hlZ hrl) τ.τ
  have B1 := hrecIH l hlZ hrl H1 BIl htyA
  have B2 := hrecIH l hlZ hrl H2 BIl hA2
  have hsl := (simpleArgs_get as0 0 hsa l hlZ).1 (by simpa using hrl)
  obtain ⟨hd1, s1, -, hPlen1, hc1⟩ := H1.end_data
  obtain ⟨hd1', s1', -, hPlen1', -⟩ := H2.end_data
  obtain ⟨hcO1, hO1⟩ := H1.outs_inst
  obtain ⟨hcO2, hO2⟩ := H2.outs_inst
  rw [← map_subst_var (rs.map (·.subst τ.τ))] at hcO1 hcO2
  obtain ⟨hrelO, htyO1⟩ := BIl _ _ I.var hd1 s1 (tOuts_length _ _ _ _ _ _) hcO1 hO1
  obtain ⟨-, htyO2⟩ := BIl _ _ I.var hd1' s1' (tOuts_length _ _ _ _ _ _) hcO2 hO2
  rw [map_subst_var] at hrelO htyO1 htyO2
  have htyO2' := htyO2.tyConv (TyEq.symm (tyB e1))
  have args12 : ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      (((tOuts d D C (PL.isub (ISub.cons y hy τ.up.tail)) ψ (X.map (·.isub τ))).take i).reverse ++
        ((PL.isub (ISub.cons y hy τ.up.tail)).dinst .one).toList.reverse))
      ((tOuts d D C (PL.isub (ISub.cons y hy τ.up.tail)) ψ (X.map (·.isub τ))).getD i .abort)
      ((tOuts d D C (PL.isub (ISub.cons y' hy' τ.up.tail)) ψ' (X.map (·.isub τ))).getD i .abort) := by
    intro i hi
    obtain ⟨-, -, -, -, -, G6, G7, -⟩ := H12.good_all i hi
    rw [tOuts_getD d D C _ ψ _ hi, tOuts_getD d D C _ ψ' _ hi]
    exact RE2.conv hW G7 G6
  have B3 := bnd_rel hW H.hD hd1 s1 (fun c'' _ => con_rel hW H.hD hd1 s1 hH hyp c'') H.hC
    (sizeOf as0.toList[l] + 1) _ (by omega) hsl (ISub.id k3) hPlen1 hPlen1' (tOuts_length _ _ _ _ _ _)
    (tOuts_length _ _ _ _ _ _) (forall2_ieq_refl _) (by rw [isub_id_of_closed hc1]; exact args12)
    (by rw [isub_id_of_closed hc1]; exact hrelO) (by rw [isub_id_of_closed hc1]; exact htyO1)
    (by rw [isub_id_of_closed hc1]; exact htyO2')
  rw [isub_id_of_closed hc1] at B3
  have B2' := RE2.conv hW (RT2.symm hW hX1 e1) B2
  exact RE2.trans hW s1 B1 (RE2.trans hW s1 B3 (RE2.symm hW s1 B2'))

end TC

end

end Model.Whnf
