import Model.Whnf.Kan2DataHITLC

/-!
# Transport of boundary terms: auxiliary facts

The arguments of a transported constructor where the face holds (`TC.face_args`), instances at restricted
interval arguments (`BI_isub`), and the arguments of a nested constructor of a boundary at the
transported arguments against those of its own transport (`TC.argsCmp`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- A transport, at another base of the start of the line. -/
theorem transp_retarget (hW : WfSig S) {L a b : Tm} {ψ : I} (hty : HasTy S k .one [] (.transp L ψ a) (L.dinst .one))
    (hb : HasTy S k .one [] b (L.dinst .zero)) : HasTy S k .one [] (.transp L ψ b) (L.dinst .one) := by
  obtain ⟨l0, ⟨hL, hψ, hc, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  exact HasTy.transp (minimal_to_spec hL) hψ (minimal_to_spec_eq hc) hb

theorem BI_isub {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor} {rs : List I} {a : Tm} (h : BI S d D c C rs a)
    (τ0 : ℕ → I) : BI S d D c C (rs.map (·.subst τ0)) a := by
  intro k3 P1 Y τ hP1 hPP hYl hcT hY
  have e : (rs.map (·.subst τ0)).map (·.subst τ) = rs.map (·.subst (fun i => (τ0 i).subst τ)) := by
    rw [List.map_map]; congr 1; funext r; exact I_subst_subst _ _ _
  rw [e] at hcT ⊢
  exact h P1 Y _ hP1 hPP hYl hcT hY

theorem map_subst_var (rs : List I) : rs.map (·.subst I.var) = rs := by
  conv_rhs => rw [← List.map_id rs]
  congr 1; funext r; exact I_subst_var r

namespace TC

variable {d : ℕ} {D : DataDecl} {PL QL : Tm} {φ φ' : I} {c : ℕ} {C : Ctor} {q q' : Tm} {X X' : List Tm}
  {rs rs' : List I}

/-- Where the face holds, the transported arguments are related to the arguments. -/
theorem face_args (H : TC S k d D PL QL φ φ' c C q q' X X' rs rs') (hφ : I.Entails .one φ) :
    ∀ j, j < C.args.length →
      RT2 S k ((C.argTy d D.params.length j).substList ((X.take j).reverse ++ (PL.dinst .zero).toList.reverse))
        ((C.argTy d D.params.length j).substList (((tOuts d D C PL φ X).take j).reverse ++
          (PL.dinst .one).toList.reverse)) ∧
      RE2 S k ((C.argTy d D.params.length j).substList ((X.take j).reverse ++ (PL.dinst .zero).toList.reverse))
        (X.getD j .abort) ((tOuts d D C PL φ X).getD j .abort) := by
  have hW := H.hW
  obtain ⟨-, -, -, -, hXl, -, hPl, -, -, -, hPc, -⟩ := H.basic
  have hP0 : PL.isub (ISub.cons .zero trivial (ISub.id k)) = PL.dinst .zero := isub_cons_id_of_closed hPc .zero trivial
  have hP1 : PL.isub (ISub.cons .one trivial (ISub.id k)) = PL.dinst .one := isub_cons_id_of_closed hPc .one trivial
  have hd0 : HasTy S k .one [] (.data d (PL.dinst .zero)) (.univ D.level) := by
    have := HasTy.isubS hW H.hPL (ISub.cons .zero trivial (ISub.id k)); rwa [show (Tm.data d PL).isub
      (ISub.cons .zero trivial (ISub.id k)) = .data d (PL.isub (ISub.cons .zero trivial (ISub.id k))) from rfl, hP0] at this
  have s0 := H.hRL k (ISub.id k) .zero .zero trivial trivial (I_eq_refl _)
  rw [hP0] at s0
  have hd1 : HasTy S k .one [] (.data d (PL.dinst .one)) (.univ D.level) := by
    have := HasTy.isubS hW H.hPL (ISub.cons .one trivial (ISub.id k)); rwa [show (Tm.data d PL).isub
      (ISub.cons .one trivial (ISub.id k)) = .data d (PL.isub (ISub.cons .one trivial (ISub.id k))) from rfl, hP1] at this
  have hholds : (ival (idEnv k) (φ.subst (ISub.id k).τ)).holds := by
    rw [I_subst_id H.hφs]; exact (holds_iff_entails H.hφs).2 hφ
  have h10 := H.hLC k (ISub.id k) .one trivial hholds
  rw [show (Tm.data d PL).isub (ISub.cons .one trivial (ISub.id k)) = .data d (PL.dinst .one) by
      show Tm.data d (PL.isub _) = _; rw [hP1],
    show (Tm.data d PL).isub (ISub.cons .zero trivial (ISub.id k)) = .data d (PL.dinst .zero) by
      show Tm.data d (PL.isub _) = _; rw [hP0]] at h10
  have h01 : RT2 S k (.data d (PL.dinst .zero)) (.data d (PL.dinst .one)) :=
    RT2.symm hW (tyCode_of_univ hW hd1) h10
  have hargsX := H.args0_self
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ihj =>
    intro hj
    have T : RT2 S k ((C.argTy d D.params.length j).substList ((X.take j).reverse ++ (PL.dinst .zero).toList.reverse))
        ((C.argTy d D.params.length j).substList (((tOuts d D C PL φ X).take j).reverse ++
          (PL.dinst .one).toList.reverse)) :=
      argTy_rt2' hW H.hD hd0 s0 h01 H.hC hj (by simp; omega) (by simp [tOuts_length]; omega) (fun i hi => by
        rw [List.take_take, Nat.min_eq_left hi.le, getD_take_lt hi, getD_take_lt hi]
        exact (ihj i hi (by omega)).2)
    obtain ⟨-, -, -, -, -, htyO⟩ := tcon_typing hW H.hD H.hp H.hC H.hty hj
    rw [← tOuts_getD d D C PL φ X hj] at htyO
    have hX : TyCode k (semK S k ((C.argTy d D.params.length j).substList ((X.take j).reverse ++
        (PL.dinst .zero).toList.reverse))) := RE2.tyCode hW (hargsX j hj)
    have htyO' := htyO.tyConv (TyEq.symm (Comp2_ty_base T).2.2.2.2.2)
    have hst := stable_transpFace hW hφ (by rw [tOuts_getD d D C PL φ X hj] at htyO'; exact htyO')
    rw [← tOuts_getD d D C PL φ X hj] at hst
    have hAA := RT2.refl hW hX T
    exact ⟨T, RE2.expandR hW hAA (RE2.typed (hargsX j hj)).1 htyO' hst (hargsX j hj)⟩

/-- The transported arguments, at the end of the line: the constructor is typed and they are related to
themselves. -/
theorem outs_inst (H : TC S k d D PL QL φ φ' c C q q' X X' rs rs') :
    HasTy S k .one [] (.con d c (PL.dinst .one) (Tm.ofList (tOuts d D C PL φ X)) rs) (.data d (PL.dinst .one)) ∧
    ∀ i (hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
      (((tOuts d D C PL φ X).take i).reverse ++ (PL.dinst .one).toList.reverse))
      ((tOuts d D C PL φ X).getD i .abort) ((tOuts d D C PL φ X).getD i .abort) := by
  have hW := H.hW
  obtain ⟨eT, -⟩ := H.basic
  refine ⟨HasTy.eqR eT, fun i hi => ?_⟩
  have G := H.good_all i hi
  obtain ⟨-, G2, -, -, -, G6, G7, -⟩ := G
  have hT := RT2.refl' hW (RE2.tyCode hW G6) G7
  have g := RE2.conv hW G7 G6
  have g' := RE2.trans hW hT g (RE2.symm hW hT g)
  rw [tOuts_getD d D C PL φ X hi]
  exact g'

/-- The arguments of a nested constructor of a boundary at the transported arguments, against the
arguments of its own transport. -/
theorem argsCmp (H : TC S k d D PL PL φ φ c C q q X X rs rs) (hH : D.isHIT = true) (hyp : HITHyp2 S) {c' : ℕ}
    {C' : Ctor} {as0 : Tm} {rs0 : List I} (hC' : D.ctors[c']? = some C')
    (hs : Ctor.simpleB D.ctors d D.params.length c C.args.length C
      (.con d c' (Ctor.paramVars D.params.length C.args.length) as0 rs0) = true)
    (hBI : BI S d D c C rs (.con d c' (Ctor.paramVars D.params.length C.args.length) as0 rs0))
    (hty' : HasTy S k .one [] (.transp (.data d PL) φ (.con d c' q
      (Tm.ofList (as0.toList.map (Ctor.bndAt · q.toList X rs))) (rs0.map (·.subst (rsSub rs)))))
      (.data d (PL.dinst .one)))
    (hrec : ∀ l (hl : l < as0.toList.length), C'.isRec l = true →
      RE2 S k (.data d (PL.dinst .one)) (Ctor.bndAt as0.toList[l] (PL.dinst .one).toList (tOuts d D C PL φ X) rs)
        (.transp (.data d PL) φ (Ctor.bndAt as0.toList[l] q.toList X rs))) :
    HasTy S k .one [] (.con d c' (PL.dinst .one)
      (Tm.ofList (as0.toList.map (Ctor.bndAt · (PL.dinst .one).toList (tOuts d D C PL φ X) rs)))
      (rs0.map (·.subst (rsSub rs)))) (.data d (PL.dinst .one)) ∧
    ∀ j (hj : j < C'.args.length), RE2 S k ((C'.argTy d D.params.length j).substList
      (((as0.toList.map (Ctor.bndAt · (PL.dinst .one).toList (tOuts d D C PL φ X) rs)).take j).reverse ++
        (PL.dinst .one).toList.reverse))
      ((as0.toList.map (Ctor.bndAt · (PL.dinst .one).toList (tOuts d D C PL φ X) rs)).getD j .abort)
      ((tOuts d D C' PL φ (as0.toList.map (Ctor.bndAt · q.toList X rs))).getD j .abort) := by
  have hW := H.hW
  obtain ⟨-, -, -, C1, hC1, hal, -, hsa, hasL⟩ := simpleB_con_inv hs
  rw [hC'] at hC1; cases hC1
  obtain ⟨-, -, -, -, hXl, -, hPl, -, hPlen, -, hPc, -⟩ := H.basic
  have hP1 : PL.isub (ISub.cons .one trivial (ISub.id k)) = PL.dinst .one := isub_cons_id_of_closed hPc .one trivial
  have hd1 : HasTy S k .one [] (.data d (PL.dinst .one)) (.univ D.level) := by
    have := HasTy.isubS hW H.hPL (ISub.cons .one trivial (ISub.id k)); rwa [show (Tm.data d PL).isub
      (ISub.cons .one trivial (ISub.id k)) = .data d (PL.isub (ISub.cons .one trivial (ISub.id k))) from rfl, hP1] at this
  have s1 := H.hRLσ (ISub.cons .one trivial (ISub.id k))
  rw [hP1] at s1
  have hPl1 : IsList (PL.dinst .one) := isList_subst hPl _ _
  have hPlen1 : (PL.dinst .one).toList.length = D.params.length := by
    rw [show PL.dinst .one = PL.subst Tm.var (I.inst0 .one) from rfl, toList_subst hPl]; simp [hPlen]
  obtain ⟨hcO, hOself⟩ := H.outs_inst
  rw [← map_subst_var rs] at hcO
  obtain ⟨hrel, htyB⟩ := hBI (PL.dinst .one) (tOuts d D C PL φ X) I.var hd1 s1 (tOuts_length _ _ _ _ _ _) hcO hOself
  rw [map_subst_var] at hrel htyB
  simp only [bndRel, hC'] at hrel
  rw [bndAt_con, bndAt_paramVars _ hPlen1 (tOuts_length _ _ _ _ _ _), show Ctor.bndAt as0 (PL.dinst .one).toList
    (tOuts d D C PL φ X) rs = Tm.ofList (as0.toList.map (Ctor.bndAt · (PL.dinst .one).toList (tOuts d D C PL φ X) rs))
    from by conv_lhs => rw [hasL]
            exact bndAt_ofList _ _ _ _, ← hPl1] at htyB
  refine ⟨htyB, fun j hj => ?_⟩
  have haj : j < as0.toList.length := by omega
  obtain ⟨hpt, -⟩ := bndRelArgs_get as0 0 [] hrel j haj
  simp only [Nat.zero_add, List.append_nil, List.map_take] at hpt
  have hZl : (as0.toList.map (Ctor.bndAt · q.toList X rs)).length = C'.args.length := by simp [hal]
  rw [tOuts_getD d D C' PL φ _ hj]
  cases hrj : C'.isRec j
  · obtain ⟨x, hx, hxn, hcr⟩ := (simpleArgs_get as0 0 hsa j haj).2 (by simpa using hrj)
    have T1 := hpt x hx hrj hxn
    obtain ⟨N1, N2⟩ := H.nested_pt hH hyp hC' hs hBI hty' j hj hrj x (by rw [List.getElem?_eq_getElem haj, hx]) hxn
    have Gi := H.good_all (C.args.length - 1 - x) (by omega)
    obtain ⟨-, -, -, -, -, G6, G7, -⟩ := Gi
    have eO : (as0.toList.map (Ctor.bndAt · (PL.dinst .one).toList (tOuts d D C PL φ X) rs)).getD j .abort =
        .transp (tl d D C PL φ X (C.args.length - 1 - x)) φ (X.getD (C.args.length - 1 - x) .abort) := by
      rw [getD_eq_get' (by simp; omega), List.getElem_map, hx, bndAt_var _ (by simp [tOuts_length]; omega),
        tOuts_length, tOuts_getD d D C PL φ X (by omega)]
    rw [eO]
    have hX1 : TyCode k (semK S k ((tl d D C' PL φ (as0.toList.map (Ctor.bndAt · q.toList X rs)) j).dinst .one)) :=
      RE2.tyCode hW N1
    have N1' := RE2.conv hW N2 N1
    have hXc1 : TyCode k (semK S k ((tl d D C PL φ X (C.args.length - 1 - x)).dinst .one)) := RE2.tyCode hW G6
    have hTc := RT2.refl hW hXc1 (RT2.trans hW hXc1 (RT2.symm hW hX1 N2) N2)
    have N1'' := RE2.symm hW hTc N1'
    exact RE2.conv hW T1 (RE2.conv hW G7 N1'')
  · rw [argTy_rec_inst hrj hPl1 hPlen1 (by simp; omega)]
    rw [tl_rec (d := d) hPl hPlen φ _ hj.le hrj, getD_eq_get' (by simp; omega), getD_eq_get' (by simp; omega),
      List.getElem_map, List.getElem_map]
    exact hrec j haj hrj

end TC

end

end Model.Whnf
