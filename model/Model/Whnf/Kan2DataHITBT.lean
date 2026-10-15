import Model.Whnf.Kan2DataHITBT2

/-!
# Transport of boundary terms of higher inductive types

The transport of the instance of a subterm of a boundary of constructor `c` is related to its instance at the
transported arguments (`bnd_transp`): by induction on the constructor and on the subterm, expanding the
transport at each restriction (`BT_at`): where the face holds, by the relation of boundary terms at related
arguments; at a nested constructor `c'` where no boundary of `c'` holds, by its `transpCon` contractum
(`TC.argsCmp`, `con_rel`); and where a boundary of `c'` holds, by the transport of that boundary (induction on
the constructor) and `HITHyp2.conBnd`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- The statement of `bnd_transp` for constructor `c`. -/
def BTSt (S : Sig) (d : ℕ) (D : DataDecl) (c : ℕ) : Prop :=
  ∀ (C : Ctor), D.ctors[c]? = some C → ∀ a, Ctor.simpleB D.ctors d D.params.length c C.args.length C a = true →
    a.closedB (D.params.length + C.args.length) C.dims = true → BTa S d D c C a

section bt
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = true)
  (hyp : HITHyp2 S (d + 1))
include hW hD hH hyp

/-- One restriction of the transport of a boundary term: a reduct related to the boundary term at the
transported arguments. -/
theorem BT_at {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) (ihc : ∀ c' < c, BTSt S d D c') (a : Tm)
    (hs : Ctor.simpleB D.ctors d D.params.length c C.args.length C a = true)
    (hcl : a.closedB (D.params.length + C.args.length) C.dims = true)
    (hsub : ∀ a', sizeOf a' < sizeOf a → Ctor.simpleB D.ctors d D.params.length c C.args.length C a' = true →
      a'.closedB (D.params.length + C.args.length) C.dims = true → BTa S d D c C a')
    {k : ℕ} {PL : Tm} {φ : I} {q : Tm} {X : List Tm} {rs : List I} (H : TC S k d D PL PL φ φ c C q q X X rs rs)
    (hBI : BI S d D c C rs a)
    (hty : HasTy S k .one [] (.transp (.data d PL) φ (Ctor.bndAt a q.toList X rs)) (.data d (PL.dinst .one))) :
    ∃ u, Red S (.transp (.data d PL) φ (Ctor.bndAt a q.toList X rs)) u ∧
      EqTm S k .one [] (.transp (.data d PL) φ (Ctor.bndAt a q.toList X rs)) u (.data d (PL.dinst .one)) ∧
      RE2 S k (.data d (PL.dinst .one)) u (Ctor.bndAt a (PL.dinst .one).toList (tOuts d D C PL φ X) rs) := by
  obtain ⟨-, -, -, -, hXl, -, hPl, -, hPlen, -, hPc, -⟩ := H.basic
  obtain ⟨hd1, s1, hPl1, hPlen1, hc1⟩ := H.end_data
  have tyB : ∀ {k4 : ℕ} {A B : Tm}, RT2 S k4 A B → TyEq S k4 A B := fun h => (Comp2_ty_base h).2.2.2.2.2
  have hP0 : PL.isub (ISub.cons .zero trivial (ISub.id k)) = PL.dinst .zero := isub_cons_id_of_closed hPc .zero trivial
  have hP1 : PL.isub (ISub.cons .one trivial (ISub.id k)) = PL.dinst .one := isub_cons_id_of_closed hPc .one trivial
  have hd0 : HasTy S k .one [] (.data d (PL.dinst .zero)) (.univ D.level) := by
    have := HasTy.isubS hW H.hPL (ISub.cons .zero trivial (ISub.id k)); rwa [show (Tm.data d PL).isub
      (ISub.cons .zero trivial (ISub.id k)) = .data d (PL.isub (ISub.cons .zero trivial (ISub.id k))) from rfl, hP0] at this
  have s0 := H.hRL k (ISub.id k) .zero .zero trivial trivial (I_eq_refl _)
  rw [hP0] at s0
  have hc0 : (PL.dinst .zero).closedB 0 k = true := data_closed hW hD hd0
  obtain ⟨-, ⟨-, -, -, hb0⟩, -⟩ := gen_transpF (spec_to_minimal hW H.hty) rfl
  have hcb : HasTy S k .one [] (.con d c q (Tm.ofList X) rs) (.data d (PL.dinst .zero)) := minimal_to_spec hb0
  have CI := con_inv hW hD hC hcb hd0
  have hrsl := CI.2.2.2.1
  have hcP0 := CI.2.2.2.2.2.2.1
  have hqL := CI.2.2.2.2.2.2.2.2.1
  have hql := CI.2.2.2.2.2.2.2.2.2
  have hXs := H.args0_self
  obtain ⟨hcO, hO⟩ := H.outs_inst
  rw [← map_subst_var rs] at hcO
  obtain ⟨-, htyR⟩ := hBI _ _ I.var hd1 s1 (tOuts_length _ _ _ _ _ _) hcO hO
  obtain ⟨hrel0, -⟩ := hBI _ X I.var hd0 s0 hXl (by rw [map_subst_var]; exact hcP0) hXs
  rw [map_subst_var] at htyR hrel0
  obtain ⟨-, ⟨-, -, -, hbase⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  have hbase' : HasTy S k .one [] (Ctor.bndAt a q.toList X rs) (.data d (PL.dinst .zero)) := minimal_to_spec hbase
  have hface : I.Entails .one φ → ∃ u, Red S (.transp (.data d PL) φ (Ctor.bndAt a q.toList X rs)) u ∧
      EqTm S k .one [] (.transp (.data d PL) φ (Ctor.bndAt a q.toList X rs)) u (.data d (PL.dinst .one)) ∧
      RE2 S k (.data d (PL.dinst .one)) u (Ctor.bndAt a (PL.dinst .one).toList (tOuts d D C PL φ X) rs) := by
    intro hφ
    -- the face holds: the base
    refine ⟨_, .step (step_transp_face hφ) (.refl _), EqTm.transpFace hφ hty, ?_⟩
    have FA := H.face_args hφ
    have hholds : (ival (idEnv k) (φ.subst (ISub.id k).τ)).holds := by
      rw [I_subst_id H.hφs]; exact (holds_iff_entails H.hφs).2 hφ
    have h10 := H.hLC k (ISub.id k) .one trivial hholds
    rw [show (Tm.data d PL).isub (ISub.cons .one trivial (ISub.id k)) = .data d (PL.dinst .one) by
        show Tm.data d (PL.isub _) = _; rw [hP1],
      show (Tm.data d PL).isub (ISub.cons .zero trivial (ISub.id k)) = .data d (PL.dinst .zero) by
        show Tm.data d (PL.isub _) = _; rw [hP0]] at h10
    have h01 : RT2 S k (.data d (PL.dinst .zero)) (.data d (PL.dinst .one)) :=
      RT2.symm hW (tyCode_of_univ hW hd1) h10
    have R := bnd_rel hW hD hd0 s0 (fun c'' _ => con_rel hW hD hd0 s0 hH hyp c'') hC (sizeOf a + 1) a (by omega) hs
      (ISub.id k) (ps := q.toList) (ps' := (PL.dinst .one).toList) hql hPlen1 hXl (tOuts_length _ _ _ _ _ _)
      (forall2_ieq_refl _) (by rw [isub_id_of_closed hc0]; exact fun i hi => (FA i hi).2)
      (by rw [isub_id_of_closed hc0]; exact hrel0) (by rw [isub_id_of_closed hc0]; exact hbase')
      (by rw [isub_id_of_closed hc0]; exact htyR.tyConv (tyB h10))
    rw [isub_id_of_closed hc0] at R
    exact RE2.conv hW h01 R
  cases a
  case var x =>
    by_cases hφ : I.Entails .one φ
    · exact hface hφ
    simp only [Ctor.simpleB, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨hx, hr⟩ := hs
    refine ⟨_, .refl _, EqTm.refl hty, ?_⟩
    rw [bndAt_var rs (show x < X.length by omega),
      bndAt_var rs (show x < (tOuts d D C PL φ X).length by rw [tOuts_length]; omega), tOuts_length, hXl,
      tOuts_getD d D C PL φ X (by omega)]
    obtain ⟨-, -, -, -, -, G6, -, -⟩ := H.good_all (C.args.length - 1 - x) (by omega)
    rw [tl_rec (d := d) hPl hPlen φ X (by omega) hr] at G6 ⊢
    exact G6
  case con d' c' ps0 as0 rs0 =>
    by_cases hφ : I.Entails .one φ
    · exact hface hφ
    obtain ⟨hdd, hcc, hps0, C', hC', hal, hrl, hsa, hasL⟩ := simpleB_con_inv hs
    subst d' hps0
    have eB : ∀ (qs Y : List Tm) (rY : List I), qs.length = D.params.length → Y.length = C.args.length →
        Ctor.bndAt (.con d c' (Ctor.paramVars D.params.length C.args.length) as0 rs0) qs Y rY =
          .con d c' (Tm.ofList qs) (Tm.ofList (as0.toList.map (Ctor.bndAt · qs Y rY)))
            (rs0.map (·.subst (rsSub rY))) := by
      intro qs Y rY h1 h2
      rw [bndAt_con, bndAt_paramVars rY h1 h2, show Ctor.bndAt as0 qs Y rY =
        Tm.ofList (as0.toList.map (Ctor.bndAt · qs Y rY)) from by conv_lhs => rw [hasL]
                                                                  exact bndAt_ofList _ _ _ _]
    rw [eB q.toList X rs hql hXl, ← hqL] at hty hbase' ⊢
    rw [eB (PL.dinst .one).toList (tOuts d D C PL φ X) rs hPlen1 (tOuts_length _ _ _ _ _ _), ← hPl1]
    have hcl' : ∀ x ∈ as0.toList, x.closedB (D.params.length + C.args.length) C.dims = true := by
      simp only [Tm.closedB, Bool.and_eq_true] at hcl
      exact closedB_toList hcl.1.2
    have hrecIH : ∀ l (hl : l < as0.toList.length), C'.isRec l = true → BTa S d D c C as0.toList[l] :=
      fun l hl hr => hsub _ (sizeOf_con_arg (List.getElem_mem hl)) ((simpleArgs_get as0 0 hsa l hl).1 (by simpa using hr))
        (hcl' _ (List.getElem_mem hl))
    have hrec : ∀ l (hl : l < as0.toList.length), C'.isRec l = true →
        RE2 S k (.data d (PL.dinst .one)) (Ctor.bndAt as0.toList[l] (PL.dinst .one).toList (tOuts d D C PL φ X) rs)
          (.transp (.data d PL) φ (Ctor.bndAt as0.toList[l] q.toList X rs)) := by
      intro l hl hr
      obtain ⟨htele, -⟩ := con_inv hW hD hC' hbase' hd0
      have hPl0 : IsList (PL.dinst .zero) := isList_subst hPl _ _
      have hPlen0 : (PL.dinst .zero).toList.length = D.params.length := by
        rw [show PL.dinst .zero = PL.subst Tm.var (I.inst0 .zero) from rfl, toList_subst hPl]; simp [hPlen]
      have g := HasTele0.get htele (k := l) (a := Ctor.bndAt as0.toList[l] q.toList X rs)
        (by rw [toList_ofList, List.getElem?_map, List.getElem?_eq_getElem hl]; rfl) (argTys_get (by omega))
      rw [argTy_rec_inst hr hPl0 hPlen0 (by simp [toList_ofList]; omega)] at g
      have htyl := transp_retarget hW hty (minimal_to_spec g)
      exact RE2.symm hW s1 (hrecIH l hl hr H (BI_sub hW hD hC hs hBI hC' hl hr) htyl)
    obtain ⟨htyO, hargsO⟩ := H.argsCmp hH hyp hC' hs hBI hty hrec
    have hZl : (as0.toList.map (Ctor.bndAt · q.toList X rs)).length = C'.args.length := by simp [hal]
    have hOl : (as0.toList.map (Ctor.bndAt · (PL.dinst .one).toList (tOuts d D C PL φ X) rs)).length =
        C'.args.length := by simp [hal]
    obtain ⟨eT, -⟩ := transpCon_eqR hW hD H.hp hC' hty
    cases hf : firstBnd C'.bnd (rs0.map (·.subst (rsSub rs))) with
    | none =>
      have hstep := step_transp_conR hD H.hp hC' (ps := PL) (qs := q) hφ hZl (step_con_none hD hC' _ _ hf)
      refine ⟨_, .step hstep (.refl _), eT, ?_⟩
      have R := con_rel hW hD hd1 s1 hH hyp c' (ISub.id k) hC' (by rw [isub_id_of_closed hc1]; exact htyO)
        (by rw [isub_id_of_closed hc1]; exact HasTy.eqR eT) (forall2_ieq_refl _)
        (by rw [isub_id_of_closed hc1]; exact hargsO)
      rw [isub_id_of_closed hc1] at R
      exact RE2.symm hW s1 R
    | some b' =>
      obtain ⟨kb', ψ', hb', hent'⟩ := firstBnd_spec hf
      obtain ⟨-, hbc', hsimple', -⟩ := ((hW.2 d D hD).2.2 c' C' hC').2.1 kb' ψ' b' hb'
      have e1 := EqTm.conBnd hD hC' hb' hent' hqL (by rw [toList_ofList]) hbase'
      rw [toList_ofList] at e1
      have s2 : step S (.con d c' q (Tm.ofList (as0.toList.map (Ctor.bndAt · q.toList X rs)))
          (rs0.map (·.subst (rsSub rs)))) = some (Ctor.bndAt b' q.toList (as0.toList.map (Ctor.bndAt · q.toList X rs))
          (rs0.map (·.subst (rsSub rs)))) := by
        rw [step_con_some hD hC' _ _ hf, toList_ofList]
      obtain ⟨htyu, eu⟩ := transp_rebase hW hty e1
      refine ⟨_, red_transp_base hD H.hp hφ (.step s2 (.refl _)), eu, ?_⟩
      have TC' := H.mkNested hH hyp hC' hs hcl hBI hty hrecIH
      have hrs2l : (rs0.map (·.subst (rsSub rs))).length = C'.dims := by simp [hrl]
      have BI' : BI S d D c' C' (rs0.map (·.subst (rsSub rs))) b' := fun {_} => BI_top hW hD hH hyp hC' hrs2l hb' hent'
      have BT' := ihc c' hcc C' hC' b' hsimple' hbc' TC' BI' htyu
      have hOself := args_self hW hD hd1 s1 (ISub.id k) hC' hOl (tOuts_length _ _ _ _ _ _)
        (by rw [isub_id_of_closed hc1]; exact hargsO)
      have hOs : ∀ i (hi : i < C'.args.length), RE2 S k ((C'.argTy d D.params.length i).substList
          (((as0.toList.map (Ctor.bndAt · (PL.dinst .one).toList (tOuts d D C PL φ X) rs)).take i).reverse ++
            (PL.dinst .one).toList.reverse))
          ((as0.toList.map (Ctor.bndAt · (PL.dinst .one).toList (tOuts d D C PL φ X) rs)).getD i .abort)
          ((as0.toList.map (Ctor.bndAt · (PL.dinst .one).toList (tOuts d D C PL φ X) rs)).getD i .abort) := by
        intro i hi
        have := (hOself i hi).2.1
        rwa [isub_id_of_closed hc1] at this
      have hrelb := hyp.bndTy (by omega) hD hH hC' hb' hent' hd1 s1 hOl htyO hOs
      have eO := EqTm.conBnd hD hC' hb' hent' hPl1 (by rw [toList_ofList]) htyO
      rw [toList_ofList] at eO
      have eT2 := EqTm.conBnd hD hC' hb' hent' hPl1 (by rw [toList_ofList])
        (HasTy.eqR eT : HasTy S k .one [] (.con d c' (PL.dinst .one)
          (Tm.ofList (tOuts d D C' PL φ (as0.toList.map (Ctor.bndAt · q.toList X rs)))) _) _)
      rw [toList_ofList] at eT2
      have R1 := bnd_rel hW hD hd1 s1 (fun c'' _ => con_rel hW hD hd1 s1 hH hyp c'') hC' (sizeOf b' + 1) b'
        (by omega) hsimple' (ISub.id k) hPlen1 hPlen1 hOl (tOuts_length _ _ _ _ _ _) (forall2_ieq_refl _)
        (by rw [isub_id_of_closed hc1]; exact hargsO) (by rw [isub_id_of_closed hc1]; exact hrelb)
        (by rw [isub_id_of_closed hc1]; exact HasTy.eqR eO) (by rw [isub_id_of_closed hc1]; exact HasTy.eqR eT2)
      rw [isub_id_of_closed hc1] at R1
      have R2 := hyp.conBnd (by omega) hD hH hC' hb' hent' hd1 s1 hOl htyO hOs
      exact RE2.trans hW s1 BT' (RE2.trans hW s1 (RE2.symm hW s1 R1) (RE2.symm hW s1 R2))
  all_goals simp [Ctor.simpleB] at hs

/-- Transport of boundary terms of higher inductive types: the transport of the instance of a subterm of a
boundary is related to its instance at the transported arguments. -/
theorem bnd_transp : ∀ c, BTSt S d D c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ihc =>
  intro C hC
  have key : ∀ N a, sizeOf a < N → Ctor.simpleB D.ctors d D.params.length c C.args.length C a = true →
      a.closedB (D.params.length + C.args.length) C.dims = true → BTa S d D c C a := by
    intro N
    induction N with
    | zero => intro a h; omega
    | succ N ihN =>
    intro a hsz hs hcl k PL φ q X rs H hBI hty
    obtain ⟨-, -, -, -, hXl, -, hPl, -, hPlen, -, hPc, -⟩ := H.basic
    obtain ⟨hd1, s1, hPl1, hPlen1, hc1⟩ := H.end_data
    have hP0 : PL.isub (ISub.cons .zero trivial (ISub.id k)) = PL.dinst .zero := isub_cons_id_of_closed hPc .zero trivial
    have hd0 : HasTy S k .one [] (.data d (PL.dinst .zero)) (.univ D.level) := by
      have := HasTy.isubS hW H.hPL (ISub.cons .zero trivial (ISub.id k)); rwa [show (Tm.data d PL).isub
        (ISub.cons .zero trivial (ISub.id k)) = .data d (PL.isub (ISub.cons .zero trivial (ISub.id k))) from rfl, hP0] at this
    obtain ⟨-, ⟨-, -, -, hb0⟩, -⟩ := gen_transpF (spec_to_minimal hW H.hty) rfl
    have CI := con_inv hW hD hC (minimal_to_spec hb0 : HasTy S k .one [] (.con d c q (Tm.ofList X) rs)
      (.data d (PL.dinst .zero))) hd0
    have hrsl := CI.2.2.2.1
    have hqL := CI.2.2.2.2.2.2.2.2.1
    have hql := CI.2.2.2.2.2.2.2.2.2
    obtain ⟨hcO, hO⟩ := H.outs_inst
    rw [← map_subst_var rs] at hcO
    obtain ⟨-, htyR⟩ := hBI _ _ I.var hd1 s1 (tOuts_length _ _ _ _ _ _) hcO hO
    rw [map_subst_var] at htyR
    refine RE2.expandH hW s1 hty htyR fun k4 σ => ?_
    have Hσ := H.isubH hH hyp (forall2_ieq_refl rs) σ
    have hclq : a.closedB (q.toList.length + X.length) rs.length = true := by rw [hql, hXl, hrsl]; exact hcl
    have hclP : a.closedB ((PL.dinst .one).toList.length + (tOuts d D C PL φ X).length) rs.length = true := by
      rw [hPlen1, tOuts_length, hrsl]; exact hcl
    have eT : (Tm.transp (.data d PL) φ (Ctor.bndAt a q.toList X rs)).isub σ =
        .transp (.data d (PL.isub σ.up)) (φ.subst σ.τ)
          (Ctor.bndAt a (q.isub σ).toList (X.map (·.isub σ)) (rs.map (·.subst σ.τ))) := by
      show Tm.transp (Tm.data d (PL.isub σ.up)) (φ.subst σ.τ) ((Ctor.bndAt a q.toList X rs).isub σ) = _
      rw [bndAt_isubL hqL hclq σ]
    have eR : (Ctor.bndAt a (PL.dinst .one).toList (tOuts d D C PL φ X) rs).isub σ =
        Ctor.bndAt a ((PL.isub σ.up).dinst .one).toList (tOuts d D C (PL.isub σ.up) (φ.subst σ.τ) (X.map (·.isub σ)))
          (rs.map (·.subst σ.τ)) := by
      rw [bndAt_isubL hPl1 hclP σ, tOuts_isub hW hD hC hPl hPlen hXl σ, isub_dinst]; rfl
    have eA : (Tm.data d (PL.dinst .one)).isub σ = .data d ((PL.isub σ.up).dinst .one) := by
      show Tm.data d ((PL.dinst .one).isub σ) = _; rw [isub_dinst]; rfl
    have htyσ := HasTy.isubS hW hty σ
    rw [eT, eA] at htyσ
    obtain ⟨u, hr, he, hu⟩ := BT_at hW hD hH hyp hC ihc a hs hcl (fun a' h hs' hcl' => ihN a' (by omega) hs' hcl') Hσ
      (BI_isub hBI σ.τ) htyσ
    exact ⟨u, by rw [eT]; exact hr, by rw [eT, eA]; exact he, by rw [eA, eR]; exact hu⟩
  exact fun a hs hcl => key _ a (Nat.lt_succ_self _) hs hcl

end bt

end

end Model.Whnf
