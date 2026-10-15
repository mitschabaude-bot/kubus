import Model.Whnf.Valid2ElimH17
import Model.Whnf.Valid2ElimHInv

/-! # Recursive arguments and constructor computation from eliminator inversion -/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S S' : Sig} {k : ℕ} (hW : WfSig S)
include hW

omit hW in
/-- A valid recursive constructor argument is valid in the declared data type. -/
theorem VTele2.recArg {Ψ : ℕ} {Φ : I} {Γ : Ctx} {d np : ℕ} {C : Ctor} {ps args : Tm}
    (hp : IsList ps) (hpl : ps.toList.length = np) (hal : args.toList.length = C.args.length)
    (hv : VTele2 S Ψ Φ Γ args args (C.argTys d np) ps.toList.reverse) {j : ℕ} (hj : j ∈ C.recPos) :
    Valid2 S Ψ Φ Γ (args.toList.getD j .abort) (args.toList.getD j .abort) (.data d ps) := by
  obtain ⟨hjn, hr⟩ := mem_recPos hj
  have hi : j < args.toList.length := by omega
  have h := VTele2.get hv j hi hi (by simp [Ctor.argTys]; exact hjn)
  simp only [Ctor.argTys, List.getElem_map, List.getElem_range] at h
  rw [argTy_rec_inst hr hp hpl (by simp; omega)] at h
  simpa only [getD_eq_get' hi] using h

/-- The formation field supplies computable recursive eliminations for constructor computation. -/
theorem ElimInv2.recElims (hDa : DataHyp2 S S') {Ψ : ℕ} {Φ : I} {Γ : Ctx}
    {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hD' : S'[d]? = some (.data D))
    (hH : D.isHIT = true) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C)
    {ps P bs t T args : Tm} (htele : HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse)
    (hv : VTele2 S Ψ Φ Γ args args (C.argTys d D.params.length) ps.toList.reverse)
    (h : ElimInv2 S Ψ Φ Γ d ps P bs t T) :
    ∀ j, j ∈ C.recPos → Valid2 S Ψ Φ Γ (.elim d ps P bs (args.toList.getD j .abort))
      (.elim d ps P bs (args.toList.getD j .abort)) (P.inst (args.toList.getD j .abort)) := by
  obtain ⟨D0, m, hd, hp, hpt, hvp, hvd, hpm, hvm, hbs, hl, hbr, hbd, ht, htr⟩ := h
  rw [hD] at hd; cases hd
  obtain ⟨D1, m1, hE, -⟩ := gen_elimP ht rfl
  have he := hE.hD
  rw [hD] at he; cases he
  have hpl := Meta.tele_length hpt
  have hal := Meta.tele_length htele
  simp only [Ctor.argTys, List.length_map, List.length_range] at hal
  intro j hj
  exact hDa.elim hD' hH hp hE.hdata hpt hpm hbs hl hE.hbr hE.hcoh
    (recArg_typed hp hpl htele hj) hvd hvp hvm hbr hbd (VTele2.recArg hp hpl hal hv hj)

/-- Closing a valid constructor telescope gives the argument relation of its literal data type. -/
theorem VTele2.ctorArgs {Ψ : ℕ} {Φ : I} {Γ : Ctx} {d : ℕ} {D : DataDecl}
    (hD : S[d]? = some (.data D)) {cc : ℕ} {C : Ctor} (hC : D.ctors[cc]? = some C)
    {ps args : Tm} (hp : IsList ps) (hpl : ps.toList.length = D.params.length)
    (hal : args.toList.length = C.args.length)
    (hv : VTele2 S Ψ Φ Γ args args (C.argTys d D.params.length) ps.toList.reverse)
    (c : CSub2 S Ψ Φ Γ k) :
    ∀ i (_hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
      (((args.toList.map c.L).take i).reverse ++ (c.L ps).toList.reverse))
      ((args.toList.map c.L).getD i .abort) ((args.toList.map c.R).getD i .abort) := by
  intro i hi
  have hin : i < args.toList.length := by omega
  have h := (VTele2.get hv i hin hin (by simp [Ctor.argTys]; exact hi) k c).2
  simp only [Ctor.argTys, List.getElem_map, List.getElem_range] at h
  have hcl : (C.argTy d D.params.length i).closedB ((args.toList.take i).reverse ++ ps.toList.reverse).length 0 = true := by
    simp only [List.length_append, List.length_reverse, List.length_take, hpl, Nat.min_eq_left hin.le]
    rw [Nat.add_comm]
    exact argTy_closed hW hD hC i
  have e : c.L ((C.argTy d D.params.length i).substList ((args.toList.take i).reverse ++ ps.toList.reverse)) =
      (C.argTy d D.params.length i).substList (((args.toList.map c.L).take i).reverse ++ (c.L ps).toList.reverse) := by
    show ((C.argTy d D.params.length i).substList _).subst c.γ c.σ.τ = _
    rw [substList_subst hcl, List.map_append, List.map_reverse, List.map_reverse, List.map_take, ← toList_subst hp]
  rw [e] at h
  simpa only [getD_eq_get' (show i < (args.toList.map c.L).length by simp; omega),
    getD_eq_get' (show i < (args.toList.map c.R).length by simp; omega), List.getElem_map] using h

/-- HIT constructor computation follows from formation and structural eliminator inversion. -/
theorem valid_elimConH (hDa : DataHyp2 S S') {Ψ : ℕ} {Φ : I} {Γ : Ctx}
    {d cc : ℕ} {D : DataDecl} {C : Ctor} (hD : S[d]? = some (.data D)) (hD' : S'[d]? = some (.data D))
    (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1)) (hC : D.ctors[cc]? = some C)
    {ps P bs b qs args T : Tm} {rs : List I} (hb : bs.toList[cc]? = some b)
    (hal : IsList args) (htele : HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse)
    (hva : VTele2 S Ψ Φ Γ args args (C.argTys d D.params.length) ps.toList.reverse)
    (hinv : ElimInv2 S Ψ Φ Γ d ps P bs (.con d cc qs args rs) T)
    (hv : Valid2 S Ψ Φ Γ (.elim d ps P bs (.con d cc qs args rs))
      (.elim d ps P bs (.con d cc qs args rs)) T) :
    Valid2 S Ψ Φ Γ (.elim d ps P bs (.con d cc qs args rs))
      (Tm.papps (Tm.apps b (args.toList ++ C.recPos.map fun j => .elim d ps P bs (args.toList.getD j .abort))) rs) T := by
  have hr := ElimInv2.recElims hW hDa hD hD' hH hC htele hva hinv
  obtain ⟨D0, m, hd, hp, hpt, hvp, hvd, hpm, hvm, hbs, hlen, hbr, hbd, hnat, htr⟩ := hinv
  rw [hD] at hd; cases hd
  obtain ⟨D1, m1, hE, hx⟩ := gen_elimP hnat rfl
  have he := hE.hD
  rw [hD] at he; cases he
  have hpl := Meta.tele_length hpt
  have hargslen := Meta.tele_length htele
  simp only [Ctor.argTys, List.length_map, List.length_range] at hargslen
  intro k c
  refine ⟨(hv k c).1, ?_⟩
  let ML := P.subst (Tm.up c.γ) c.σ.τ
  let MR := P.subst (Tm.up c.γ') c.σ'.τ
  let XL := args.toList.map c.L
  let XR := args.toList.map c.R
  have eXL : c.L args = Tm.ofList XL := by
    show args.subst c.γ c.σ.τ = _
    conv_lhs => rw [hal]
    exact ofList_subst _ _ _
  have eXR : c.R args = Tm.ofList XR := by
    show args.subst c.γ' c.σ'.τ = _
    conv_lhs => rw [hal]
    exact ofList_subst _ _ _
  have hPL : HasTy S k .one [] (.data d (c.L ps)) (.univ D.level) := c.ty hW hE.hdata
  have hAA : RT2 S k (.data d (c.L ps)) (.data d (c.L ps)) := hvd.ty hW (c.diagL hW)
  have hRL : ElimRelH S d D k (c.L ps) ML (c.L bs) (c.L ps) ML (c.L bs) := elimRelH_of hW hD hnat hnat hvd hvm
    (fun cc C b b' hc hb hb' => by rw [hb] at hb'; cases hb'; exact hbr cc C b hc hb) (c.diagL hW)
  have hR : ElimRelH S d D k (c.L ps) ML (c.L bs) (c.R ps) MR (c.R bs) := elimRelH_of hW hD hnat hnat hvd hvm
    (fun cc C b b' hc hb hb' => by rw [hb] at hb'; cases hb'; exact hbr cc C b hc hb) c
  have hB : ElimBndRel2 S d D k (c.L ps) ML (c.L bs) := elimBndRel_of hW hD hp hpt hbs hlen hbr hbd (c.diagL hW)
  have hcl := closed_of_ty hW (c.ty hW hnat)
  change ((c.L ps).closedB 0 k && ML.closedB 1 k && (c.L bs).closedB 0 k &&
    (c.L (.con d cc qs args rs)).closedB 0 k) = true at hcl
  simp only [Bool.and_eq_true] at hcl
  have hcr := closed_of_ty hW (c.tyR hW hnat)
  change ((c.R ps).closedB 0 k && MR.closedB 1 k && (c.R bs).closedB 0 k &&
    (c.R (.con d cc qs args rs)).closedB 0 k) = true at hcr
  simp only [Bool.and_eq_true] at hcr
  have ep := isub_id_of_closed hcl.1.1.1
  have em := isub_id_of_closed hcl.1.1.2
  have eb := isub_id_of_closed hcl.1.2
  have eqp := isub_id_of_closed hcr.1.1.1
  have eqm := isub_id_of_closed hcr.1.1.2
  have eqb := isub_id_of_closed hcr.1.2
  have hct : HasTy S k .one [] (.con d cc (c.L qs) (Tm.ofList XL) (rs.map (·.subst c.σ.τ)))
      (.data d (c.L ps)) := by
    have h := c.ty hW hx
    change HasTy S k .one [] (.con d cc (c.L qs) (c.L args) (rs.map (·.subst c.σ.τ))) (.data d (c.L ps)) at h
    rwa [eXL] at h
  have hct' : HasTy S k .one [] (.con d cc (c.R qs) (Tm.ofList XR) (rs.map (·.subst c.σ'.τ)))
      (.data d (c.L ps)) := by
    have h := c.tyR' hW hx
    change HasTy S k .one [] (.con d cc (c.R qs) (c.R args) (rs.map (·.subst c.σ'.τ))) (.data d (c.L ps)) at h
    rwa [eXR] at h
  have ha := VTele2.ctorArgs hW hD hC hp hpl hargslen hva c
  have haL := VTele2.ctorArgs hW hD hC hp hpl hargslen hva (c.diagL hW)
  have hiAt : ∀ (c0 : CSub2 S Ψ Φ Γ k) j, j ∈ C.recPos →
      RE2 S k ((P.subst (Tm.up c0.γ) c0.σ.τ).inst ((args.toList.map c0.L).getD j .abort))
        (.elim d (c0.L ps) (P.subst (Tm.up c0.γ) c0.σ.τ) (c0.L bs) ((args.toList.map c0.L).getD j .abort))
        (.elim d (c0.R ps) (P.subst (Tm.up c0.γ') c0.σ'.τ) (c0.R bs) ((args.toList.map c0.R).getD j .abort)) := by
    intro c0 j hj
    have R := (hr j hj k c0).2
    change RE2 S k ((P.inst (args.toList.getD j .abort)).subst c0.γ c0.σ.τ) _ _ at R
    rw [inst_subst] at R
    simpa only [CSub2.L, CSub2.R, getD_map_abort] using R
  have comp := elimCon_compH hW hD hH hyp hPL hAA hRL hB cc (ISub.id k) hC
    (by rw [ep]; exact hct) (by intro i hi; rw [ep]; exact haL i hi)
    (by intro j hj; rw [ep, em, eb]; exact hiAt (c.diagL hW) j hj)
  rw [ep, em, eb] at comp
  have CI := con_inv hW hD hC hct hPL
  have CI' := con_inv hW hD hC hct' hPL
  have hbranch := hR.br k (ISub.id k) cc C hC
  rw [ep, em, eb, eqb] at hbranch
  have hrs : IEqL (rs.map (·.subst c.σ.τ)) (rs.map (·.subst c.σ'.τ)) := by
    apply ieqL_iff.2
    have key : ∀ L : List I, List.Forall₂ I.Eq (L.map (·.subst c.σ.τ)) (L.map (·.subst c.σ'.τ)) := by
      intro L
      induction L with
      | nil => exact .nil
      | cons r L ih => exact .cons (c.ieq_subst (I_eq_refl r)) ih
    exact key rs
  have pair := elimCon_relH hW hD hC (by
    have h := data_len_of hW (⟨_, .inl hPL⟩ : IsTyK S k (.data d (c.L ps)))
    rwa [dataD_eq hW hD] at h) hbranch (by simp [XL, hargslen]) (by simp [XR, hargslen])
    (fun i hi hi' => by
      have R := ha i (by simpa only [XL, List.length_map, hargslen] using hi)
      change RE2 S k _ (XL.getD i .abort) (XR.getD i .abort) at R
      simpa only [XL, XR, getD_eq_get' hi, getD_eq_get' hi'] using R)
    (hiAt c) CI.2.2.2.1 hrs CI.2.2.2.2.1 CI'.2.2.2.2.1
  have cr := con_rel hW hD hPL hAA hH hyp cc (ISub.id k) hC
    (by rw [ep]; exact CI.2.2.2.2.2.2.1) (by rw [ep]; exact hct) (forall2_ieq_refl _) (by
      intro i hi; rw [ep]; exact haL i hi)
  have TmRel := hRL.mot k (ISub.id k) _ _ cr
  rw [em] at TmRel
  have crS := con_rel hW hD hPL hAA hH hyp cc (ISub.id k) hC
    (by rw [ep]; exact hct) (by rw [ep]; exact hct) (forall2_ieq_refl _) (by intro i hi; rw [ep]; exact haL i hi)
  have TSelf := hRL.mot k (ISub.id k) _ _ crS
  rw [em] at TSelf
  have r := RE2.trans hW TSelf comp (RE2.conv hW TmRel pair)
  have hbL : (c.L bs).toList.getD cc .abort = c.L b := by
    show (bs.subst c.γ c.σ.τ).toList.getD cc .abort = _
    rw [toList_subst hbs]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, hb]
  have hbR : (c.R bs).toList.getD cc .abort = c.R b := by
    show (bs.subst c.γ' c.σ'.τ).toList.getD cc .abort = _
    rw [toList_subst hbs]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, hb]
  change RE2 S k (c.L T) (c.L (.elim d ps P bs (.con d cc qs args rs)))
    (c.R (Tm.papps (Tm.apps b (args.toList ++ C.recPos.map fun j => .elim d ps P bs (args.toList.getD j .abort))) rs))
  apply htr k c
  change RE2 S k ((P.inst (.con d cc qs args rs)).subst c.γ c.σ.τ) _ _
  rw [inst_subst]
  change RE2 S k (ML.inst (.con d cc (c.L qs) (c.L args) (rs.map (·.subst c.σ.τ))))
    (.elim d (c.L ps) ML (c.L bs) (.con d cc (c.L qs) (c.L args) (rs.map (·.subst c.σ.τ)))) _
  rw [eXL]
  show RE2 S k _ _ ((Tm.papps (Tm.apps b (args.toList ++ C.recPos.map fun j => .elim d ps P bs (args.toList.getD j .abort))) rs).subst c.γ' c.σ'.τ)
  rw [elimCon_subst hal, toList_subst hal]
  simpa only [ecTm, ihsOf, hbR, XL, XR, ML, MR] using r

end

end Model.Whnf
