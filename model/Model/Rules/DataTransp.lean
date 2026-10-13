import Model.Rules.Data

/-!
# Transport of constructors (`transpCon`)

The right-hand side transports the arguments one by one along their type lines, whose earlier
arguments are the transport fillers of the earlier arguments (`Tm.transpTele`). In the model
these are the output and filler lists of the transport relation `TR` of the constructor value.
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore KubusCore.Tm

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

/-- The transport fillers of the first `j` arguments in `Tm.transpTele` (most recent first). -/
def tFills (argTy : ℕ → Tm) (psL : List Tm) (φ : I) (args : List Tm) : ℕ → List Tm
  | 0 => []
  | j + 1 => Tm.transpFill ((argTy j).substList (tFills argTy psL φ args j ++ psL.reverse)) φ (args.getD j .abort) ::
      tFills argTy psL φ args j

theorem tFills_length (argTy : ℕ → Tm) (psL : List Tm) (φ : I) (args : List Tm) :
    ∀ j, (tFills argTy psL φ args j).length = j
  | 0 => rfl
  | j + 1 => by simp [tFills, tFills_length argTy psL φ args j]

theorem transpTele_eq (argTy : ℕ → Tm) (psL : List Tm) (φ : I) (args : List Tm) :
    ∀ N k, args.length - k = N → k ≤ args.length →
      Tm.transpTele argTy psL φ k (tFills argTy psL φ args k) (args.drop k) =
        (List.range' k N).map fun j => Tm.transp ((argTy j).substList (tFills argTy psL φ args j ++ psL.reverse)) φ
          (args.getD j .abort)
  | 0, k, hN, hk => by
    rw [List.drop_of_length_le (by omega)]; rfl
  | N + 1, k, hN, hk => by
    rw [List.drop_eq_getElem_cons (by omega), Tm.transpTele, List.range'_succ, List.map_cons]
    have e : args.getD k .abort = args[k]'(by omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    rw [e]
    congr 1
    have := transpTele_eq argTy psL φ args N (k + 1) (by omega) (by omega)
    rw [← this, tFills, e]

theorem transpTele_eq0 (argTy : ℕ → Tm) (psL : List Tm) (φ : I) (args : List Tm) :
    Tm.transpTele argTy psL φ 0 [] args =
      (List.range args.length).map fun j => Tm.transp ((argTy j).substList (tFills argTy psL φ args j ++ psL.reverse)) φ
        (args.getD j .abort) := by
  have := transpTele_eq argTy psL φ args args.length 0 (by omega) (by omega)
  rw [List.drop_zero] at this
  rw [List.range_eq_range', ← this]; rfl

/-- Parameters at an endpoint of a parameter line. -/
theorem psRV_endpt (t : Tm) (ρ : IEnv m) (γ : ℕ → V) (e : I) :
    psRV S (t.dinst e) m ρ γ = fun k f => psRV S t (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) k
      ((Hom.endpt m (ival ρ e)).comp f) := by
  funext k f
  simp only [psRV]
  rw [sem_dinst, ← IEnv.restr_restr, IEnv.ext_restr_endpt, IEnv.cons_restr, TEnv.restr_restr,
    ← Hom.comp_assoc, Hom.wk_comp_endpt, Hom.id_comp, ival.restr]

theorem dinst_ofList (ps : Tm) (hpl : ps = Tm.ofList ps.toList) (e : I) :
    ps.dinst e = Tm.ofList (ps.dinst e).toList := by
  have h1 : ps.dinst e = Tm.ofList (ps.toList.map (·.dinst e)) := by
    conv_lhs => rw [hpl]
    exact Tm.subst_ofList _ _ _
  rw [h1, toList_ofList_eq]

theorem sem_EqTm_transpCon {Ψ Φ Γ d D c C ps φ qs args rs T} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : D.params ≠ []) (h2 : D.ctors[c]? = some C)
    (hpl : ps = Tm.ofList ps.toList) (hal : args = Tm.ofList args.toList)
    (hat : SemTele S Ψ Φ Γ args (C.argTys d D.params.length) (ps.dinst .zero).toList.reverse)
    (h3 : SemTy S Ψ Φ Γ (transp (data d ps) φ (con d c qs args rs)) T) :
    SemEq S Ψ Φ Γ (transp (data d ps) φ (con d c qs args rs))
      (con d c (ps.dinst .one)
        (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs) T := by
  set np := D.params.length
  set Lt : ℕ → Tm := fun j => (C.argTy d np j).substList (tFills (C.argTy d np) ps.toList φ args.toList j ++
    ps.toList.reverse) with hLt
  have hcl : (con d c (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d np) ps.toList φ 0 [] args.toList)) rs).ConstsLt S.length := by
    obtain ⟨⟨hdl, hpc⟩, -, -, hac⟩ := h3.2.1
    have hsubL : ∀ (L : List Tm) (t : Tm), t.ConstsLt S.length → (∀ x ∈ L, x.ConstsLt S.length) →
        (t.substList L).ConstsLt S.length := by
      intro L t ht hL
      refine ht.subst (fun x => ?_) _
      rw [List.getD_eq_getElem?_getD]
      cases hx : L[x]? with
      | none => trivial
      | some y => exact hL y (List.mem_of_getElem? hx)
    have hgetD : ∀ j, (args.toList.getD j .abort).ConstsLt S.length := by
      intro j
      rw [List.getD_eq_getElem?_getD]
      cases hx : args.toList[j]? with
      | none => trivial
      | some y => exact Tm.ConstsLt.toList_mem hac y (List.mem_of_getElem? hx)
    have hargTy : ∀ j, (C.argTy d np j).ConstsLt S.length := by
      intro j
      unfold Ctor.argTy
      split
      · rename_i A hA
        exact ((hS.2 d D h0).1.2.2.1 c C h2 j A hA).2.1.mono (by omega)
      · exact ⟨hdl, constsLt_ofList fun t ht => by obtain ⟨_, -, rfl⟩ := List.mem_map.1 ht; trivial⟩
    have hpsC : ∀ x ∈ ps.toList.reverse, x.ConstsLt S.length := fun x hx =>
      Tm.ConstsLt.toList_mem hpc x (List.mem_reverse.1 hx)
    have hfills : ∀ j, ∀ t ∈ tFills (C.argTy d np) ps.toList φ args.toList j, t.ConstsLt S.length := by
      intro j
      induction j with
      | zero => intro t ht; simp [tFills] at ht
      | succ j ih =>
        intro t ht
        simp only [tFills, List.mem_cons] at ht
        rcases ht with rfl | ht
        · refine ⟨(hsubL _ _ (hargTy j) fun x hx => ?_).dsubst _, (hgetD j).ren _ _⟩
          rcases List.mem_append.1 hx with hx | hx
          · exact ih x hx
          · exact hpsC x hx
        · exact ih t ht
    refine ⟨hdl, hpc.dsubst _, constsLt_ofList fun t ht => ?_⟩
    rw [transpTele_eq0] at ht
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 ht
    refine ⟨hsubL _ _ (hargTy j) fun x hx => ?_, hgetD j⟩
    rcases List.mem_append.1 hx with hx | hx
    · exact hfills j x hx
    · exact hpsC x hx
  have he : ∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ →
      sem S (con d c (ps.dinst .one)
        (Tm.ofList (Tm.transpTele (C.argTy d np) ps.toList φ 0 [] args.toList)) rs) m ρ γ =
      sem S (transp (data d ps) φ (con d c qs args rs)) m ρ γ := by
    intro m ρ γ hp
    obtain ⟨hmem, -, hty, -⟩ := h3.2.2.2 m ρ γ hp
    have hcT := cond_of_sem_transp (hty.ne_empty hmem)
    obtain ⟨hLty, hconst, hVmem, hLN, hVnat⟩ := id hcT
    have hok := hS.2 d D h0
    have hpL := paramsOK_of_code h0 hLty
    set ΘL := dataSD (sigUpTo S d) D d (m + 1) (psRV S ps (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))) with hΘL
    have hLd : lineV S (data d ps) m ρ γ = dataC ΘL := sem_data_of h0 hpL
    have hgL := (hok.2 _ _ hpL).1
    have hpar : ΘL.params = true := by simp [hΘL, dataSD, h1]
    have hF := isCof_ival_face ρ φ
    have hconst' : ConstOn (dataC ΘL) (Hom.id (m + 1)) (ival ρ φ).face := hLd ▸ hconst
    have hgC : ΘL.ctors.getD c default = C := getD_ctors h2
    -- the arguments, typed at the start of the line
    have hp0 := psRV_endpt (S := S) ps ρ γ .zero
    rw [ival_zero] at hp0
    have hpok0 : ParamsOK (sigUpTo S d) D m (psRV S (ps.dinst .zero) m ρ γ) := by
      rw [hp0]; exact hpL.restr _
    obtain ⟨hatv, hnat, hlen⟩ := tele_argsTyped hS h0 h2 (dinst_ofList ps hpl .zero) hat hp hpok0
    set vals := args.toList.map fun t => sem S t m ρ γ with hvals
    have hvl : vals.length = C.args.length := by simp [vals, hlen]
    have hta : ΘL.ArgsTyped c C m ((Hom.id (m + 1)).comp (Hom.endpt m (DM.zero m))) vals := by
      rw [hp0, dataSD_restr', argsTyped_restr_iff, Hom.comp_id] at hatv
      rwa [Hom.id_comp]
    have hkv : ∀ a ∈ vals, IsKV m a := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      cases hr : C.isRec j
      · have hPV : ΘL.PtValid c m ((Hom.id (m + 1)).comp (Hom.endpt m (DM.zero m))) vals := by
          have := SData.ptValid_take h2 hta.2.2 vals.length; rwa [List.take_length] at this
        exact hgL.pt_kv hPV hj (by rw [hgC]; exact hr)
      · exact (hta.2.1 j _ (List.getElem?_eq_getElem hj) hr).kv
    -- the outputs and fillers of the transport
    obtain ⟨outs, fills, hlo, hlf, hro, hrf, hpt⟩ := exists_outs_fills ΘL c m (Hom.id (m + 1)) (ival ρ φ).face vals
      (fun j hj hr => by
        rw [hgC] at hr
        have hd := hta.2.1 j _ (List.getElem?_eq_getElem hj) hr
        refine ⟨hd.tr_exists hgL _, ?_⟩
        have hd' := hd.res hgL.resClosed (m + 1) (Hom.wk m)
        rw [Hom.comp_assoc, ← tfLine_endpt0, ← Hom.comp_assoc] at hd'
        exact hd'.tr_exists hgL _)
    have iho : ∀ j (hj : j < vals.length), (ΘL.ctors.getD c default).isRec j = true →
        TRProps ΘL m (Hom.id (m + 1)) (ival ρ φ).face vals[j] (outs.getD j ∅) :=
      fun j hj hr => (hro j hj hr).props hgL
    have ihf : ∀ j (hj : j < vals.length), (ΘL.ctors.getD c default).isRec j = true →
        TRProps ΘL (m + 1) ((Hom.id (m + 1)).comp (tfLine m)) (fillFace (ival ρ φ).face)
          (res (Hom.wk m) vals[j]) (fills.getD j ∅) :=
      fun j hj hr => (hrf j hj hr).props hgL
    have hfacts : ∀ {j : ℕ} (hj : j < vals.length), _ := fun {j} hj =>
      con_point_facts hgL hkv hlo hlf hro hpt iho ihf hF hconst' h2 hta hj
    have hfpv := fills_ptValid hgL hkv hlo hlf hro hpt iho ihf hF hconst' h2 hta
    have hto := con_outs_typed hgL hkv hlo hlf hro hpt iho ihf hF hconst' h2 hta
    set γL := TEnv.restr γ (Hom.wk m) with hγL
    have hkvL : ∀ x, IsKV (m + 1) (γL x) := fun x => isKV_res _ _
    have hpsl : ps.toList.length = np := by
      have h1' := (hpL (m + 1) (Hom.id (m + 1))).1
      simp only [psRV, IEnv.restr_id, TEnv.restr_id_of_kv hkvL] at h1'
      rw [hpl] at h1'
      exact listLen_unique (listLen_sem_ofList _ _ _) h1'
    have hpsnat := psnat_of_paramsOK hpl hpsl hkvL hpL
    have htfl : ∀ j, (tFills (C.argTy d np) ps.toList φ args.toList j).length = j := tFills_length _ _ _ _
    have hlvl : D.level ≤ maxLevel := by have := hok.1.1; omega
    -- one argument, given the fillers of the earlier ones
    have hone : ∀ j (hj : j < vals.length),
        ((tFills (C.argTy d np) ps.toList φ args.toList j).reverse.map fun t => sem S t (m + 1) ρ.ext γL) =
          fills.take j →
        (∀ t ∈ tFills (C.argTy d np) ps.toList φ args.toList j, Natural S t (m + 1) ρ.ext γL) →
        sem S (transp (Lt j) φ (args.toList.getD j .abort)) m ρ γ = outs.getD j ∅ ∧
        sem S (Tm.transpFill (Lt j) φ (args.toList.getD j .abort)) (m + 1) ρ.ext γL = fills.getD j ∅ ∧
        Natural S (Tm.transpFill (Lt j) φ (args.toList.getD j .abort)) (m + 1) ρ.ext γL := by
      intro j hj hfv hfn
      have hjl : j < args.toList.length := by simpa [vals] using hj
      have ha : args.toList.getD j .abort = args.toList[j] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]; rfl
      have hav : sem S (args.toList.getD j .abort) m ρ γ = vals[j] := by rw [ha]; simp [vals]
      have hanat : Natural S (args.toList.getD j .abort) m ρ γ := by rw [ha]; exact hnat _ (List.getElem_mem _)
      have hjC : j < C.args.length := by omega
      by_cases hr : C.isRec j = true
      · have hr' : (ΘL.ctors.getD c default).isRec j = true := by rw [hgC]; exact hr
        have hLtd : Lt j = data d ps := by
          have harg : C.argTy d np j = .data d (Ctor.paramVars np j) := by
            cases h' : C.args[j]'hjC with
            | point A => simp [Ctor.isRec, List.getElem?_eq_getElem hjC, h'] at hr
            | recur => simp [Ctor.argTy, List.getElem?_eq_getElem hjC, h']
          simp only [hLt, harg]
          rw [Tm.substList, show (Tm.data d (Ctor.paramVars np j)).subst _ I.var =
            Tm.data d ((Ctor.paramVars np j).substList
              (tFills (C.argTy d np) ps.toList φ args.toList j ++ ps.toList.reverse)) from rfl]
          have e := paramVars_substList ps.toList (tFills (C.argTy d np) ps.toList φ args.toList j)
          rw [hpsl, htfl] at e
          rw [e, ← hpl]
        have hd := hta.2.1 j _ (List.getElem?_eq_getElem hj) hr
        have tc : TranspCond S (Lt j) φ (args.toList.getD j .abort) m ρ γ := by
          rw [hLtd]
          refine ⟨hLty, hconst, ?_, hLN, hanat⟩
          rw [hav, hLd, mem_El_dataC]; exact hd
        obtain ⟨tc', hfill⟩ := transpFill_cond tc
        refine ⟨?_, ?_, tc'.natural⟩
        · rw [sem_transp tc, hav, hLtd, hLd]
          exact (transpAt_dataC_eq hgL (mem_El_dataC.2 hd)).2 hpar _ (hro j hj hr')
        · rw [hfill, hav, hLtd, hLd, transpFillF]
          have hd' := hd.res hgL.resClosed (m + 1) (Hom.wk m)
          rw [Hom.comp_assoc, ← tfLine_endpt0, ← Hom.comp_assoc] at hd'
          exact (transpAt_dataC_eq hgL (mem_El_dataC.2 hd')).2 hpar _ (hrf j hj hr')
      · have hr0 : C.isRec j = false := by simpa using hr
        have hr' : (ΘL.ctors.getD c default).isRec j = false := by rw [hgC]; exact hr0
        obtain ⟨A, hA⟩ : ∃ A, C.args[j]? = some (.point A) := by
          cases h' : C.args[j]'hjC with
          | point A => exact ⟨A, by rw [List.getElem?_eq_getElem hjC, h']⟩
          | recur => simp [Ctor.isRec, List.getElem?_eq_getElem hjC, h'] at hr0
        have hpvj : ΘL.PtValid c (m + 1) (Hom.id (m + 1)) (fills.take j) := hfpv.take j
        have hLtj : ∀ k' (g' : Hom k' (m + 1)), sem S (Lt j) k' (ρ.ext.restr g') (TEnv.restr γL g') =
            ΘL.ty c j k' g' ((fills.take j).map (res g')) := by
          intro k' g'
          have hkv' : ∀ x, IsKV k' (TEnv.restr γL g' x) := fun x => isKV_res _ _
          rw [show Lt j = (A.substList (tFills (C.argTy d np) ps.toList φ args.toList j ++ ps.toList.reverse)) by
            simp [hLt, Ctor.argTy, hA]]
          rw [sem_argTy_subst h0 hok.1 h2 hA _ ps.toList (htfl j) hpsl (fun t ht => by
            rcases List.mem_append.1 ht with ht | ht
            · exact (hfn t ht).restr g'
            · exact (hpsnat t (List.mem_reverse.1 ht)).restr g')]
          have e1 : ((tFills (C.argTy d np) ps.toList φ args.toList j).reverse.map
              fun t => sem S t k' (ρ.ext.restr g') (TEnv.restr γL g')) = (fills.take j).map (res g') := by
            rw [← hfv, List.map_map]
            exact List.map_congr_left fun t ht => hfn t (List.mem_reverse.1 ht) k' g'
          have e2 : sem S (Tm.ofList ps.toList) k' (ρ.ext.restr g') (TEnv.restr γL g') =
              psRV S ps (m + 1) ρ.ext γL k' g' := by rw [← hpl]
          rw [e1, e2]
          show _ = argTySem _ _ _ _ _ _ _ _
          have hpv' : ΘL.PtValid c k' g' ((fills.take j).map (res g')) := by
            have := hgL.ptValid_res hpvj k' g'; rwa [Hom.id_comp] at this
          rw [argTySem_eq, if_pos ⟨by rw [getD_ctors h2]; omega, by rw [getD_ctors h2]; exact hr0,
            ptValid_argPreValid hpv' (j := j) (by rw [List.length_map, List.length_take]; omega)⟩]
        have hline : lineV S (Lt j) m ρ γ = ΘL.ty c j (m + 1) (Hom.id (m + 1)) (fills.take j) := by
          show sem S (Lt j) (m + 1) ρ.ext γL = _
          rw [show Lt j = (A.substList (tFills (C.argTy d np) ps.toList φ args.toList j ++ ps.toList.reverse)) by
            simp [hLt, Ctor.argTy, hA]]
          rw [sem_argTy_subst h0 hok.1 h2 hA _ ps.toList (htfl j) hpsl (fun t ht => by
            rcases List.mem_append.1 ht with ht | ht
            · exact hfn t ht
            · exact hpsnat t (List.mem_reverse.1 ht)), hfv]
          have e2 : sem S (Tm.ofList ps.toList) (m + 1) ρ.ext γL = psRV S ps (m + 1) ρ.ext γL (m + 1) (Hom.id (m + 1)) := by
            rw [← hpl]; simp only [psRV, IEnv.restr_id, TEnv.restr_id_of_kv hkvL]
          rw [e2]
          show _ = argTySem _ _ _ _ _ _ _ _
          rw [argTySem_eq, if_pos ⟨by rw [getD_ctors h2]; omega, by rw [getD_ctors h2]; exact hr0,
            ptValid_argPreValid hpvj (j := j) (by rw [List.length_take]; omega)⟩]
        obtain ⟨hfib, hcon, hbase⟩ := hfacts hj
        have tc : TranspCond S (Lt j) φ (args.toList.getD j .abort) m ρ γ := by
          refine ⟨?_, ?_, ?_, fun k' g' => ?_, hanat⟩
          · rw [hline]
            obtain ⟨hV, hW⟩ := (hok.2 (m + 1) _ hpL).2 c j (m + 1) (Hom.id (m + 1)) (fills.take j)
            exact ⟨D.level, hlvl, Or.inl ⟨hW hpvj, hV⟩⟩
          · rw [hline]; exact hcon
          · rw [hline, hav]; exact hbase hr0
          · show _ = res g' (lineV S (Lt j) m ρ γ)
            rw [hLtj, hline, hgL.nat c j (m + 1) _ _ hpvj k' g', Hom.id_comp]
        obtain ⟨tc', hfill⟩ := transpFill_cond tc
        refine ⟨?_, ?_, tc'.natural⟩
        · rw [sem_transp tc, hline, hav]; exact ((hpt j hj hr').1).symm
        · rw [hfill, hline, hav]; exact ((hpt j hj hr').2).symm
    have hall : ∀ j, j ≤ vals.length →
        ((tFills (C.argTy d np) ps.toList φ args.toList j).reverse.map fun t => sem S t (m + 1) ρ.ext γL) =
          fills.take j ∧ (∀ t ∈ tFills (C.argTy d np) ps.toList φ args.toList j, Natural S t (m + 1) ρ.ext γL) := by
      intro j
      induction j with
      | zero => intro _; exact ⟨by simp [tFills], fun t ht => by simp [tFills] at ht⟩
      | succ j ih =>
        intro hj
        obtain ⟨h1', h2'⟩ := ih (by omega)
        obtain ⟨-, hf, hfn⟩ := hone j (by omega) h1' h2'
        refine ⟨?_, fun t ht => ?_⟩
        · simp only [tFills, List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
          rw [h1', List.take_succ, List.getElem?_eq_getElem (by omega)]
          change _ ++ [sem S (Tm.transpFill (Lt j) φ (args.toList.getD j .abort)) (m + 1) ρ.ext γL] = _
          rw [hf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
          rfl
        · simp only [tFills, List.mem_cons] at ht
          rcases ht with rfl | ht
          · exact hfn
          · exact h2' t ht
    have hTv : (Tm.transpTele (C.argTy d np) ps.toList φ 0 [] args.toList).map (fun t => sem S t m ρ γ) = outs := by
      rw [transpTele_eq0, List.map_map]
      apply List.ext_getElem (by simp [hlo, vals])
      intro i h1' h2'
      simp only [List.getElem_map, List.getElem_range, Function.comp, List.length_range] at h1' ⊢
      have hi : i < vals.length := by simpa [vals] using h1'
      change sem S (transp (Lt i) φ (args.toList.getD i .abort)) m ρ γ = _
      rw [(hone i hi (hall i hi.le).1 (hall i hi.le).2).1, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      rfl
    -- the scrutinee
    have hρ : ρ.restr (Hom.id m) = ρ := IEnv.restr_id ρ
    have hγ : TEnv.restr γ (Hom.id m) = γ := TEnv.restr_id_of_kv hp.kv
    have hne : sem S (con d c qs args rs) m ρ γ ≠ ∅ := fun h => by
      rw [h] at hVmem; exact hLty.fib.empty_notMem _ hVmem
    have hcg := conGuard_of_sem h0 hne
    have hplv : plist (psRV S args m ρ γ m (Hom.id m)) C.args.length = vals := by
      simp only [psRV, hρ, hγ]
      rw [hal, sem_ofList_vlist, ← hlen,
        show args.toList.length = (args.toList.map fun t => sem S t m ρ γ).length by simp, plist_vlist]
    have hV : sem S (con d c qs args rs) m ρ γ = conV D.ctors m c vals (rs.map (ival ρ)) := by
      rw [sem_con_of h0 hcg, getD_ctors h2, hplv]
    obtain ⟨C', hC', hrsl, -⟩ := hcg
    rw [h2] at hC'; cases hC'
    have hrs' : (rs.map (ival ρ)).length = C.dims := by simpa using hrsl
    -- the right-hand side
    have hp1 := psRV_endpt (S := S) ps ρ γ .one
    rw [ival_one] at hp1
    have hTl : (Tm.transpTele (C.argTy d np) ps.toList φ 0 [] args.toList).length = C.args.length := by
      rw [← List.length_map (f := fun t => sem S t m ρ γ), hTv, hlo, hvl]
    have hplT : plist (psRV S (Tm.ofList (Tm.transpTele (C.argTy d np) ps.toList φ 0 [] args.toList)) m ρ γ m
        (Hom.id m)) C.args.length = outs := by
      simp only [psRV, hρ, hγ]
      rw [sem_ofList_vlist, hTv, show C.args.length = outs.length by rw [hlo, hvl], plist_vlist]
    have hgR : ConGuard (sigUpTo S d) D d m (psRV S (ps.dinst .one) m ρ γ) c
        (psRV S (Tm.ofList (Tm.transpTele (C.argTy d np) ps.toList φ 0 [] args.toList)) m ρ γ) (rs.map (ival ρ)) := by
      refine ⟨C, h2, hrsl, ?_, by rw [hp1]; exact hpL.restr _, ?_⟩
      · simp only [psRV, hρ, hγ]
        have := listLen_sem_ofList (S := S) (Tm.transpTele (C.argTy d np) ps.toList φ 0 [] args.toList) ρ γ
        rwa [hTl] at this
      · rw [hplT, hp1, dataSD_restr', argsTyped_restr_iff, Hom.comp_id]
        have := hto; rwa [Hom.id_comp] at this
    rw [sem_con_of h0 hgR, getD_ctors h2, hplT]
    -- the left-hand side
    rw [sem_transp hcT, hLd, hV]
    refine ((transpAt_dataC_eq hgL (by rw [← hV, ← hLd]; exact hVmem)).2 hpar _ ?_).symm
    exact tr_conV_any hgL c C h2 m (Hom.id (m + 1)) (ival ρ φ).face vals outs fills (rs.map (ival ρ)) hta hto hkv
      hrs' hlo hlf hfpv (fun j hj hr => hro j hj (by rw [hgC]; exact hr))
      (fun j hj hr => hrf j hj (by rw [hgC]; exact hr)) (fun j hj hr => hpt j hj (by rw [hgC]; exact hr))
  exact ⟨h3, h3.of_eq hcl he, fun m ρ γ hp => (he m ρ γ hp).symm⟩

end

end Model
