import Model.Rules.Inj
import Model.Rules.DataTransp

/-!
# Composition in inductive types without path constructors (`hcompCon`)
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore KubusCore.Tm

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

/-! ### The componentwise composition, syntactically -/

section syn

variable (C : Ctor) (argTy : ℕ → Tm) (dataT : Tm) (psL : List Tm) (φ : I) (us as : List Tm)

/-- The output and the filler of argument `j` in `Tm.hcompTele`, given the fillers of the
earlier arguments (most recent first). -/
def hArg (fills : List Tm) (j : ℕ) : Tm × Tm :=
  if C.isRec j then (hcomp dataT φ (us.getD j .abort) (as.getD j .abort), hfill dataT φ (us.getD j .abort) (as.getD j .abort))
  else (Tm.comp ((argTy j).substList (fills ++ psL.reverse)) φ (us.getD j .abort) (as.getD j .abort),
    Tm.fill ((argTy j).substList (fills ++ psL.reverse)) φ (us.getD j .abort) (as.getD j .abort))

/-- The fillers of the first `j` arguments in `Tm.hcompTele` (most recent first). -/
def hFills : ℕ → List Tm
  | 0 => []
  | j + 1 => (hArg C argTy dataT psL φ us as (hFills j) j).2 :: hFills j

theorem hFills_length : ∀ j, (hFills C argTy dataT psL φ us as j).length = j
  | 0 => rfl
  | j + 1 => by simp [hFills, hFills_length j]

theorem hcompTele_eq (hl : us.length = as.length) : ∀ N k, as.length - k = N → k ≤ as.length →
    Tm.hcompTele C argTy dataT psL φ k (hFills C argTy dataT psL φ us as k) (us.drop k) (as.drop k) =
      (List.range' k N).map fun j => (hArg C argTy dataT psL φ us as (hFills C argTy dataT psL φ us as j) j).1
  | 0, k, hN, hk => by
    rw [List.drop_of_length_le (l := as) (by omega)]
    cases us.drop k <;> rfl
  | N + 1, k, hN, hk => by
    rw [List.drop_eq_getElem_cons (l := us) (by omega), List.drop_eq_getElem_cons (l := as) (by omega), Tm.hcompTele,
      List.range'_succ, List.map_cons]
    have eu : us.getD k .abort = us[k]'(by omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have ea : as.getD k .abort = as[k]'(by omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have ih := hcompTele_eq hl N (k + 1) (by omega) (by omega)
    rw [hFills] at ih
    by_cases hr : C.isRec k = true
    · simp only [hr, if_true]
      simp only [hArg, hr, if_true, eu, ea] at ih ⊢
      rw [ih]
    · simp only [hr, Bool.false_eq_true, if_false]
      simp only [hArg, hr, Bool.false_eq_true, if_false, eu, ea] at ih ⊢
      rw [ih]

theorem hcompTele_eq0 (hl : us.length = as.length) :
    Tm.hcompTele C argTy dataT psL φ 0 [] us as =
      (List.range as.length).map fun j => (hArg C argTy dataT psL φ us as (hFills C argTy dataT psL φ us as j) j).1 := by
  have := hcompTele_eq C argTy dataT psL φ us as hl as.length 0 (by omega) (by omega)
  rw [List.drop_zero, List.drop_zero] at this
  rw [List.range_eq_range', ← this]; rfl

end syn

theorem constsLt_comp {n : ℕ} {L u a : Tm} {ψ : I} (hL : L.ConstsLt n) (hu : u.ConstsLt n) (ha : a.ConstsLt n) :
    (Tm.comp L ψ u a).ConstsLt n :=
  ⟨hL.dinst _, ⟨hL.dsubst _, hu⟩, hL, ha⟩

theorem constsLt_fill {n : ℕ} {L u a : Tm} {ψ : I} (hL : L.ConstsLt n) (hu : u.ConstsLt n) (ha : a.ConstsLt n) :
    (Tm.fill L ψ u a).ConstsLt n :=
  constsLt_comp (hL.dsubst _) ⟨hu.dsubst _, (ha.ren _ _).ren _ _⟩ (ha.ren _ _)

theorem constsLt_hfill {n : ℕ} {A u a : Tm} {ψ : I} (hA : A.ConstsLt n) (hu : u.ConstsLt n) (ha : a.ConstsLt n) :
    (Tm.hfill A ψ u a).ConstsLt n :=
  ⟨hA.ren _ _, ⟨hu.dsubst _, (ha.ren _ _).ren _ _⟩, ha.ren _ _⟩

theorem Tm.ren_ofList (ρ δ : ℕ → ℕ) : ∀ L : List Tm, (Tm.ofList L).ren ρ δ = Tm.ofList (L.map (·.ren ρ δ))
  | [] => rfl
  | t :: L => by simp [Tm.ofList, Tm.ren, Tm.ren_ofList ρ δ L]

theorem dshift_toList (ps : Tm) (hpl : ps = Tm.ofList ps.toList) : ps.dshift.toList = ps.toList.map (·.dshift) := by
  conv_lhs => rw [hpl]
  rw [Tm.dshift, Tm.ren_ofList, toList_ofList_eq]; rfl

theorem sem_EqTm_hcompCon {Ψ Φ Γ d D c C ps φ u qs uargs args T} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : D.isHIT = false) (h2 : D.ctors[c]? = some C) (hpl : ps = Tm.ofList ps.toList)
    (hal : args = Tm.ofList args.toList) (hul : uargs = Tm.ofList uargs.toList)
    (h3 : SemTele S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse)
    (h4 : SemTele S (Ψ + 1) (cof Φ φ).shift Γ.dshift uargs (C.argTys d D.params.length) ps.dshift.toList.reverse)
    (h5 : SemEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift u (con d c ps.dshift uargs []) (data d ps.dshift))
    (_h6 : SemEqTele S Ψ (cof Φ φ) Γ (uargs.dinst .zero) args (C.argTys d D.params.length) ps.toList.reverse)
    (h7 : SemTy S Ψ Φ Γ (hcomp (data d ps) φ u (con d c qs args [])) T) :
    SemEq S Ψ Φ Γ (hcomp (data d ps) φ u (con d c qs args []))
      (con d c ps (Tm.ofList (Tm.hcompTele C (C.argTy d D.params.length) (data d ps) ps.dshift.toList φ 0 []
        uargs.toList args.toList)) []) T := by
  set np := D.params.length with hnp
  have hok := hS.2 d D h0
  have hlenA : args.toList.length = C.args.length := by
    have := h3.toList.1; simpa [Ctor.argTys] using this
  have hlenU : uargs.toList.length = C.args.length := by
    have := h4.toList.1; simpa [Ctor.argTys] using this
  have hlUA : uargs.toList.length = args.toList.length := by rw [hlenU, hlenA]
  have hT0 := hcompTele_eq0 C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList hlUA
  -- the constants of the right-hand side
  have hcl : (con d c ps (Tm.ofList (Tm.hcompTele C (C.argTy d np) (data d ps) ps.dshift.toList φ 0 []
      uargs.toList args.toList)) []).ConstsLt S.length := by
    obtain ⟨⟨hdl, hpc⟩, -, -⟩ := h7.2.1
    have hsubL : ∀ (L : List Tm) (t : Tm), t.ConstsLt S.length → (∀ x ∈ L, x.ConstsLt S.length) →
        (t.substList L).ConstsLt S.length := by
      intro L t ht hL
      refine ht.subst (fun x => ?_) _
      rw [List.getD_eq_getElem?_getD]
      cases hx : L[x]? with
      | none => trivial
      | some y => exact hL y (List.mem_of_getElem? hx)
    have hgetD : ∀ (t : Tm), t.ConstsLt S.length → ∀ j, (t.toList.getD j .abort).ConstsLt S.length := by
      intro t ht j
      rw [List.getD_eq_getElem?_getD]
      cases hx : t.toList[j]? with
      | none => trivial
      | some y => exact Tm.ConstsLt.toList_mem ht y (List.mem_of_getElem? hx)
    have hac := hgetD _ h3.constsLt
    have huc := hgetD _ h4.constsLt
    have hargTy : ∀ j, (C.argTy d np j).ConstsLt S.length := by
      intro j
      unfold Ctor.argTy
      split
      · rename_i A hA
        exact ((hS.2 d D h0).1.2.2.1 c C h2 j A hA).2.1.mono (by omega)
      · exact ⟨hdl, constsLt_ofList fun t ht => by obtain ⟨_, -, rfl⟩ := List.mem_map.1 ht; trivial⟩
    have hpsC : ∀ x ∈ ps.dshift.toList.reverse, x.ConstsLt S.length := fun x hx =>
      Tm.ConstsLt.toList_mem (hpc.ren _ _) x (List.mem_reverse.1 hx)
    have hboth : ∀ j, (∀ t ∈ hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j,
        t.ConstsLt S.length) ∧
        ((hArg C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList
          (hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j) j).1.ConstsLt S.length ∧
         (hArg C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList
          (hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j) j).2.ConstsLt S.length) := by
      intro j
      induction j with
      | zero =>
        refine ⟨fun t ht => by simp [hFills] at ht, ?_⟩
        unfold hArg; split
        · exact ⟨⟨⟨hdl, hpc⟩, huc 0, hac 0⟩, constsLt_hfill ⟨hdl, hpc⟩ (huc 0) (hac 0)⟩
        · refine ⟨constsLt_comp ?_ (huc 0) (hac 0), constsLt_fill ?_ (huc 0) (hac 0)⟩ <;>
            exact hsubL _ _ (hargTy 0) fun x hx => hpsC x (by simpa [hFills] using hx)
      | succ j ih =>
        have hF : ∀ t ∈ hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList (j + 1),
            t.ConstsLt S.length := by
          intro t ht
          simp only [hFills, List.mem_cons] at ht
          rcases ht with rfl | ht
          · exact ih.2.2
          · exact ih.1 t ht
        refine ⟨hF, ?_⟩
        unfold hArg; split
        · exact ⟨⟨⟨hdl, hpc⟩, huc _, hac _⟩, constsLt_hfill ⟨hdl, hpc⟩ (huc _) (hac _)⟩
        · have hL := hsubL _ _ (hargTy (j + 1)) fun x hx => by
            rcases List.mem_append.1 hx with hx | hx
            · exact hF x hx
            · exact hpsC x hx
          exact ⟨constsLt_comp hL (huc _) (hac _), constsLt_fill hL (huc _) (hac _)⟩
    refine ⟨hdl, hpc, constsLt_ofList fun t ht => ?_⟩
    rw [hT0] at ht
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 ht
    exact (hboth j).2.1
  have he : ∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ →
      sem S (con d c ps (Tm.ofList (Tm.hcompTele C (C.argTy d np) (data d ps) ps.dshift.toList φ 0 []
        uargs.toList args.toList)) []) m ρ γ =
      sem S (hcomp (data d ps) φ u (con d c qs args [])) m ρ γ := by
    intro m ρ γ hp
    have hwf : SemWf S Ψ Φ Γ := h7.1
    obtain ⟨hmem, -, hty, -⟩ := h7.2.2.2 m ρ γ hp
    have hcH := cond_of_sem_hcomp (hty.ne_empty hmem)
    obtain ⟨hTy, hTube, hbm, hAn, hbn⟩ := id hcH
    have hpL := paramsOK_of_code h0 hTy
    set Θ := dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ) with hΘ
    have hLd : sem S (data d ps) m ρ γ = dataC Θ := sem_data_of h0 hpL
    have hgL : Θ.Good := (hok.2 _ _ hpL).1
    have hH : Θ.hit = false := h1
    have hgC : Θ.ctors.getD c default = C := getD_ctors h2
    have hF := isCof_ival_face ρ φ
    have hlvl : D.level ≤ maxLevel := by have := hok.1.1; omega
    have hρ : ρ.restr (Hom.id m) = ρ := IEnv.restr_id ρ
    have hγ : TEnv.restr γ (Hom.id m) = γ := TEnv.restr_id_of_kv hp.kv
    -- the base
    obtain ⟨hta, hnat, -⟩ := tele_argsTyped hS h0 h2 hpl h3 hp hpL
    set vals := args.toList.map fun t => sem S t m ρ γ with hvals
    have hvl : vals.length = C.args.length := by simp [vals, hlenA]
    have hkv := argsTyped_kv hgL h2 hta
    have hne : sem S (con d c qs args []) m ρ γ ≠ ∅ := fun h => by
      rw [h] at hbm; exact hTy.fib.empty_notMem _ hbm
    have hcg := conGuard_of_sem h0 hne
    have hplv : plist (psRV S args m ρ γ m (Hom.id m)) C.args.length = vals := by
      simp only [psRV, hρ, hγ]
      rw [hal, sem_ofList_vlist, ← hlenA,
        show args.toList.length = (args.toList.map fun t => sem S t m ρ γ).length by simp, plist_vlist]
    have hV : sem S (con d c qs args []) m ρ γ = conV D.ctors m c vals [] := by
      rw [sem_con_of h0 hcg, getD_ctors h2, hplv]; rfl
    have hu0 : conV D.ctors m c vals [] ∈ El (dataC Θ) (Hom.id m) := by rw [← hV, ← hLd]; exact hbm
    have hu : TubeOK (dataC Θ) (Hom.id m) (ival ρ φ).face (tubeV S u ρ γ) (conV D.ctors m c vals []) := by
      rw [← hV, ← hLd]; exact hTube
    obtain ⟨w, hw⟩ := hr_exists hgL hH (mem_El_dataC.1 hu0) _ _ hF hu
    have hLHS : sem S (hcomp (data d ps) φ u (con d c qs args [])) m ρ γ = w := by
      rw [sem_hcomp hcH, hLd, hV]; exact hcompAt_dataC_of_HR hgL hH hF hu0 hu hw
    rw [hLHS]
    obtain ⟨c', vals', outs, fills, ua, hv', rfl, hb, hkv', htu, hlo, hlf, hro, hpt⟩ := hw.inv
    obtain ⟨hc', hvv, -⟩ := conV_inj (bndAtMap_of_nil (bnd_nil hgL hH h2) _ _) (bndAtMap_of_nil hb _ _) hkv hkv' hv'
    subst hc' hvv
    obtain ⟨hut, huc, hub⟩ := tube_args_facts hgL hH hF h2 hta hu htu
    have iho : ∀ j (hj : j < vals.length), (Θ.ctors.getD c default).isRec j = true →
        HRProps Θ m (Hom.id m) (ival ρ φ).face (fun n h r => (ua n h r).getD j ∅) vals[j] (outs.getD j ∅) :=
      fun j hj hr => (hro j hj hr).props hgL hH
    have hfpv := hfills_ptValid hgL h2 hta hF hlo hlf hut huc hub hpt
    have hto := hcon_outs_typed hgL h2 hta hF hlo hlf hut huc hub hpt iho
    -- the tube's arguments
    have hpE : ∀ n (h : Hom n m) r, (Cof.restr (ival ρ φ).face h).holds →
        IsPoint S (cof Φ φ).shift Γ.dshift n ((ρ.restr h).cons r) (TEnv.restr γ h) := by
      intro n h r hh
      rw [holds_face_restr_iff] at hh
      exact isPoint_dshift_iff.2 (isPoint_cof_iff.2 ⟨hp.restr hwf h, hh⟩)
    have hua : ∀ n (h : Hom n m) r, (Cof.restr (ival ρ φ).face h).holds →
        ua n h r = uargs.toList.map fun t => sem S t n ((ρ.restr h).cons r) (TEnv.restr γ h) := by
      intro n h r hh
      have hpe := hpE n h r hh
      have e := h5.2.2 n _ _ hpe
      obtain ⟨hm5, -, hty5, -⟩ := h5.2.1.2.2.2 n _ _ hpe
      have hcg5 := conGuard_of_sem h0 (hty5.ne_empty hm5)
      have hkvE : ∀ x, IsKV n (TEnv.restr γ h x) := fun x => isKV_res _ _
      have hsv : sem S uargs n ((ρ.restr h).cons r) (TEnv.restr γ h) =
          vlist (uargs.toList.map fun t => sem S t n ((ρ.restr h).cons r) (TEnv.restr γ h)) := by
        conv_lhs => rw [hul]
        exact sem_ofList_vlist _ _ _ _
      have hpl5 : plist (psRV S uargs n ((ρ.restr h).cons r) (TEnv.restr γ h) n (Hom.id n)) C.args.length =
          uargs.toList.map fun t => sem S t n ((ρ.restr h).cons r) (TEnv.restr γ h) := by
        simp only [psRV, IEnv.restr_id, TEnv.restr_id_of_kv hkvE]
        rw [hsv, ← hlenU, show uargs.toList.length =
          (uargs.toList.map fun t => sem S t n ((ρ.restr h).cons r) (TEnv.restr γ h)).length by simp, plist_vlist]
      obtain ⟨C5, hC5, -, -, hpok5, hta5⟩ := id hcg5
      rw [h2] at hC5; cases hC5
      rw [hpl5] at hta5
      have hkv5 := argsTyped_kv (hok.2 _ _ hpok5).1 h2 hta5
      have e2 : tubeV S u ρ γ n h r = conV D.ctors n c
          (uargs.toList.map fun t => sem S t n ((ρ.restr h).cons r) (TEnv.restr γ h)) [] := by
        simp only [tubeV]; rw [e, sem_con_of h0 hcg5, getD_ctors h2, hpl5]; rfl
      rw [(htu n h r hh).1] at e2
      exact (conV_inj (bndAtMap_of_nil hb _ _) (bndAtMap_of_nil hb _ _) (htu n h r hh).2.2 hkv5 e2).2.1
    have htj : ∀ j, j < args.toList.length → ∀ n (h : Hom n m) r, (Cof.restr (ival ρ φ).face h).holds →
        (ua n h r).getD j ∅ = tubeV S (uargs.toList.getD j .abort) ρ γ n h r := by
      intro j hj n h r hh
      rw [hua n h r hh, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (by omega : j < uargs.toList.length), List.getD_eq_getElem?_getD (l := uargs.toList),
        List.getElem?_eq_getElem (by omega : j < uargs.toList.length)]
      rfl
    -- the parameters in the extended context
    set γL := TEnv.restr γ (Hom.wk m) with hγL
    have hkvL : ∀ x, IsKV (m + 1) (γL x) := fun x => isKV_res _ _
    have hpsl : ps.toList.length = np := by
      have h1' := (hpL m (Hom.id m)).1
      simp only [psRV, hρ, hγ] at h1'
      rw [hpl] at h1'
      exact listLen_unique (listLen_sem_ofList _ _ _) h1'
    have hpsnat := psnat_of_paramsOK hpl hpsl hp.kv hpL
    have hpsL : ps.dshift.toList = ps.toList.map (·.dshift) := dshift_toList ps hpl
    have hpsLl : ps.dshift.toList.length = np := by rw [hpsL, List.length_map, hpsl]
    have hpsLnat : ∀ t ∈ ps.dshift.toList, Natural S t (m + 1) ρ.ext γL := by
      intro t ht; rw [hpsL] at ht; obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht; exact (hpsnat t' ht').dshift
    have hpsD : Tm.ofList ps.dshift.toList = ps.dshift := by
      rw [hpsL]; conv_rhs => rw [hpl]
      exact (Tm.ren_ofList id Nat.succ ps.toList).symm
    have hpsLsem : ∀ k' (g' : Hom k' (m + 1)), sem S (Tm.ofList ps.dshift.toList) k' (ρ.ext.restr g') (TEnv.restr γL g') =
        psRV S ps m ρ γ k' ((Hom.wk m).comp g') := by
      intro k' g'
      rw [hpsD, sem_dshift_tail, IEnv.tail_restr]
      show sem S ps k' ((ρ.restr (Hom.wk m)).restr g') (TEnv.restr (TEnv.restr γ (Hom.wk m)) g') = _
      rw [IEnv.restr_restr, TEnv.restr_restr]
    -- one argument, given the fillers of the earlier ones
    have hone : ∀ j (hj : j < vals.length),
        (∀ i, i < j → (Θ.ctors.getD c default).isRec i = false →
          (((hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j)).reverse.map fun t => sem S t (m + 1) ρ.ext γL).getD i ∅ = fills.getD i ∅) →
        (∀ t ∈ (hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j), Natural S t (m + 1) ρ.ext γL) →
        sem S (hArg C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList (hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j) j).1 m ρ γ = outs.getD j ∅ ∧
        ((Θ.ctors.getD c default).isRec j = false → sem S (hArg C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList (hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j) j).2 (m + 1) ρ.ext γL = fills.getD j ∅) ∧
        Natural S (hArg C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList (hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j) j).2 (m + 1) ρ.ext γL := by
      intro j hj hfv hfn
      have hjl : j < args.toList.length := by simpa [vals] using hj
      have hjC : j < C.args.length := by omega
      have hav : sem S (args.toList.getD j .abort) m ρ γ = vals[j] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]; simp [vals]
      have hanat : Natural S (args.toList.getD j .abort) m ρ γ := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]; exact hnat _ (List.getElem_mem _)
      by_cases hr : C.isRec j = true
      · have hr' : (Θ.ctors.getD c default).isRec j = true := by rw [hgC]; exact hr
        have hHA : hArg C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList (hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j) j = (hcomp (data d ps) φ (uargs.toList.getD j .abort) (args.toList.getD j .abort),
            hfill (data d ps) φ (uargs.toList.getD j .abort) (args.toList.getD j .abort)) := by
          simp [hArg, hr]
        rw [hHA]
        have hd := hta.2.1 j _ (List.getElem?_eq_getElem hj) hr
        have htk := (comp_tube_ok hta hut huc hub hj hr).congr hF (fun n h r hh => htj j hjl n h r hh)
        have hcc : HcompCond S (data d ps) φ (uargs.toList.getD j .abort) (args.toList.getD j .abort) m ρ γ := by
          refine ⟨hTy, ?_, ?_, hAn, hanat⟩
          · rw [hLd, hav]; exact htk
          · rw [hLd, hav, mem_El_dataC]; exact hd
        refine ⟨?_, fun h => absurd (hr'.symm.trans h) (by decide), (hfill_cond hcc).1.natural⟩
        rw [sem_hcomp hcc, hLd, hav]
        exact hcompAt_dataC_of_HR hgL hH hF (mem_El_dataC.2 hd) htk
          ((hro j hj hr').congr_tube (fun n h r hh => htj j hjl n h r hh))
      · have hr0 : C.isRec j = false := by simpa using hr
        have hr' : (Θ.ctors.getD c default).isRec j = false := by rw [hgC]; exact hr0
        obtain ⟨A, hA⟩ : ∃ A, C.args[j]? = some (.point A) := by
          cases h' : C.args[j]'hjC with
          | point A => exact ⟨A, by rw [List.getElem?_eq_getElem hjC, h']⟩
          | recur => simp [Ctor.isRec, List.getElem?_eq_getElem hjC, h'] at hr0
        have hHA : hArg C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList (hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j) j =
            (Tm.comp (A.substList ((hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j) ++ ps.dshift.toList.reverse)) φ (uargs.toList.getD j .abort) (args.toList.getD j .abort),
             Tm.fill (A.substList ((hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j) ++ ps.dshift.toList.reverse)) φ (uargs.toList.getD j .abort) (args.toList.getD j .abort)) := by
          simp [hArg, hr0, Ctor.argTy, hA]
        rw [hHA]
        set Lj := A.substList ((hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j) ++ ps.dshift.toList.reverse) with hLj
        have hfl : ((hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j)).length = j := hFills_length _ _ _ _ _ _ _ j
        set sF := ((hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j)).reverse.map fun t => sem S t (m + 1) ρ.ext γL with hsF
        have hsl : sF.length = j := by simp [sF, hfl]
        have hfpvj := hfpv.take j
        rw [Hom.id_comp] at hfpvj
        have hptS : Θ.PtValid c (m + 1) (Hom.wk m) sF := by
          refine ptValid_congr hgL (by simp [hlf, hsl]; omega) (fun i hi hri => ?_) hfpvj
          simp only [List.length_take] at hi
          rw [hfv i (by omega) hri, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_take_of_lt (by omega)]
        have hsem : ∀ k' (g' : Hom k' (m + 1)), sem S Lj k' (ρ.ext.restr g') (TEnv.restr γL g') =
            Θ.ty c j k' ((Hom.wk m).comp g') (sF.map (res g')) := by
          intro k' g'
          rw [hLj, sem_argTy_subst h0 hok.1 h2 hA _ _ hfl hpsLl (fun t ht => by
            rcases List.mem_append.1 ht with ht | ht
            · exact (hfn t ht).restr g'
            · exact (hpsLnat t (List.mem_reverse.1 ht)).restr g'), hpsLsem]
          have e1 : (((hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j)).reverse.map fun t => sem S t k' (ρ.ext.restr g') (TEnv.restr γL g')) = sF.map (res g') := by
            rw [hsF, List.map_map]
            exact List.map_congr_left fun t ht => hfn t (List.mem_reverse.1 ht) k' g'
          rw [e1]
          show _ = argTySem _ _ _ _ _ _ _ _
          have hpv' : Θ.PtValid c k' ((Hom.wk m).comp g') (sF.map (res g')) := hgL.ptValid_res hptS k' g'
          rw [argTySem_eq, if_pos ⟨by rw [getD_ctors h2]; omega, by rw [getD_ctors h2]; exact hr0,
            ptValid_argPreValid hpv' (j := j) (by simp [hsl])⟩]
        have hsFid : sF.map (res (Hom.id (m + 1))) = sF := by
          rw [hsF, List.map_map]
          refine List.map_congr_left fun t ht => ?_
          have := hfn t (List.mem_reverse.1 ht) (m + 1) (Hom.id _)
          rw [IEnv.restr_id, TEnv.restr_id_of_kv hkvL] at this
          exact this.symm
        have hline0 : lineV S Lj m ρ γ = Θ.ty c j (m + 1) (Hom.wk m) sF := by
          have := hsem (m + 1) (Hom.id (m + 1))
          rw [IEnv.restr_id, TEnv.restr_id_of_kv hkvL, Hom.comp_id, hsFid] at this
          exact this
        have hline : lineV S Lj m ρ γ = Θ.ty c j (m + 1) ((Hom.id m).comp (Hom.wk m)) (fills.take j) := by
          rw [hline0, Hom.id_comp, ← List.take_of_length_le (l := sF) (i := j) (by omega)]
          exact ty_take_eq hgL (by omega) (by omega) (fun i hi hri => hfv i hi hri)
        have hN : Natural S Lj (m + 1) ρ.ext γL := by
          intro k' g'
          rw [hsem, show sem S Lj (m + 1) ρ.ext γL = lineV S Lj m ρ γ from rfl, hline0,
            hgL.nat c j (m + 1) _ _ hptS k' g']
        obtain ⟨hfib, hbase, htube⟩ := hcon_point_facts hgL h2 hta hF hlo hlf hut huc hub hpt hj hr'
        have hTyC : TyCode (m + 1) (lineV S Lj m ρ γ) := by
          rw [hline]
          obtain ⟨hV, hW⟩ := (hok.2 m _ hpL).2.1 c j (m + 1) ((Hom.id m).comp (Hom.wk m)) (fills.take j)
          exact ⟨D.level, hlvl, Or.inl ⟨hW (hfpv.take j), hV⟩⟩
        have hLT : LineTubeOK (lineV S Lj m ρ γ) (Hom.id (m + 1)) (ival ρ φ).face
            (tubeV S (uargs.toList.getD j .abort) ρ γ) (sem S (args.toList.getD j .abort) m ρ γ) := by
          rw [hline, hav]; exact htube.congr hF (fun n h r hh => htj j hjl n h r hh)
        have hB : sem S (args.toList.getD j .abort) m ρ γ ∈
            El (lineV S Lj m ρ γ) ((Hom.id (m + 1)).comp (Hom.endpt m (DM.zero m))) := by
          rw [hline, hav]; exact hbase
        have hcomp_eq := (comp_cond hTyC hN hLT hB hanat hp.kv).2
        obtain ⟨hfn', hfill_eq⟩ := fill_cond hTyC hN hLT hB hanat
        refine ⟨?_, fun _ => ?_, hfn'⟩
        · rw [hcomp_eq, hline, hav, (hpt j hj hr').1]
          exact compF_congr fun n h r hh => (htj j hjl n h r hh).symm
        · rw [hfill_eq, hline, hav, (hpt j hj hr').2, fillF, fillF,
            fillTube_congr (u' := fun n h r => (ua n h r).getD j ∅) _ fun n h r hh => (htj j hjl n h r hh).symm]
    have hall : ∀ j, j ≤ vals.length →
        (∀ i, i < j → (Θ.ctors.getD c default).isRec i = false →
          (((hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j)).reverse.map fun t => sem S t (m + 1) ρ.ext γL).getD i ∅ = fills.getD i ∅) ∧
        (∀ t ∈ (hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j), Natural S t (m + 1) ρ.ext γL) := by
      intro j
      induction j with
      | zero => intro _; exact ⟨fun i hi => absurd hi (by omega), fun t ht => by simp [hFills] at ht⟩
      | succ j ih =>
        intro hj
        obtain ⟨h1', h2'⟩ := ih (by omega)
        obtain ⟨-, hf, hfn⟩ := hone j (by omega) h1' h2'
        have hfl : ((hFills C (C.argTy d np) (data d ps) ps.dshift.toList φ uargs.toList args.toList j)).length = j := hFills_length _ _ _ _ _ _ _ j
        refine ⟨fun i hi hri => ?_, fun t ht => ?_⟩
        · simp only [hFills, List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
          rw [List.getD_eq_getElem?_getD]
          by_cases hij : i < j
          · rw [List.getElem?_append_left (by simp [hfl]; omega), ← List.getD_eq_getElem?_getD]
            exact h1' i hij hri
          · obtain rfl : i = j := by omega
            rw [List.getElem?_append_right (by simp [hfl])]
            simp only [List.length_map, List.length_reverse, hfl, Nat.sub_self, List.getElem?_cons_zero,
              Option.getD_some]
            exact hf hri
        · simp only [hFills, List.mem_cons] at ht
          rcases ht with rfl | ht
          · exact hfn
          · exact h2' t ht
    have hTv : (Tm.hcompTele C (C.argTy d np) (data d ps) ps.dshift.toList φ 0 [] uargs.toList args.toList).map (fun t => sem S t m ρ γ) = outs := by
      rw [hT0, List.map_map]
      apply List.ext_getElem (by simp [hlo, vals])
      intro i h1' h2'
      simp only [List.getElem_map, List.getElem_range, Function.comp] at h1' ⊢
      have hi : i < vals.length := by simpa [vals] using h1'
      rw [(hone i hi (hall i hi.le).1 (hall i hi.le).2).1, gd_eq]
    -- the right-hand side
    have hTl : (Tm.hcompTele C (C.argTy d np) (data d ps) ps.dshift.toList φ 0 [] uargs.toList args.toList).length = C.args.length := by
      rw [← List.length_map (f := fun t => sem S t m ρ γ), hTv, hlo, hvl]
    have hplT : plist (psRV S (Tm.ofList (Tm.hcompTele C (C.argTy d np) (data d ps) ps.dshift.toList φ 0 [] uargs.toList args.toList)) m ρ γ m (Hom.id m)) C.args.length = outs := by
      simp only [psRV, hρ, hγ]
      rw [sem_ofList_vlist, hTv, show C.args.length = outs.length by rw [hlo, hvl], plist_vlist]
    have hdims : (([] : List I).map (ival ρ)).length = C.dims := by rw [(hgL.nonhit hH c C h2).1]; rfl
    have hgR : ConGuard (sigUpTo S d) D d m (psRV S ps m ρ γ) c (psRV S (Tm.ofList (Tm.hcompTele C (C.argTy d np) (data d ps) ps.dshift.toList φ 0 [] uargs.toList args.toList)) m ρ γ)
        (([] : List I).map (ival ρ)) := by
      refine ⟨C, h2, hdims, ?_, hpL, ?_⟩
      · simp only [psRV, hρ, hγ]
        have := listLen_sem_ofList (S := S) (Tm.hcompTele C (C.argTy d np) (data d ps) ps.dshift.toList φ 0 [] uargs.toList args.toList) ρ γ
        rwa [hTl] at this
      · rw [hplT]; exact hto
    rw [sem_con_of h0 hgR, getD_ctors h2, hplT]
    rfl
  exact ⟨h7, h7.of_eq hcl he, fun m ρ γ hp => (he m ρ γ hp).symm⟩

end

end Model
