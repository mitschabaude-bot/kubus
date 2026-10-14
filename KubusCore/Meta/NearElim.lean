import KubusCore.Meta.NearData

/-!
# Metatheory: congruence of the eliminator's branch data

Congruences for iterated application through telescopes, the branch types, branch contexts and
the eliminator on boundaries, used to type the eliminator at near parameters, motive and
branches.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-! ## Iterated application -/

theorem EqTeleS.refl {Ψ Φ Γ} : ∀ {ts Δ prev}, HasTele0 S Ψ Φ Γ ts Δ prev → EqTeleS S Ψ Φ Γ ts ts Δ prev
  | _, _, _, .nil hw => .nil hw
  | _, _, _, .cons ha hs => .cons (EqTm0.refl ha) (EqTeleS.refl hs)

theorem EqTeleS.retype {Ψ Φ Γ} : ∀ {as as' Δ prev}, EqTeleS S Ψ Φ Γ as as' Δ prev → ∀ {Δ' prev'},
    Δ'.length = Δ.length →
    (∀ (k : Nat) (A A' : Tm) (L : List Tm), Δ[k]? = some A → Δ'[k]? = some A' → L.length = k →
      A.substList (L ++ prev) = A'.substList (L ++ prev')) →
    EqTeleS S Ψ Φ Γ as as' Δ' prev'
  | _, _, _, _, .nil hw, Δ', _, hl, _ => by
    cases Δ' with
    | nil => exact .nil hw
    | cons _ _ => simp at hl
  | _, _, _, _, .cons (a := a) (A := A) (Δ := Δ) (prev := prev) ha hs, Δ', prev', hl, he => by
    cases Δ' with
    | nil => simp at hl
    | cons A' Δ'' =>
      refine .cons ?_ (hs.retype (by simpa using hl) ?_)
      · have := he 0 A A' [] rfl rfl rfl
        simp only [List.nil_append] at this
        rw [← this]; exact ha
      · intro k B B' L hB hB' hL
        have := he (k + 1) B B' (L ++ [a]) hB hB' (by simp [hL])
        simpa using this

theorem EqTeleS.length_left {Ψ Φ Γ} : ∀ {ts ts' Δ prev}, EqTeleS S Ψ Φ Γ ts ts' Δ prev →
    ts.toList.length = Δ.length
  | _, _, _, _, .nil _ => rfl
  | _, _, _, _, .cons _ h1 => by simp [Tm.toList, h1.length_left]

/-- Congruence of application through a Π-telescope. -/
theorem apps_eq {Ψ Φ Γ} : ∀ {as as' Δ prev}, EqTeleS S Ψ Φ Γ as as' Δ prev → ∀ {f f' base},
    EqTm0 S Ψ Φ Γ f f' ((Δ.foldr pi base).substList prev) →
    EqTm0 S Ψ Φ Γ (Tm.apps f as.toList) (Tm.apps f' as'.toList) (base.substList (as.toList.reverse ++ prev))
  | _, _, _, _, .nil _, _, _, _, hf => hf
  | _, _, _, _, .cons (a := a) (a' := a') (Δ := Δ) (prev := prev) ha hs, f, f', base, hf => by
    have h1 : EqTm0 S Ψ Φ Γ (app f a) (app f' a') ((Δ.foldr pi base).substList (a :: prev)) := by
      rw [← up_slS_inst]; exact EqTm0.app hf ha
    have := apps_eq hs h1
    simpa [Tm.toList, Tm.apps, List.foldl] using this

theorem papps_ipis_eq {Ψ Φ Γ σ B} : ∀ (rs : List I) {g g' τ}, (∀ r ∈ rs, r.Scoped Ψ) →
    EqTm0 S Ψ Φ Γ g g' ((ipis rs.length B).subst σ τ) →
    EqTm0 S Ψ Φ Γ (Tm.papps g rs) (Tm.papps g' rs) (B.subst σ (consIs rs τ))
  | [], g, g', τ, _, hg => hg
  | r :: rs, g, g', τ, hrs, hg => by
    rw [List.length_cons, ipis_succ] at hg
    have hr := hrs r (List.mem_cons_self ..)
    have h1 := EqTm0.iapp hg hr hr (I_eq_refl r)
    rw [dup_dinst] at h1
    exact papps_ipis_eq rs (fun r' h => hrs r' (List.mem_cons_of_mem _ h)) h1

/-- Congruence of a branch applied to arguments, hypotheses and interval arguments. -/
theorem branch_app_eq (hS : SigClosed S) {Ψ Φ Γ d D c C ps P b b'} (hD : S[d]? = some (.data D))
    (hC : D.ctors[c]? = some C) (hlen : ps.toList.length = D.params.length)
    (hb : EqTm0 S Ψ Φ Γ b b' (D.branchTy d c C ps P)) {args args' ihs ihs' : List Tm} {rs : List I}
    (ha : EqTeleS S Ψ Φ Γ (Tm.ofList args) (Tm.ofList args') (C.argTys d D.params.length) ps.toList.reverse)
    (hi : EqTeleS S Ψ Φ Γ (Tm.ofList ihs) (Tm.ofList ihs')
      ((List.range C.recPos.length).map (DataDecl.branchIhTy C P)) args.reverse)
    (hrs : rs.length = C.dims) (hrsc : ∀ r ∈ rs, r.Scoped Ψ) :
    EqTm0 S Ψ Φ Γ (Tm.papps (Tm.apps b (args ++ ihs)) rs) (Tm.papps (Tm.apps b' (args' ++ ihs')) rs)
      (P.inst (con d c ps (Tm.ofList args) rs)) := by
  have hal : args.length = C.args.length := by
    have := ha.length_left; rwa [toList_ofList, argTys_length] at this
  have hil : ihs.length = C.recPos.length := by
    have := hi.length_left; rwa [toList_ofList, List.length_map, List.length_range] at this
  have ha' : EqTeleS S Ψ Φ Γ (Tm.ofList args) (Tm.ofList args')
      ((List.range C.args.length).map (DataDecl.branchArgTy d D.params.length C ps)) [] :=
    ha.retype (by simp [argTys_length]) (fun k A A' L hA hA' hL => by
      simp only [Ctor.argTys, List.getElem?_map, Option.map_eq_some_iff] at hA hA'
      obtain ⟨k1, hk1, rfl⟩ := hA
      obtain ⟨k2, hk2, rfl⟩ := hA'
      obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.1 hk1
      obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.1 hk2
      simp only [List.getElem_range]
      rw [List.append_nil, branchArgTy_substList hS hD hC hlen hL])
  have hb' : EqTm0 S Ψ Φ Γ b b' ((((List.range C.args.length).map
      (DataDecl.branchArgTy d D.params.length C ps)).foldr pi
        (((List.range C.recPos.length).map (DataDecl.branchIhTy C P)).foldr pi
          (ipis C.dims (DataDecl.branchBody d c C ps P)))).substList []) := by
    rw [substList_nil, ← branchTy_eq]; exact hb
  have h1 := apps_eq ha' hb'
  rw [toList_ofList, toList_ofList, List.append_nil] at h1
  have h2 := apps_eq hi h1
  rw [toList_ofList, toList_ofList, substList_eq, ← hrs] at h2
  have h3 := papps_ipis_eq rs hrsc h2
  rw [branchBody_inst hil hal hrs] at h3
  rw [Tm.apps, List.foldl_append, Tm.apps, List.foldl_append]; exact h3

/-! ## Type formers -/

theorem pis_congr {Ψ Φ l} : ∀ (As As' : List Tm) {Δ : Ctx} {base base' : Tm}, As.length = As'.length →
    (∀ k (hk : k < As.length) (hk' : k < As'.length),
      EqTm0 S Ψ Φ ((As.take k).reverse ++ Δ) As[k] As'[k] (univ l)) →
    EqTm0 S Ψ Φ (As.reverse ++ Δ) base base' (univ l) →
    EqTm0 S Ψ Φ Δ (As.foldr pi base) (As'.foldr pi base') (univ l)
  | [], [], _, _, _, _, _, hb => by simpa using hb
  | A :: As, A' :: As', Δ, base, base', hl, he, hb => by
    simp only [List.foldr_cons]
    refine EqTm0.pi (by simpa using he 0 (by simp) (by simp)) ?_
    refine pis_congr As As' (Δ := A :: Δ) (by simpa using hl) (fun k hk hk' => ?_) (by simpa using hb)
    have := he (k + 1) (by simp; omega) (by simp; omega)
    simpa using this
  | [], _ :: _, _, _, _, hl, _, _ | _ :: _, [], _, _, _, hl, _, _ => by simp at hl

theorem ipis_congr (hS : SigClosed S) {l : Nat} : ∀ (m : Nat) {Ψ Φ Δ B B'}, Wf0 S Ψ Φ Δ →
    EqTm0 S (Ψ + m) (Φ.subst (wkIv m)) (ctxWkI m Δ) B B' (univ l) →
    EqTm0 S Ψ Φ Δ (ipis m B) (ipis m B') (univ l)
  | 0, Ψ, Φ, Δ, B, B', _, h => by
    rw [wkI_zero, I_wkI_zero] at h; exact h
  | m + 1, Ψ, Φ, Δ, B, B', hw, h => by
    rw [ipis_succ, ipis_succ]
    refine EqTm0.ipi hw (ipis_congr hS m (Wf0.dwk hS hw) ?_)
    rw [Ctx_dshift_eq, wkI_wkI, I_shift_eq, I_wkI_wkI, show Ψ + 1 + m = Ψ + (m + 1) by omega,
      show 1 + m = m + 1 by omega]
    exact h

/-! ## Prefixes of argument telescopes along equal instantiations -/

theorem pts_near (hS : SigClosed S) (hW : WfSig S) {d : Nat} {D : DataDecl} {c : Nat} {C : Ctor}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C)
    {Ψ Φ Γ} {ps ps' : Tm} {xs xs' : List Tm} (hpres : ∀ {t u A}, EqTm0 S Ψ Φ Γ t u A → HasTy0 S Ψ Φ Γ u A)
    (ht : HasTele0 S Ψ Φ Γ ps D.params []) (es : EqTeleS S Ψ Φ Γ ps ps' D.params [])
    {l : Nat} (edata : EqTm0 S Ψ Φ Γ (data d ps) (data d ps') (univ l))
    (k0 : Nat) (hk0 : k0 ≤ C.args.length) (hx : k0 ≤ xs.length) (hx' : k0 ≤ xs'.length)
    (hty : ∀ i, i < k0 → HasTy0 S Ψ Φ Γ (xs.getD i .abort)
      ((C.argTy d D.params.length i).substList ((xs.take i).reverse ++ ps.toList.reverse)))
    (heq : ∀ i, i < k0 → EqTm0 S Ψ Φ Γ (xs.getD i .abort) (xs'.getD i .abort)
      ((C.argTy d D.params.length i).substList ((xs.take i).reverse ++ ps.toList.reverse))) :
    ∀ k, k ≤ k0 →
      TySub S 0 .one (D.pointCtx d C k) Ψ Φ Γ (lsub (ptL C xs ps.toList.reverse k) 0) I.var ∧
      TySub S 0 .one (D.pointCtx d C k) Ψ Φ Γ (lsub (ptL C xs' ps'.toList.reverse k) 0) I.var ∧
      EqSub S 0 (D.pointCtx d C k) Ψ Φ Γ (lsub (ptL C xs ps.toList.reverse k) 0) I.var
        (lsub (ptL C xs' ps'.toList.reverse k) 0) I.var ∧
      ∀ i, i < k → HasTy0 S Ψ Φ Γ (xs'.getD i .abort)
        ((C.argTy d D.params.length i).substList ((xs'.take i).reverse ++ ps'.toList.reverse)) := by
  have hw := wf_of_tele ht
  have hpl : ps.toList.length = D.params.length := by simpa using tele_length ht
  have hpl' : ps'.toList.length = D.params.length := by simpa using es.length'
  have hpsL := tele_isList ht
  have hpsL' := es.isList'
  have h0 : ∀ σ, TySub S 0 .one [] Ψ Φ Γ σ I.var :=
    fun σ => tySub_nil (fun i hi => absurd hi (Nat.not_lt_zero _)) (ent_one _) hw
  intro k hk
  induction k with
  | zero =>
    obtain ⟨T, E, -⟩ := params_near hS hW hD hpres ht es 0 I.var I.var _ (Nat.le_refl _)
    have TL := tySub_params hS hD ht 0 h0 _ (Nat.le_refl _)
    rw [List.take_of_length_le (show ps.toList.length ≤ D.params.length by omega)] at TL
    rw [List.take_of_length_le (show ps'.toList.length ≤ D.params.length by omega)] at T
    rw [List.take_of_length_le (show ps'.toList.length ≤ D.params.length by omega),
      List.take_of_length_le (show ps.toList.length ≤ D.params.length by omega)] at E
    have hpc : D.pointCtx d C 0 = D.paramCtx D.params.length := by simp [DataDecl.pointCtx]
    simp only [ptL, hpc]
    exact ⟨TL, T, E, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    have hkn : k < C.args.length := by omega
    obtain ⟨TL, T', E, Tel⟩ := ih (by omega)
    have e := heq k (by omega)
    have hxk := hty k (by omega)
    have ha2t := hpres e
    rw [pointCtx_succ]
    cases hr : C.isRec k
    · simp only [hr, Bool.false_eq_true, if_false, ptL]
      obtain ⟨A0, hA0⟩ := point_of_not_rec hkn hr
      have hAk : C.argTy d D.params.length k = A0 := by simp [Ctor.argTy, hA0]
      rw [hAk]
      rw [hAk] at e ha2t hxk
      have hP11 := pt_typed hW (htr_of_wf hW hD) hD hC hA0
      have F := (sub_ty hS hP11).2.2 TL T' E
      rw [pt_inst hW hD hC hA0 (by omega) (by simp [hpl]) 0 I.var,
        pt_inst hW hD hC hA0 (by omega) (by simp [hpl']) 0 I.var] at F
      have ha2' := HasTy0.conv ha2t F
      have TL' := TL.cons (A := A0.ren (C.pointRen k) id) (a := xs.getD k .abort)
        (by rw [pt_inst hW hD hC hA0 (by omega) (by simp [hpl]) 0 I.var]; exact hxk)
      have T'' := T'.cons (A := A0.ren (C.pointRen k) id) (a := xs'.getD k .abort)
        (by rw [pt_inst hW hD hC hA0 (by omega) (by simp [hpl']) 0 I.var]; exact ha2')
      have E' := E.cons (A := A0.ren (C.pointRen k) id) (a1 := xs.getD k .abort)
        (a2 := xs'.getD k .abort)
        (by rw [pt_inst hW hD hC hA0 (by omega) (by simp [hpl]) 0 I.var]; exact e)
      rw [consT_lsub] at TL' T''
      rw [consT_lsub, consT_lsub] at E'
      refine ⟨TL', T'', E', fun i hi => ?_⟩
      by_cases hik : i = k
      · subst hik; rw [hAk]; exact ha2'
      · exact Tel i (by omega)
    · simp only [hr, if_true, ptL]
      refine ⟨TL, T', E, fun i hi => ?_⟩
      by_cases hik : i = k
      · subst hik
        have hAk := argTy_rec' (np := D.params.length) (d := d) hr
        rw [hAk, substList_eq] at e
        simp only [Tm.subst] at e
        rw [← substList_eq, paramVars_substList hpsL hpl (by simp; omega)] at e
        rw [hAk, substList_eq]; simp only [Tm.subst]
        rw [← substList_eq, paramVars_substList hpsL' hpl' (by simp; omega)]
        exact HasTy0.conv (hpres e) edata
      · exact Tel i (by omega)

/-! ## Weakening into extended contexts -/

theorem lookup_append (Γ : Ctx) (x : Nat) : ∀ E : Ctx,
    (E ++ Γ).lookup (x + E.length) = (Γ.lookup x).map (·.ren (· + E.length) id)
  | [] => by
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    cases Γ.lookup x with
    | none => rfl
    | some A =>
      simp only [Option.map_some, Option.some.injEq]; rw [ren_eq_subst]
      exact (subst_id_of (fun _ => rfl) (fun _ => rfl) A).symm
  | B :: E => by
    simp only [List.cons_append, List.length_cons]
    rw [show x + (E.length + 1) = (x + E.length) + 1 by omega]
    simp only [Ctx.lookup, lookup_append Γ x E, Option.map_map]
    cases Γ.lookup x with
    | none => rfl
    | some A =>
      simp only [Option.map_some, Function.comp, Tm.shift, ren_ren]
      congr 1

theorem tySub_wkE {Ψ Φ Γ} (E : Ctx) (m : Nat) {X : I}
    (hw : Wf0 S (Ψ + m) X (ctxWkI m (E ++ Γ))) (he : I.Entails X (Φ.subst (wkIv m))) :
    TySub S Ψ Φ Γ (Ψ + m) X (ctxWkI m (E ++ Γ)) (fun j => .var (j + E.length)) (wkIv m) where
  bound := fun i hi => show i + m < Ψ + m by omega
  hscoped := scoped_of_wf hw
  ent := he
  wf := hw
  look := fun x A hx => by
    refine HasTy0.var hw ?_
    rw [lookup_wkI, lookup_append, hx]
    simp only [Option.map_some, Option.some.injEq]
    rw [ren_eq_subst, subst_subst]
    rfl

theorem EqTeleS.sub (hS : SigClosed S) {Ψ Φ Γ Ψ' Φ' Δ σ τ} (hσ : TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ) :
    ∀ {ts ts' Δt prev}, EqTeleS S Ψ Φ Γ ts ts' Δt prev →
    (∀ (k : Nat) (A : Tm), Δt[k]? = some A → A.closedB (prev.length + k) 0 = true) →
    EqTeleS S Ψ' Φ' Δ (ts.subst σ τ) (ts'.subst σ τ) Δt (prev.map (·.subst σ τ))
  | _, _, _, _, .nil _, _ => .nil hσ.wf
  | _, _, _, _, .cons (A := A) (prev := prev) ha hs, hcl => by
    have h1 := (sub_eq hS ha).2 hσ
    rw [substList_subst (by simpa using hcl 0 A rfl)] at h1
    refine .cons h1 ?_
    have := EqTeleS.sub hS hσ hs (fun k B hB => by
      have := hcl (k + 1) B (by simpa using hB); simp only [List.length_cons]; rwa [Nat.add_assoc, Nat.add_comm 1 k])
    simpa using this

/-! ## Variables of the branch context -/

/-- The argument part of the branch context before argument `k` (innermost first). -/
def argCtxB (d np : Nat) (C : Ctor) (ps : Tm) (k : Nat) : Ctx :=
  (List.range k).reverse.map (DataDecl.branchArgTy d np C ps)

/-- The hypothesis part of the branch context before hypothesis `s` (innermost first). -/
def ihCtxB (C : Ctor) (P : Tm) (s : Nat) : Ctx := (List.range s).reverse.map (DataDecl.branchIhTy C P)

theorem argCtxB_length (d np : Nat) (C : Ctor) (ps : Tm) (k : Nat) : (argCtxB d np C ps k).length = k := by
  simp [argCtxB]

theorem ihCtxB_length (C : Ctor) (P : Tm) (s : Nat) : (ihCtxB C P s).length = s := by
  simp [ihCtxB]

theorem range_rev_map_get (f : Nat → Tm) {k i : Nat} (h : i < k) :
    ((List.range k).reverse.map f)[k - 1 - i]? = some (f i) := by
  rw [List.getElem?_map, List.getElem?_reverse (by simp; omega)]
  simp only [List.length_range, show k - 1 - (k - 1 - i) = i by omega, List.getElem?_range h, Option.map_some]

theorem wkN_wkN_eq (p : Tm) (a b c : Nat) :
    (p.wkN a 0).subst (fun x => .var (x + b)) (wkIv c) = p.wkN (a + b) c := by
  rw [wkN_eq, wkN_eq, subst_subst]
  apply subst_congr
  · intro x; simp only [Tm.subst]; congr 1; omega
  · intro i; simp only [I.subst, wkIv]; congr 1

/-- An argument variable of the branch context, typed at its argument type. -/
theorem argvar_ty (hS : SigClosed S) {d : Nat} {D : DataDecl} {c : Nat} {C : Ctor}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C) {ps : Tm} (hps : IsList ps)
    (hpl : ps.toList.length = D.params.length) {Ψ' X Γ} (E : Ctx) (m n' : Nat)
    (hw : Wf0 S Ψ' X (ctxWkI m (E ++ argCtxB d D.params.length C ps n' ++ Γ))) {i : Nat} (hi : i < n') :
    HasTy0 S Ψ' X (ctxWkI m (E ++ argCtxB d D.params.length C ps n' ++ Γ))
      (.var (E.length + n' - 1 - i))
      ((C.argTy d D.params.length i).substList ((List.range i).map (fun j => .var (j + (E.length + n' - i))) ++
        (ps.toList.map (·.wkN (E.length + n') m)).reverse)) := by
  have hget : (E ++ argCtxB d D.params.length C ps n' ++ Γ)[E.length + n' - 1 - i]? =
      some (DataDecl.branchArgTy d D.params.length C ps i) := by
    rw [List.append_assoc, List.getElem?_append_right (by omega),
      List.getElem?_append_left (by rw [argCtxB_length]; omega)]
    rw [show E.length + n' - 1 - i - E.length = n' - 1 - i by omega]
    exact range_rev_map_get _ hi
  refine HasTy0.var hw ?_
  rw [lookup_wkI, lookup_of_get _ _ _ hget]
  simp only [Option.map_some, Option.some.injEq]
  unfold DataDecl.branchArgTy
  have hcl := argTy_closed hS hD hC i
  rw [ren_eq_subst, subst_subst, substList_subst (by simp [hpl]; rw [Nat.add_comm]; exact hcl)]
  congr 1
  simp only [List.map_append, List.map_map, List.map_reverse]
  congr 1
  · apply List.map_congr_left; intro j hj
    have := List.mem_range.1 hj
    simp only [Function.comp, Tm.subst]; congr 1; omega
  · congr 1; apply List.map_congr_left; intro p _
    simp only [Function.comp]
    rw [wkN_eq, wkN_eq, subst_subst]
    apply subst_congr
    · intro x; simp only [Tm.subst, wkIv]; congr 1; omega
    · intro j; simp [I.subst, wkIv]

end KubusCore.Meta
