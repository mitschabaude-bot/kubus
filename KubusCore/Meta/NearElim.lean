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

end KubusCore.Meta
