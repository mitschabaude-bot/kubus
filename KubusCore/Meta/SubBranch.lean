import KubusCore.Meta.SubFace

/-!
# Metatheory: lifting typed substitutions through binders and branch contexts
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem TySub.upC (hS : SigClosed S) {Ψ Φ Γ Ψ' Φ' Δ σ τ} (h : TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ) {A : Tm}
    (hc : CtxSub S Ψ Φ (A :: Γ)) : TySub S Ψ Φ (A :: Γ) Ψ' Φ' (A.subst σ τ :: Δ) (Tm.up σ) τ := by
  obtain ⟨_, l, hA, _, _⟩ := hc
  exact h.up' hS (hA h)

/-- Lift two equal substitutions under a term binder (into the first one's extension). -/
theorem TySub.up2 (hS : SigClosed S) {Ψ Φ Γ Ψ' Φ' Δ σ1 τ1 σ2 τ2} (h1 : TySub S Ψ Φ Γ Ψ' Φ' Δ σ1 τ1)
    (h2 : TySub S Ψ Φ Γ Ψ' Φ' Δ σ2 τ2) (hE : EqSub S Ψ Γ Ψ' Φ' Δ σ1 τ1 σ2 τ2) {A : Tm}
    (hc : CtxSub S Ψ Φ (A :: Γ)) :
    TySub S Ψ Φ (A :: Γ) Ψ' Φ' (A.subst σ1 τ1 :: Δ) (Tm.up σ1) τ1 ∧
    TySub S Ψ Φ (A :: Γ) Ψ' Φ' (A.subst σ1 τ1 :: Δ) (Tm.up σ2) τ2 ∧
    EqSub S Ψ (A :: Γ) Ψ' Φ' (A.subst σ1 τ1 :: Δ) (Tm.up σ1) τ1 (Tm.up σ2) τ2 := by
  obtain ⟨_, l, hA, hAf, _⟩ := hc
  exact ⟨h1.up' hS (hA h1), h2.up hS (hA h1) (hAf h1 h2 hE),
    hE.up hS h1 (hA h1) (EqTm0.refl (hA h1))⟩

/-- Extend a substitution by a term for a new variable. -/
def consT (a : Tm) (σ : Nat → Tm) : Nat → Tm
  | 0 => a
  | n + 1 => σ n

theorem shift_consT (A a : Tm) (σ : Nat → Tm) (τ : Nat → I) : A.shift.subst (consT a σ) τ = A.subst σ τ := by
  rw [shift_subst]; rfl

theorem TySub.cons {Ψ Φ Γ Ψ' Φ' Δ σ τ} (h : TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ) {A a : Tm}
    (ha : HasTy0 S Ψ' Φ' Δ a (A.subst σ τ)) : TySub S Ψ Φ (A :: Γ) Ψ' Φ' Δ (consT a σ) τ :=
  { bound := h.bound, hscoped := h.hscoped, ent := h.ent, wf := h.wf
    look := fun x B hx => by
      cases x with
      | zero =>
        simp only [Ctx.lookup, Option.some.injEq] at hx; subst hx
        rw [shift_consT]; exact ha
      | succ x =>
        simp only [Ctx.lookup, Option.map_eq_some_iff] at hx
        obtain ⟨B0, hB0, rfl⟩ := hx
        rw [shift_consT]; exact h.look x B0 hB0 }

theorem EqSub.cons {Ψ Γ Ψ' Φ' Δ σ1 τ1 σ2 τ2} (h : EqSub S Ψ Γ Ψ' Φ' Δ σ1 τ1 σ2 τ2) {A a1 a2 : Tm}
    (ha : EqTm0 S Ψ' Φ' Δ a1 a2 (A.subst σ1 τ1)) :
    EqSub S Ψ (A :: Γ) Ψ' Φ' Δ (consT a1 σ1) τ1 (consT a2 σ2) τ2 :=
  ⟨fun x B hx => by
    cases x with
    | zero =>
      simp only [Ctx.lookup, Option.some.injEq] at hx; subst hx
      rw [shift_consT]; exact ha
    | succ x =>
      simp only [Ctx.lookup, Option.map_eq_some_iff] at hx
      obtain ⟨B0, hB0, rfl⟩ := hx
      rw [shift_consT]; exact h.1 x B0 hB0, h.2⟩

theorem inst_consT (P t : Tm) (σ : Nat → Tm) (τ : Nat → I) :
    (P.inst t).subst σ τ = P.subst (consT (t.subst σ τ) σ) τ := by
  simp only [Tm.inst, subst_subst]
  apply subst_congr
  · intro n; cases n with
    | zero => rfl
    | succ n => rfl
  · intro i; rfl

theorem I_eq_subst_scoped {r : I} {n : Nat} (hr : r.Scoped n) {τ1 τ2 : Nat → I}
    (h : ∀ i < n, I.Eq (τ1 i) (τ2 i)) : I.Eq (r.subst τ1) (r.subst τ2) := by
  intro ρ; rw [eval_subst, eval_subst]
  exact eval_scoped_congr hr fun i hi => h i hi ρ

/-! ## Interval weakening and branch contexts -/

theorem tyRen_wkI (hS : SigClosed S) {Ψ Φ Δ} (hw : Wf0 S Ψ Φ Δ) (m : Nat) :
    TyRen S Ψ Φ Δ (Ψ + m) (Φ.subst (wkIv m)) (ctxWkI m Δ) id (· + m) :=
  { inj := fun i j h => by simpa using h
    bound := fun i hi => by simp; omega
    hscoped := scoped_subst (scoped_of_wf hw) fun i hi => show i + m < Ψ + m by omega
    ent := ent_refl _
    look := fun x B hx => by rw [lookup_wkI, id, hx]; rfl
    wf := (wfAll_of_wf hS hw).wk m (ent_refl _) }

theorem dupN_subst_eq (m : Nat) (σ : Nat → Tm) (n : Nat) :
    dupN m σ n = (σ n).subst (rS id) (rI (· + m)) := by rw [dupN_eq]; rfl

theorem TySub.dupI (hS : SigClosed S) {Ψ Φ Γ Ψ' Φ' Δ σ τ} (h : TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ) (m : Nat) :
    TySub S (Ψ + m) (Φ.subst (wkIv m)) (ctxWkI m Γ) (Ψ' + m) (Φ'.subst (wkIv m)) (ctxWkI m Δ)
      (dupN m σ) (IupN m τ) :=
  { bound := fun i hi => by
      rw [IupN_eq]; split
      · show i < Ψ' + m; omega
      · exact scoped_subst (h.bound (i - m) (by omega)) fun j hj => show j + m < Ψ' + m by omega
    hscoped := scoped_subst h.hscoped fun j hj => show j + m < Ψ' + m by omega
    ent := by
      refine ent_trans (ent_subst h.ent (wkIv m)) ?_
      rw [I_subst_subst, I_subst_subst]
      apply eq_ent; apply I_eq_subst_congr; intro i
      simp only [wkIv, I.subst, IupN_add]; exact I_eq_refl _
    wf := by
      have := (wfAll_of_wf hS h.wf).wk m (Φ1 := Φ'.subst (wkIv m)) (ent_refl _)
      exact this.wf (scoped_subst h.hscoped fun j hj => show j + m < Ψ' + m by omega)
    look := fun x A hx => by
      rw [lookup_wkI, Option.map_eq_some_iff] at hx
      obtain ⟨A0, hA0, rfl⟩ := hx
      have := (ren_ty hS (h.look x A0 hA0)).2 (tyRen_wkI hS h.wf m)
      have e1 : (σ x).subst (rS id) (rI (· + m)) = dupN m σ x := (dupN_subst_eq m σ x).symm
      have e2 : (A0.subst σ τ).subst (rS id) (rI (· + m)) =
          (A0.subst Tm.var (wkIv m)).subst (dupN m σ) (IupN m τ) := by
        simp only [subst_subst]
        apply subst_congr
        · intro n; simp only [Tm.subst, dupN_eq]; rfl
        · intro i; simp only [I.subst, wkIv, IupN_add]; rfl
      rw [e1, e2] at this
      exact this }

/-- The substitution of a context extension. -/
def subExt (σ : Nat → Tm) (τ : Nat → I) : List Tm → List Tm
  | [] => []
  | A :: E => A.subst (upN E.length σ) τ :: subExt σ τ E

theorem TySub.ext (hS : SigClosed S) {Ψ Φ Γ Ψ' Φ' Δ σ τ} (h : TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ) :
    ∀ E : List Tm, CtxSub S Ψ Φ (E ++ Γ) →
      TySub S Ψ Φ (E ++ Γ) Ψ' Φ' (subExt σ τ E ++ Δ) (upN E.length σ) τ
  | [], _ => h
  | A :: E, hc => by
    have := (TySub.ext hS h E hc.1).upC hS hc
    simpa [subExt, upN] using this

theorem subExt_range_append (σ : Nat → Tm) (τ : Nat → I) (f : Nat → Tm) (E2 : List Tm) (k : Nat) :
    subExt σ τ ((List.range k).reverse.map f ++ E2) =
      (List.range k).reverse.map (fun j => (f j).subst (upN (j + E2.length) σ) τ) ++ subExt σ τ E2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.map_cons, List.cons_append, subExt]
    rw [ih]
    congr 3
    simp [List.length_append, List.length_map, List.length_reverse, List.length_range]

theorem upN_dupN (k m : Nat) (σ : Nat → Tm) : upN k (dupN m σ) = dupN m (upN k σ) := by
  funext n
  simp only [upN_eq, dupN_eq]
  split
  · rfl
  · rw [subst_subst, subst_subst]
    apply subst_congr
    · intro x; rfl
    · intro i; rfl

theorem subExt_wkI (σ : Nat → Tm) (τ : Nat → I) (m : Nat) (E : List Tm) :
    subExt (dupN m σ) (IupN m τ) (ctxWkI m E) = ctxWkI m (subExt σ τ E) := by
  induction E with
  | nil => rfl
  | cons A E ih =>
    simp only [ctxWkI, List.map_cons, subExt, List.length_map] at *
    rw [ih]
    congr 1
    rw [upN_dupN, subst_subst, subst_subst]
    apply subst_congr
    · intro n; simp only [Tm.subst, dupN_eq]; rfl
    · intro i; simp only [I.subst, wkIv, IupN_add]; rfl

theorem TySub.extI (hS : SigClosed S) {Ψ Φ Γ Ψ' Φ' Δ σ τ} (h : TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ) (m : Nat)
    {ψ : I} (hψ : ψ.Scoped m) (E : List Tm)
    (hctx : CtxSub S (Ψ + m) (KubusCore.cof (Φ.ren (· + m)) ψ) (ctxWkI m (E ++ Γ))) :
    TySub S (Ψ + m) (KubusCore.cof (Φ.ren (· + m)) ψ) (ctxWkI m (E ++ Γ))
      (Ψ' + m) (KubusCore.cof (Φ'.ren (· + m)) ψ) (ctxWkI m (subExt σ τ E ++ Δ))
      (dupN m (upN E.length σ)) (IupN m τ) := by
  have hψ' : ψ.subst (IupN m τ) = ψ := subst_scoped_id hψ fun i hi => IupN_lt hi τ
  have h1 := (h.dupI hS m).restrict (Ξ := KubusCore.cof (Φ'.ren (· + m)) ψ)
    ⟨(h.dupI hS m).hscoped, scoped_mono hψ (by omega)⟩ (ent_and_left _ _)
  have hent : I.Entails (KubusCore.cof (Φ'.ren (· + m)) ψ)
      ((KubusCore.cof (Φ.ren (· + m)) ψ).subst (IupN m τ)) := by
    show I.Entails (.and _ ψ) (.and _ (ψ.subst _))
    rw [hψ', I_ren_add_eq, I_ren_add_eq]
    exact ent_and_mono (h.dupI hS m).ent (ent_refl _)
  have h1' : TySub S (Ψ + m) (KubusCore.cof (Φ.ren (· + m)) ψ) (ctxWkI m Γ) (Ψ' + m)
      (KubusCore.cof (Φ'.ren (· + m)) ψ) (ctxWkI m Δ) (dupN m σ) (IupN m τ) :=
    ⟨h1.bound, h1.hscoped, hent, h1.look, h1.wf⟩
  rw [ctxWkI_append] at hctx
  have h2 := h1'.ext hS _ hctx
  rw [subExt_wkI, ctxWkI, List.length_map, ← ctxWkI, upN_dupN] at h2
  rw [ctxWkI_append, ctxWkI_append]
  exact h2

/-- The branch context of the eliminator, substituted. -/
theorem TySub.branch {Ψ Φ Γ Ψ' Φ' Δ σ τ} (hS : SigClosed S) (h : TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ)
    {d : Nat} {D : DataDecl} {c : Nat} {C : Ctor} (hd : S[d]? = some (.data D))
    (hc : D.ctors[c]? = some C) {ps P : Tm} (hps : IsList ps) (hlen : ps.toList.length = D.params.length)
    {ψ : I} (hψ : ψ.Scoped C.dims)
    (hctx : CtxSub S (Ψ + C.dims) (KubusCore.cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)) :
    TySub S (Ψ + C.dims) (KubusCore.cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)
      (Ψ' + C.dims) (KubusCore.cof (Φ'.ren (· + C.dims)) ψ)
      (D.branchCtx d C (ps.subst σ τ) (P.subst (Tm.up σ) τ) Δ)
      (dupN C.dims (upN (C.args.length + C.recPos.length) σ)) (IupN C.dims τ) := by
  let E := (List.range C.recPos.length).reverse.map (DataDecl.branchIhTy C P) ++
    (List.range C.args.length).reverse.map (DataDecl.branchArgTy d D.params.length C ps)
  have hsrc : D.branchCtx d C ps P Γ = ctxWkI C.dims (E ++ Γ) := by
    unfold DataDecl.branchCtx; rw [Ctx_ren_add_eq, List.append_assoc]
  have hlenE : E.length = C.args.length + C.recPos.length := by
    simp [E, List.length_append, List.length_map, List.length_reverse, List.length_range]; omega
  have hE : subExt σ τ E =
      (List.range C.recPos.length).reverse.map (DataDecl.branchIhTy C (P.subst (Tm.up σ) τ)) ++
      (List.range C.args.length).reverse.map
        (DataDecl.branchArgTy d D.params.length C (ps.subst σ τ)) := by
    simp only [E]
    rw [subExt_range_append, ← List.append_nil (List.map _ (List.range C.args.length).reverse),
      subExt_range_append]
    simp only [subExt, List.length_nil, List.append_nil, List.length_map, List.length_reverse,
      List.length_range, Nat.add_zero]
    congr 1
    · apply List.map_congr_left; intro s hs
      have hs' := List.mem_range.1 (List.mem_reverse.1 hs)
      rw [show s + C.args.length = C.args.length + s by omega, branchIhTy_subst _ _ hs']
    · apply List.map_congr_left; intro k _
      rw [branchArgTy_subst _ _ (argTy_closed hS hd hc k) hps hlen]
  have htgt : D.branchCtx d C (ps.subst σ τ) (P.subst (Tm.up σ) τ) Δ =
      ctxWkI C.dims (subExt σ τ E ++ Δ) := by
    rw [hE]; unfold DataDecl.branchCtx; rw [Ctx_ren_add_eq, List.append_assoc]
  rw [hsrc] at hctx ⊢
  rw [htgt, ← hlenE]
  exact h.extI hS C.dims hψ E hctx

/-! ## Congruence of λ in the domain -/

theorem upShift_inst0 (B : Tm) : (B.ren (upRen Nat.succ) id).inst (.var 0) = B := by
  simp only [Tm.inst, ren_eq_subst, subst_subst]
  exact subst_id_of (fun n => by cases n <;> rfl) (fun i => rfl) B

/-- `λ` is a congruence also in its domain (by η and β). -/
theorem lam_congr' (hS : SigClosed S) {Ψ Φ Γ A A' B t t' l l'} (hA : HasTy0 S Ψ Φ Γ A (univ l'))
    (hpi : HasTy0 S Ψ Φ Γ (pi A B) (univ l)) (hl' : HasTy0 S Ψ Φ Γ (lam A' t') (pi A B))
    (htt : EqTm0 S Ψ Φ (A :: Γ) t t' B) : EqTm0 S Ψ Φ Γ (lam A t) (lam A' t') (pi A B) := by
  have heta := EqTm0.piEta hl'
  have hw := HasTy0.wk hS hA hl'
  have hv : HasTy0 S Ψ Φ (A :: Γ) (var 0) A.shift := HasTy0.var (Wf0.cons hA) rfl
  simp only [Tm.shift, Tm.ren] at hw
  have happ := HasTy0.app hw hv
  rw [upShift_inst0] at happ
  have hbeta := EqTm0.piBeta happ
  rw [upShift_inst0] at hbeta
  have hlam := EqTm0.lam hpi (EqTm0.trans htt (EqTm0.symm hbeta))
  exact EqTm0.trans hlam (EqTm0.symm heta)

theorem dinst_one_consI (A : Tm) (σ : Nat → Tm) (τ : Nat → I) :
    (A.dinst .one).subst σ τ = A.subst σ (consI .one τ) := dinst_consI A .one σ τ

/-- Restrict a second substitution to the first one's cofibration. -/
theorem TySub.underCofE {Ψ Φ Γ Ψ' Φ' Δ σ τ} (h : TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ) {φ φ1 : I}
    (hφ1 : φ1.Scoped Ψ') (he : I.Entails φ1 (φ.subst τ)) :
    TySub S Ψ (cof Φ φ) Γ Ψ' (cof Φ' φ1) Δ σ τ :=
  { bound := h.bound
    hscoped := ⟨h.hscoped, hφ1⟩
    ent := ent_and_mono h.ent he
    look := fun x A hx => HasTy0.restrict ⟨h.hscoped, hφ1⟩ (ent_and_left _ _) (h.look x A hx)
    wf := h.wf.restrict ⟨h.hscoped, hφ1⟩ (ent_and_left _ _) }

theorem EqSub.underCof {Ψ Γ Ψ' Φ' Δ σ1 τ1 σ2 τ2} (h : EqSub S Ψ Γ Ψ' Φ' Δ σ1 τ1 σ2 τ2) {φ1 : I}
    (hs : Φ'.Scoped Ψ') (hφ1 : φ1.Scoped Ψ') : EqSub S Ψ Γ Ψ' (cof Φ' φ1) Δ σ1 τ1 σ2 τ2 :=
  h.restrict ⟨hs, hφ1⟩ (ent_and_left _ _)

theorem tele_closed_tail {Δt : List Tm} {A : Tm} {n : Nat}
    (h : ∀ (k : Nat) (B : Tm), (A :: Δt)[k]? = some B → B.closedB (n + k) 0 = true) :
    ∀ (k : Nat) (B : Tm), Δt[k]? = some B → B.closedB (n + 1 + k) 0 = true :=
  fun k B hk => by have := h (k + 1) B hk; rwa [Nat.add_assoc, Nat.add_comm 1 k]

theorem tele_closed_head {Δt : List Tm} {A : Tm} {n : Nat}
    (h : ∀ (k : Nat) (B : Tm), (A :: Δt)[k]? = some B → B.closedB (n + k) 0 = true) :
    A.closedB n 0 = true := by simpa using h 0 A rfl

end KubusCore.Meta
