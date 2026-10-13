import Model.Canon.KanUniv

/-!
# Canonicity: projections out of constructors of an inductive type

For a constructor `c` of an inductive type without path constructors, the `j`-th argument of
an element is extracted by an eliminator (`proj_j`), whose motive is computed by a large
elimination (`Q_j`): the argument type for `c`, and an arbitrary type for the other
constructors. Then `proj_j (con c X) ≡ X_j`, which glues the arguments of a composition's tube
over the faces of its cofibration.

This file builds the branch telescopes (the arguments of a constructor as variables) and their
typing, in the empty term context over any interval context.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig}

/-! ## Weakening closed terms -/

theorem ren_closed {t : Tm} {Ψ : ℕ} (h : t.closedB 0 Ψ = true) (ρ : ℕ → ℕ) : t.ren ρ id = t := by
  rw [ren_eq_subst]
  exact (closed_subst_eq t 0 Ψ _ Tm.var _ I.var h (fun x hx => absurd hx (Nat.not_lt_zero _)) (fun _ _ => rfl)).trans
    (subst_var t)

theorem shift_closed {t : Tm} {Ψ : ℕ} (h : t.closedB 0 Ψ = true) : t.shift = t := ren_closed h _

theorem wkN_closed {t : Tm} {Ψ : ℕ} (h : t.closedB 0 Ψ = true) (n : ℕ) : t.wkN n 0 = t := ren_closed h _

theorem closed_type (hW : WfSig S) {Ψ : ℕ} {Φ : I} {t A : Tm} (h : HasTy0 S Ψ Φ [] t A) : A.closedB 0 Ψ = true := by
  obtain ⟨hT, hC⟩ := wf_typed _ S rfl hW
  rcases pre_ty (sigClosed_of_wfSig hW) hT hC h with ⟨l, hA⟩ | ⟨l, rfl, -⟩
  · exact closed_ty hA
  · rfl

/-- A closed typed term is typed in any well-formed context. -/
theorem HasTy0.of_closed (hS : SigClosed S) {Ψ : ℕ} {Φ : I} {t A : Tm} (h : HasTy0 S Ψ Φ [] t A)
    (hA : A.closedB 0 Ψ = true) : ∀ {Γ : Ctx}, Wf0 S Ψ Φ Γ → HasTy0 S Ψ Φ Γ t A
  | [], _ => h
  | _ :: Γ, .cons hB => by
    have ih := HasTy0.of_closed hS h hA (wf_of_ty hB)
    have := HasTy0.wk hS hB ih
    rwa [shift_closed (closed_ty h), shift_closed hA] at this

theorem HasTele0.of_closed (hW : WfSig S) {Ψ : ℕ} {Φ : I} {Γ : Ctx} (hw : Wf0 S Ψ Φ Γ) :
    ∀ {ts : Tm} {Δ prev : List Tm}, HasTele0 S Ψ Φ [] ts Δ prev → HasTele0 S Ψ Φ Γ ts Δ prev
  | _, _, _, .nil _ => .nil hw
  | _, _, _, .cons h0 h1 =>
    .cons (HasTy0.of_closed (sigClosed_of_wfSig hW) h0 (closed_type hW h0) hw) (HasTele0.of_closed hW hw h1)

/-- The substitution of the parameters and the first point arguments of `C` (a prefix version of
`KubusCore.Meta.tySub_points`). -/
theorem tySub_pointsP (hS : SigClosed S) (hW : WfSig S) {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C) {Ψs : ℕ} {Φs : I} {Ψ : ℕ} {Φ : I} {Γ : Ctx}
    {τ : ℕ → I} {ps : Tm} {args : List Tm} {e : ℕ}
    (hP : TySub S Ψs Φs (D.paramCtx D.params.length) Ψ Φ Γ (lsub ps.toList.reverse e) τ)
    (hat : ∀ k (hk : k < args.length), k < C.args.length →
      HasTy0 S Ψ Φ Γ args[k] ((C.argTy d D.params.length k).substList ((args.take k).reverse ++ ps.toList.reverse)))
    (hpl : ps.toList.length = D.params.length) :
    ∀ k, k ≤ args.length → k ≤ C.args.length →
      TySub S Ψs Φs (D.pointCtx d C k) Ψ Φ Γ (lsub (ptL C args ps.toList.reverse k) e) τ
  | 0, _, _ => by simpa [DataDecl.pointCtx, ptL] using hP
  | k + 1, hk, hkC => by
    have ih := tySub_pointsP hS hW hD hC hP hat hpl k (by omega) (by omega)
    rw [pointCtx_succ]
    cases hr : C.isRec k
    · simp only [hr, Bool.false_eq_true, if_false, ptL]
      have hk' : k < C.args.length := by omega
      obtain ⟨A, hA⟩ : ∃ A, C.args[k]? = some (.point A) := by
        simp only [Ctor.isRec, List.getElem?_eq_getElem hk'] at hr ⊢
        cases h : C.args[k] with
        | point A => exact ⟨A, rfl⟩
        | recur => simp [h] at hr
      obtain ⟨hcl, -, hnr, -⟩ := ((hW.2 d D hD).2.2 c C hC).1 k A hA
      have hty : C.argTy d D.params.length k = A := by simp [Ctor.argTy, hA]
      have hak : args[k]? = some args[k] := List.getElem?_eq_getElem (by omega)
      have ha := hat k (by omega) hk'
      have hFl : ((args.take k).reverse ++ ps.toList.reverse).length = k + D.params.length := by
        simp [hpl]; omega
      have heq : (A.ren (C.pointRen k) id).subst (lsub (ptL C args ps.toList.reverse k) e) τ =
          A.substList ((args.take k).reverse ++ ps.toList.reverse) := by
        rw [subst_ren, substList_eq_lsub,
          closed_subst_eq A _ 0 _ (fun y => lsub (ptL C args ps.toList.reverse k) e (C.pointRen k y))
            _ I.var hcl (fun _ _ => rfl) (fun i hi => by omega)]
        apply subst_freeIn_congr
        intro y hy
        have hyl := freeIn_lt A _ _ _ hcl hy
        have hc : y < k → C.isRec (k - 1 - y) = false := by
          intro hy'
          simp only [Ctor.noRecDeps, List.all_eq_true, List.mem_range] at hnr
          have := hnr (k - 1 - y) (by omega)
          rw [show k - 1 - (k - 1 - y) = y by omega, hy] at this
          simpa using this
        have h1 := ptL_get C args ps.toList.reverse k (by omega) y (by simp [hpl]; omega) hc
        have h2 : ((args.take k).reverse ++ ps.toList.reverse)[y]? =
            some ((args.take k).reverse ++ ps.toList.reverse)[y] :=
          List.getElem?_eq_getElem (by rw [hFl]; omega)
        rw [lsub_of_getElem? (h1.trans h2), lsub_lt (by rw [hFl]; omega)]
      rw [hty] at ha
      rw [← heq] at ha
      have := ih.cons ha
      rw [consT_lsub] at this
      rw [hty]
      simpa [List.getD_eq_getElem?_getD, hak] using this
    · simpa [hr, ptL] using ih

/-- The arguments of a constructor as variables, in the context of the arguments (the first
argument outermost). -/
def argVars (j : ℕ) : List Tm := (List.range j).map fun i => Tm.var (j - 1 - i)

/-- The context of the first `j` arguments of a branch (innermost first). -/
def BCtx (d np : ℕ) (C : Ctor) (ps : Tm) (j : ℕ) : Ctx :=
  (List.range j).reverse.map (DataDecl.branchArgTy d np C ps)

theorem argVars_length (j : ℕ) : (argVars j).length = j := by simp [argVars]

theorem substList_ren {t : Tm} {L : List Tm} (ht : t.closedB L.length 0 = true) (ρ : ℕ → ℕ) :
    (t.substList L).ren ρ id = t.substList (L.map (·.ren ρ id)) := by
  rw [substList_eq_lsub, substList_eq_lsub, ren_subst]
  exact closed_subst_eq t _ 0 _ _ _ _ ht (fun x hx => by
    rw [lsub_lt hx, lsub_lt (by simpa using hx)]; simp) (fun i hi => absurd hi (Nat.not_lt_zero _))

section
variable {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor} {ps : Tm} {Ψ : ℕ}

theorem branchArgTy_eq (hpc : ∀ p ∈ ps.toList, p.closedB 0 Ψ = true) (k : ℕ) :
    DataDecl.branchArgTy d D.params.length C ps k =
      (C.argTy d D.params.length k).substList ((List.range k).map Tm.var ++ ps.toList.reverse) := by
  unfold DataDecl.branchArgTy
  congr 2
  conv => rhs; rw [← List.map_id ps.toList.reverse]
  exact List.map_congr_left fun p hp => wkN_closed (hpc p (List.mem_reverse.1 hp)) k

theorem lookup_BCtx (hS : SigClosed S) (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C)
    (hpc : ∀ p ∈ ps.toList, p.closedB 0 Ψ = true) (hpl : ps.toList.length = D.params.length) {j i : ℕ} (hij : i < j) :
    (BCtx d D.params.length C ps j).lookup (j - 1 - i) =
      some ((C.argTy d D.params.length i).substList (((argVars j).take i).reverse ++ ps.toList.reverse)) := by
  have hg : (BCtx d D.params.length C ps j)[j - 1 - i]? = some (DataDecl.branchArgTy d D.params.length C ps i) := by
    simp only [BCtx, List.getElem?_map, List.getElem?_reverse (show j - 1 - i < (List.range j).length by simp; omega)]
    simp only [List.length_range, show j - 1 - (j - 1 - i) = i by omega, List.getElem?_range hij, Option.map_some]
  rw [lookup_of_get _ _ _ hg, branchArgTy_eq hpc,
    substList_ren (by simpa [hpl, Nat.add_comm] using argTy_closed hS hD hC i)]
  congr 2
  rw [List.map_append]
  congr 1
  · apply List.ext_getElem (by simp [argVars]; omega)
    intro x h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, List.getElem_take, argVars,
      List.length_map, List.length_range, List.length_take]
    simp only [Tm.ren, Tm.var.injEq]
    simp at h1
    omega
  · conv => rhs; rw [← List.map_id ps.toList.reverse]
    exact List.map_congr_left fun p hp => ren_closed (hpc p (List.mem_reverse.1 hp)) _

theorem argVars_get {j i : ℕ} (hi : i < (argVars j).length) : (argVars j)[i] = Tm.var (j - 1 - i) := by
  simp [argVars]

theorem argVars_rev (j : ℕ) : (argVars j).reverse = (List.range j).map Tm.var := by
  apply List.ext_getElem (by simp [argVars])
  intro x h1 h2
  simp only [List.getElem_reverse, argVars, List.getElem_map, List.getElem_range, List.length_map,
    List.length_range]
  simp at h2
  congr 1; omega

/-- The branch context of the arguments is well formed, and its variables are a telescope of
arguments. -/
theorem bc_wf (hS : SigClosed S) (hW : WfSig S) (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C) {Φ : I}
    (hpsL : IsList ps) (hpc : ∀ p ∈ ps.toList, p.closedB 0 Ψ = true) (hpl : ps.toList.length = D.params.length)
    (hpt : HasTele0 S Ψ Φ [] ps D.params []) (hdata : HasTy0 S Ψ Φ [] (.data d ps) (.univ D.level))
    (hw : Wf0 S Ψ Φ []) : ∀ j, j ≤ C.args.length → Wf0 S Ψ Φ (BCtx d D.params.length C ps j)
  | 0, _ => hw
  | j + 1, hj => by
    have ih := bc_wf hS hW hD hC hpsL hpc hpl hpt hdata hw j (by omega)
    have hty : HasTy0 S Ψ Φ (BCtx d D.params.length C ps j) (DataDecl.branchArgTy d D.params.length C ps j)
        (.univ D.level) := by
      rw [branchArgTy_eq hpc]
      cases hr : C.isRec j
      · have hjC : j < C.args.length := by omega
        obtain ⟨A, hA⟩ : ∃ A, C.args[j]? = some (.point A) := by
          simp only [Ctor.isRec, List.getElem?_eq_getElem hjC] at hr ⊢
          cases h : C.args[j] with
          | point A => exact ⟨A, rfl⟩
          | recur => simp [h] at hr
        have hAk : C.argTy d D.params.length j = A := by simp [Ctor.argTy, hA]
        have h0 : ∀ σ, TySub S 0 .one [] Ψ Φ (BCtx d D.params.length C ps j) σ (fun _ => .zero) := fun σ =>
          ⟨fun i hi => absurd hi (Nat.not_lt_zero _), scoped_of_wf ih, ent_one _,
            fun x A hx => by simp [Ctx.lookup] at hx, ih⟩
        have hP := tySub_params hS hD (HasTele0.of_closed hW ih hpt) 0 h0 D.params.length (Nat.le_refl _)
        rw [List.take_of_length_le (by omega)] at hP
        have hvars : ∀ i (hi : i < (argVars j).length), i < C.args.length →
            HasTy0 S Ψ Φ (BCtx d D.params.length C ps j) (argVars j)[i]
              ((C.argTy d D.params.length i).substList (((argVars j).take i).reverse ++ ps.toList.reverse)) := by
          intro i hi _
          rw [argVars_get hi]
          exact HasTy0.var ih (lookup_BCtx hS hD hC hpc hpl (by simpa [argVars] using hi))
        have hσ := tySub_pointsP hS hW hD hC hP hvars hpl j (by simp [argVars]) (by omega)
        have ht := (sub_ty hS (pt_typed hW (htr_of hW d) hD hC hA)).2.1 hσ
        rw [pt_inst hW hD hC hA (by simp [argVars]) (by simp [hpl]) 0 _] at ht
        rw [List.take_of_length_le (by simp [argVars]), argVars_rev] at ht
        rw [hAk]; exact ht
      · rw [argTy_rec hr]
        show HasTy0 S Ψ Φ _ (.data d ((Ctor.paramVars D.params.length j).substList _)) _
        rw [Meta.paramVars_substList hpsL hpl (by simp)]
        exact HasTy0.of_closed hS hdata rfl ih
    have e : BCtx d D.params.length C ps (j + 1) =
        DataDecl.branchArgTy d D.params.length C ps j :: BCtx d D.params.length C ps j := by
      simp [BCtx, List.range_succ]
    rw [e]; exact Wf0.cons hty

end

/-! ## Iterated abstraction and application -/

/-- `λ T₀. … λ Tₙ₋₁. b`. -/
def lams (Ts : List Tm) (b : Tm) : Tm := Ts.foldr Tm.lam b

/-- `Π T₀. … Π Tₙ₋₁. B`. -/
def pis (Ts : List Tm) (B : Tm) : Tm := Ts.foldr Tm.pi B

theorem slS_cons (a : Tm) (L : List Tm) : slS (a :: L) = consT a (slS L) := by
  funext j; cases j with
  | zero => rfl
  | succ j => simp [slS, consT]

theorem pis_typed (hS : SigClosed S) {Ψ : ℕ} {Φ : I} : ∀ (Ts : List Tm) {Γ0 : Ctx} {B : Tm} {l : ℕ},
    (∀ i (hi : i < Ts.length), HasTy0 S Ψ Φ ((Ts.take i).reverse ++ Γ0) Ts[i] (.univ l)) →
    HasTy0 S Ψ Φ (Ts.reverse ++ Γ0) B (.univ l) → HasTy0 S Ψ Φ Γ0 (pis Ts B) (.univ l)
  | [], _, _, _, _, hB => hB
  | T :: Ts, Γ0, B, l, hT, hB => by
    have h0 := hT 0 (by simp)
    simp only [List.take_zero, List.reverse_nil, List.nil_append, List.getElem_cons_zero] at h0
    refine HasTy0.pi h0 (pis_typed hS Ts (Γ0 := T :: Γ0) (fun i hi => ?_) ?_)
    · have := hT (i + 1) (by simp; omega)
      simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using this
    · simpa [List.reverse_cons, List.append_assoc] using hB

theorem lams_typed (hS : SigClosed S) {Ψ : ℕ} {Φ : I} : ∀ (Ts : List Tm) {Γ0 : Ctx} {b B : Tm} {l : ℕ},
    HasTy0 S Ψ Φ Γ0 (pis Ts B) (.univ l) → HasTy0 S Ψ Φ (Ts.reverse ++ Γ0) b B →
    HasTy0 S Ψ Φ Γ0 (lams Ts b) (pis Ts B)
  | [], _, _, _, _, _, hb => hb
  | T :: Ts, Γ0, b, B, l, hpi, hb => by
    refine HasTy0.lam hpi (lams_typed hS Ts (HasTy0.piCod hS hpi) ?_)
    simpa [List.reverse_cons, List.append_assoc] using hb

theorem pis_inv (hS : SigClosed S) {Ψ : ℕ} {Φ : I} : ∀ (Ts : List Tm) {Γ0 : Ctx} {B : Tm} {l : ℕ},
    HasTy0 S Ψ Φ Γ0 (pis Ts B) (.univ l) → ∀ k, k ≤ Ts.length →
    HasTy0 S Ψ Φ ((Ts.take k).reverse ++ Γ0) (pis (Ts.drop k) B) (.univ l)
  | _, _, _, _, h, 0, _ => by simpa using h
  | [], _, _, _, _, _ + 1, hk => by simp at hk
  | T :: Ts, Γ0, B, l, h, k + 1, hk => by
    have := pis_inv hS Ts (Γ0 := T :: Γ0) (HasTy0.piCod hS h) k (by simp at hk; omega)
    simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using this

/-- The values of a closed telescope, as a substitution out of the context of its types. -/
theorem tySub_tele {Ψ : ℕ} {Φ : I} {Ts vals : List Tm} (ht : HasTele0 S Ψ Φ [] (Tm.ofList vals) Ts []) :
    ∀ k, k ≤ Ts.length → TySub S Ψ Φ ((Ts.take k).reverse) Ψ Φ [] (slS ((vals.take k).reverse)) I.var
  | 0, _ => by
    have hw := wf_of_tele ht
    have h : TySub S Ψ Φ [] Ψ Φ [] (slS []) I.var :=
      ⟨fun i hi => hi, scoped_of_wf hw, by rw [I_subst_var]; exact ent_refl _, fun x A hx => by simp [Ctx.lookup] at hx, hw⟩
    simpa using h
  | k + 1, hk => by
    have ih := tySub_tele ht k (by omega)
    have hvl : vals.length = Ts.length := by have := tele_length ht; rwa [toList_ofList] at this
    have hv : vals[k]? = some vals[k] := List.getElem?_eq_getElem (by omega)
    have hT : Ts[k]? = some Ts[k] := List.getElem?_eq_getElem (by omega)
    have ha := tele_get ht k vals[k] Ts[k] (by rw [toList_ofList]; exact hv) hT
    rw [toList_ofList, List.append_nil, substList_eq] at ha
    have := ih.cons (A := Ts[k]) ha
    rw [← slS_cons] at this
    have e1 : (Ts.take (k + 1)).reverse = Ts[k] :: (Ts.take k).reverse := by rw [List.take_succ, hT]; simp
    have e2 : (vals.take (k + 1)).reverse = vals[k] :: (vals.take k).reverse := by rw [List.take_succ, hv]; simp
    rw [e1, e2]; exact this

theorem subst_up_inst (t : Tm) (σ : ℕ → Tm) (a : Tm) :
    (t.subst (Tm.up σ) I.var).inst a = t.subst (consT a σ) I.var := by
  rw [Tm.inst, subst_subst]
  congr 1
  · funext n; cases n with
    | zero => rfl
    | succ n => show ((σ n).shift).subst _ I.var = σ n; exact shift_inst (σ n) a

theorem subst_slS_nil (t : Tm) : t.subst (slS []) I.var = t := by
  rw [show slS [] = Tm.var from funext fun j => by simp [slS]]; exact subst_var t

/-- Iterated β-reduction of an abstraction over a closed telescope. -/
theorem apps_lams (hS : SigClosed S) {Ψ : ℕ} {Φ : I} {Ts vals : List Tm} {b B : Tm} {l : ℕ}
    (hpi : HasTy0 S Ψ Φ [] (pis Ts B) (.univ l)) (hb : HasTy0 S Ψ Φ Ts.reverse b B)
    (ht : HasTele0 S Ψ Φ [] (Tm.ofList vals) Ts []) :
    EqTm0 S Ψ Φ [] (Tm.apps (lams Ts b) vals) (b.substList vals.reverse) (B.substList vals.reverse) := by
  have hvl : vals.length = Ts.length := by have := tele_length ht; rwa [toList_ofList] at this
  have hG : ∀ k, k ≤ Ts.length → HasTy0 S Ψ Φ [] ((lams (Ts.drop k) b).subst (slS ((vals.take k).reverse)) I.var)
      ((pis (Ts.drop k) B).subst (slS ((vals.take k).reverse)) I.var) := fun k hk => by
    have hb' : HasTy0 S Ψ Φ ((Ts.drop k).reverse ++ (Ts.take k).reverse) b B := by
      rw [← List.reverse_append, List.take_append_drop]; exact hb
    have := lams_typed hS (Ts.drop k) (by simpa using pis_inv hS Ts hpi k hk) (by simpa using hb')
    exact (sub_ty hS this).2.1 (tySub_tele ht k hk)
  have claim : ∀ k, k ≤ Ts.length → EqTm0 S Ψ Φ [] (Tm.apps (lams Ts b) (vals.take k))
      ((lams (Ts.drop k) b).subst (slS ((vals.take k).reverse)) I.var)
      ((pis (Ts.drop k) B).subst (slS ((vals.take k).reverse)) I.var) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have := hG 0 hk
      simp only [List.take_zero, List.reverse_nil, List.drop_zero, subst_slS_nil] at this ⊢
      exact EqTm0.refl this
    | succ k ih =>
      intro hk
      have ih := ih (by omega)
      have hv : vals[k]? = some vals[k] := List.getElem?_eq_getElem (by omega)
      have hT : Ts[k]? = some Ts[k] := List.getElem?_eq_getElem (by omega)
      have ha := tele_get ht k vals[k] Ts[k] (by rw [toList_ofList]; exact hv) hT
      rw [toList_ofList, List.append_nil, substList_eq] at ha
      have hd : Ts.drop k = Ts[k] :: Ts.drop (k + 1) := List.drop_eq_getElem_cons (by omega)
      rw [hd] at ih
      have hGk := hG k (by omega)
      rw [hd] at hGk
      change EqTm0 S Ψ Φ [] _ (Tm.lam (Ts[k].subst _ I.var) ((lams (Ts.drop (k + 1)) b).subst (Tm.up _) I.var))
        (Tm.pi (Ts[k].subst _ I.var) ((pis (Ts.drop (k + 1)) B).subst (Tm.up _) I.var)) at ih
      change HasTy0 S Ψ Φ [] (Tm.lam (Ts[k].subst _ I.var) ((lams (Ts.drop (k + 1)) b).subst (Tm.up _) I.var))
        (Tm.pi (Ts[k].subst _ I.var) ((pis (Ts.drop (k + 1)) B).subst (Tm.up _) I.var)) at hGk
      have e1 := EqTm0.app ih (EqTm0.refl ha)
      have e2 := EqTm0.piBeta (HasTy0.app hGk ha)
      rw [subst_up_inst, subst_up_inst, ← slS_cons] at e2
      rw [subst_up_inst, ← slS_cons] at e1
      have e3 := e1.trans e2
      have et : (vals.take (k + 1)).reverse = vals[k] :: (vals.take k).reverse := by rw [List.take_add_one, hv]; simp
      have ea : Tm.apps (lams Ts b) (vals.take (k + 1)) = .app (Tm.apps (lams Ts b) (vals.take k)) vals[k] := by
        rw [List.take_add_one, hv]; simp only [Option.toList_some]; unfold Tm.apps; rw [List.foldl_append]; rfl
      rw [ea, et]; exact e3
  have := claim Ts.length (Nat.le_refl _)
  rw [List.drop_length, List.take_of_length_le (by omega)] at this
  simpa [lams, pis, substList_eq] using this

end

end Model.Canon
