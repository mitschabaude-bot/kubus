import KubusCore.Meta.PresupB

/-!
# Metatheory: iterated application through telescopes

Typing `Tm.apps` through a Π-telescope (`HasTele0` of the arguments) and `Tm.papps` through
iterated `(i : I) → _`.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-- The substitution of `substList`. -/
def slS (L : List Tm) : Nat → Tm := fun j => L.getD j (var (j - L.length))

theorem substList_eq (L : List Tm) (t : Tm) : t.substList L = t.subst (slS L) I.var := rfl

theorem substList_nil (t : Tm) : t.substList [] = t := by
  rw [substList_eq]; apply subst_id_of _ (fun _ => rfl); intro n; simp [slS]

theorem pi_substList (A B : Tm) (L : List Tm) :
    (pi A B).substList L = pi (A.substList L) (B.subst (up (slS L)) I.var) := rfl

theorem up_slS_inst (B a : Tm) (L : List Tm) :
    (B.subst (up (slS L)) I.var).inst a = B.substList (a :: L) := by
  simp only [Tm.inst, subst_subst, substList_eq]
  apply subst_congr
  · intro n; cases n with
    | zero => rfl
    | succ n =>
      simp only [up, shift_subst, slS]
      rw [subst_id_of (fun _ => rfl) (fun _ => rfl)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.length_cons]
      congr 2; omega
  · intro i; rfl

/-- Application through a Π-telescope. -/
theorem apps_tele {Ψ Φ Γ} : ∀ {as Δ prev}, HasTele0 S Ψ Φ Γ as Δ prev → ∀ {f base},
    HasTy0 S Ψ Φ Γ f ((Δ.foldr pi base).substList prev) →
    HasTy0 S Ψ Φ Γ (Tm.apps f as.toList) (base.substList (as.toList.reverse ++ prev))
  | _, _, _, .nil _, _, _, hf => hf
  | _, _, _, .cons (a := a) (as := as) (Δ := Δ) (prev := prev) ha hs, f, base, hf => by
    have h1 : HasTy0 S Ψ Φ Γ (app f a) ((Δ.foldr pi base).substList (a :: prev)) := by
      rw [← up_slS_inst]; exact HasTy0.app hf ha
    have := apps_tele hs h1
    simpa [Tm.toList, Tm.apps, List.foldl] using this

/-- `(i₁ … iₘ : I) → B`, as in `DataDecl.branchTy`. -/
def ipis (m : Nat) (B : Tm) : Tm := (List.range m).foldl (fun acc _ => Tm.ipi acc) B

theorem ipis_succ (m : Nat) (B : Tm) : ipis (m + 1) B = ipi (ipis m B) := by
  simp only [ipis, List.range_succ, List.foldl_append, List.foldl]

/-- Instantiate the interval variables `0, 1, …` by the reversed list `rs`, then continue with `τ`. -/
def consIs : List I → (Nat → I) → Nat → I
  | [], τ => τ
  | r :: rs, τ => consIs rs (consI r τ)

theorem consIs_eq : ∀ (rs : List I) (τ : Nat → I) (i : Nat),
    consIs rs τ i = rs.reverse.getD i (τ (i - rs.length))
  | [], τ, i => by simp [consIs]
  | r :: rs, τ, i => by
    rw [consIs, consIs_eq rs]
    simp only [List.reverse_cons, List.getD_eq_getElem?_getD, List.length_cons]
    by_cases h : i < rs.length
    · rw [List.getElem?_append_left (by simpa using h),
        List.getElem?_eq_getElem (by simpa using h)]; rfl
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_reverse]
      by_cases h' : i = rs.length
      · subst h'; simp [consI]
      · rw [show i - rs.length = (i - (rs.length + 1)) + 1 by omega]
        rw [List.getElem?_eq_none (by simp; omega)]; simp [consI]

theorem dup_dinst (t : Tm) (σ : Nat → Tm) (τ : Nat → I) (r : I) :
    (t.subst (dupS σ) (I.up τ)).dinst r = t.subst σ (consI r τ) := by
  simp only [Tm.dinst, Tm.dsubst, subst_subst]
  apply subst_congr
  · intro n; simp only [dupS]; rw [dshift_subst]; exact subst_id_of (fun _ => rfl) (fun _ => rfl) _
  · intro i; cases i with
    | zero => rfl
    | succ i => simp only [I.up, I.shift, I_ren_subst]; exact I_subst_var _

/-- Interval application through iterated `(i : I) → _`. -/
theorem papps_ipis {Ψ Φ Γ σ B} : ∀ (rs : List I) {g τ}, (∀ r ∈ rs, r.Scoped Ψ) →
    HasTy0 S Ψ Φ Γ g ((ipis rs.length B).subst σ τ) →
    HasTy0 S Ψ Φ Γ (Tm.papps g rs) (B.subst σ (consIs rs τ))
  | [], g, τ, _, hg => hg
  | r :: rs, g, τ, hrs, hg => by
    rw [List.length_cons, ipis_succ] at hg
    have h1 := HasTy0.iapp hg (hrs r (List.mem_cons_self ..))
    rw [dup_dinst] at h1
    exact papps_ipis rs (fun r' h => hrs r' (List.mem_cons_of_mem _ h)) h1

/-! ## Telescopes -/

/-- Retyping a telescope whose instantiated types agree. -/
theorem HasTele0.retype {Ψ Φ Γ} : ∀ {as Δ prev}, HasTele0 S Ψ Φ Γ as Δ prev → ∀ {Δ' prev'},
    Δ'.length = Δ.length →
    (∀ (k : Nat) (A A' : Tm) (L : List Tm), Δ[k]? = some A → Δ'[k]? = some A' → L.length = k →
      A.substList (L ++ prev) = A'.substList (L ++ prev')) →
    HasTele0 S Ψ Φ Γ as Δ' prev'
  | _, _, _, .nil hw, Δ', _, hl, _ => by
    cases Δ' with
    | nil => exact .nil hw
    | cons _ _ => simp at hl
  | _, _, _, .cons (a := a) (A := A) (Δ := Δ) (prev := prev) ha hs, Δ', prev', hl, he => by
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

/-- An element of a telescope is typed at its instantiated type. -/
theorem HasTele0.get {Ψ Φ Γ} : ∀ {as Δ prev}, HasTele0 S Ψ Φ Γ as Δ prev → ∀ {k : Nat} {a A : Tm},
    as.toList[k]? = some a → Δ[k]? = some A →
    HasTy0 S Ψ Φ Γ a (A.substList ((as.toList.take k).reverse ++ prev))
  | _, _, _, .nil _, k, _, _, h, _ => by simp [Tm.toList] at h
  | _, _, _, .cons (a := a) (prev := prev) ha hs, k, b, B, h, hB => by
    cases k with
    | zero =>
      simp only [Tm.toList, List.getElem?_cons_zero, Option.some.injEq] at h hB
      subst h hB; simpa using ha
    | succ k =>
      simp only [Tm.toList, List.getElem?_cons_succ] at h hB
      have := hs.get h hB
      simpa [Tm.toList] using this

/-! ## Branch types -/

theorem branchTy_eq (D : DataDecl) (d c : Nat) (C : Ctor) (ps P : Tm) :
    D.branchTy d c C ps P =
      ((List.range C.args.length).map (DataDecl.branchArgTy d D.params.length C ps)).foldr pi
        (((List.range C.recPos.length).map (DataDecl.branchIhTy C P)).foldr pi
          (ipis C.dims (DataDecl.branchBody d c C ps P))) := by
  simp only [DataDecl.branchTy, List.foldr_map, ipis]

theorem slS_lt {L : List Tm} {j : Nat} (h : j < L.length) : slS L j = L[j] := by
  simp [slS, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem slS_add (L : List Tm) (x : Nat) : slS L (x + L.length) = var x := by
  simp [slS, List.getD_eq_getElem?_getD]

theorem wkN_substList (p : Tm) (L : List Tm) : (p.wkN L.length 0).substList L = p := by
  rw [wkN_eq, substList_eq, subst_subst]
  exact subst_id_of (fun n => by simp only [Tm.subst]; exact slS_add L n) (fun i => rfl) p

theorem branchArgTy_substList (hS : SigClosed S) {d : Nat} {D : DataDecl} {c : Nat} {C : Ctor} (hD : S[d]? = some (.data D))
    (hC : D.ctors[c]? = some C) {ps : Tm} (hlen : ps.toList.length = D.params.length)
    {k : Nat} {L : List Tm} (hL : L.length = k) :
    (DataDecl.branchArgTy d D.params.length C ps k).substList L =
      (C.argTy d D.params.length k).substList (L ++ ps.toList.reverse) := by
  unfold DataDecl.branchArgTy
  rw [substList_eq _ (Tm.substList _ _), substList_subst (by
    simp only [List.length_append, List.length_map, List.length_range, List.length_reverse, hlen]
    rw [Nat.add_comm]; exact argTy_closed hS hD hC k)]
  congr 1
  simp only [List.map_append, List.map_map]
  congr 1
  · subst hL
    apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_range, Function.comp, Tm.subst]
    exact slS_lt h2
  · rw [List.map_congr_left (g := id) (fun p _ => by
      simp only [Function.comp, id]; rw [← hL]; exact wkN_substList p L), List.map_id]

theorem branchIhTy_substList {C : Ctor} (P : Tm) {s : Nat} (hs : s < C.recPos.length) {L args : List Tm}
    (hL : L.length = s) (hargs : args.length = C.args.length) :
    (DataDecl.branchIhTy C P s).substList (L ++ args.reverse) =
      P.inst (args.getD (C.recPos.getD s 0) .abort) := by
  have hk : C.recPos.getD s 0 < C.args.length := by
    have hm : C.recPos.getD s 0 ∈ C.recPos := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]; exact List.getElem_mem hs
    unfold Ctor.recPos at hm
    exact List.mem_range.1 (List.mem_filter.1 hm).1
  unfold DataDecl.branchIhTy
  generalize C.recPos.getD s 0 = k at hk ⊢
  rw [substList_eq, subst_subst]
  simp only [Tm.inst]
  apply subst_congr
  · intro x; cases x with
    | zero =>
      simp only [Tm.subst]
      rw [slS_lt (by simp only [List.length_append, List.length_reverse, hL, hargs]; omega)]
      rw [List.getElem_append_right (by rw [hL]; omega)]
      simp only [List.getElem_reverse, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by omega)]
      simp only [Option.getD_some]
      congr 1; simp only [hL, hargs]; omega
    | succ x =>
      simp only [Tm.subst]
      have := slS_add (L ++ args.reverse) x
      simp only [List.length_append, List.length_reverse, hL, hargs] at this
      rw [show x + C.args.length + s = x + (s + C.args.length) by omega, this]
  · intro i; rfl

theorem branchBody_inst {d c : Nat} {C : Ctor} {ps P : Tm} {ihs args : List Tm} {rs : List I}
    (hihs : ihs.length = C.recPos.length) (hargs : args.length = C.args.length) (hrs : rs.length = C.dims) :
    (DataDecl.branchBody d c C ps P).subst (slS (ihs.reverse ++ args.reverse)) (consIs rs I.var) =
      P.inst (con d c ps (Tm.ofList args) rs) := by
  have hLl : (ihs.reverse ++ args.reverse).length = C.args.length + C.recPos.length := by
    simp [hihs, hargs, Nat.add_comm]
  unfold DataDecl.branchBody
  simp only [Tm.inst, subst_subst]
  apply subst_congr
  · intro x; cases x with
    | zero =>
      simp only [Tm.subst, ofList_subst, List.map_map]
      congr 1
      · rw [wkN_eq, subst_subst]
        apply subst_id_of
        · intro n; simp only [Tm.subst]; rw [← hLl]; exact slS_add _ n
        · intro i; simp only [I.subst]; rw [consIs_eq]; simp [hrs]
      · congr 1
        apply List.ext_getElem (by simp [hargs])
        intro k h1 h2
        simp only [List.getElem_map, List.getElem_range, Function.comp, Tm.subst]
        simp only [List.length_map, List.length_range] at h1
        rw [slS_lt (by rw [hLl]; omega), List.getElem_append_right (by simp [hihs]; omega)]
        simp only [List.getElem_reverse]
        congr 1; simp [hihs, hargs]; omega
      · apply List.ext_getElem (by simp [hrs])
        intro l h1 h2
        simp only [List.getElem_map, List.getElem_range, Function.comp, I.subst]
        simp only [List.length_map, List.length_range] at h1
        rw [consIs_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
        simp only [List.getElem_reverse, Option.getD_some]
        congr 1; omega
    | succ x =>
      simp only [Tm.subst]
      rw [show x + C.args.length + C.recPos.length = x + (ihs.reverse ++ args.reverse).length by
        rw [hLl]; omega]
      exact slS_add _ x
  · intro i; simp only [I.subst]; rw [consIs_eq]; simp [hrs]

/-- Building a telescope typing of a literal list elementwise. -/
theorem HasTele0.ofList_of {Ψ Φ Γ} (hw : Wf0 S Ψ Φ Γ) : ∀ (as Δ prev : List Tm), as.length = Δ.length →
    (∀ (k : Nat) (a A : Tm), as[k]? = some a → Δ[k]? = some A →
      HasTy0 S Ψ Φ Γ a (A.substList ((as.take k).reverse ++ prev))) →
    HasTele0 S Ψ Φ Γ (Tm.ofList as) Δ prev
  | [], [], _, _, _ => .nil hw
  | a :: as, A :: Δ, prev, hl, h => by
    refine .cons (by simpa using h 0 a A rfl rfl) (HasTele0.ofList_of hw as Δ (a :: prev) (by simpa using hl) ?_)
    intro k b B hb hB
    have := h (k + 1) b B (by simpa using hb) (by simpa using hB)
    simpa using this
  | [], _ :: _, _, hl, _ | _ :: _, [], _, hl, _ => by simp at hl

theorem paramVars_substList {ps : Tm} (hps : IsList ps) {np : Nat} (hlen : ps.toList.length = np)
    {L : List Tm} {k : Nat} (hL : L.length = k) :
    (Ctor.paramVars np k).substList (L ++ ps.toList.reverse) = ps := by
  unfold Ctor.paramVars
  rw [substList_eq, ofList_subst]
  conv => rhs; rw [hps]
  congr 1
  apply List.ext_getElem (by simp [hlen])
  intro p h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, Tm.subst]
  rw [slS_lt (by simp [hL, hlen]; omega), List.getElem_append_right (by rw [hL]; omega)]
  simp only [List.getElem_reverse]
  congr 1; simp only [hL, hlen]; omega

theorem argTy_rec {C : Ctor} {k : Nat} (h : C.isRec k = true) (d np : Nat) :
    C.argTy d np k = data d (Ctor.paramVars np k) := by
  unfold Ctor.isRec at h
  unfold Ctor.argTy
  have : C.args[k]? = some .recur := by simpa using h
  rw [this]

theorem mem_recPos {C : Ctor} {k : Nat} (h : k ∈ C.recPos) : k < C.args.length ∧ C.isRec k = true := by
  unfold Ctor.recPos at h
  exact ⟨List.mem_range.1 (List.mem_filter.1 h).1, (List.mem_filter.1 h).2⟩

/-- A recursive argument of a constructor at parameters `ps` is in the inductive type at `ps`. -/
theorem recArg_typed {Ψ Φ Γ d np} {C : Ctor} {ps args : Tm} (hps : IsList ps) (hlen : ps.toList.length = np)
    (ha : HasTele0 S Ψ Φ Γ args (C.argTys d np) ps.toList.reverse)
    {k : Nat} (hk : k ∈ C.recPos) :
    HasTy0 S Ψ Φ Γ (args.toList.getD k .abort) (data d ps) := by
  obtain ⟨hkn, hr⟩ := mem_recPos hk
  have hl := tele_length ha
  rw [argTys_length] at hl
  have hget : args.toList[k]? = some (args.toList[k]'(by omega)) := List.getElem?_eq_getElem _
  have hA : (C.argTys d np)[k]? = some (C.argTy d np k) := by
    simp [Ctor.argTys, List.getElem?_map, List.getElem?_range hkn]
  have := ha.get hget hA
  rw [argTy_rec hr, substList_eq] at this
  simp only [Tm.subst] at this
  rw [← substList_eq, paramVars_substList hps hlen (by simp; omega)] at this
  rw [List.getD_eq_getElem?_getD, hget]; exact this

end KubusCore.Meta
