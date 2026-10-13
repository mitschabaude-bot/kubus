import KubusCore.Meta.SubstOps

/-!
# Metatheory: substitution and the instantiations of inductive types

Lifting substitutions under several binders (`upN`, `dupN`, `IupN`), and commutation of
substitution with the branch types and contexts of the eliminator, boundaries, and the
transport of constructor arguments. These need the declarations of the signature to be
closed (`SigClosed`) and the parameter lists to be literal lists of the right length.
-/

namespace KubusCore.Meta

open Tm

/-! ## Iterated lifting -/

/-- Lift a term substitution under `k` term binders. -/
def upN : Nat → (Nat → Tm) → Nat → Tm
  | 0, σ => σ
  | k + 1, σ => up (upN k σ)

/-- Lift a term substitution under `k` interval binders. -/
def dupN : Nat → (Nat → Tm) → Nat → Tm
  | 0, σ => σ
  | k + 1, σ => dupS (dupN k σ)

/-- Lift an interval substitution under `k` interval binders. -/
def IupN : Nat → (Nat → I) → Nat → I
  | 0, τ => τ
  | k + 1, τ => I.up (IupN k τ)

theorem upN_eq (k : Nat) (σ : Nat → Tm) (j : Nat) :
    upN k σ j = if j < k then .var j else (σ (j - k)).subst (fun n => .var (n + k)) I.var := by
  induction k generalizing j with
  | zero => simp [upN, subst_var]
  | succ k ih =>
    cases j with
    | zero => simp [upN, up]
    | succ j =>
      simp only [upN, up, ih]
      split
      · rename_i h; simp [h, shift, ren, upRen]
      · rename_i h
        have h' : ¬ j + 1 < k + 1 := by omega
        simp only [h', if_false, shift_eq, subst_subst]
        rw [show j + 1 - (k + 1) = j - k by omega]
        apply subst_congr
        · intro n; simp only [Tm.subst]; congr 1
        · intro i; rfl

theorem dupN_eq (m : Nat) (σ : Nat → Tm) (n : Nat) :
    dupN m σ n = (σ n).subst Tm.var (fun i => .var (i + m)) := by
  induction m with
  | zero => simp [dupN, subst_var]
  | succ m ih =>
    simp only [dupN, dupS, ih, dshift_eq, subst_subst]
    apply subst_congr
    · intro n; rfl
    · intro i; simp only [I.subst]; congr 1

theorem IupN_eq (m : Nat) (τ : Nat → I) (i : Nat) :
    IupN m τ i = if i < m then .var i else (τ (i - m)).subst (fun i => .var (i + m)) := by
  induction m generalizing i with
  | zero => simp [IupN, I_subst_var]
  | succ m ih =>
    cases i with
    | zero => simp [IupN, I.up]
    | succ i =>
      simp only [IupN, I.up, ih, I.shift, I_ren_eq]
      split
      · rename_i h; simp [h, I.subst]
      · rename_i h
        have h' : ¬ i + 1 < m + 1 := by omega
        simp only [h', if_false, I_subst_subst]
        rw [show i + 1 - (m + 1) = i - m by omega]
        apply I_subst_congr; intro i; simp only [I.subst]; congr 1

theorem upN_lt {k j : Nat} (h : j < k) (σ : Nat → Tm) : upN k σ j = .var j := by
  simp [upN_eq, h]

theorem upN_add (k j : Nat) (σ : Nat → Tm) :
    upN k σ (j + k) = (σ j).subst (fun n => .var (n + k)) I.var := by
  rw [upN_eq, if_neg (by omega), Nat.add_sub_cancel]

theorem IupN_lt {m i : Nat} (h : i < m) (τ : Nat → I) : IupN m τ i = .var i := by
  simp [IupN_eq, h]

theorem IupN_add (m i : Nat) (τ : Nat → I) :
    IupN m τ (i + m) = (τ i).subst (fun i => .var (i + m)) := by
  rw [IupN_eq, if_neg (by omega), Nat.add_sub_cancel]

theorem upN_upN (a b : Nat) (σ : Nat → Tm) : upN b (upN a σ) = upN (a + b) σ := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [upN, ih]; rfl

theorem wkN_eq (k m : Nat) (t : Tm) :
    t.wkN k m = t.subst (fun n => .var (n + k)) (fun i => .var (i + m)) := by
  rw [Tm.wkN, ren_eq_subst]

/-- Weakening past the lifted part of a lifted substitution. -/
theorem wkN_subst (t : Tm) (k m : Nat) (σ : Nat → Tm) (τ : Nat → I) :
    (t.wkN k m).subst (dupN m (upN k σ)) (IupN m τ) = (t.subst σ τ).wkN k m := by
  simp only [wkN_eq, subst_subst]
  apply subst_congr
  · intro n; simp only [Tm.subst, dupN_eq, upN_add, subst_subst]
    apply subst_congr
    · intro x; simp [Tm.subst]
    · intro i; simp [I.subst]
  · intro i; simp only [I.subst, IupN_add]

theorem wkN_subst0 (t : Tm) (k : Nat) (σ : Nat → Tm) (τ : Nat → I) :
    (t.wkN k 0).subst (upN k σ) τ = (t.subst σ τ).wkN k 0 := by
  have := wkN_subst t k 0 σ τ
  simpa [dupN, IupN] using this

/-! ## Closedness of the declarations -/

theorem paramVars_closed (np depth : Nat) : (Ctor.paramVars np depth).closedB (np + depth) 0 = true := by
  simp only [Ctor.paramVars]
  suffices ∀ L : List Nat, (∀ p ∈ L, p < np) →
      (Tm.ofList (L.map fun p => Tm.var (depth + np - 1 - p))).closedB (np + depth) 0 = true by
    exact this _ (fun p hp => List.mem_range.1 hp)
  intro L hL
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [List.map_cons, Tm.ofList, closedB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by have := hL p (List.mem_cons_self ..); omega, ih fun q hq => hL q (List.mem_cons_of_mem _ hq)⟩

theorem argTy_closed {S : Sig} (hS : SigClosed S) {d : Nat} {D : DataDecl} {c : Nat} {C : Ctor}
    (hd : S[d]? = some (.data D)) (hc : D.ctors[c]? = some C) (k : Nat) :
    (C.argTy d D.params.length k).closedB (D.params.length + k) 0 = true := by
  unfold Ctor.argTy
  split
  · rename_i A hA; exact hS.args d D c C k A hd hc hA
  · simp only [closedB]; exact paramVars_closed _ _

theorem recPos_length_le (C : Ctor) : C.recPos.length ≤ C.args.length := by
  unfold Ctor.recPos
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem transpFill_subst (A : Tm) (φ : I) (a : Tm) (σ : Nat → Tm) (τ : Nat → I) :
    (transpFill A φ a).subst (dupS σ) (I.up τ) =
      transpFill (A.subst (dupS σ) (I.up τ)) (φ.subst τ) (a.subst σ τ) := by
  simp only [transpFill]; scalc

theorem closed_toList {t : Tm} {n m : Nat} (h : t.closedB n m = true) : ∀ a ∈ t.toList, a.closedB n m = true := by
  induction t with
  | tcons a as _ iha =>
    simp only [closedB, Bool.and_eq_true] at h
    intro x hx
    simp only [Tm.toList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h.1
    · exact iha h.2 x hx
  | _ => intro x hx; simp [Tm.toList] at hx

section
variable (σ : Nat → Tm) (τ : Nat → I)

/-! ## The eliminator -/

theorem branchArgTy_subst {d np k : Nat} {C : Ctor} {ps : Tm}
    (hA : (C.argTy d np k).closedB (np + k) 0 = true) (hps : IsList ps) (hlen : ps.toList.length = np) :
    (DataDecl.branchArgTy d np C ps k).subst (upN k σ) τ = DataDecl.branchArgTy d np C (ps.subst σ τ) k := by
  unfold DataDecl.branchArgTy
  rw [substList_subst (by simp [hlen]; rw [Nat.add_comm]; exact hA)]
  congr 1
  simp only [List.map_append, List.map_map, toList_subst hps, ← List.map_reverse]
  congr 1
  · apply List.map_congr_left; intro j hj
    simp only [Function.comp, Tm.subst]; exact upN_lt (List.mem_range.1 hj) σ
  · apply List.map_congr_left; intro p _
    simp only [Function.comp]; exact wkN_subst0 p k σ τ

theorem branchIhTy_subst {C : Ctor} {s : Nat} (hs : s < C.recPos.length) (P : Tm) :
    (DataDecl.branchIhTy C P s).subst (upN (C.args.length + s) σ) τ =
      DataDecl.branchIhTy C (P.subst (up σ) τ) s := by
  have hn := recPos_length_le C
  unfold DataDecl.branchIhTy
  simp only [subst_subst]
  apply subst_congr
  · intro x; cases x with
    | zero => simp only [Tm.subst]; exact upN_lt (by omega) σ
    | succ x =>
      simp only [Tm.subst, up, shift_subst]
      rw [show x + C.args.length + s = x + (C.args.length + s) by omega, upN_add]
      apply subst_congr
      · intro n; congr 1; omega
      · intro i; rfl
  · intro i; simp [I.subst, I_subst_var]

theorem branchBody_subst (d c : Nat) (C : Ctor) (ps P : Tm) :
    (DataDecl.branchBody d c C ps P).subst
        (dupN C.dims (upN (C.args.length + C.recPos.length) σ)) (IupN C.dims τ) =
      DataDecl.branchBody d c C (ps.subst σ τ) (P.subst (up σ) τ) := by
  unfold DataDecl.branchBody
  simp only [subst_subst]
  apply subst_congr
  · intro x; cases x with
    | zero =>
      simp only [Tm.subst, wkN_subst, ofList_subst, List.map_map]
      congr 1
      · congr 1; apply List.map_congr_left; intro k hk
        have := List.mem_range.1 hk
        simp only [Function.comp, Tm.subst, dupN_eq, upN_lt (show C.recPos.length + C.args.length - 1 - k < C.args.length + C.recPos.length by omega), Tm.subst]
      · apply List.map_congr_left; intro l hl
        have := List.mem_range.1 hl
        simp only [Function.comp, I.subst, IupN_lt (show C.dims - 1 - l < C.dims by omega)]
    | succ x =>
      simp only [Tm.subst, up, shift_subst, dupN_eq]
      rw [show x + C.args.length + C.recPos.length = x + (C.args.length + C.recPos.length) by omega,
        upN_add, subst_subst]
      apply subst_congr
      · intro n; simp only [Tm.subst]; congr 1; omega
      · intro i; simp [I.subst]
  · intro i; simp only [I.subst, IupN_add]

theorem branchApp_subst (C : Ctor) (b : Tm) :
    (DataDecl.branchApp C b).subst (dupN C.dims (upN (C.args.length + C.recPos.length) σ)) (IupN C.dims τ) =
      DataDecl.branchApp C (b.subst σ τ) := by
  unfold DataDecl.branchApp
  simp only [papps_subst, apps_subst, wkN_subst, List.map_append, List.map_map]
  congr 1
  · congr 1; congr 1
    · apply List.map_congr_left; intro k hk
      have := List.mem_range.1 hk
      simp only [Function.comp, Tm.subst, dupN_eq,
        upN_lt (show C.recPos.length + C.args.length - 1 - k < C.args.length + C.recPos.length by omega)]
    · apply List.map_congr_left; intro k hk
      have := List.mem_range.1 hk
      simp only [Function.comp, Tm.subst, dupN_eq,
        upN_lt (show C.recPos.length - 1 - k < C.args.length + C.recPos.length by omega)]
  · apply List.map_congr_left; intro l hl
    have := List.mem_range.1 hl
    simp only [Function.comp, I.subst, IupN_lt (show C.dims - 1 - l < C.dims by omega)]

theorem IupN_up (m : Nat) (τ : Nat → I) : IupN m (I.up τ) = IupN (m + 1) τ := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [IupN] at *; rw [ih]

theorem dupN_dupS (m : Nat) (σ : Nat → Tm) : dupN m (dupS σ) = dupN (m + 1) σ := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [dupN] at *; rw [ih]

/-- `(i₁ … iₘ : I) → B` -/
theorem ipis_subst (m : Nat) (B : Tm) (σ : Nat → Tm) (τ : Nat → I) :
    ((List.range m).foldl (fun acc _ => Tm.ipi acc) B).subst σ τ =
      (List.range m).foldl (fun acc _ => Tm.ipi acc) (B.subst (dupN m σ) (IupN m τ)) := by
  induction m generalizing σ τ with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl, Tm.subst]
    rw [ih, IupN_up, dupN_dupS]

/-- Π-types over `List.range' a len`, with the binder of index `k` under `k` binders. -/
theorem pis_subst (f g : Nat → Tm) (base base' : Tm) (a len : Nat) (σ : Nat → Tm) (τ : Nat → I)
    (hf : ∀ k, a ≤ k → k < a + len → (f k).subst (upN k σ) τ = g k)
    (hb : base.subst (upN (a + len) σ) τ = base') :
    ((List.range' a len).foldr (fun k acc => Tm.pi (f k) acc) base).subst (upN a σ) τ =
      (List.range' a len).foldr (fun k acc => Tm.pi (g k) acc) base' := by
  induction len generalizing a with
  | zero => simpa using hb
  | succ len ih =>
    simp only [List.range'_succ, List.foldr_cons, Tm.subst]
    rw [hf a (Nat.le_refl _) (by omega)]
    congr 1
    exact ih (a + 1) (fun k h1 h2 => hf k (by omega) (by omega)) (by rw [← hb]; congr 2; omega)

theorem branchTy_subst {S : Sig} (hS : SigClosed S) {d : Nat} {D : DataDecl} {c : Nat} {C : Ctor}
    (hd : S[d]? = some (.data D)) (hc : D.ctors[c]? = some C) {ps : Tm} (hps : IsList ps)
    (hlen : ps.toList.length = D.params.length) (P : Tm) :
    (D.branchTy d c C ps P).subst σ τ = D.branchTy d c C (ps.subst σ τ) (P.subst (up σ) τ) := by
  unfold DataDecl.branchTy
  simp only [List.range_eq_range']
  have hin : ((List.range' 0 C.recPos.length).foldr
      (fun s acc => Tm.pi (DataDecl.branchIhTy C P s) acc)
      ((List.range C.dims).foldl (fun acc _ => Tm.ipi acc) (DataDecl.branchBody d c C ps P))).subst
        (upN 0 (upN C.args.length σ)) τ =
      (List.range' 0 C.recPos.length).foldr
      (fun s acc => Tm.pi (DataDecl.branchIhTy C (P.subst (up σ) τ) s) acc)
      ((List.range C.dims).foldl (fun acc _ => Tm.ipi acc)
        (DataDecl.branchBody d c C (ps.subst σ τ) (P.subst (up σ) τ))) := by
    apply pis_subst
    · intro s _ hs
      rw [upN_upN]; exact branchIhTy_subst σ τ (by omega) P
    · rw [upN_upN, Nat.zero_add, ipis_subst]
      congr 1
      exact branchBody_subst σ τ d c C ps P
  exact pis_subst _ _ _ _ 0 _ σ τ
    (fun k _ hk => branchArgTy_subst σ τ (argTy_closed hS hd hc k) hps hlen) (by
      rw [Nat.zero_add, List.range_eq_range'] at *; exact hin)
theorem dupN_upN_lt {m k j : Nat} (h : j < k) (σ : Nat → Tm) : dupN m (upN k σ) j = .var j := by
  rw [dupN_eq, upN_lt h]; rfl

theorem bndPoint_subst {C : Ctor} {ps : Tm} (hps : IsList ps) {np : Nat} (hlen : ps.toList.length = np)
    {a : Tm} (ha : a.closedB (np + C.args.length) C.dims = true) :
    (DataDecl.bndPoint C ps a).subst (dupN C.dims (upN (C.args.length + C.recPos.length) σ)) (IupN C.dims τ) =
      DataDecl.bndPoint C (ps.subst σ τ) a := by
  unfold DataDecl.bndPoint
  simp only [subst_subst]
  apply closed_subst_eq a _ _ _ _ _ _ ha
  · intro j hj
    split
    · rename_i h; simp only [Tm.subst]; exact dupN_upN_lt (by omega) σ
    · rename_i h
      rw [wkN_subst, toList_subst hps, ← List.map_reverse, List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (by simp [hlen]; omega)]
      rfl
  · intro i hi; simp only [I.subst]; exact IupN_lt hi τ

theorem closedB_con {d c : Nat} {ps as : Tm} {rs : List I} {n m : Nat}
    (h : (Tm.con d c ps as rs).closedB n m = true) :
    ps.closedB n m = true ∧ as.closedB n m = true ∧ ∀ r ∈ rs, r.Scoped m := by
  simp only [closedB, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, fun r hr => (I.scopedB_iff _ _).1 (h.2 r hr)⟩

mutual
theorem bndElim_subst {D : DataDecl} {C : Ctor} {ps bs : Tm} (hps : IsList ps) {np : Nat}
    (hlen : ps.toList.length = np) (hbs : IsList bs) :
    ∀ e : Tm, e.closedB (np + C.args.length) C.dims = true →
    (DataDecl.bndElim D C ps bs e).subst (dupN C.dims (upN (C.args.length + C.recPos.length) σ)) (IupN C.dims τ) =
      DataDecl.bndElim D C (ps.subst σ τ) (bs.subst σ τ) e
  | .var j, _ => by
    simp only [DataDecl.bndElim]
    split
    · rename_i s hs
      have : s < C.recPos.length := (List.idxOf?_eq_some_iff.1 hs).1
      simp only [Tm.subst]; exact dupN_upN_lt (by omega) σ
    · rfl
  | .con d' c' ps' as rs, h => by
    obtain ⟨_, has, hrs⟩ := closedB_con h
    simp only [DataDecl.bndElim, toList_subst hbs, List.getElem?_map]
    cases hC : D.ctors[c']? with
    | none => rfl
    | some C' =>
      cases hb : bs.toList[c']? with
      | none => rfl
      | some b =>
        simp only [Option.map_some, papps_subst, apps_subst, wkN_subst, List.map_append, List.map_map]
        congr 1
        · congr 1; congr 1
          · apply List.map_congr_left; intro a ha
            exact bndPoint_subst σ τ hps hlen (closed_toList has a ha)
          · exact bndElimArgs_subst hps hlen hbs C' 0 as has
        · conv => rhs; rw [← List.map_id rs]
          apply List.map_congr_left; intro r hr
          exact subst_scoped_id (hrs r hr) fun i hi => IupN_lt hi τ
  | .const _, _ | .univ _, _ | .pi _ _, _ | .lam _ _, _ | .app _ _, _ | .sigma _ _, _ | .pair _ _, _
  | .fst _, _ | .snd _, _ | .path _ _ _, _ | .plam _, _ | .papp _ _, _ | .ipi _, _ | .split _ _ _ _, _
  | .abort, _ | .transp _ _ _, _ | .hcomp _ _ _ _, _ | .glue _ _ _ _, _ | .glueEl _ _ _ _, _
  | .unglue _ _ _, _ | .tnil, _ | .tcons _ _, _ | .data _ _, _ | .elim _ _ _ _ _, _ => by
    simp [DataDecl.bndElim, Tm.subst]

theorem bndElimArgs_subst {D : DataDecl} {C : Ctor} {ps bs : Tm} (hps : IsList ps) {np : Nat}
    (hlen : ps.toList.length = np) (hbs : IsList bs) (C' : Ctor) :
    ∀ (k : Nat) (as : Tm), as.closedB (np + C.args.length) C.dims = true →
    (DataDecl.bndElimArgs D C ps bs C' k as).map
        (·.subst (dupN C.dims (upN (C.args.length + C.recPos.length) σ)) (IupN C.dims τ)) =
      DataDecl.bndElimArgs D C (ps.subst σ τ) (bs.subst σ τ) C' k as
  | k, .tcons a as, h => by
    simp only [closedB, Bool.and_eq_true] at h
    simp only [DataDecl.bndElimArgs, List.map_append]
    congr 1
    · split
      · simp only [List.map_cons, List.map_nil]; rw [bndElim_subst hps hlen hbs a h.1]
      · rfl
    · exact bndElimArgs_subst hps hlen hbs C' (k + 1) as h.2
  | _, .var _, _ | _, .const _, _ | _, .univ _, _ | _, .pi _ _, _ | _, .lam _ _, _ | _, .app _ _, _
  | _, .sigma _ _, _ | _, .pair _ _, _ | _, .fst _, _ | _, .snd _, _ | _, .path _ _ _, _ | _, .plam _, _
  | _, .papp _ _, _ | _, .ipi _, _ | _, .split _ _ _ _, _ | _, .abort, _ | _, .transp _ _ _, _
  | _, .hcomp _ _ _ _, _ | _, .glue _ _ _ _, _ | _, .glueEl _ _ _ _, _ | _, .unglue _ _ _, _
  | _, .tnil, _ | _, .data _ _, _ | _, .con _ _ _ _ _, _ | _, .elim _ _ _ _ _, _ => by
    simp [DataDecl.bndElimArgs]
end

/-! ## Boundaries -/

theorem bndAt_subst {b : Tm} {ps args : List Tm} {rs : List I}
    (hb : b.closedB (ps.length + args.length) rs.length = true) :
    (Ctor.bndAt b ps args rs).subst σ τ =
      Ctor.bndAt b (ps.map (·.subst σ τ)) (args.map (·.subst σ τ)) (rs.map (·.subst τ)) := by
  unfold Ctor.bndAt
  simp only [subst_subst]
  apply closed_subst_eq b _ _ _ _ _ _ hb
  · intro j hj
    simp only [List.getD_eq_getElem?_getD, ← List.map_reverse, ← List.map_append, List.getElem?_map]
    rw [List.getElem?_eq_getElem (by simp; omega)]
    rfl
  · intro i hi
    simp only [List.getD_eq_getElem?_getD, ← List.map_reverse, List.getElem?_map]
    rw [List.getElem?_eq_getElem (by simp; omega)]
    rfl

theorem cofAt_subst {ψ : I} {rs : List I} (h : ψ.Scoped rs.length) :
    (Ctor.cofAt ψ rs).subst τ = Ctor.cofAt ψ (rs.map (·.subst τ)) := by
  unfold Ctor.cofAt
  rw [I_subst_subst]
  apply subst_scoped_eq h
  intro i hi
  simp only [List.getD_eq_getElem?_getD, ← List.map_reverse, List.getElem?_map]
  rw [List.getElem?_eq_getElem (by simp; omega)]
  rfl

/-! ## Transport of constructor arguments -/

theorem transpTele_subst {argTy : Nat → Tm} {np : Nat} (hA : ∀ k, (argTy k).closedB (np + k) 0 = true)
    {psL : List Tm} (hlen : psL.length = np) (φ : I) :
    ∀ (args : List Tm) (k : Nat) (fills : List Tm), fills.length = k →
    (Tm.transpTele argTy psL φ k fills args).map (·.subst σ τ) =
      Tm.transpTele argTy (psL.map (·.subst (dupS σ) (I.up τ))) (φ.subst τ) k
        (fills.map (·.subst (dupS σ) (I.up τ))) (args.map (·.subst σ τ))
  | [], _, _, _ => rfl
  | a :: as, k, fills, hf => by
    have hL : ((argTy k).substList (fills ++ psL.reverse)).subst (dupS σ) (I.up τ) =
        (argTy k).substList (fills.map (·.subst (dupS σ) (I.up τ)) ++
          (psL.map (·.subst (dupS σ) (I.up τ))).reverse) := by
      rw [substList_subst (by simp [hf, hlen]; rw [Nat.add_comm]; exact hA k)]
      simp [List.map_append, List.map_reverse]
    simp only [Tm.transpTele, List.map_cons, Tm.subst]
    rw [hL]
    congr 1
    rw [transpTele_subst hA hlen φ as (k + 1) _ (by simp [hf])]
    simp only [List.map_cons, transpFill_subst, hL]

end

end KubusCore.Meta
