import Model.Sound

/-!
# Validity of data declarations

`DataOK` for a declaration well-formed in the sense of `DataDecl.Wf`: its argument types are
fibrant codes (from their typing in the signature with the declaration truncated to a single
generator), and its boundaries are simple with the right argument types and agree on overlaps
(from their typing in the signature truncated before each constructor, by a generic-element
argument).
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

theorem freeIn_lt_of_closedB : ∀ (t : Tm) (n d x : ℕ), t.closedB n d = true → t.freeIn x = true → x < n := by
  intro t
  induction t with
  | var y => intro n d x h1 h2; simp [Tm.closedB, Tm.freeIn] at h1 h2; omega
  | pi A B iA iB | sigma A B iA iB | lam A B iA iB =>
    intro n d x h1 h2
    simp only [Tm.closedB, Tm.freeIn, Bool.and_eq_true, Bool.or_eq_true] at h1 h2
    rcases h2 with h2 | h2
    · exact iA n d x h1.1 h2
    · have := iB (n + 1) d (x + 1) h1.2 h2; omega
  | elim j ps P bs t ip iP ib it =>
    intro n d x h1 h2
    simp only [Tm.closedB, Tm.freeIn, Bool.and_eq_true, Bool.or_eq_true] at h1 h2
    rcases h2 with ((h2 | h2) | h2) | h2
    · exact ip n d x h1.1.1.1 h2
    · have := iP (n + 1) d (x + 1) h1.1.1.2 h2; omega
    · exact ib n d x h1.1.2 h2
    · exact it n d x h1.2 h2
  | _ => intros; simp_all [Tm.closedB, Tm.freeIn] <;> aesop

theorem Ctx.lookup_eq : ∀ (Γ : Ctx) (x : ℕ), Γ.lookup x = Γ[x]?.map (fun A => A.ren (· + (x + 1)) id)
  | [], _ => rfl
  | A :: Γ, 0 => by simp [Ctx.lookup, Tm.shift]
  | A :: Γ, x + 1 => by
    simp only [Ctx.lookup, Ctx.lookup_eq Γ x, Option.map_map, List.getElem?_cons_succ]
    congr 1; funext B
    simp only [Function.comp, Tm.shift, Tm.ren_ren]
    have e1 : (fun x_1 => (x_1 + (x + 1)).succ) = (fun y => y + (x + 1 + 1)) := by funext y; omega
    rw [e1]; rfl

/-! ### Signatures extended by one declaration -/

section ext

variable (S0 : Sig) (E : DataDecl)

theorem sigUpTo_ext : sigUpTo (S0 ++ [.data E]) S0.length = sigV S0 := by
  have := sigUpTo_take (S0 ++ [.data E]) (K := S0.length) S0.length le_rfl
  rw [← this, List.take_left' rfl]; rfl

theorem agree_ext : SigV.AgreeLt S0.length (sigV S0) (sigV (S0 ++ [.data E])) := by
  have := sigUpTo_agree (S0 ++ [Entry.data E]) (k := S0.length) (S0 ++ [Entry.data E]).length (by simp)
  rwa [sigUpTo_ext] at this

theorem sem_ext {A : Tm} (hA : A.ConstsLt S0.length) :
    sem (S0 ++ [.data E]) A = interp (sigV S0) univC TyCode A :=
  (interp_congr_cst _ _ (agree_ext S0 E) A hA).symm

theorem entry_ext : (S0 ++ [.data E])[S0.length]? = some (.data E) := by simp

end ext

/-! ### List values -/

theorem plist_pair (a b : V) (n : ℕ) : plist (ZFSet.pair a b) (n + 1) = a :: plist b n := by
  simp only [plist, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp [vnth]
  · apply List.map_congr_left; intro i _; simp [vnth]

theorem listLen_vlist : ∀ {v : V} {n : ℕ}, ListLen v n → v = vlist (plist v n)
  | v, 0, h => by simp [ListLen] at h; simp [h, plist, vlist]
  | v, n + 1, h => by
    obtain ⟨⟨a, b, rfl⟩, h2⟩ := h
    simp only [π2_pair] at h2
    rw [plist_pair, vlist, ← listLen_vlist h2]

theorem sem_ofList_vlist (S : Sig) (L : List Tm) (ρ : IEnv m) (γ : ℕ → V) :
    sem S (Tm.ofList L) m ρ γ = vlist (L.map fun t => sem S t m ρ γ) := by
  induction L with
  | nil => rfl
  | cons t L ih => simp only [Tm.ofList, List.map_cons, vlist]; rw [← ih]; rfl

theorem ParamsOK.restr {σ : SigV} {D : DataDecl} {ps : RV m} (h : ParamsOK σ D m ps) (g : Hom n m) :
    ParamsOK σ D n (fun k f => ps k (g.comp f)) := fun k f => h k (g.comp f)

/-- The generator of a truncated declaration, as an element. -/
def genV (c n : ℕ) (ctors : List Ctor) : V := conV ctors n c [] []

/-! ### Environments of argument contexts -/

/-- The environment of an argument context with Kripke-value junk out of range. -/
def argEnvKV (n : ℕ) (ps pre : List V) : ℕ → V := fun x => (pre.reverse ++ ps.reverse).getD x (emptyC n)

/-- Earlier arguments with the recursive ones replaced by `gv`. -/
def genPre (C : Ctor) (gv : V) (pre : List V) : List V := pre.mapIdx fun i a => if C.isRec i then gv else a

theorem genPre_length (C : Ctor) (gv : V) (pre : List V) : (genPre C gv pre).length = pre.length := by
  simp [genPre]

theorem genPre_getElem (C : Ctor) (gv : V) (pre : List V) (i : ℕ) (hi : i < (genPre C gv pre).length) :
    (genPre C gv pre)[i] = if C.isRec i then gv else pre[i]'(by simpa [genPre_length] using hi) := by
  simp [genPre]

theorem genPre_take (C : Ctor) (gv : V) (pre : List V) (i : ℕ) :
    (genPre C gv pre).take i = genPre C gv (pre.take i) := by
  apply List.ext_getElem (by simp [genPre_length])
  intro q h1 h2
  simp only [List.getElem_take, genPre_getElem]

theorem argEnvKV_eq_of_lt {n : ℕ} {ps pre : List V} {x : ℕ} (hx : x < pre.length + ps.length) :
    argEnvKV n ps pre x = (pre.reverse ++ ps.reverse)[x]'(by simp; omega) := by
  simp [argEnvKV, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega : x < (pre.reverse ++ ps.reverse).length)]

theorem argEnv_eq_of_lt {ps pre : List V} {x : ℕ} (hx : x < pre.length + ps.length) :
    argEnv ps pre x = (pre.reverse ++ ps.reverse)[x]'(by simp; omega) := by
  simp [argEnv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega : x < (pre.reverse ++ ps.reverse).length)]

/-- Shifting the environment of an argument context drops its most recent entries. -/
theorem argEnvKV_shift {n : ℕ} (ps pre : List V) {x : ℕ} (hx : x < pre.length) :
    (fun y => argEnvKV n ps pre (y + (x + 1))) = argEnvKV n ps (pre.take (pre.length - 1 - x)) := by
  funext y
  simp only [argEnvKV, List.getD_eq_getElem?_getD]
  rw [show y + (x + 1) = (x + 1) + y by omega, ← List.getElem?_drop, List.drop_append_of_le_length (by simp; omega),
    List.drop_reverse, show pre.length - (x + 1) = pre.length - 1 - x by omega]

theorem argEnvKV_shift_ps {n : ℕ} (ps pre : List V) {x : ℕ} (hx : pre.length ≤ x) :
    (fun y => argEnvKV n ps pre (y + (x + 1))) = argEnvKV n (ps.take (ps.length - (x + 1 - pre.length))) [] := by
  funext y
  simp only [argEnvKV, List.getD_eq_getElem?_getD, List.reverse_nil, List.nil_append]
  rw [show y + (x + 1) = (x + 1) + y by omega, ← List.getElem?_drop, List.drop_append,
    List.drop_eq_nil_of_le (by simp; omega), List.nil_append, List.drop_reverse]
  simp

theorem noRecDeps_point {C : Ctor} {i : ℕ} {A : Tm} (h : C.noRecDeps i A = true) {x : ℕ} (hx : x < i)
    (hf : A.freeIn x = true) : C.isRec (i - 1 - x) = false := by
  unfold Ctor.noRecDeps at h
  have := List.all_eq_true.1 h (i - 1 - x) (List.mem_range.2 (by omega))
  rw [show i - 1 - (i - 1 - x) = x by omega, hf] at this
  simpa using this

/-- The interpretation of a point argument type at the generic environment is `argTyRaw`. -/
theorem sem_argTy_eq (S0 : Sig) (E D : DataDecl) (hsyn : DataSyn S0.length D) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) {i : ℕ} {A : Tm} (hA : C.args[i]? = some (.point A)) (psv : V) (pre : List V)
    (hi : i ≤ pre.length) (gv : V) :
    sem (S0 ++ [.data E]) A n (fun _ => DM.zero n)
      (argEnvKV n (plist psv D.params.length) (genPre C gv (pre.take i))) =
      argTyRaw (sigV S0) D S0.length c i n psv pre := by
  obtain ⟨hcl, hcs, hnr⟩ := hsyn.2.2 c C hC i A hA
  have harg : (D.ctors.getD c default).argTy S0.length D.params.length i = A := by
    rw [getD_ctors hC]; simp [Ctor.argTy, hA]
  rw [argTyRaw, harg, sem_ext S0 E hcs]
  refine interp_congr_free _ _ _ A n _ _ _ fun x hx => ?_
  have hxl := freeIn_lt_of_closedB A _ 0 x hcl hx
  have hgl : (genPre C gv (pre.take i)).length = i := by simp [genPre_length]; omega
  rw [argEnvKV_eq_of_lt (by simp [plist, hgl]; omega), argEnv_eq_of_lt (by simp [plist]; omega)]
  by_cases hxi : x < i
  · rw [List.getElem_append_left (by simp [hgl]; omega), List.getElem_append_left (by simp; omega)]
    simp only [List.getElem_reverse, genPre_getElem, List.getElem_take]
    have hq := noRecDeps_point hnr hxi hx
    simp only [hgl, List.length_take, Nat.min_eq_left hi] at *
    rw [if_neg (by simp [hq])]
  · rw [List.getElem_append_right (by simp [hgl]; omega), List.getElem_append_right (by simp; omega)]
    simp [hgl, Nat.min_eq_left hi]

theorem sem_paramVars_rv (S : Sig) {σ : SigV} {D : DataDecl} {ps : RV m} (hps : ParamsOK σ D m ps) (g : Hom n m)
    (preL : List V) {i : ℕ} (hi : preL.length = i) (ρ : IEnv n) :
    (fun k (f : Hom k n) => sem S (Ctor.paramVars D.params.length i) k (IEnv.restr ρ f)
      (TEnv.restr (argEnvKV n (plist (ps n g) D.params.length) preL) f)) = fun k f => ps k (g.comp f) := by
  subst hi
  funext k f
  rw [Ctor.paramVars, sem_ofList_vlist, listLen_vlist (hps k (g.comp f)).1]
  congr 1
  simp only [plist, List.map_map]
  apply List.map_congr_left
  intro p hp
  rw [List.mem_range] at hp
  simp only [Function.comp, sem_var, TEnv.restr]
  rw [(hps n g).2.2 k f p hp, argEnvKV_eq_of_lt (by simp [plist]; omega),
    List.getElem_append_right (by simp; omega)]
  simp only [List.getElem_reverse, plist, List.getElem_map, List.getElem_range, List.length_map, List.length_range,
    List.length_reverse]
  congr 2; omega

/-! ### Argument types are well-formed codes -/

theorem argCtx_lt (D : DataDecl) (d : ℕ) (C : Ctor) (j x : ℕ) (hx : x < j) :
    (D.argCtx d C j)[x]? = some (C.argTy d D.params.length (j - 1 - x)) := by
  rw [DataDecl.argCtx, List.getElem?_append_left (by simp; omega), List.getElem?_map,
    List.getElem?_reverse (by simp; omega), List.getElem?_range (by simp; omega)]
  simp

theorem argCtx_ge (D : DataDecl) (d : ℕ) (C : Ctor) (j x : ℕ) (hx : j ≤ x) (hx' : x < j + D.params.length) :
    (D.argCtx d C j)[x]? = some (D.params[D.params.length - 1 - (x - j)]'(by omega)) := by
  rw [DataDecl.argCtx, List.getElem?_append_right (by simp; omega), DataDecl.paramCtx, List.take_length]
  simp only [List.length_map, List.length_reverse, List.length_range]
  rw [List.getElem?_reverse (by omega), List.getElem?_eq_getElem (by omega)]

theorem truncate_gen (D : DataDecl) {c0 : ℕ} (hc0 : c0 ≤ D.ctors.length) :
    (D.truncate c0).ctors[c0]? = some { args := [], dims := 0, bnd := [] } := by
  simp [DataDecl.truncate, Nat.min_eq_left hc0]

theorem genV_mem {S0 : Sig} {D : DataDecl} {c0 : ℕ} (hc0 : c0 ≤ D.ctors.length) {n : ℕ} {ps : RV n} :
    genV c0 n (D.truncate c0).ctors ∈ El (dataC (dataSD (sigV S0) (D.truncate c0) S0.length n ps)) (Hom.id n) := by
  rw [mem_El_dataC]
  exact DElem.con (C := { args := [], dims := 0, bnd := [] }) (truncate_gen D hc0) rfl rfl
    (fun j a ha => by simp at ha) (fun j a ha => by simp at ha)

theorem sem_rho_irrel (S : Sig) {A : Tm} {k : ℕ} (hA : A.closedB k 0 = true) (ρ ρ' : IEnv n) (γ : ℕ → V) :
    sem S A n ρ γ = sem S A n ρ' γ :=
  interp_congr_closed _ _ _ A k 0 hA n ρ ρ' γ γ (fun _ h => absurd h (by omega)) (fun _ _ => rfl)

section argty

variable (S0 : Sig) (D : DataDecl) (hsyn : DataSyn S0.length D)
  {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {m : ℕ} {ps : RV m} (hps : ParamsOK (sigV S0) D m ps)

include hsyn hC hps in
theorem isPoint_argCtx (c0 : ℕ) (hc0 : c0 ≤ D.ctors.length) {Φ : I} {j : ℕ} {n : ℕ} (g : Hom n m)
    (ρ : IEnv n) (hρ : (ival ρ Φ).holds) {pre : List V} (hjp : j ≤ pre.length)
    (hjC : j ≤ C.args.length)
    (hpt : ∀ i (hi : i < j), C.isRec i = false →
      pre[i]'(by omega) ∈ El (argTyRaw (sigV S0) D S0.length c i n (ps n g) pre) (Hom.id n) ∧ IsKV n (pre[i]'(by omega))) :
    IsPoint (S0 ++ [.data (D.truncate c0)]) Φ (D.argCtx S0.length C j) n ρ
      (argEnvKV n (plist (ps n g) D.params.length) (genPre C (genV c0 n (D.truncate c0).ctors) (pre.take j))) := by
  set np := D.params.length
  set gv := genV c0 n (D.truncate c0).ctors
  have hgl : (genPre C gv (pre.take j)).length = j := by simp [genPre_length]; omega
  have hpl : (plist (ps n g) np).length = np := by simp [plist]
  refine ⟨hρ, fun x B hB => ?_, fun x => ?_⟩
  · rw [Ctx.lookup_eq] at hB
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.1 hB
    rw [sem_ren]
    by_cases hxj : x < j
    · rw [argCtx_lt D _ C j x hxj] at hT
      cases hT
      rw [show (fun y => argEnvKV n (plist (ps n g) np) (genPre C gv (pre.take j)) (y + (x + 1))) =
          argEnvKV n (plist (ps n g) np) (genPre C gv (pre.take (j - 1 - x))) by
        rw [argEnvKV_shift _ _ (by omega), hgl, genPre_take, List.take_take, Nat.min_eq_left (by omega)]]
      rw [argEnvKV_eq_of_lt (by omega), List.getElem_append_left (by simp; omega), List.getElem_reverse,
        genPre_getElem]
      simp only [hgl]
      cases hA : C.args[j - 1 - x]? with
      | none => have := (List.getElem?_eq_none_iff.1 hA); omega
      | some a =>
        cases a with
        | point A =>
          have hr : C.isRec (j - 1 - x) = false := by simp [Ctor.isRec, hA]
          rw [if_neg (by simp [hr]), List.getElem_take]
          have harg : C.argTy S0.length np (j - 1 - x) = A := by simp [Ctor.argTy, hA]
          rw [harg, sem_rho_irrel _ (hsyn.2.2 c C hC _ A hA).1 _ (fun _ => DM.zero n),
            sem_argTy_eq S0 _ D hsyn hC hA (ps n g) pre (by omega)]
          exact (hpt _ (by omega) hr).1
        | recur =>
          have hr : C.isRec (j - 1 - x) = true := by simp [Ctor.isRec, hA]
          rw [if_pos hr]
          have harg : C.argTy S0.length np (j - 1 - x) = .data S0.length (Ctor.paramVars np (j - 1 - x)) := by
            simp [Ctor.argTy, hA]
          rw [harg, sem_data (entry_ext S0 _), sigUpTo_ext]
          have hpv := sem_paramVars_rv (i := j - 1 - x) (S0 ++ [.data (D.truncate c0)]) hps g
            (genPre C gv (pre.take (j - 1 - x))) (by simp [genPre_length]; omega) (fun i => ρ (id i))
          unfold psRV
          rw [hpv, if_pos (show ParamsOK (sigV S0) (D.truncate c0) n _ from hps.restr g)]
          exact genV_mem hc0
    · by_cases hxp : x < j + np
      · rw [argCtx_ge D _ C j x (by omega) hxp] at hT
        cases hT
        set p := np - 1 - (x - j)
        rw [argEnvKV_shift_ps _ _ (by omega), hgl, hpl, show np - (x + 1 - j) = p by omega]
        rw [sem_ext S0 _ (hsyn.2.1 p _ (List.getElem?_eq_getElem _)).2]
        have hm := ((hps n g).2.1 p (by omega)).2
        rw [argEnvKV_eq_of_lt (by omega), List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_reverse, List.length_reverse, hgl, hpl]
        have e : (plist (ps n g) np)[np - 1 - (x - j)]'(by omega) = vnth (ps n g) p := by
          simp [plist, p]
        rw [e]
        convert hm using 2
        refine interp_congr_closed _ _ _ _ p 0 (hsyn.2.1 p _ (List.getElem?_eq_getElem _)).1 n _ _ _ _
          (fun _ h => absurd h (by omega)) fun y hy => ?_
        rw [argEnvKV_eq_of_lt (by simp [plist]; omega), argEnv_eq_of_lt (by simp [plist]; omega)]
        simp [plist, List.take_take, Nat.min_eq_left (show p ≤ np by omega)]
      · have := List.getElem?_eq_none_iff.2 (show (D.argCtx S0.length C j).length ≤ x by
          simp [DataDecl.argCtx, DataDecl.paramCtx]; omega)
        rw [this] at hT; cases hT
  · by_cases hx : x < j + np
    · rw [argEnvKV_eq_of_lt (by omega)]
      by_cases hxj : x < j
      · rw [List.getElem_append_left (by simp; omega), List.getElem_reverse, genPre_getElem]
        split
        · exact isKV_conV _ _ _ _
        · simp only [hgl, List.getElem_take]
          rename_i hr
          exact (hpt _ (by omega) (by simpa [hgl] using hr)).2
      · rw [List.getElem_append_right (by simp; omega), List.getElem_reverse]
        simp only [hgl, plist, List.getElem_map, List.getElem_range]
        exact ((hps n g).2.1 _ (by simp [plist] at *; omega)).1
    · simp only [argEnvKV, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp; omega), Option.getD_none]
      exact isKV_mkKV _

theorem restr_argEnvKV (ps pre : List V) (h : Hom k n) :
    TEnv.restr (argEnvKV n ps pre) h = argEnvKV k (ps.map (res h)) (pre.map (res h)) := by
  funext x
  simp only [TEnv.restr, argEnvKV, List.getD_eq_getElem?_getD]
  rw [← List.map_reverse, ← List.map_reverse, ← List.map_append, List.getElem?_map]
  cases (pre.reverse ++ ps.reverse)[x]? <;> simp [res_emptyC]

theorem genPre_map (C : Ctor) (gv : V) (pre : List V) (f : V → V) :
    (genPre C gv pre).map f = genPre C (f gv) (pre.map f) := by
  apply List.ext_getElem (by simp [genPre_length])
  intro i h1 h2
  simp only [List.getElem_map, genPre_getElem]
  split <;> rfl

theorem res_genV (c : ℕ) (ctors : List Ctor) (h : Hom k n) : res h (genV c n ctors) = genV c k ctors := by
  simp [genV, res_conV]

include hsyn hC hps in
theorem argTy_univ (hok0 : SigOK (S0 ++ [.data (D.truncate 0)]))
    (hck : ∀ k A, C.args[k]? = some (.point A) →
      HasTy (S0 ++ [.data (D.truncate 0)]) 0 .one (D.argCtx S0.length C k) A (.univ D.level)) :
    ∀ j A, C.args[j]? = some (.point A) → ∀ n (g : Hom n m) (pre : List V) (hjp : j ≤ pre.length),
      (∀ i (hi : i < j), C.isRec i = false →
        pre[i]'(by omega) ∈ El (argTyRaw (sigV S0) D S0.length c i n (ps n g) pre) (Hom.id n)) →
      argTyRaw (sigV S0) D S0.length c j n (ps n g) pre ∈ El (univC n D.level) (Hom.id n) ∧
      ∀ n' (h : Hom n' n), res h (argTyRaw (sigV S0) D S0.length c j n (ps n g) pre) =
        argTyRaw (sigV S0) D S0.length c j n' (ps n' (g.comp h)) (pre.map (res h)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro A hA n g pre hjp hpre
    have hjC : j ≤ C.args.length := (List.getElem?_eq_some_iff.1 hA).1.le
    have hkv : ∀ i (hi : i < j), C.isRec i = false →
        pre[i]'(by omega) ∈ El (argTyRaw (sigV S0) D S0.length c i n (ps n g) pre) (Hom.id n) ∧
          IsKV n (pre[i]'(by omega)) := by
      intro i hi hr
      refine ⟨hpre i hi hr, ?_⟩
      have hAi : ∃ Ai, C.args[i]? = some (.point Ai) := by
        have : i < C.args.length := by omega
        cases h' : C.args[i]'this with
        | point Ai => exact ⟨Ai, by rw [List.getElem?_eq_getElem this, h']⟩
        | recur => simp [Ctor.isRec, List.getElem?_eq_getElem this, h'] at hr
      obtain ⟨Ai, hAi⟩ := hAi
      have := (ih i hi Ai hAi n g pre (by omega) fun i' hi' hr' => hpre i' (by omega) hr').1
      rw [mem_El_univ_iff] at this
      exact this.2.fib.elKV n (Hom.id n) _ (hpre i hi hr)
    have hp := isPoint_argCtx S0 D hsyn hC hps 0 (Nat.zero_le _) (Φ := .one) g (fun _ => DM.zero n)
      (by simp [DM.holds, ival.fn, I.eval]) hjp hjC hkv
    obtain ⟨hmem, hnat, -, -⟩ := (sound_ty hok0 (hck j A hA)).2.2.2 n _ _ hp
    rw [← sem_argTy_eq S0 _ D hsyn hC hA (ps n g) pre hjp]
    refine ⟨hmem, fun n' h => ?_⟩
    rw [← hnat n' h, restr_argEnvKV, genPre_map, res_genV,
      ← sem_argTy_eq S0 (D.truncate 0) D hsyn hC hA (ps n' (g.comp h)) (pre.map (res h)) (by simpa using hjp)]
    have e1 : IEnv.restr (fun _ => DM.zero n) h = fun _ => DM.zero n' := by funext i; simp [IEnv.restr]
    have e2 : (plist (ps n g) D.params.length).map (res h) = plist (ps n' (g.comp h)) D.params.length := by
      simp only [plist, List.map_map]
      apply List.map_congr_left; intro p hp; rw [List.mem_range] at hp
      exact ((hps n g).2.2 n' h p hp).symm
    rw [e1, e2, List.map_take]

include hsyn hC in
omit hps in
theorem sem_lookup_point (E : DataDecl) {j x : ℕ} (hx : x < j) (hjC : j ≤ C.args.length)
    (hr : C.isRec (j - 1 - x) = false) {T : Tm} (hT : (D.argCtx S0.length C j).lookup x = some T)
    (ρ : IEnv n) (psv gv : V) {pre : List V} (hjp : j ≤ pre.length) :
    sem (S0 ++ [.data E]) T n ρ (argEnvKV n (plist psv D.params.length) (genPre C gv (pre.take j))) =
      argTyRaw (sigV S0) D S0.length c (j - 1 - x) n psv pre := by
  rw [Ctx.lookup_eq, argCtx_lt D _ C j x hx] at hT
  simp only [Option.map_some, Option.some.injEq] at hT
  subst hT
  have hgl : (genPre C gv (pre.take j)).length = j := by simp [genPre_length]; omega
  rw [sem_ren, show (fun y => argEnvKV n (plist psv D.params.length) (genPre C gv (pre.take j)) (y + (x + 1))) =
      argEnvKV n (plist psv D.params.length) (genPre C gv (pre.take (j - 1 - x))) by
    rw [argEnvKV_shift _ _ (by omega), hgl, genPre_take, List.take_take, Nat.min_eq_left (by omega)]]
  obtain ⟨A, hA⟩ : ∃ A, C.args[j - 1 - x]? = some (.point A) := by
    have hi : j - 1 - x < C.args.length := by omega
    cases h' : C.args[j - 1 - x]'hi with
    | point A => exact ⟨A, by rw [List.getElem?_eq_getElem hi, h']⟩
    | recur => simp [Ctor.isRec, List.getElem?_eq_getElem hi, h'] at hr
  have harg : C.argTy S0.length D.params.length (j - 1 - x) = A := by simp [Ctor.argTy, hA]
  rw [harg, sem_rho_irrel _ (hsyn.2.2 c C hC _ A hA).1 _ (fun _ => DM.zero n),
    sem_argTy_eq S0 _ D hsyn hC hA psv pre (by omega)]

end argty

/-! ### Simple boundary terms are natural -/

/-- The terms built from variables and constructors of `d` with the right number of arguments. -/
def SimpleShape (ctors : List Ctor) (d : ℕ) : Tm → Prop
  | .var _ => True
  | .con d' c' _ as _ => d' = d ∧ as.toList.length = (ctors.getD c' default).args.length ∧ SimpleShapeL ctors d as
  | _ => False
where SimpleShapeL (ctors : List Ctor) (d : ℕ) : Tm → Prop
  | .tcons a as => SimpleShape ctors d a ∧ SimpleShapeL ctors d as
  | _ => True

theorem natural_simple {S : Sig} {d : ℕ} {E : DataDecl} (hd : S[d]? = some (.data E)) {ρ : IEnv m} {γ : ℕ → V}
    (hkv : ∀ x, IsKV m (γ x)) : ∀ t, (SimpleShape E.ctors d t → Natural S t m ρ γ) ∧
      (SimpleShape.SimpleShapeL E.ctors d t → ∀ a ∈ t.toList, Natural S a m ρ γ) := by
  intro t
  induction t with
  | var x => exact ⟨fun _ k f => rfl, fun _ a ha => by simp [Tm.toList] at ha⟩
  | con d' c' ps as rs' _ ihas =>
    refine ⟨fun hs => ?_, fun _ a ha => by simp [Tm.toList] at ha⟩
    obtain ⟨rfl, hlen, hsl⟩ := hs
    have hall := ihas.2 hsl
    intro k f
    rw [sem_con hd, sem_con hd, res_conV, IEnv.restr_id, IEnv.restr_id, TEnv.restr_id_of_kv hkv,
      TEnv.restr_restr, Hom.comp_id, plist_sem _ _ _ hlen, plist_sem _ _ _ hlen, List.map_map,
      List.map_map]
    congr 1
    exact List.map_congr_left fun a ha => hall a ha k f
  | tcons a as iha ihas =>
    refine ⟨fun hs => by simp [SimpleShape] at hs, fun hs b hb => ?_⟩
    obtain ⟨h1, h2⟩ := hs
    simp only [Tm.toList, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact iha.1 h1
    · exact ihas.2 h2 b hb
  | _ => exact ⟨fun hs => by simp [SimpleShape] at hs, fun _ a ha => by simp [Tm.toList] at ha⟩

/-! ### The argument types of the semantic data -/

theorem argTyRaw_recIrr {σ : SigV} {D : DataDecl} {d : ℕ} (hsyn : DataSyn d D) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) {j : ℕ} {A : Tm} (hA : C.args[j]? = some (.point A)) (n : ℕ) (psv : V)
    {pre pre' : List V} (hj : j ≤ pre.length) (hj' : j ≤ pre'.length)
    (he : ∀ i (hi : i < j), C.isRec i = false → pre[i]'(by omega) = pre'[i]'(by omega)) :
    argTyRaw σ D d c j n psv pre = argTyRaw σ D d c j n psv pre' := by
  obtain ⟨hcl, -, hnr⟩ := hsyn.2.2 c C hC j A hA
  have harg : (D.ctors.getD c default).argTy d D.params.length j = A := by
    rw [getD_ctors hC]; simp [Ctor.argTy, hA]
  simp only [argTyRaw, harg]
  refine interp_congr_free _ _ _ A n _ _ _ fun x hx => ?_
  have hxl := freeIn_lt_of_closedB A _ 0 x hcl hx
  rw [argEnv_eq_of_lt (by simp [plist]; omega), argEnv_eq_of_lt (by simp [plist]; omega)]
  by_cases hxi : x < j
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
    simp only [List.getElem_reverse, List.getElem_take, List.length_take, Nat.min_eq_left hj, Nat.min_eq_left hj']
    exact he _ (by omega) (noRecDeps_point hnr hxi hx)
  · rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by simp; omega)]
    simp [Nat.min_eq_left hj, Nat.min_eq_left hj']

/-- The condition under which `argTySem` is the raw type. -/
theorem argTySem_eq {σ : SigV} {D : DataDecl} {d c j n : ℕ} {psv : V} {pre : List V} :
    argTySem σ D d c j n psv pre = if j < (D.ctors.getD c default).args.length ∧
      (D.ctors.getD c default).isRec j = false ∧ argPreValid σ D d c j n psv pre
    then argTyRaw σ D d c j n psv pre else emptyC n := rfl

/-- At valid earlier arguments the argument types are the raw ones. -/
theorem ptValid_argPreValid {σ : SigV} {D : DataDecl} {d m : ℕ} {ps : RV m} {c n : ℕ} {g : Hom n m}
    {pre : List V} (hp : (dataSD σ D d m ps).PtValid c n g pre) {j : ℕ} (hj : j ≤ pre.length) :
    argPreValid σ D d c j n (ps n g) pre := by
  refine ⟨hj, fun i hi hip hr => ?_⟩
  have := hp i hip hr
  simp only [dataSD, argTySem_eq] at this
  split at this
  · rename_i hc
    have e : argTyRaw σ D d c i n (ps n g) (pre.take i) = argTyRaw σ D d c i n (ps n g) pre := by
      simp [argTyRaw, List.take_take]
    rw [← e]; exact this
  · simp at this

theorem ctor_of_lt {D : DataDecl} {c j : ℕ} (h : j < (D.ctors.getD c default).args.length)
    (hr : (D.ctors.getD c default).isRec j = false) :
    ∃ C A, D.ctors[c]? = some C ∧ C.args[j]? = some (.point A) ∧ D.ctors.getD c default = C := by
  by_cases hc : c < D.ctors.length
  · refine ⟨D.ctors[c], ?_⟩
    have hg : D.ctors.getD c default = D.ctors[c] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]; rfl
    rw [hg] at h hr
    cases ha : D.ctors[c].args[j] with
    | point A => exact ⟨A, List.getElem?_eq_getElem hc, by rw [List.getElem?_eq_getElem h, ha], hg⟩
    | recur => simp [Ctor.isRec, List.getElem?_eq_getElem h, ha] at hr
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
    exact absurd h (by simp [show (default : Ctor).args = [] from rfl])

section dataok

variable (S0 : Sig) (E : DataDecl) (hsyn : DataSyn S0.length E)
  (hok0 : SigOK (S0 ++ [.data (E.truncate 0)]))
  (hck : ∀ (c : ℕ) (C : Ctor), E.ctors[c]? = some C → ∀ (k : ℕ) (A : Tm), C.args[k]? = some (.point A) →
    HasTy (S0 ++ [.data (E.truncate 0)]) 0 .one (E.argCtx S0.length C k) A (.univ E.level))
include hsyn hok0 hck

theorem argTySem_facts {m : ℕ} {ps : RV m} (hps : ParamsOK (sigV S0) E m ps) (c j n : ℕ) (g : Hom n m)
    (pre : List V) :
    argTySem (sigV S0) E S0.length c j n (ps n g) pre ∈ El (univC n E.level) (Hom.id n) ∨
      argTySem (sigV S0) E S0.length c j n (ps n g) pre = emptyC n := by
  rw [argTySem_eq]
  split
  · rename_i hc
    obtain ⟨hj, hr, hv⟩ := hc
    have hv1 := hv.1
    obtain ⟨C, A, hC, hA, -⟩ := ctor_of_lt hj hr
    left
    exact (argTy_univ S0 E hsyn hC hps hok0 (hck c C hC) j A hA n g pre hv.1
      fun i hi hr' => hv.2 i hi (by omega) (by rw [getD_ctors hC]; exact hr')).1
  · right; rfl

theorem argTySem_nat {m : ℕ} {ps : RV m} (hps : ParamsOK (sigV S0) E m ps) (c j n : ℕ) (g : Hom n m)
    (pre : List V) (hp : (dataSD (sigV S0) E S0.length m ps).PtValid c n g pre) (n' : ℕ) (h : Hom n' n) :
    res h (argTySem (sigV S0) E S0.length c j n (ps n g) pre) =
      argTySem (sigV S0) E S0.length c j n' (ps n' (g.comp h)) (pre.map (res h)) := by
  by_cases hc : j < (E.ctors.getD c default).args.length ∧ (E.ctors.getD c default).isRec j = false ∧
      argPreValid (sigV S0) E S0.length c j n (ps n g) pre
  · obtain ⟨hj, hr, hv⟩ := hc
    have hv1 := hv.1
    obtain ⟨C, A, hC, hA, hgC⟩ := ctor_of_lt hj hr
    have hU : ∀ i (hi : i < j), C.isRec i = false →
        argTyRaw (sigV S0) E S0.length c i n (ps n g) pre ∈ El (univC n E.level) (Hom.id n) ∧
        ∀ n' (h : Hom n' n), res h (argTyRaw (sigV S0) E S0.length c i n (ps n g) pre) =
          argTyRaw (sigV S0) E S0.length c i n' (ps n' (g.comp h)) (pre.map (res h)) := by
      intro i hi hri
      have hiC : i < C.args.length := by rw [← hgC]; omega
      obtain ⟨Ai, hAi⟩ : ∃ Ai, C.args[i]? = some (.point Ai) := by
        cases h' : C.args[i]'hiC with
        | point Ai => exact ⟨Ai, by rw [List.getElem?_eq_getElem hiC, h']⟩
        | recur => simp [Ctor.isRec, List.getElem?_eq_getElem hiC, h'] at hri
      exact argTy_univ S0 E hsyn hC hps hok0 (hck c C hC) i Ai hAi n g pre (by omega)
        fun i' hi' hr' => hv.2 i' (by omega) (by omega) (by rw [hgC]; exact hr')
    have hc' : j < (E.ctors.getD c default).args.length ∧ (E.ctors.getD c default).isRec j = false ∧
        argPreValid (sigV S0) E S0.length c j n' (ps n' (g.comp h)) (pre.map (res h)) := by
      refine ⟨hj, hr, by simpa using hv1, fun i hi hip hri => ?_⟩
      rw [hgC] at hri
      obtain ⟨hmem, hnat⟩ := hU i hi hri
      rw [← hnat n' h, List.getElem_map]
      rw [mem_El_univ_iff] at hmem
      have := hmem.2.fib.elRes n (Hom.id n) _ (hv.2 i hi (by omega) (by rw [hgC]; exact hri)) n' h
      rwa [El_eq_res_id, Hom.id_comp] at this
    rw [argTySem_eq, if_pos ⟨hj, hr, hv⟩, argTySem_eq, if_pos hc']
    exact (argTy_univ S0 E hsyn hC hps hok0 (hck c C hC) j A hA n g pre hv1
      fun i' hi' hr' => hv.2 i' hi' (by omega) (by rw [hgC]; exact hr')).2 n' h
  · have hc' : ¬ (j < (E.ctors.getD c default).args.length ∧ (E.ctors.getD c default).isRec j = false ∧
        argPreValid (sigV S0) E S0.length c j n' (ps n' (g.comp h)) (pre.map (res h))) := by
      rintro ⟨hj, hr, hv⟩
      exact hc ⟨hj, hr, ptValid_argPreValid hp (by simpa using hv.1)⟩
    rw [argTySem_eq, if_neg hc, argTySem_eq, if_neg hc', res_emptyC]

omit hok0 hck in
theorem argTySem_recIrr (c j n : ℕ) (psv : V) (pre pre' : List V) (hl : pre.length = pre'.length)
    (he : ∀ i (hi : i < pre.length) (hi' : i < pre'.length), (E.ctors.getD c default).isRec i = false →
      pre[i] = pre'[i]) :
    argTySem (sigV S0) E S0.length c j n psv pre = argTySem (sigV S0) E S0.length c j n psv pre' := by
  have hraw : ∀ i, i < (E.ctors.getD c default).args.length → (E.ctors.getD c default).isRec i = false →
      i ≤ pre.length → argTyRaw (sigV S0) E S0.length c i n psv pre = argTyRaw (sigV S0) E S0.length c i n psv pre' := by
    intro i hi hri hip
    obtain ⟨C, A, hC, hA, hgC⟩ := ctor_of_lt hi hri
    exact argTyRaw_recIrr hsyn hC hA n psv hip (by omega) fun i' hi' hr' =>
      he i' (by omega) (by omega) (by rw [hgC]; exact hr')
  have hcond : (j < (E.ctors.getD c default).args.length ∧ (E.ctors.getD c default).isRec j = false ∧
      argPreValid (sigV S0) E S0.length c j n psv pre) ↔ (j < (E.ctors.getD c default).args.length ∧
      (E.ctors.getD c default).isRec j = false ∧ argPreValid (sigV S0) E S0.length c j n psv pre') := by
    constructor
    · rintro ⟨hj, hr, hv1, hv2⟩
      refine ⟨hj, hr, by omega, fun i hi hip hri => ?_⟩
      rw [← hraw i (by omega) hri (by omega), ← he i (by omega) hip hri]
      exact hv2 i hi (by omega) hri
    · rintro ⟨hj, hr, hv1, hv2⟩
      refine ⟨hj, hr, by omega, fun i hi hip hri => ?_⟩
      rw [hraw i (by omega) hri (by omega), he i hip (by omega) hri]
      exact hv2 i hi (by omega) hri
  rw [argTySem_eq, argTySem_eq]
  by_cases h : j < (E.ctors.getD c default).args.length ∧ (E.ctors.getD c default).isRec j = false ∧
      argPreValid (sigV S0) E S0.length c j n psv pre
  · rw [if_pos h, if_pos (hcond.1 h)]
    exact hraw j h.1 h.2.1 h.2.2.1
  · rw [if_neg h, if_neg (fun h' => h (hcond.2 h'))]

omit hsyn hok0 hck in
theorem argTySem_noparams (hnp : E.params = []) (c j n : ℕ) (psv psv' : V) (pre : List V) :
    argTySem (sigV S0) E S0.length c j n psv pre = argTySem (sigV S0) E S0.length c j n psv' pre := by
  have h0 : ∀ v, plist v E.params.length = [] := by intro v; simp [plist, hnp]
  simp only [argTySem, argPreValid, argTyRaw, h0]

theorem dataOK_of
    (hbo : ∀ m (ps : RV m), ParamsOK (sigV S0) E m ps →
      (∀ c C, (dataSD (sigV S0) E S0.length m ps).ctors[c]? = some C → ∀ ψ b, (ψ, b) ∈ C.bnd →
        ∀ n (rs : List (DM n)), (ival (renv rs) ψ).holds → BTy (dataSD (sigV S0) E S0.length m ps) c C b) ∧
      (∀ c C, (dataSD (sigV S0) E S0.length m ps).ctors[c]? = some C → ∀ ψ b ψ' b', (ψ, b) ∈ C.bnd →
        (ψ', b') ∈ C.bnd → ∀ n (g : Hom n m) args (rs : List (DM n)),
          (dataSD (sigV S0) E S0.length m ps).ArgsTyped c C n g args → rs.length = C.dims →
          (ival (renv rs) ψ).holds → (ival (renv rs) ψ').holds →
          evalBnd (conBefore (dataSD (sigV S0) E S0.length m ps).ctors c n) args rs b =
            evalBnd (conBefore (dataSD (sigV S0) E S0.length m ps).ctors c n) args rs b')) :
    DataOK (S0 ++ [.data E]) S0.length E := by
  refine ⟨hsyn, fun m ps hps => ?_⟩
  rw [sigUpTo_ext] at hps ⊢
  obtain ⟨hb, ho⟩ := hbo m ps hps
  have hl : E.level ≤ 4 := by have := hsyn.1; unfold maxLevel at this; omega
  refine ⟨{ nat := fun c j n g pre hp n' h => argTySem_nat S0 E hsyn hok0 hck hps c j n g pre hp n' h
            recIrr := fun c j n g pre pre' hl he => argTySem_recIrr S0 E hsyn c j n _ pre pre' hl he
            bnd := hb
            const := fun hp c j n g g' pre => argTySem_noparams S0 E (by
              simpa [dataSD] using hp) c j n _ _ pre
            ovl := ho
            fib := fun c j n g pre _ => ?_ }, fun c j n g pre => ?_⟩
  · rcases argTySem_facts S0 E hsyn hok0 hck hps c j n g pre with h | h
    · rw [mem_El_univ_iff] at h; exact h.2.fib
    · show Fib (argTySem _ _ _ _ _ _ _ _) n
      rw [h]; exact fib_emptyC
  · rcases argTySem_facts S0 E hsyn hok0 hck hps c j n g pre with h | h
    · rw [mem_El_univ_iff] at h; exact ⟨h.1, fun _ => h.2⟩
    · show argTySem _ _ _ _ _ _ _ _ ∈ Vt E.level ∧ (_ → WF E.level n (argTySem _ _ _ _ _ _ _ _))
      rw [h]; exact ⟨emptyC_mem_Vt' hl, fun _ => WFI.empty⟩

end dataok

theorem argTySem_congr {σ : SigV} {E D : DataDecl} {d c : ℕ} (hp : E.params = D.params)
    (hg : E.ctors.getD c default = D.ctors.getD c default) :
    argTySem σ E d c = argTySem σ D d c := by
  funext j n psv pre
  simp only [argTySem, argPreValid, argTyRaw, hp, hg]

theorem nestPre_cons (pre : List V) (a : Tm) (prev : List Tm) :
    nestPre pre (a :: prev) = nestPre pre prev ++ [nestVal pre a] := by
  simp [nestPre]

theorem argTyRaw_take_eq {σ : SigV} {D : DataDecl} {d c j n : ℕ} {psv : V} {pre pre' : List V}
    (h : pre.take j = pre'.take j) : argTyRaw σ D d c j n psv pre = argTyRaw σ D d c j n psv pre' := by
  simp only [argTyRaw, h]


section tyeq

variable (S0 : Sig) (D : DataDecl) (hsyn : DataSyn S0.length D)
  {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {m : ℕ} {ps : RV m} (hps : ParamsOK (sigV S0) D m ps)

theorem toList_ofList : ∀ L : List Tm, (Tm.ofList L).toList = L
  | [] => rfl
  | t :: L => by simp [Tm.ofList, Tm.toList, toList_ofList L]

theorem nestPre_length (pre : List V) (prev : List Tm) : (nestPre pre prev).length = prev.length := by
  simp [nestPre]

include hsyn hC hps in
/-- The type equality of a boundary point argument, from its judgmental version. -/
theorem tyEq_core (hokc : SigOK (S0 ++ [.data (D.truncate c)])) (hc : c ≤ D.ctors.length)
    {ψ : I} {n0 : ℕ} {rs0 : List (DM n0)} (hrs0 : (ival (renv rs0) ψ).holds)
    {c' : ℕ} {C' : Ctor} (hC' : D.ctors[c']? = some C') {k : ℕ} {A' : Tm} (hA' : C'.args[k]? = some (.point A'))
    {prev : List Tm} (hpl : prev.length = k)
    (Hprev : ∀ q (hq : q < k), C'.isRec q = false → ∃ y, prev.reverse[q]'(by simp; omega) = .var y ∧
      y < C.args.length ∧ C.isRec (C.args.length - 1 - y) = false)
    (hprevS : ∀ t ∈ prev, SimpleShape (D.truncate c).ctors S0.length t)
    {x : ℕ} (hx : x < C.args.length) (hxr : C.isRec (C.args.length - 1 - x) = false) {T : Tm}
    (hT : (D.argCtx S0.length C C.args.length).lookup x = some T)
    (heq : EqTm (S0 ++ [.data (D.truncate c)]) C.dims ψ (D.argCtx S0.length C C.args.length) T
      ((C'.argTy S0.length D.params.length k).substList
        (prev ++ (Ctor.paramVars D.params.length C.args.length).toList.reverse)) (.univ D.level))
    {n2 : ℕ} (g : Hom n2 m) (pre : List V) (hpre : pre.length = C.args.length)
    (hpt : ∀ i (hi : i < C.args.length), C.isRec i = false →
      pre[i]'(by omega) ∈ El (argTyRaw (sigV S0) D S0.length c i n2 (ps n2 g) pre) (Hom.id n2) ∧
        IsKV n2 (pre[i]'(by omega))) :
    argTyRaw (sigV S0) D S0.length c' k n2 (ps n2 g) (nestPre pre prev) =
      argTyRaw (sigV S0) D S0.length c (C.args.length - 1 - x) n2 (ps n2 g) pre := by
  set n := C.args.length
  set np := D.params.length
  set Sc := S0 ++ [Entry.data (D.truncate c)]
  set ρ2 : IEnv n2 := (renv rs0).restr (fun _ => DM.zero n2)
  have hρ2 : (ival ρ2 ψ).holds := by rw [ival.restr]; exact hrs0.restr _
  set gv := genV c n2 (D.truncate c).ctors
  set γ2 := argEnvKV n2 (plist (ps n2 g) np) (genPre C gv (pre.take n))
  have hp := isPoint_argCtx S0 D hsyn hC hps c hc g ρ2 hρ2 (j := n) (by omega) le_rfl
    (fun i hi hr => hpt i hi hr)
  have hE := (sound_eq hokc heq).2.2 n2 ρ2 γ2 hp
  rw [sem_lookup_point S0 D hsyn hC _ hx le_rfl hxr hT ρ2 (ps n2 g) gv (by omega)] at hE
  rw [hE]
  -- the right-hand side
  have harg : C'.argTy S0.length np k = A' := by simp [Ctor.argTy, hA']
  obtain ⟨hcl, hcs, hnr⟩ := hsyn.2.2 c' C' hC' k A' hA'
  set L := prev ++ (Ctor.paramVars np n).toList.reverse
  have hPV : (Ctor.paramVars np n).toList = (List.range np).map fun p => Tm.var (n + np - 1 - p) := by
    rw [Ctor.paramVars, toList_ofList]
  have hLl : L.length = k + np := by simp [L, hpl, hPV]
  have hkv2 : ∀ y, IsKV n2 (γ2 y) := hp.kv
  have hnat : ∀ y, Natural Sc ((fun j => L.getD j (.var (j - L.length))) y) n2 ρ2 γ2 := by
    intro y
    by_cases hy : y < L.length
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy, Option.getD_some]
      by_cases hyk : y < prev.length
      · rw [List.getElem_append_left hyk]
        exact (natural_simple (entry_ext S0 _) hkv2 _).1 (hprevS _ (List.getElem_mem _))
      · rw [List.getElem_append_right (by omega)]
        simp only [hPV, List.getElem_reverse, List.getElem_map]
        intro k' f; rfl
    · have e : L.getD y (.var (y - L.length)) = .var (y - L.length) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hy)]
      show Natural Sc (L.getD y _) n2 ρ2 γ2
      rw [e]; intro k' f; rfl
  rw [harg, Tm.substList, sem_subst Sc A' n2 ρ2 γ2 _ _ hnat,
    sem_rho_irrel _ hcl _ (fun _ => DM.zero n2), sem_ext S0 _ hcs]
  have harg' : (D.ctors.getD c' default).argTy S0.length np k = A' := by rw [getD_ctors hC']; exact harg
  rw [argTyRaw, harg']
  refine interp_congr_free _ _ _ A' n2 _ _ _ fun y hy => ?_
  have hyl := freeIn_lt_of_closedB A' _ 0 y hcl hy
  have hnl : (nestPre pre prev).length = k := by rw [nestPre_length, hpl]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : y < L.length), Option.getD_some]
  simp only [argEnv, List.getD_eq_getElem?_getD, List.take_of_length_le (by rw [hnl] : (nestPre pre prev).length ≤ k)]
  by_cases hyk : y < k
  · have hq := noRecDeps_point hnr hyk hy
    obtain ⟨y', hy'e, hy'l, hy'r⟩ := Hprev (k - 1 - y) (by omega) hq
    have e1 : L[y]'(by omega) = .var y' := by
      rw [List.getElem_append_left (by omega)]
      rw [← hy'e, List.getElem_reverse]; congr 1; omega
    rw [e1, sem_var]
    have hL : γ2 y' = pre[n - 1 - y']'(by omega) := by
      simp only [γ2]
      rw [argEnvKV_eq_of_lt (by simp [genPre_length, plist]; omega),
        List.getElem_append_left (by simp [genPre_length]; omega), List.getElem_reverse, genPre_getElem]
      simp only [genPre_length, List.length_take, Nat.min_eq_left (show n ≤ pre.length by omega)]
      rw [if_neg (by simp [hy'r]), List.getElem_take]
    rw [hL, List.getElem?_append_left (by simp [hnl]; omega), List.getElem?_reverse (by simp [hnl]; omega)]
    have hq' : prev.reverse[k - 1 - y]? = some (.var y') := by
      rw [List.getElem?_eq_getElem (by simp; omega), hy'e]
    simp only [hnl, nestPre, List.getElem?_map, List.length_map, List.length_reverse, hpl, hq', Option.map_some,
      Option.getD_some, nestVal]
    rw [getD_reverse_eq (by omega)]
    simp [hpre]
  · rw [List.getElem_append_right (by omega)]
    simp only [hPV, List.getElem_reverse, List.getElem_map, List.getElem_range, List.length_map,
      List.length_range, hpl, sem_var]
    simp only [γ2]
    rw [argEnvKV_eq_of_lt (by simp [genPre_length, plist]; omega), List.getElem_append_right (by simp [genPre_length]; omega),
      List.getElem?_append_right (by simp [hnl]; omega)]
    simp only [genPre_length, List.length_take, Nat.min_eq_left (show n ≤ pre.length by omega), List.length_reverse, hnl]
    rw [List.getElem?_eq_getElem (by simp [plist]; omega), Option.getD_some]
    congr 1; omega

include hsyn hC hps in
theorem bty_of_wf (hok0 : SigOK (S0 ++ [.data (D.truncate 0)]))
    (hck : ∀ (c : ℕ) (C : Ctor), D.ctors[c]? = some C → ∀ (k : ℕ) (A : Tm), C.args[k]? = some (.point A) →
      HasTy (S0 ++ [.data (D.truncate 0)]) 0 .one (D.argCtx S0.length C k) A (.univ D.level))
    (hokc : SigOK (S0 ++ [.data (D.truncate c)])) (hc : c ≤ D.ctors.length)
    {ψ : I} {n0 : ℕ} {rs0 : List (DM n0)} (hrs0 : (ival (renv rs0) ψ).holds)
    {E : DataDecl} (hEp : E.params = D.params) (hEc : ∀ c' ≤ c, E.ctors[c']? = D.ctors[c']?) :
    ∀ t : Tm,
      (Ctor.simpleB D.ctors S0.length D.params.length c C.args.length C t = true →
        Ctor.bndTyped (S0 ++ [.data (D.truncate c)]) C.dims ψ (D.argCtx S0.length C C.args.length) D.level
          D.ctors S0.length D.params.length t →
        SimpleShape (D.truncate c).ctors S0.length t ∧ BTy (dataSD (sigV S0) E S0.length m ps) c C t) ∧
      (∀ (C' : Ctor) (c' k : ℕ) (prev : List Tm), c' < c → D.ctors[c']? = some C' →
        k + t.toList.length = C'.args.length →
        Ctor.simpleArgs D.ctors S0.length D.params.length c C.args.length C C' k t = true →
        Ctor.bndTypedArgs (S0 ++ [.data (D.truncate c)]) C.dims ψ (D.argCtx S0.length C C.args.length) D.level
          D.ctors S0.length D.params.length C' (Ctor.paramVars D.params.length C.args.length) k prev t →
        ∀ (hpl : prev.length = k), (∀ u ∈ prev, SimpleShape (D.truncate c).ctors S0.length u) →
        (∀ q (hq : q < k), C'.isRec q = false → ∃ y, prev.reverse[q]'(by simp; omega) = .var y ∧
          y < C.args.length ∧ C.isRec (C.args.length - 1 - y) = false ∧
          ∀ n2 (g : Hom n2 m) (pre : List V) (hpre : pre.length = C.args.length),
            (∀ i (hi : i < C.args.length), C.isRec i = false →
              pre[i]'(by omega) ∈ El (argTyRaw (sigV S0) D S0.length c i n2 (ps n2 g) pre) (Hom.id n2) ∧
                IsKV n2 (pre[i]'(by omega))) →
            argTyRaw (sigV S0) D S0.length c' q n2 (ps n2 g) (nestPre pre prev) =
              argTyRaw (sigV S0) D S0.length c (C.args.length - 1 - y) n2 (ps n2 g) pre) →
        SimpleShape.SimpleShapeL (D.truncate c).ctors S0.length t ∧
          BTyArgs (dataSD (sigV S0) E S0.length m ps) c C C' c' k prev t) := by
  have hgC := getD_ctors hC
  have hgetD : ∀ c', c' ≤ c → E.ctors.getD c' default = D.ctors.getD c' default := fun c' h => by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hEc c' h]
  have hty : ∀ c', c' ≤ c → ∀ j n2 (g : Hom n2 m) pre, (dataSD (sigV S0) E S0.length m ps).ty c' j n2 g pre =
      argTySem (sigV S0) D S0.length c' j n2 (ps n2 g) pre := fun c' h j n2 g pre => by
    show argTySem (sigV S0) E S0.length c' j n2 (ps n2 g) pre = _
    rw [argTySem_congr hEp (hgetD c' h)]
  have hraw : ∀ c', c' ≤ c → argTyRaw (sigV S0) E S0.length c' = argTyRaw (sigV S0) D S0.length c' := by
    intro c' h; funext j n psv pre; simp only [argTyRaw, hEp, hgetD c' h]
  -- valid arguments of `c` are typed
  have htyped : ∀ n2 (g : Hom n2 m) (pre : List V), (dataSD (sigV S0) E S0.length m ps).PtValid c n2 g pre →
      ∀ i (hi : i < pre.length), i < C.args.length → C.isRec i = false →
        pre[i] ∈ El (argTyRaw (sigV S0) D S0.length c i n2 (ps n2 g) pre) (Hom.id n2) ∧ IsKV n2 pre[i] := by
    intro n2 g pre hp i hi hiC hr
    have hv := ptValid_argPreValid hp (j := pre.length) le_rfl
    have hr' : (E.ctors.getD c default).isRec i = false := by rw [hgetD c le_rfl, hgC]; exact hr
    have hmem := hv.2 i hi hi hr'
    rw [hraw c le_rfl] at hmem
    refine ⟨hmem, ?_⟩
    obtain ⟨A, hA⟩ : ∃ A, C.args[i]? = some (.point A) := by
      cases h' : C.args[i]'hiC with
      | point A => exact ⟨A, by rw [List.getElem?_eq_getElem hiC, h']⟩
      | recur => simp [Ctor.isRec, List.getElem?_eq_getElem hiC, h'] at hr
    have hU := (argTy_univ S0 D hsyn hC hps hok0 (hck c C hC) i A hA n2 g pre hi.le fun i' hi' hr' => by
      have := hv.2 i' (by omega) (by omega) (by rw [hgetD c le_rfl, hgC]; exact hr')
      rwa [hraw c le_rfl] at this).1
    rw [mem_El_univ_iff] at hU
    exact hU.2.fib.elKV n2 (Hom.id n2) _ hmem
  intro t
  induction t with
  | var x =>
    refine ⟨fun hs _ => ⟨trivial, ?_⟩, fun _ _ _ _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩⟩
    simp only [Ctor.simpleB, Bool.and_eq_true, decide_eq_true_eq] at hs
    exact hs
  | con d' c' ps' as rs' _ ihas =>
    refine ⟨fun hs hb => ?_, fun _ _ _ _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩⟩
    simp only [Ctor.simpleB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
    obtain ⟨⟨⟨hd', hc'⟩, hps'⟩, hrest⟩ := hs
    cases hC' : D.ctors[c']? with
    | none => simp [hC'] at hrest
    | some C' =>
      simp only [hC', Bool.and_eq_true, beq_iff_eq] at hrest
      obtain ⟨⟨hlen, hdims⟩, hsa⟩ := hrest
      simp only [Ctor.bndTyped, hC'] at hb
      subst hps'
      obtain ⟨hsh, hbt⟩ := ihas.2 C' c' 0 [] hc' hC' (by omega) hsa hb rfl (by simp) (fun q hq => absurd hq (by omega))
      have hgt : (D.truncate c).ctors.getD c' default = C' := by
        rw [List.getD_eq_getElem?_getD]
        simp [DataDecl.truncate, List.getElem?_append_left (by simp; omega : c' < (D.ctors.take c).length), hc', hC']
      refine ⟨⟨hd', by rw [hgt, hlen], hsh⟩, hc', C', ?_, hlen, hdims, hbt⟩
      show E.ctors[c']? = some C'
      rw [hEc c' hc'.le, hC']
  | tcons a as iha ihas =>
    refine ⟨fun hs _ => by simp [Ctor.simpleB] at hs, fun C' c' k prev hc' hC' hkl hsa hb hpl hprevS Hprev => ?_⟩
    simp only [Ctor.simpleArgs, Bool.and_eq_true] at hsa
    obtain ⟨hsa1, hsa2⟩ := hsa
    obtain ⟨hb1, hb2, hb3⟩ := hb
    have hpl' : (a :: prev).length = k + 1 := by simp [hpl]
    have hrevq : ∀ q (hq : q < k), (a :: prev).reverse[q]'(by simp; omega) = prev.reverse[q]'(by simp; omega) := by
      intro q hq; simp [List.reverse_cons, List.getElem_append_left (by simp; omega : q < prev.reverse.length)]
    have hrevk : (a :: prev).reverse[k]'(by simp; omega) = a := by
      simp [List.reverse_cons, List.getElem_append_right (by simp; omega : prev.reverse.length ≤ k), hpl]
    have hnest : ∀ pre q, q ≤ k → (nestPre pre (a :: prev)).take q = (nestPre pre prev).take q := by
      intro pre q hq
      rw [nestPre_cons, List.take_append_of_le_length (by rw [nestPre_length]; omega)]
    cases hr : C'.isRec k
    · -- a point argument: a variable of `c` of the right type
      simp only [hr, if_false, Bool.false_eq_true] at hsa1
      obtain ⟨x, rfl, hx, hxr⟩ : ∃ x, a = .var x ∧ x < C.args.length ∧ C.isRec (C.args.length - 1 - x) = false := by
        cases a with
        | var x => simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hsa1; exact ⟨x, rfl, hsa1⟩
        | _ => simp at hsa1
      obtain ⟨A', hA'⟩ : ∃ A', C'.args[k]? = some (.point A') := by
        have hkC : k < C'.args.length := by simp [Tm.toList] at hkl; omega
        cases h' : C'.args[k]'hkC with
        | point A' => exact ⟨A', by rw [List.getElem?_eq_getElem hkC, h']⟩
        | recur => simp [Ctor.isRec, List.getElem?_eq_getElem hkC, h'] at hr
      obtain ⟨T, hT⟩ : ∃ T, (D.argCtx S0.length C C.args.length).lookup x = some T := by
        rw [Ctx.lookup_eq, argCtx_lt D _ C _ x hx]; exact ⟨_, rfl⟩
      have heq := hb1 x T rfl hr hT
      have hcore := fun n2 (g : Hom n2 m) pre hpre htp => tyEq_core S0 D hsyn hC hps hokc hc hrs0 hC' hA' hpl
        (fun q hq hrq => by obtain ⟨y, h1, h2, h3, -⟩ := Hprev q hq hrq; exact ⟨y, h1, h2, h3⟩) hprevS hx hxr hT heq
        g pre hpre htp
      have hgC' := getD_ctors hC'
      have hrec := ihas.2 C' c' (k + 1) (.var x :: prev) hc' hC' (by simp [Tm.toList] at hkl; omega)
        hsa2 hb3 hpl'
        (fun u hu => by
          rcases List.mem_cons.1 hu with rfl | hu
          · trivial
          · exact hprevS u hu)
        (fun q hq hrq => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hqk | hqk
          · obtain ⟨y, h1, h2, h3, h4⟩ := Hprev q hqk hrq
            refine ⟨y, by rw [hrevq q hqk]; exact h1, h2, h3, fun n2 g pre hpre htp => ?_⟩
            rw [← h4 n2 g pre hpre htp]
            exact argTyRaw_take_eq (hnest pre q hqk.le)
          · subst hqk
            refine ⟨x, hrevk, hx, hxr, fun n2 g pre hpre htp => ?_⟩
            rw [← hcore n2 g pre hpre htp]
            exact argTyRaw_take_eq (hnest pre q le_rfl))
      refine ⟨⟨trivial, hrec.1⟩, fun h => absurd (hr.symm.trans h) (by decide), fun _ => ⟨x, rfl, hx, hxr,
        fun n2 g pre hpre hpv => ?_⟩, hrec.2⟩
      have htp : ∀ i (hi : i < C.args.length), C.isRec i = false →
          pre[i]'(by omega) ∈ El (argTyRaw (sigV S0) D S0.length c i n2 (ps n2 g) pre) (Hom.id n2) ∧
            IsKV n2 (pre[i]'(by omega)) := fun i hi hri => htyped n2 g pre hpv i (by omega) hi hri
      rw [hty c' hc'.le, hty c le_rfl]
      have hrhs : argTySem (sigV S0) D S0.length c (C.args.length - 1 - x) n2 (ps n2 g)
          (pre.take (C.args.length - 1 - x)) =
          argTyRaw (sigV S0) D S0.length c (C.args.length - 1 - x) n2 (ps n2 g) pre := by
        have hcond : C.args.length - 1 - x < (D.ctors.getD c default).args.length ∧
            (D.ctors.getD c default).isRec (C.args.length - 1 - x) = false ∧
            argPreValid (sigV S0) D S0.length c (C.args.length - 1 - x) n2 (ps n2 g)
              (pre.take (C.args.length - 1 - x)) := by
          refine ⟨by rw [hgC]; omega, by rw [hgC]; exact hxr, by simp; omega, fun i hi hip hri => ?_⟩
          rw [argTyRaw_take_eq (pre' := pre) (by simp [List.take_take]; omega), List.getElem_take]
          exact (htp i (by omega) (by rw [hgC] at hri; exact hri)).1
        rw [argTySem_eq, if_pos hcond]
        exact argTyRaw_take_eq (by simp [List.take_take])
      have hcond' : k < (D.ctors.getD c' default).args.length ∧ (D.ctors.getD c' default).isRec k = false ∧
          argPreValid (sigV S0) D S0.length c' k n2 (ps n2 g) (nestPre pre prev) := by
        refine ⟨by rw [hgC']; simp [Tm.toList] at hkl; omega, by rw [hgC']; exact hr, by rw [nestPre_length]; omega,
          fun q hq hqp hrq => ?_⟩
        rw [hgC'] at hrq
        obtain ⟨y, h1, h2, h3, h4⟩ := Hprev q hq hrq
        rw [h4 n2 g pre hpre htp]
        have e : (nestPre pre prev)[q] = pre[C.args.length - 1 - y]'(by omega) := by
          simp only [nestPre, List.getElem_map, h1, nestVal]
          rw [getD_reverse_eq (by omega)]; simp [hpre]
        rw [e]
        exact (htp _ (by omega) h3).1
      rw [hrhs, argTySem_eq, if_pos hcond']
      exact hcore n2 g pre hpre htp
    · -- a recursive argument: a simple term
      simp only [hr, if_true] at hsa1
      obtain ⟨hsh, hbt⟩ := iha.1 hsa1 (hb2 hr)
      obtain ⟨hsh', hbt'⟩ := ihas.2 C' c' (k + 1) (a :: prev) hc' hC' (by simp [Tm.toList] at hkl; omega)
        hsa2 hb3 hpl'
        (fun u hu => by
          rcases List.mem_cons.1 hu with rfl | hu
          · exact hsh
          · exact hprevS u hu)
        (fun q hq hrq => by
          have hqk : q < k := by
            rcases Nat.lt_succ_iff_lt_or_eq.1 hq with h | h
            · exact h
            · subst h; rw [hr] at hrq; exact absurd hrq (by decide)
          obtain ⟨y, h1, h2, h3, h4⟩ := Hprev q hqk hrq
          refine ⟨y, by rw [hrevq q hqk]; exact h1, h2, h3, fun n2 g pre hpre htp => ?_⟩
          rw [← h4 n2 g pre hpre htp]
          exact argTyRaw_take_eq (hnest pre q hqk.le))
      exact ⟨⟨hsh, hsh'⟩, fun _ => hbt, fun h => absurd (hr.symm.trans h) (by decide), hbt'⟩
  | _ =>
    exact ⟨fun hs _ => by simp [Ctor.simpleB] at hs, fun _ _ _ _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩⟩

end tyeq

end

end Model
