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
    (preL : List V) {i : ℕ} (hi : preL.length = i) :
    (fun k (f : Hom k n) => sem S (Ctor.paramVars D.params.length i) k (IEnv.restr (fun _ => DM.zero n) f)
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

theorem genV_mem {S0 : Sig} {D : DataDecl} {n : ℕ} {ps : RV n}
    (hps : ParamsOK (sigV S0) D n ps) :
    genV 0 n (D.truncate 0).ctors ∈ El (dataC (dataSD (sigV S0) (D.truncate 0) S0.length n ps)) (Hom.id n) := by
  rw [mem_El_dataC]
  exact DElem.con (C := { args := [], dims := 0, bnd := [] }) rfl rfl rfl
    (fun j a ha => by simp at ha) (fun j a ha => by simp at ha)

section argty

variable (S0 : Sig) (D : DataDecl) (hsyn : DataSyn S0.length D)
  {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {m : ℕ} {ps : RV m} (hps : ParamsOK (sigV S0) D m ps)

include hsyn hC hps in
theorem isPoint_argCtx {j : ℕ} {n : ℕ} (g : Hom n m) {pre : List V} (hjp : j ≤ pre.length)
    (hjC : j ≤ C.args.length)
    (hpt : ∀ i (hi : i < j), C.isRec i = false →
      pre[i]'(by omega) ∈ El (argTyRaw (sigV S0) D S0.length c i n (ps n g) pre) (Hom.id n) ∧ IsKV n (pre[i]'(by omega))) :
    IsPoint (S0 ++ [.data (D.truncate 0)]) .one (D.argCtx S0.length C j) n (fun _ => DM.zero n)
      (argEnvKV n (plist (ps n g) D.params.length) (genPre C (genV 0 n (D.truncate 0).ctors) (pre.take j))) := by
  set np := D.params.length
  set gv := genV 0 n (D.truncate 0).ctors
  have hgl : (genPre C gv (pre.take j)).length = j := by simp [genPre_length]; omega
  have hpl : (plist (ps n g) np).length = np := by simp [plist]
  refine ⟨by simp [DM.holds, ival.fn, I.eval], fun x B hB => ?_, fun x => ?_⟩
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
          rw [harg, sem_argTy_eq S0 _ D hsyn hC hA (ps n g) pre (by omega)]
          exact (hpt _ (by omega) hr).1
        | recur =>
          have hr : C.isRec (j - 1 - x) = true := by simp [Ctor.isRec, hA]
          rw [if_pos hr]
          have harg : C.argTy S0.length np (j - 1 - x) = .data S0.length (Ctor.paramVars np (j - 1 - x)) := by
            simp [Ctor.argTy, hA]
          rw [harg, sem_data (entry_ext S0 _), sigUpTo_ext]
          have hpv := sem_paramVars_rv (i := j - 1 - x) (S0 ++ [.data (D.truncate 0)]) hps g
            (genPre C gv (pre.take (j - 1 - x))) (by simp [genPre_length]; omega)
          unfold psRV
          rw [hpv, if_pos (show ParamsOK (sigV S0) (D.truncate 0) n _ from hps.restr g)]
          exact genV_mem (hps.restr g)
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
    have hp := isPoint_argCtx S0 D hsyn hC hps g hjp hjC hkv
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

end argty

end

end Model
