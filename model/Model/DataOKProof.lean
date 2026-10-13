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

theorem sem_ext' {A : Tm} (hA : A.ConstsLt (S0.length + 1)) (hm : A.mentionsData S0.length = false) :
    sem (S0 ++ [.data E]) A = interp (sigV S0) univC TyCode A :=
  (interp_congr_md _ _ (agree_ext S0 E) (fun m => by
    rw [sigV_cst_data (entry_ext S0 E)]; exact sigUpTo_cst_ge S0 _ _ m le_rfl) A hA hm).symm

end ext

/-! ### List values -/

theorem listLen_vlist : ∀ {v : V} {n : ℕ}, ListLen v n → v = vlist (plist v n)
  | v, 0, h => by simp [ListLen] at h; simp [h, plist, vlist]
  | v, n + 1, h => by
    obtain ⟨⟨a, b, rfl⟩, h2⟩ := h
    simp only [π2_pair] at h2
    rw [plist_pair, vlist, ← listLen_vlist h2]

/-- The generator of a truncated declaration, as an element. -/
def genV (c n : ℕ) (ctors : List Ctor) : V := conV ctors n c [] []

/-! ### Environments of argument contexts -/

/-- The environment of an argument context with Kripke-value junk out of range. -/
def argEnvKV (n : ℕ) (ps pre : List V) : ℕ → V := fun x => (pre.reverse ++ ps.reverse).getD x (emptyC n)

/-- Earlier arguments with the recursive one at position `i` replaced by `gf i`. -/
def genPre (C : Ctor) (gf : ℕ → V) (pre : List V) : List V := pre.mapIdx fun i a => if C.isRec i then gf i else a

theorem genPre_length (C : Ctor) (gf : ℕ → V) (pre : List V) : (genPre C gf pre).length = pre.length := by
  simp [genPre]

theorem genPre_getElem (C : Ctor) (gf : ℕ → V) (pre : List V) (i : ℕ) (hi : i < (genPre C gf pre).length) :
    (genPre C gf pre)[i] = if C.isRec i then gf i else pre[i]'(by simpa [genPre_length] using hi) := by
  simp [genPre]

theorem genPre_take (C : Ctor) (gf : ℕ → V) (pre : List V) (i : ℕ) :
    (genPre C gf pre).take i = genPre C gf (pre.take i) := by
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
    (hi : i ≤ pre.length) (gf : ℕ → V) :
    sem (S0 ++ [.data E]) A n (fun _ => DM.zero n)
      (argEnvKV n (plist psv D.params.length) (genPre C gf (pre.take i))) =
      argTyRaw (sigV S0) D S0.length c i n psv pre := by
  obtain ⟨hcl, hcs, hmd, hnr⟩ := hsyn.2.2.1 c C hC i A hA
  have harg : (D.ctors.getD c default).argTy S0.length D.params.length i = A := by
    rw [getD_ctors hC]; simp [Ctor.argTy, hA]
  rw [argTyRaw, harg, sem_ext' S0 E hcs hmd]
  refine interp_congr_free _ _ _ A n _ _ _ fun x hx => ?_
  have hxl := freeIn_lt_of_closedB A _ 0 x hcl hx
  have hgl : (genPre C gf (pre.take i)).length = i := by simp [genPre_length]; omega
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
theorem isPoint_argCtx (c0 : ℕ) {Φ : I} {j : ℕ} {n : ℕ} (g : Hom n m)
    (ρ : IEnv n) (hρ : (ival ρ Φ).holds) (gf : ℕ → V)
    (hgf : ∀ i, C.isRec i = true →
      gf i ∈ El (dataC (dataSD (sigV S0) (D.truncate c0) S0.length n fun k f => ps k (g.comp f))) (Hom.id n))
    {pre : List V} (hjp : j ≤ pre.length)
    (hjC : j ≤ C.args.length)
    (hpt : ∀ i (hi : i < j), C.isRec i = false →
      pre[i]'(by omega) ∈ El (argTyRaw (sigV S0) D S0.length c i n (ps n g) pre) (Hom.id n) ∧ IsKV n (pre[i]'(by omega))) :
    IsPoint (S0 ++ [.data (D.truncate c0)]) Φ (D.argCtx S0.length C j) n ρ
      (argEnvKV n (plist (ps n g) D.params.length) (genPre C gf (pre.take j))) := by
  set np := D.params.length
  have hgl : (genPre C gf (pre.take j)).length = j := by simp [genPre_length]; omega
  have hpl : (plist (ps n g) np).length = np := by simp [plist]
  refine ⟨hρ, fun x B hB => ?_, fun x => ?_⟩
  · rw [Ctx.lookup_eq] at hB
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.1 hB
    rw [sem_ren]
    by_cases hxj : x < j
    · rw [argCtx_lt D _ C j x hxj] at hT
      cases hT
      rw [show (fun y => argEnvKV n (plist (ps n g) np) (genPre C gf (pre.take j)) (y + (x + 1))) =
          argEnvKV n (plist (ps n g) np) (genPre C gf (pre.take (j - 1 - x))) by
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
          rw [harg, sem_rho_irrel _ (hsyn.2.2.1 c C hC _ A hA).1 _ (fun _ => DM.zero n),
            sem_argTy_eq S0 _ D hsyn hC hA (ps n g) pre (by omega)]
          exact (hpt _ (by omega) hr).1
        | recur =>
          have hr : C.isRec (j - 1 - x) = true := by simp [Ctor.isRec, hA]
          rw [if_pos hr]
          have harg : C.argTy S0.length np (j - 1 - x) = .data S0.length (Ctor.paramVars np (j - 1 - x)) := by
            simp [Ctor.argTy, hA]
          rw [harg, sem_data (entry_ext S0 _), sigUpTo_ext]
          have hpv := sem_paramVars_rv (i := j - 1 - x) (S0 ++ [.data (D.truncate c0)]) hps g
            (genPre C gf (pre.take (j - 1 - x))) (by simp [genPre_length]; omega) (fun i => ρ (id i))
          unfold psRV
          rw [hpv, if_pos (show ParamsOK (sigV S0) (D.truncate c0) n _ from hps.restr g)]
          exact hgf _ hr
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
        · rename_i hr'
          exact (mem_El_dataC.1 (hgf _ hr')).kv
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

theorem genPre_map (C : Ctor) (gf : ℕ → V) (pre : List V) (f : V → V) :
    (genPre C gf pre).map f = genPre C (fun i => f (gf i)) (pre.map f) := by
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
    have hp := isPoint_argCtx S0 D hsyn hC hps 0 (Φ := .one) g (fun _ => DM.zero n)
      (by simp [DM.holds, ival.fn, I.eval]) (fun _ => genV 0 n (D.truncate 0).ctors)
      (fun _ _ => genV_mem (Nat.zero_le _)) hjp hjC hkv
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
    (ρ : IEnv n) (psv : V) (gf : ℕ → V) {pre : List V} (hjp : j ≤ pre.length) :
    sem (S0 ++ [.data E]) T n ρ (argEnvKV n (plist psv D.params.length) (genPre C gf (pre.take j))) =
      argTyRaw (sigV S0) D S0.length c (j - 1 - x) n psv pre := by
  rw [Ctx.lookup_eq, argCtx_lt D _ C j x hx] at hT
  simp only [Option.map_some, Option.some.injEq] at hT
  subst hT
  have hgl : (genPre C gf (pre.take j)).length = j := by simp [genPre_length]; omega
  rw [sem_ren, show (fun y => argEnvKV n (plist psv D.params.length) (genPre C gf (pre.take j)) (y + (x + 1))) =
      argEnvKV n (plist psv D.params.length) (genPre C gf (pre.take (j - 1 - x))) by
    rw [argEnvKV_shift _ _ (by omega), hgl, genPre_take, List.take_take, Nat.min_eq_left (by omega)]]
  obtain ⟨A, hA⟩ : ∃ A, C.args[j - 1 - x]? = some (.point A) := by
    have hi : j - 1 - x < C.args.length := by omega
    cases h' : C.args[j - 1 - x]'hi with
    | point A => exact ⟨A, by rw [List.getElem?_eq_getElem hi, h']⟩
    | recur => simp [Ctor.isRec, List.getElem?_eq_getElem hi, h'] at hr
  have harg : C.argTy S0.length D.params.length (j - 1 - x) = A := by simp [Ctor.argTy, hA]
  rw [harg, sem_rho_irrel _ (hsyn.2.2.1 c C hC _ A hA).1 _ (fun _ => DM.zero n),
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

/-! ### The argument types of the semantic data -/

theorem argTyRaw_recIrr {σ : SigV} {D : DataDecl} {d : ℕ} (hsyn : DataSyn d D) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) {j : ℕ} {A : Tm} (hA : C.args[j]? = some (.point A)) (n : ℕ) (psv : V)
    {pre pre' : List V} (hj : j ≤ pre.length) (hj' : j ≤ pre'.length)
    (he : ∀ i (hi : i < j), C.isRec i = false → pre[i]'(by omega) = pre'[i]'(by omega)) :
    argTyRaw σ D d c j n psv pre = argTyRaw σ D d c j n psv pre' := by
  obtain ⟨hcl, -, -, hnr⟩ := hsyn.2.2.1 c C hC j A hA
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

/-- At valid earlier arguments the argument types are the raw ones. -/
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

/-- The argument types of `E` are well-formed codes (`argTy_univ`). -/
def ArgTysOK (S0 : Sig) (E : DataDecl) : Prop :=
  ∀ (c : ℕ) (C : Ctor), E.ctors[c]? = some C → ∀ (j : ℕ) (A : Tm), C.args[j]? = some (.point A) →
    ∀ (m : ℕ) (ps : RV m), ParamsOK (sigV S0) E m ps → ∀ n (g : Hom n m) (pre : List V) (hjp : j ≤ pre.length),
      (∀ i (hi : i < j), C.isRec i = false →
        pre[i]'(by omega) ∈ El (argTyRaw (sigV S0) E S0.length c i n (ps n g) pre) (Hom.id n)) →
      argTyRaw (sigV S0) E S0.length c j n (ps n g) pre ∈ El (univC n E.level) (Hom.id n) ∧
      ∀ n' (h : Hom n' n), res h (argTyRaw (sigV S0) E S0.length c j n (ps n g) pre) =
        argTyRaw (sigV S0) E S0.length c j n' (ps n' (g.comp h)) (pre.map (res h))

theorem argTysOK_of (S0 : Sig) (E : DataDecl) (hsyn : DataSyn S0.length E)
    (hok0 : SigOK (S0 ++ [.data (E.truncate 0)]))
    (hck : ∀ (c : ℕ) (C : Ctor), E.ctors[c]? = some C → ∀ (k : ℕ) (A : Tm), C.args[k]? = some (.point A) →
      HasTy (S0 ++ [.data (E.truncate 0)]) 0 .one (E.argCtx S0.length C k) A (.univ E.level)) :
    ArgTysOK S0 E := fun c C hC j A hA m ps hps n g pre hjp hpre =>
  argTy_univ S0 E hsyn hC hps hok0 (hck c C hC) j A hA n g pre hjp hpre

variable (S0 : Sig) (E : DataDecl) (hsyn : DataSyn S0.length E) (hU : ArgTysOK S0 E)
include hsyn hU

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
    exact (hU c C hC j A hA m ps hps n g pre hv.1
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
    have hUi : ∀ i (hi : i < j), C.isRec i = false →
        argTyRaw (sigV S0) E S0.length c i n (ps n g) pre ∈ El (univC n E.level) (Hom.id n) ∧
        ∀ n' (h : Hom n' n), res h (argTyRaw (sigV S0) E S0.length c i n (ps n g) pre) =
          argTyRaw (sigV S0) E S0.length c i n' (ps n' (g.comp h)) (pre.map (res h)) := by
      intro i hi hri
      have hiC : i < C.args.length := by rw [← hgC]; omega
      obtain ⟨Ai, hAi⟩ : ∃ Ai, C.args[i]? = some (.point Ai) := by
        cases h' : C.args[i]'hiC with
        | point Ai => exact ⟨Ai, by rw [List.getElem?_eq_getElem hiC, h']⟩
        | recur => simp [Ctor.isRec, List.getElem?_eq_getElem hiC, h'] at hri
      exact hU c C hC i Ai hAi m ps hps n g pre (by omega)
        fun i' hi' hr' => hv.2 i' (by omega) (by omega) (by rw [hgC]; exact hr')
    have hc' : j < (E.ctors.getD c default).args.length ∧ (E.ctors.getD c default).isRec j = false ∧
        argPreValid (sigV S0) E S0.length c j n' (ps n' (g.comp h)) (pre.map (res h)) := by
      refine ⟨hj, hr, by simpa using hv1, fun i hi hip hri => ?_⟩
      rw [hgC] at hri
      obtain ⟨hmem, hnat⟩ := hUi i hi hri
      rw [← hnat n' h, List.getElem_map]
      rw [mem_El_univ_iff] at hmem
      have := hmem.2.fib.elRes n (Hom.id n) _ (hv.2 i hi (by omega) (by rw [hgC]; exact hri)) n' h
      rwa [El_eq_res_id, Hom.id_comp] at this
    rw [argTySem_eq, if_pos ⟨hj, hr, hv⟩, argTySem_eq, if_pos hc']
    exact (hU c C hC j A hA m ps hps n g pre hv1
      fun i' hi' hr' => hv.2 i' hi' (by omega) (by rw [hgC]; exact hr')).2 n' h
  · have hc' : ¬ (j < (E.ctors.getD c default).args.length ∧ (E.ctors.getD c default).isRec j = false ∧
        argPreValid (sigV S0) E S0.length c j n' (ps n' (g.comp h)) (pre.map (res h))) := by
      rintro ⟨hj, hr, hv⟩
      exact hc ⟨hj, hr, ptValid_argPreValid hp (by simpa using hv.1)⟩
    rw [argTySem_eq, if_neg hc, argTySem_eq, if_neg hc', res_emptyC]

omit hU in
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

omit hsyn hU in
theorem argTySem_noparams (hnp : E.params = []) (c j n : ℕ) (psv psv' : V) (pre : List V) :
    argTySem (sigV S0) E S0.length c j n psv pre = argTySem (sigV S0) E S0.length c j n psv' pre := by
  have h0 : ∀ v, plist v E.params.length = [] := by intro v; simp [plist, hnp]
  simp only [argTySem, argPreValid, argTyRaw, h0]

theorem dataSD_resClosed {m : ℕ} {ps : RV m} (hps : ParamsOK (sigV S0) E m ps) :
    (dataSD (sigV S0) E S0.length m ps).ResClosed := by
  intro c j n g pre a hp ha n' h
  have hfib : Fib (argTySem (sigV S0) E S0.length c j n (ps n g) pre) n := by
    rcases argTySem_facts S0 E hsyn hU hps c j n g pre with h' | h'
    · rw [mem_El_univ_iff] at h'; exact h'.2.fib
    · rw [h']; exact fib_emptyC
  have := hfib.elRes n (Hom.id n) a ha n' h
  rw [El_eq_res_id, Hom.id_comp] at this
  have e := argTySem_nat S0 E hsyn hU hps c j n g pre hp n' h
  change a ∈ El (argTySem (sigV S0) E S0.length c j n (ps n g) pre) (Hom.id n) at ha
  change res h a ∈ El (argTySem (sigV S0) E S0.length c j n' (ps n' (g.comp h)) (pre.map (res h))) (Hom.id n')
  rwa [e] at this

theorem dataSD_basic {m : ℕ} {ps : RV m} (hps : ParamsOK (sigV S0) E m ps) :
    (dataSD (sigV S0) E S0.length m ps).Basic where
  recIrr c j n g pre pre' hl he := argTySem_recIrr S0 E hsyn c j n _ pre pre' hl he
  fib c j n g pre _ := by
    rcases argTySem_facts S0 E hsyn hU hps c j n g pre with h | h
    · rw [mem_El_univ_iff] at h; exact h.2.fib
    · show Fib (argTySem _ _ _ _ _ _ _ _) n
      rw [h]; exact fib_emptyC

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
  refine ⟨{ nat := fun c j n g pre hp n' h => argTySem_nat S0 E hsyn hU hps c j n g pre hp n' h
            recIrr := fun c j n g pre pre' hl he => argTySem_recIrr S0 E hsyn c j n _ pre pre' hl he
            bnd := hb
            const := fun hp c j n g g' pre => argTySem_noparams S0 E (by
              simpa [dataSD] using hp) c j n _ _ pre
            ovl := ho
            fib := fun c j n g pre _ => ?_ }, fun c j n g pre => ?_⟩
  · rcases argTySem_facts S0 E hsyn hU hps c j n g pre with h | h
    · rw [mem_El_univ_iff] at h; exact h.2.fib
    · show Fib (argTySem _ _ _ _ _ _ _ _) n
      rw [h]; exact fib_emptyC
  · rcases argTySem_facts S0 E hsyn hU hps c j n g pre with h | h
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


/-! ### Point contexts (parameters and point arguments) -/

/-- The point arguments among the first `j` arguments (oldest first). -/
def pointsOf (C : Ctor) (pre : List V) (j : ℕ) : List V :=
  ((List.range j).filter fun k => !C.isRec k).map fun k => pre.getD k ∅

theorem pointsOf_succ (C : Ctor) (pre : List V) (j : ℕ) :
    pointsOf C pre (j + 1) = pointsOf C pre j ++ (if C.isRec j then [] else [pre.getD j ∅]) := by
  unfold pointsOf
  rw [List.range_succ, List.filter_append, List.map_append]
  congr 1
  by_cases h : C.isRec j <;> simp [h]

theorem pointRen_zero (C : Ctor) (j : ℕ) : C.pointRen (j + 1) 0 = 0 := by
  simp [Ctor.pointRen]

theorem pointRen_succ (C : Ctor) (j y : ℕ) :
    C.pointRen (j + 1) (y + 1) = (if C.isRec j then 0 else 1) + C.pointRen j y := by
  unfold Ctor.pointRen
  by_cases hy : y < j
  · rw [if_pos (by omega), if_pos hy, List.range_succ_eq_map, List.filter_cons, List.filter_map]
    have e : List.filter ((fun x => !C.isRec (j + 1 - 1 - x)) ∘ Nat.succ) (List.range y) =
        List.filter (fun x => !C.isRec (j - 1 - x)) (List.range y) :=
      List.filter_congr fun x _ => by simp only [Function.comp]; congr 2; omega
    rw [e]
    by_cases h : C.isRec j <;> simp [h, show j + 1 - 1 - 0 = j by omega] <;> omega
  · rw [if_neg (by omega), if_neg hy, List.range_succ, List.filter_append]
    have hle : ((List.range j).filter C.isRec).length ≤ j := by
      have := List.length_filter_le C.isRec (List.range j); simpa using this
    by_cases h : C.isRec j <;> simp [h] <;> omega

theorem argEnvKV_snoc (ps L : List V) (a : V) : argEnvKV n ps (L ++ [a]) = TEnv.cons (argEnvKV n ps L) a := by
  funext x
  cases x with
  | zero => simp [argEnvKV, TEnv.cons]
  | succ x => simp [argEnvKV, TEnv.cons, List.getD_eq_getElem?_getD]

/-- The point environment, renamed back to the argument context, agrees with the argument
environment at the parameters and the point arguments. -/
theorem pointsOf_env (C : Ctor) (ps pre : List V) :
    ∀ j, j ≤ pre.length → ∀ y, (y < j → C.isRec (j - 1 - y) = false) →
      argEnvKV n ps (pointsOf C pre j) (C.pointRen j y) = argEnvKV n ps (pre.take j) y := by
  intro j
  induction j with
  | zero => intro _ y _; simp [pointsOf, Ctor.pointRen]
  | succ j ih =>
    intro hj y hy
    rw [pointsOf_succ]
    have htk : pre.take (j + 1) = pre.take j ++ [pre.getD j ∅] := by
      rw [List.take_succ, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]; rfl
    cases y with
    | zero =>
      have hr : C.isRec j = false := by simpa using hy (by omega)
      rw [pointRen_zero, if_neg (by simp [hr]), argEnvKV_snoc, htk, argEnvKV_snoc]; rfl
    | succ y =>
      rw [pointRen_succ, htk, argEnvKV_snoc]
      have ih' := ih (by omega) y (fun h => by have := hy (by omega); rwa [show j + 1 - 1 - (y + 1) = j - 1 - y by omega] at this)
      by_cases hr : C.isRec j = true
      · rw [if_pos hr, if_pos hr, List.append_nil, Nat.zero_add, ih']; rfl
      · rw [if_neg hr, if_neg hr, argEnvKV_snoc, Nat.add_comm]; exact ih'


theorem mentionsData_ren (d : ℕ) : ∀ (t : Tm) (ρ δ : ℕ → ℕ), (t.ren ρ δ).mentionsData d = t.mentionsData d := by
  intro t
  induction t <;> intros <;> simp_all [Tm.ren, Tm.mentionsData]

theorem pointCtx_succ (D : DataDecl) (d : ℕ) (C : Ctor) (j : ℕ) :
    D.pointCtx d C (j + 1) = if C.isRec j then D.pointCtx d C j else
      ((C.argTy d D.params.length j).ren (C.pointRen j) id) :: D.pointCtx d C j := by
  unfold DataDecl.pointCtx
  rw [List.range_succ, List.filter_append]
  by_cases h : C.isRec j <;> simp [h]

theorem argEnvKV_genPre (C : Ctor) (gf : ℕ → V) (ps L : List V) (y : ℕ)
    (hy : y < L.length → C.isRec (L.length - 1 - y) = false) :
    argEnvKV n ps (genPre C gf L) y = argEnvKV n ps L y := by
  simp only [argEnvKV, List.getD_eq_getElem?_getD]
  by_cases hyl : y < L.length
  · rw [List.getElem?_append_left (by simp [genPre_length]; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_reverse (by simp [genPre_length]; omega), List.getElem?_reverse (by omega)]
    simp only [genPre_length]
    rw [List.getElem?_eq_getElem (by simp [genPre_length]; omega), List.getElem?_eq_getElem (by omega), genPre_getElem,
      if_neg (by simp [hy hyl])]
  · rw [List.getElem?_append_right (by simp [genPre_length]; omega), List.getElem?_append_right (by simp; omega)]
    simp [genPre_length]

section tyeq

variable (S0 : Sig) (D : DataDecl) (hsyn : DataSyn S0.length D)
  {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {m : ℕ} {ps : RV m} (hps : ParamsOK (sigV S0) D m ps)

theorem toList_ofList : ∀ L : List Tm, (Tm.ofList L).toList = L
  | [] => rfl
  | t :: L => by simp [Tm.ofList, Tm.toList, toList_ofList L]

theorem nestPre_length (pre : List V) (prev : List Tm) : (nestPre pre prev).length = prev.length := by
  simp [nestPre]

include hsyn hC hps in
theorem isPoint_pointCtx {Φ : I} {n2 : ℕ} (g : Hom n2 m) (ρ : IEnv n2) (hρ : (ival ρ Φ).holds) {pre : List V} :
    ∀ j (hjp : j ≤ pre.length), j ≤ C.args.length →
    (∀ i (hi : i < j), C.isRec i = false →
      pre[i]'(by omega) ∈ El (argTyRaw (sigV S0) D S0.length c i n2 (ps n2 g) pre) (Hom.id n2) ∧
        IsKV n2 (pre[i]'(by omega))) →
    IsPoint S0 Φ (D.pointCtx S0.length C j) n2 ρ (argEnvKV n2 (plist (ps n2 g) D.params.length) (pointsOf C pre j))
  | 0, _, _, _ => by
    have hb := isPoint_argCtx S0 D hsyn hC hps 0 g ρ hρ (fun _ => genV 0 n2 (D.truncate 0).ctors)
      (fun _ _ => genV_mem (Nat.zero_le _)) (j := 0) (pre := pre) (Nat.zero_le _) (Nat.zero_le _)
      (fun i hi => absurd hi (Nat.not_lt_zero i))
    have e1 : D.argCtx S0.length C 0 = D.pointCtx S0.length C 0 := by simp [DataDecl.argCtx, DataDecl.pointCtx]
    have e2 : genPre C (fun _ => genV 0 n2 (D.truncate 0).ctors) (pre.take 0) = pointsOf C pre 0 := by
      simp [genPre, pointsOf]
    rw [e1, e2] at hb
    refine ⟨hb.cof, fun x B hB => ?_, hb.kv⟩
    have hm := hb.typ x B hB
    rw [Ctx.lookup_eq] at hB
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.1 hB
    have hTm : T ∈ D.paramCtx D.params.length := by
      have := List.mem_of_getElem? hT; simpa [DataDecl.pointCtx] using this
    simp only [DataDecl.paramCtx, List.take_length, List.mem_reverse] at hTm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hTm
    have hc := (hsyn.2.1 i _ (List.getElem?_eq_getElem hi)).2
    rw [sem_ext S0 _ (hc.ren _ _)] at hm
    exact hm
  | j + 1, hj, hjC, hpt => by
    have ih := isPoint_pointCtx g ρ hρ j (by omega) (by omega) (fun i hi hr => hpt i (by omega) hr)
    rw [pointCtx_succ, pointsOf_succ]
    by_cases hr : C.isRec j = true
    · simp only [hr, if_true, List.append_nil]; exact ih
    · have hr' : C.isRec j = false := by simpa using hr
      simp only [hr', Bool.false_eq_true, if_false]
      rw [argEnvKV_snoc]
      have hgj : pre.getD j ∅ = pre[j]'(by omega) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      obtain ⟨hmem, hkv⟩ := hpt j (by omega) hr'
      refine ih.cons ?_ (by rw [hgj]; exact hkv)
      obtain ⟨A, hA⟩ : ∃ A, C.args[j]? = some (.point A) := by
        cases h' : C.args[j]'(by omega) with
        | point A => exact ⟨A, by rw [List.getElem?_eq_getElem (by omega), h']⟩
        | recur => simp [Ctor.isRec, List.getElem?_eq_getElem (show j < C.args.length by omega), h'] at hr'
      obtain ⟨hcl, hcs, hmd, hnr⟩ := hsyn.2.2.1 c C hC j A hA
      have harg : C.argTy S0.length D.params.length j = A := by simp [Ctor.argTy, hA]
      have harg' : (D.ctors.getD c default).argTy S0.length D.params.length j = A := by
        rw [getD_ctors hC]; exact harg
      rw [hgj, harg, sem_ren]
      rw [argTyRaw, harg'] at hmem
      convert hmem using 2
      rw [sem_rho_irrel _ hcl _ (fun _ => DM.zero n2)]
      refine interp_congr_free _ _ _ A n2 _ _ _ fun y hy => ?_
      have hyl := freeIn_lt_of_closedB A _ 0 y hcl hy
      rw [pointsOf_env C _ pre j (by omega) y (fun h => noRecDeps_point hnr h hy)]
      rw [argEnvKV_eq_of_lt (by simp [plist]; omega), argEnv_eq_of_lt (by simp [plist]; omega)]

include hsyn hC hps in
/-- The type equality of a boundary point argument, from its judgmental version. -/
theorem tyEq_core (hc : c ≤ D.ctors.length)
    {ψ : I} {n0 : ℕ} {rs0 : List (DM n0)} (hrs0 : (ival (renv rs0) ψ).holds)
    {c' : ℕ} {C' : Ctor} (hC' : D.ctors[c']? = some C') {k : ℕ} {A' : Tm} (hA' : C'.args[k]? = some (.point A'))
    {prev : List Tm} (hpl : prev.length = k)
    (Hprev : ∀ q (hq : q < k), C'.isRec q = false → ∃ y, prev.reverse[q]'(by simp; omega) = .var y ∧
      y < C.args.length ∧ C.isRec (C.args.length - 1 - y) = false)
    {x : ℕ} (hx : x < C.args.length) (hxr : C.isRec (C.args.length - 1 - x) = false) {T : Tm}
    (hT : (D.argCtx S0.length C C.args.length).lookup x = some T)
    (hS0 : SigOK S0) (hm1 : C.mentionsRec C.args.length T = false)
    (hm2 : C.mentionsRec C.args.length ((C'.argTy S0.length D.params.length k).substList
        (prev ++ (Ctor.paramVars D.params.length C.args.length).toList.reverse)) = false)
    (heq : EqTm S0 C.dims ψ (D.pointCtx S0.length C C.args.length) (T.ren (C.pointRen C.args.length) id)
      (((C'.argTy S0.length D.params.length k).substList
        (prev ++ (Ctor.paramVars D.params.length C.args.length).toList.reverse)).ren (C.pointRen C.args.length) id)
      (.univ D.level))
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
  set gv : ℕ → V := fun _ => genV c n2 (D.truncate c).ctors
  set γ2 := argEnvKV n2 (plist (ps n2 g) np) (genPre C gv (pre.take n))
  have hp := isPoint_argCtx S0 D hsyn hC hps c g ρ2 hρ2 gv (fun _ _ => genV_mem hc) (j := n) (by omega) le_rfl
    (fun i hi hr => hpt i hi hr)
  have hE : sem S0 T n2 ρ2 γ2 = sem S0 ((C'.argTy S0.length np k).substList
      (prev ++ (Ctor.paramVars np n).toList.reverse)) n2 ρ2 γ2 := by
    have hpP := isPoint_pointCtx S0 D hsyn hC hps g ρ2 hρ2 (pre := pre) n (by omega) le_rfl
      (fun i hi hr => hpt i hi hr)
    have hEq := (sound_eq hS0 heq).2.2 n2 ρ2 _ hpP
    rw [sem_ren, sem_ren] at hEq
    have htr : ∀ t : Tm, C.mentionsRec n t = false →
        sem S0 t n2 (fun i => ρ2 (id i)) (fun y => argEnvKV n2 (plist (ps n2 g) np) (pointsOf C pre n)
          (C.pointRen n y)) = sem S0 t n2 ρ2 γ2 := by
      intro t ht
      refine interp_congr_free _ _ _ t n2 _ _ _ fun y hy => ?_
      have hnr : y < n → C.isRec (n - 1 - y) = false := by
        intro hyn
        unfold Ctor.mentionsRec at ht
        have := List.any_eq_false.1 ht y (List.mem_range.2 hyn)
        simp only [Bool.and_eq_true, not_and] at this
        cases h : C.isRec (n - 1 - y)
        · rfl
        · exact absurd hy (by simpa using this h)
      rw [pointsOf_env C _ pre n (by omega) y hnr]
      have hcond : y < (pre.take n).length → C.isRec ((pre.take n).length - 1 - y) = false := by
        rw [List.length_take, Nat.min_eq_left (by omega)]; exact hnr
      simp only [γ2]
      rw [argEnvKV_genPre C gv _ _ y hcond]
    rw [htr T hm1, htr _ hm2] at hEq
    exact hEq
  obtain ⟨Ax, hAx⟩ : ∃ A, C.args[n - 1 - x]? = some (.point A) := by
    cases h' : C.args[n - 1 - x]'(by omega) with
    | point A => exact ⟨A, by rw [List.getElem?_eq_getElem (by omega), h']⟩
    | recur => simp [Ctor.isRec, List.getElem?_eq_getElem (show n - 1 - x < C.args.length by omega), h'] at hxr
  have hTe : T = Ax.ren (· + (x + 1)) id := by
    have hT' := hT
    rw [Ctx.lookup_eq, argCtx_lt D _ C _ x hx] at hT'
    simp only [Option.map_some, Option.some.injEq] at hT'
    rw [← hT']; simp [Ctor.argTy, hAx]
  obtain ⟨-, hcsx, hmdx, -⟩ := hsyn.2.2.1 c C hC _ Ax hAx
  have hTS : sem S0 T n2 ρ2 γ2 = sem Sc T n2 ρ2 γ2 := by
    rw [sem_ext' S0 _ (by rw [hTe]; exact hcsx.ren _ _) (by rw [hTe, mentionsData_ren]; exact hmdx)]
  rw [hTS, sem_lookup_point S0 D hsyn hC _ hx le_rfl hxr hT ρ2 (ps n2 g) gv (by omega)] at hE
  rw [hE]
  -- the right-hand side
  have harg : C'.argTy S0.length np k = A' := by simp [Ctor.argTy, hA']
  obtain ⟨hcl, hcs, hmd, hnr⟩ := hsyn.2.2.1 c' C' hC' k A' hA'
  set L := prev ++ (Ctor.paramVars np n).toList.reverse
  have hPV : (Ctor.paramVars np n).toList = (List.range np).map fun p => Tm.var (n + np - 1 - p) := by
    rw [Ctor.paramVars, toList_ofList]
  have hLl : L.length = k + np := by simp [L, hpl, hPV]
  have hkv2 : ∀ y, IsKV n2 (γ2 y) := hp.kv
  set σ : ℕ → Tm := fun j => L.getD j (.var (j - L.length)) with hσdef
  set σ' : ℕ → Tm := fun j => match σ j with | .var y => .var y | _ => .var 0 with hσ'def
  have hσvar : ∀ y, A'.freeIn y = true → ∃ z, σ y = .var z := by
    intro y hy
    have hyl := freeIn_lt_of_closedB A' _ 0 y hcl hy
    simp only [hσdef, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : y < L.length),
      Option.getD_some]
    by_cases hyk : y < k
    · obtain ⟨y', hy'e, -⟩ := Hprev (k - 1 - y) (by omega) (noRecDeps_point hnr hyk hy)
      refine ⟨y', ?_⟩
      rw [List.getElem_append_left (by omega), ← hy'e, List.getElem_reverse]; congr 1; omega
    · rw [List.getElem_append_right (by omega)]
      simp only [hPV, List.getElem_reverse, List.getElem_map]
      exact ⟨_, rfl⟩
  have hσ' : ∀ y, A'.freeIn y = true → σ y = σ' y := by
    intro y hy
    obtain ⟨z, hz⟩ := hσvar y hy
    simp only [hσ'def, hz]
  have hnat : ∀ y, Natural S0 (σ' y) n2 ρ2 γ2 := by
    intro y; simp only [hσ'def]; split <;> (intro k' f; rfl)
  rw [harg, Tm.substList, ← hσdef, Tm.subst_congr_free A' σ σ' I.var hσ', sem_subst S0 A' n2 ρ2 γ2 _ _ hnat,
    sem_rho_irrel _ hcl _ (fun _ => DM.zero n2)]
  have harg' : (D.ctors.getD c' default).argTy S0.length np k = A' := by rw [getD_ctors hC']; exact harg
  rw [argTyRaw, harg']
  refine interp_congr_free _ _ _ A' n2 _ _ _ fun y hy => ?_
  have hyl := freeIn_lt_of_closedB A' _ 0 y hcl hy
  have hnl : (nestPre pre prev).length = k := by rw [nestPre_length, hpl]
  rw [← hσ' y hy]
  simp only [hσdef, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : y < L.length), Option.getD_some]
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
    (hS0 : SigOK S0) (hc : c ≤ D.ctors.length)
    {ψ : I} {n0 : ℕ} {rs0 : List (DM n0)} (hrs0 : (ival (renv rs0) ψ).holds)
    {E : DataDecl} (hEp : E.params = D.params) (hEc : ∀ c' ≤ c, E.ctors[c']? = D.ctors[c']?) :
    ∀ t : Tm,
      (Ctor.simpleB D.ctors S0.length D.params.length c C.args.length C t = true →
        Ctor.bndTyped S0 C.dims ψ (D.argCtx S0.length C C.args.length) C (D.pointCtx S0.length C C.args.length)
          D.level D.ctors S0.length D.params.length t →
        SimpleShape (D.truncate c).ctors S0.length t ∧ BTy (dataSD (sigV S0) E S0.length m ps) c C t) ∧
      (∀ (C' : Ctor) (c' k : ℕ) (prev : List Tm), c' < c → D.ctors[c']? = some C' →
        k + t.toList.length = C'.args.length →
        Ctor.simpleArgs D.ctors S0.length D.params.length c C.args.length C C' k t = true →
        Ctor.bndTypedArgs S0 C.dims ψ (D.argCtx S0.length C C.args.length) C (D.pointCtx S0.length C C.args.length)
          D.level D.ctors S0.length D.params.length C' (Ctor.paramVars D.params.length C.args.length) k prev t →
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
      obtain ⟨hm1, hm2, heq⟩ := hb1 x T rfl hr hT
      have hcore := fun n2 (g : Hom n2 m) pre hpre htp => tyEq_core S0 D hsyn hC hps hc hrs0 hC' hA' hpl
        (fun q hq hrq => by obtain ⟨y, h1, h2, h3, -⟩ := Hprev q hq hrq; exact ⟨y, h1, h2, h3⟩) hx hxr hT hS0 hm1 hm2 heq
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

/-! ### Assembly -/

/-- The generator constructor of truncated declarations. -/
abbrev genCtor : Ctor := { args := [], dims := 0, bnd := [] }

theorem sigOK_ext {S0 : Sig} (hS0 : SigOK S0) {E : DataDecl} (hE : DataOK (S0 ++ [.data E]) S0.length E) :
    SigOK (S0 ++ [.data E]) := by
  refine ⟨fun k t A hk => ?_, fun k D' hk => ?_⟩
  · have hkl : k < S0.length := by
      by_contra h
      have : k < (S0 ++ [Entry.data E]).length := (List.getElem?_eq_some_iff.1 hk).1
      simp at this
      have hk' : k = S0.length := by omega
      subst hk'; simp at hk
    rw [List.getElem?_append_left hkl] at hk
    have := hS0.1 k t A hk
    rwa [List.take_append_of_le_length hkl.le]
  · by_cases hkl : k < S0.length
    · rw [List.getElem?_append_left hkl] at hk
      have := hS0.2 k D' hk
      have e : sigUpTo (S0 ++ [Entry.data E]) k = sigUpTo S0 k := by
        rw [← sigUpTo_take (S0 ++ [Entry.data E]) (K := S0.length) k hkl.le, List.take_left' rfl]
      unfold DataOK at this ⊢
      rwa [e]
    · have : k < (S0 ++ [Entry.data E]).length := (List.getElem?_eq_some_iff.1 hk).1
      simp at this
      have hk' : k = S0.length := by omega
      subst hk'
      simp at hk; subst hk; exact hE

/-! ### Overlaps: generic arguments -/

theorem conV_congr_ctors {ctors1 ctors2 : List Ctor} (n : ℕ) : ∀ k,
    (∀ k' ≤ k, ctors1.getD k' default = ctors2.getD k' default) → conV ctors1 n k = conV ctors2 n k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro h
    funext args rs
    rw [conV_eq, conV_eq, h k le_rfl]
    congr 1; funext k' f
    split
    · rename_i b _
      congr 2
      funext c' as rs'
      split
      · rename_i hc; rw [ih c' hc fun k'' hk'' => h k'' (by omega)]
      · rfl
    · rfl

theorem conBefore_congr_ctors {ctors1 ctors2 : List Ctor} {c n : ℕ}
    (h : ∀ k' < c, ctors1.getD k' default = ctors2.getD k' default) :
    conBefore ctors1 c n = conBefore ctors2 c n := by
  funext c' as rs'
  unfold conBefore
  split
  · rename_i hc; rw [conV_congr_ctors n c' fun k'' hk'' => h k'' (by omega)]
  · rfl

/-- Formal compositions with an empty face, iterated over `a0`: fresh, pairwise distinct values. -/
def atomV (n : ℕ) (a0 : V) : ℕ → V
  | 0 => a0
  | i + 1 => hcV n (Cof.bot n) (fun _ _ _ => ∅) (atomV n a0 i)

theorem not_bot_holds (n : ℕ) : ¬ (Cof.bot n).holds := by simp [Cof.holds, Cof.bot]

theorem atomV_kv {a0 : V} (ha0 : IsKV n a0) : ∀ i, IsKV n (atomV n a0 i)
  | 0 => ha0
  | _ + 1 => isKV_hcV _ _ _

theorem atomV_inj {a0 : V} (ha0 : IsKV n a0) (hne : ∀ ψ u a, ¬ ψ.holds → a0 ≠ hcV n ψ u a) :
    ∀ i j, atomV n a0 i = atomV n a0 j → i = j
  | 0, 0, _ => rfl
  | 0, j + 1, h => absurd h (hne _ _ _ (not_bot_holds n))
  | i + 1, 0, h => absurd h.symm (hne _ _ _ (not_bot_holds n))
  | i + 1, j + 1, h => by
    obtain ⟨-, -, hb⟩ := hcV_inj (Cof.isCof_bot n) (Cof.isCof_bot n) (not_bot_holds n) (not_bot_holds n)
      (atomV_kv ha0 i) (atomV_kv ha0 j) h
    rw [atomV_inj ha0 hne i j hb]

theorem atomV_DElem {Θ : SData m} {g : Hom n m} {a0 : V} (ha0 : DElem Θ n g a0) : ∀ i, DElem Θ n g (atomV n a0 i)
  | 0 => ha0
  | i + 1 => DElem.hcomp (Cof.isCof_bot n) (atomV_DElem ha0 i)
      (fun n' h r hh => absurd hh (by rw [Cof.bot_restr]; exact not_bot_holds n'))
      (fun n' h r hh => absurd hh (by rw [Cof.bot_restr]; exact not_bot_holds n'))
      (fun n' h hh => absurd hh (by rw [Cof.bot_restr]; exact not_bot_holds n'))

/-- Corresponding values: generic atoms and their actual values, and constructor values without
boundary at corresponding arguments. -/
inductive Corr (ctors : List Ctor) (n : ℕ) (gen act : ℕ → V) (P : ℕ → Prop) : V → V → Prop
  | atom {i : ℕ} : P i → Corr ctors n gen act P (gen i) (act i)
  | con {k : ℕ} {vT vX : List V} {rs : List (DM n)} :
      bndAtMap (ctors.getD k default) rs (Hom.id n) = none →
      (∀ a ∈ vT, IsKV n a) → (∀ a ∈ vX, IsKV n a) → vT.length = vX.length →
      (∀ j (hj : j < vT.length) (hj' : j < vX.length), (ctors.getD k default).isRec j = true →
        Corr ctors n gen act P vT[j] vX[j]) →
      (∀ j (hj : j < vT.length) (hj' : j < vX.length), (ctors.getD k default).isRec j = false → vT[j] = vX[j]) →
      Corr ctors n gen act P (conV ctors n k vT rs) (conV ctors n k vX rs)

theorem Corr.unique {ctors : List Ctor} {n : ℕ} {gen act : ℕ → V} {P : ℕ → Prop}
    (hinj : ∀ i j, P i → P j → gen i = gen j → i = j)
    (hne : ∀ i, P i → ∀ k vs (rs : List (DM n)), bndAtMap (ctors.getD k default) rs (Hom.id n) = none →
      gen i ≠ conV ctors n k vs rs) {v w : V} (h : Corr ctors n gen act P v w) :
    ∀ {w'}, Corr ctors n gen act P v w' → w = w' := by
  induction h with
  | @atom i hi =>
    intro w' h'
    generalize hv : gen i = v at h'
    cases h' with
    | @atom j hj => rw [hinj i j hi hj hv]
    | con hb _ _ _ _ _ => exact absurd hv (hne i hi _ _ _ hb)
  | @con k vT vX rs hb hkT hkX hl hrec hpt ih =>
    intro w' h'
    generalize hv : conV ctors n k vT rs = v at h'
    cases h' with
    | @atom j hj => exact absurd hv.symm (hne j hj _ _ _ hb)
    | @con k' vT' vX' rs' hb' hkT' hkX' hl' hrec' hpt' =>
      obtain ⟨rfl, rfl, rfl⟩ := conV_inj hb hb' hkT hkT' hv
      congr 1
      apply List.ext_getElem (by omega)
      intro j h1 h2
      cases hr : (ctors.getD k default).isRec j
      · rw [← hpt j (by omega) h1 hr, hpt' j (by omega) h2 hr]
      · exact ih j (by omega) h1 hr (hrec' j (by omega) h2 hr)


theorem simpleArgs_ofList {ctors : List Ctor} {d np c n : ℕ} {C C' : Ctor} : ∀ {k : ℕ} {t : Tm},
    Ctor.simpleArgs ctors d np c n C C' k t = true → t = Tm.ofList t.toList
  | _, .tcons a as, h => by
    simp only [Ctor.simpleArgs, Bool.and_eq_true] at h
    simp only [Tm.toList, Tm.ofList]
    rw [← simpleArgs_ofList h.2]
  | _, .tnil, _ => rfl
  | _, .var _, h | _, .const _, h | _, .univ _, h | _, .pi _ _, h | _, .lam _ _, h | _, .app _ _, h
  | _, .sigma _ _, h | _, .pair _ _, h | _, .fst _, h | _, .snd _, h | _, .path _ _ _, h | _, .plam _, h
  | _, .papp _ _, h | _, .ipi _, h | _, .abort, h | _, .split _ _ _ _, h | _, .transp _ _ _, h
  | _, .hcomp _ _ _ _, h | _, .glue _ _ _ _, h | _, .glueEl _ _ _ _, h | _, .unglue _ _ _, h
  | _, .data _ _, h | _, .con _ _ _ _ _, h | _, .elim _ _ _ _ _, h => by simp [Ctor.simpleArgs] at h

/-- A simple boundary term denotes its boundary value wherever it denotes something (the
guards of its constructors then hold). -/
theorem sem_simple_eval {S : Sig} {d : ℕ} {E : DataDecl} (hd : S[d]? = some (.data E)) {c : ℕ} {C : Ctor}
    {n : ℕ} {ρ : IEnv n} {γ : ℕ → V} (hγ : ∀ x, IsKV n (γ x)) (args : List V) (hl : args.length = C.args.length)
    (hargs : ∀ x (hx : x < C.args.length), γ x = args.reverse[x]'(by simp; omega)) (rs : List (DM n))
    (hρ : ∀ i < C.dims, ρ i = renv rs i) : ∀ t : Tm,
    (Ctor.simpleB E.ctors d E.params.length c C.args.length C t = true →
      t.closedB (E.params.length + C.args.length) C.dims = true → sem S t n ρ γ ≠ ∅ →
      sem S t n ρ γ = evalBnd (conBefore E.ctors c n) args rs t) ∧
    (∀ C' k, Ctor.simpleArgs E.ctors d E.params.length c C.args.length C C' k t = true →
      t.closedB (E.params.length + C.args.length) C.dims = true →
      ∀ i (hi : i < t.toList.length), (C'.isRec (k + i) = true → sem S (t.toList[i]) n ρ γ ≠ ∅ →
        sem S (t.toList[i]) n ρ γ = evalBnd (conBefore E.ctors c n) args rs (t.toList[i])) ∧
        (C'.isRec (k + i) = false → sem S (t.toList[i]) n ρ γ = evalBnd (conBefore E.ctors c n) args rs (t.toList[i]))) := by
  have hvar : ∀ x (hx : x < C.args.length), sem S (.var x) n ρ γ = evalBnd (conBefore E.ctors c n) args rs (.var x) := by
    intro x hx
    simp only [sem_var, evalBnd]
    rw [hargs x hx, getD_reverse_eq (by omega), List.getElem_reverse]
    have hkv := hγ x
    rw [hargs x hx, List.getElem_reverse] at hkv
    rw [res_id hkv]
  intro t
  induction t with
  | var x =>
    refine ⟨fun hs _ _ => ?_, fun _ _ hs => by simp [Ctor.simpleArgs] at hs⟩
    simp only [Ctor.simpleB, Bool.and_eq_true, decide_eq_true_eq] at hs
    exact hvar x hs.1
  | con d' c' ps' as rs'' _ ihas =>
    refine ⟨fun hs hcl hne => ?_, fun _ _ hs => by simp [Ctor.simpleArgs] at hs⟩
    simp only [Ctor.simpleB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
    obtain ⟨⟨⟨rfl, hc'⟩, -⟩, hrest⟩ := hs
    cases hC' : E.ctors[c']? with
    | none => rw [hC'] at hrest; simp at hrest
    | some C' =>
    rw [hC'] at hrest
    simp only [Bool.and_eq_true, beq_iff_eq] at hrest
    obtain ⟨⟨hlen', -⟩, hsa⟩ := hrest
    simp only [Tm.closedB, Bool.and_eq_true, List.all_eq_true] at hcl
    obtain ⟨⟨-, hcla⟩, hclr⟩ := hcl
    rw [sem_con hd] at hne ⊢
    split at hne
    swap; · exact absurd rfl hne
    rename_i hg
    rw [if_pos hg]
    obtain ⟨C'', hC'', -, -, -, hat⟩ := hg
    rw [hC'] at hC''; cases hC''
    have hlit := simpleArgs_ofList hsa
    have hsas : sem S as n (ρ.restr (Hom.id n)) (TEnv.restr γ (Hom.id n)) = vlist (as.toList.map fun t => sem S t n ρ γ) := by
      rw [IEnv.restr_id, TEnv.restr_id_of_kv hγ, hlit, sem_ofList_vlist, toList_ofList]
    have hplv : plist (sem S as n (ρ.restr (Hom.id n)) (TEnv.restr γ (Hom.id n))) (E.ctors.getD c' default).args.length =
        as.toList.map fun t => sem S t n ρ γ := by
      rw [hsas, getD_ctors hC', ← hlen', show as.toList.length = (as.toList.map fun t => sem S t n ρ γ).length by simp,
        plist_vlist]
    have hatv := hat
    simp only [psRV, IEnv.restr_id, TEnv.restr_id_of_kv hγ] at hatv
    have hsas' : sem S as n ρ γ = vlist (as.toList.map fun t => sem S t n ρ γ) := by
      rw [hlit, sem_ofList_vlist, toList_ofList]
    rw [hsas', show C'.args.length = (as.toList.map fun t => sem S t n ρ γ).length by simp [← hlen'], plist_vlist] at hatv
    have hrs3 : rs''.map (ival ρ) = rs''.map (ival (renv rs)) :=
      List.map_congr_left fun r hr => ival_congr_scoped ((I.scopedB_iff _ _).1 (hclr r hr)) fun i hi => hρ i hi
    rw [hplv, hrs3]
    simp only [evalBnd, conBefore, dif_pos hc', evalBndList_eq]
    congr 1
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map]
    have hi : i < as.toList.length := by simpa using h1
    obtain ⟨hr, hp⟩ := ihas.2 C' 0 hsa hcla i hi
    cases hri : C'.isRec i
    · exact hp (by simpa using hri)
    · have hd' := hatv.2.1 i _ (List.getElem?_eq_getElem (by simpa using hi)) hri
      simp only [List.getElem_map] at hd'
      exact hr (by simpa using hri) (fun h => not_isKV_empty (h ▸ hd'.kv))
  | tcons a as iha ihas =>
    refine ⟨fun hs => by simp [Ctor.simpleB] at hs, fun C' k hs hcl i hi => ?_⟩
    simp only [Ctor.simpleArgs, Bool.and_eq_true] at hs
    obtain ⟨hs1, hs2⟩ := hs
    simp only [Tm.closedB, Bool.and_eq_true] at hcl
    cases i with
    | zero =>
      simp only [Tm.toList, List.getElem_cons_zero, Nat.add_zero]
      refine ⟨fun hr hne => ?_, fun hr => ?_⟩
      · rw [if_pos hr] at hs1; exact iha.1 hs1 hcl.1 hne
      · rw [if_neg (by simp [hr])] at hs1
        cases a with
        | var x =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hs1
          exact hvar x hs1.1
        | _ => simp at hs1
    | succ i =>
      simp only [Tm.toList, List.getElem_cons_succ]
      have := ihas.2 C' (k + 1) hs2 hcl.2 i (by simp [Tm.toList] at hi; omega)
      rw [show k + 1 + i = k + (i + 1) by omega] at this
      exact this
  | tnil => exact ⟨fun hs => by simp [Ctor.simpleB] at hs, fun _ _ _ _ i hi => by simp [Tm.toList] at hi⟩
  | _ => exact ⟨fun hs => by simp [Ctor.simpleB] at hs, fun _ _ hs => by simp [Ctor.simpleArgs] at hs⟩


/-- Boundary trees at corresponding arguments are corresponding (given this for the constructor
values of the earlier constructors). -/
theorem ovl_tree {ΘX : SData m} (hbX : ΘX.Basic) {ΘT : SData n} {g : Hom n m}
    {gen act : ℕ → V} {P : ℕ → Prop} {k0 : ℕ} {C0 : Ctor} (hC0 : ΘX.ctors[k0]? = some C0)
    (hct : ∀ k < k0, ΘT.ctors.getD k default = ΘX.ctors.getD k default)
    (hctO : ∀ k < k0, ΘT.ctors[k]? = ΘX.ctors[k]?)
    (hty : ∀ k < k0, ∀ j pre, ΘT.ty k j n (Hom.id n) pre = ΘX.ty k j n g pre)
    (hQ : ∀ k < k0, ∀ C', ΘX.ctors[k]? = some C' → ∀ (vT vX : List V) (rs : List (DM n)),
      ΘX.ArgsTyped k C' n g vX → ΘT.ArgsTyped k C' n (Hom.id n) vT → vT.length = vX.length →
      (∀ j (hj : j < vT.length) (hj' : j < vX.length), C'.isRec j = true → Corr ΘX.ctors n gen act P vT[j] vX[j]) →
      (∀ j (hj : j < vT.length) (hj' : j < vX.length), C'.isRec j = false → vT[j] = vX[j]) →
      rs.length = C'.dims → Corr ΘX.ctors n gen act P (conV ΘX.ctors n k vT rs) (conV ΘX.ctors n k vX rs))
    {aT aX : List V} (hatX : ΘX.ArgsTyped k0 C0 n g aX) (hlT : aT.length = C0.args.length)
    (hrecT : ∀ j (hj : j < aT.length) (hj' : j < aX.length), C0.isRec j = true →
      Corr ΘX.ctors n gen act P aT[j] aX[j] ∧ DElem ΘT n (Hom.id n) aT[j])
    (hptT : ∀ j (hj : j < aT.length) (hj' : j < aX.length), C0.isRec j = false → aT[j] = aX[j])
    (hkvT : ∀ a ∈ aT, IsKV n a) (rs : List (DM n)) : ∀ t : Tm,
    (BTy ΘX k0 C0 t → Corr ΘX.ctors n gen act P (evalBnd (conBefore ΘX.ctors k0 n) aT rs t)
        (evalBnd (conBefore ΘX.ctors k0 n) aX rs t) ∧
      DElem ΘT n (Hom.id n) (evalBnd (conBefore ΘX.ctors k0 n) aT rs t)) ∧
    (∀ C' k' j prev, BTyArgs ΘX k0 C0 C' k' j prev t → ∀ i (hi : i < t.toList.length),
      (C'.isRec (j + i) = true → Corr ΘX.ctors n gen act P (evalBnd (conBefore ΘX.ctors k0 n) aT rs t.toList[i])
          (evalBnd (conBefore ΘX.ctors k0 n) aX rs t.toList[i]) ∧
        DElem ΘT n (Hom.id n) (evalBnd (conBefore ΘX.ctors k0 n) aT rs t.toList[i])) ∧
      (C'.isRec (j + i) = false → evalBnd (conBefore ΘX.ctors k0 n) aT rs t.toList[i] =
        evalBnd (conBefore ΘX.ctors k0 n) aX rs t.toList[i])) := by
  have hlX : aX.length = C0.args.length := hatX.1
  have hPVX : ΘX.PtValid k0 n g aX := by
    have := SData.ptValid_take hC0 hatX.2.2 aX.length; rwa [List.take_length] at this
  have hkvX : ∀ a ∈ aX, IsKV n a := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    cases hr : C0.isRec j
    · exact hbX.pt_kv hPVX hj (by rw [getD_ctors hC0]; exact hr)
    · exact (hatX.2.1 j _ (List.getElem?_eq_getElem hj) hr).kv
  have hvar : ∀ x (hx : x < C0.args.length), evalBnd (conBefore ΘX.ctors k0 n) aT rs (.var x) = aT[C0.args.length - 1 - x]'(by omega) ∧
      evalBnd (conBefore ΘX.ctors k0 n) aX rs (.var x) = aX[C0.args.length - 1 - x]'(by omega) := by
    intro x hx
    simp only [evalBnd]
    rw [getD_reverse_eq (by omega), getD_reverse_eq (by omega), res_id (hkvT _ (List.getElem_mem _)),
      res_id (hkvX _ (List.getElem_mem _))]
    constructor <;> congr 1 <;> omega
  intro t
  induction t with
  | var x =>
    refine ⟨fun hb => ?_, fun _ _ _ _ _ i hi => by simp [Tm.toList] at hi⟩
    obtain ⟨hx, hr⟩ := hb
    rw [(hvar x hx).1, (hvar x hx).2]
    exact hrecT _ (by omega) (by omega) hr
  | con d' c' ps' as rs'' _ ihas =>
    refine ⟨fun hb => ?_, fun _ _ _ _ _ i hi => by simp [Tm.toList] at hi⟩
    obtain ⟨hc', C', hC', hlen', hrs', hargs⟩ := hb
    have houtX := (bnd_delem_aux hbX hC0 hatX.1 hatX.2.1 hatX.2.2 rs as).2 C' c' 0 [] hargs
    have htaX := nested_argsTyped hbX hC0 hatX.1 hatX.2.1 hatX.2.2 rs hC' hlen' houtX
    have hIH := ihas.2 C' c' 0 [] hargs
    simp only [evalBnd, conBefore, dif_pos hc', evalBndList_eq]
    set vT := as.toList.map (evalBnd (fun c'' as' rs' => if _ : c'' < k0 then conV ΘX.ctors n c'' as' rs' else junkV n) aT rs)
    set vX := as.toList.map (evalBnd (fun c'' as' rs' => if _ : c'' < k0 then conV ΘX.ctors n c'' as' rs' else junkV n) aX rs)
    have hrecv : ∀ j (hj : j < vT.length) (hj' : j < vX.length), C'.isRec j = true →
        Corr ΘX.ctors n gen act P vT[j] vX[j] ∧ DElem ΘT n (Hom.id n) vT[j] := by
      intro j hj hj' hr
      simp only [vT, vX, List.getElem_map]
      exact (hIH j (by simpa [vT] using hj)).1 (by simpa using hr)
    have hptv : ∀ j (hj : j < vT.length) (hj' : j < vX.length), C'.isRec j = false → vT[j] = vX[j] := by
      intro j hj hj' hr
      simp only [vT, vX, List.getElem_map]
      exact (hIH j (by simpa [vT] using hj)).2 (by simpa using hr)
    have hC'T : ΘT.ctors[c']? = some C' := by rw [hctO c' hc']; exact hC'
    have htaT : ΘT.ArgsTyped c' C' n (Hom.id n) vT := by
      refine ⟨by simp [vT, hlen'], fun j a ha hr => ?_, fun j a ha hr => ?_⟩
      · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 ha
        exact (hrecv j hj (by simpa [vX, vT] using hj) hr).2
      · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 ha
        have hjX : j < vX.length := by simpa [vX, vT] using hj
        rw [hptv j hj hjX hr, hty c' hc']
        have hmem := htaX.2.2 j _ (List.getElem?_eq_getElem hjX) hr
        have heq : ΘX.ty c' j n g (vT.take j) = ΘX.ty c' j n g (vX.take j) := by
          apply hbX.recIrr
          · simp [vT, vX]
          · intro i hi hi' hri
            simp only [List.getElem_take]
            exact hptv i (by simp at hi; omega) (by simp at hi'; omega) (by rw [getD_ctors hC'] at hri; exact hri)
        rw [heq]; exact hmem
    have hrsv : (rs''.map (ival (renv rs))).length = C'.dims := by simp [hrs']
    refine ⟨hQ c' hc' C' hC' vT vX _ htaX htaT (by simp [vT, vX]) (fun j hj hj' hr => (hrecv j hj hj' hr).1) hptv hrsv, ?_⟩
    have hd := DElem.con hC'T htaT.1 hrsv htaT.2.1 htaT.2.2 (rs := rs''.map (ival (renv rs)))
    rwa [conV_congr_ctors n c' fun k'' hk'' => hct k'' (by omega)] at hd
  | tcons a as iha ihas =>
    refine ⟨fun hb => by simp [BTy] at hb, fun C' k' j prev hb i hi => ?_⟩
    obtain ⟨hb1, hb2, hb3⟩ := hb
    cases i with
    | zero =>
      simp only [Tm.toList, List.getElem_cons_zero, Nat.add_zero]
      refine ⟨fun hr => iha.1 (hb1 hr), fun hr => ?_⟩
      obtain ⟨x, rfl, hx, hxr, -⟩ := hb2 hr
      rw [(hvar x hx).1, (hvar x hx).2]
      exact hptT _ (by omega) (by omega) hxr
    | succ i =>
      simp only [Tm.toList, List.getElem_cons_succ]
      have := ihas.2 C' k' (j + 1) (a :: prev) hb3 i (by simp [Tm.toList] at hi; omega)
      rw [show j + 1 + i = j + (i + 1) by omega] at this
      exact this
  | _ => exact ⟨fun hb => by simp [BTy] at hb, fun _ _ _ _ _ i hi => by simp [Tm.toList] at hi⟩

section assembly

variable (S0 : Sig) (hS0 : SigOK S0) (D : DataDecl) (hWf : D.Wf S0 S0.length)
  (X : List Ctor) (B : ℕ) (hB : B ≤ D.ctors.length) (hXB : ∀ c' < B, X[c']? = D.ctors[c']?)
  (hXr : ∀ c', B ≤ c' → ∀ C', X[c']? = some C' → C' = genCtor)
  (hokB : ∀ c' < B, SigOK (S0 ++ [.data (D.truncate c')]))

theorem simpleB_congr {ctors1 ctors2 : List Ctor} {d np c n : ℕ} {C : Ctor}
    (h : ∀ c' < c, ctors1[c']? = ctors2[c']?) : ∀ t : Tm,
    Ctor.simpleB ctors1 d np c n C t = Ctor.simpleB ctors2 d np c n C t ∧
      ∀ C' k, Ctor.simpleArgs ctors1 d np c n C C' k t = Ctor.simpleArgs ctors2 d np c n C C' k t := by
  intro t
  induction t with
  | con d' c' ps as rs _ ihas =>
    refine ⟨?_, fun C' k => by simp [Ctor.simpleArgs]⟩
    simp only [Ctor.simpleB]
    by_cases hc : c' < c
    · rw [h c' hc]
      cases ctors2[c']? with
      | none => rfl
      | some C' => simp only [(ihas.2 C' 0)]
    · simp [hc]
  | tcons a as iha ihas =>
    refine ⟨by simp [Ctor.simpleB], fun C' k => ?_⟩
    simp only [Ctor.simpleArgs, iha.1, ihas.2]
  | _ => exact ⟨by simp [Ctor.simpleB], fun _ _ => by simp [Ctor.simpleArgs]⟩

include hS0 hWf hXB hXr in
theorem dataSyn_X (hok0 : 0 < B → SigOK (S0 ++ [.data (D.truncate 0)])) :
    DataSyn S0.length { D with ctors := X } := by
  refine ⟨hWf.1, fun j A hA => ⟨(hWf.2.1 j A hA).1, ?_⟩, fun c C hC k A hA => ?_, fun c C hC ψ b hb => ?_⟩
  · obtain ⟨l, hl⟩ := (hWf.2.1 j A hA).2.2
    exact (sound_ty hS0 hl).2.1
  rotate_left
  · by_cases hcB : c < B
    · rw [show ({ D with ctors := X } : DataDecl).ctors = X from rfl, hXB c hcB] at hC
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hb
      obtain ⟨h1, h2, h3, -, -⟩ := (hWf.2.2 c C hC).2.1 k ψ b hk
      refine ⟨h1, h2, ?_⟩
      rw [show ({ D with ctors := X } : DataDecl).ctors = X from rfl,
        (simpleB_congr (fun c' hc' => hXB c' (by omega)) b).1]
      exact h3
    · have := hXr c (by omega) C hC
      subst this; simp at hb
  · by_cases hcB : c < B
    · rw [show ({ D with ctors := X } : DataDecl).ctors = X from rfl, hXB c hcB] at hC
      obtain ⟨h1, h2, h3, h4⟩ := (hWf.2.2 c C hC).1 k A hA
      refine ⟨h1, ?_, h2, h3⟩
      have := (sound_ty (hok0 (by omega)) h4).2.1
      simpa using this
    · have := hXr c (by omega) C hC
      subst this; simp at hA

include hWf hXB in
theorem hck_X : ∀ (c : ℕ) (C : Ctor), ({ D with ctors := X } : DataDecl).ctors[c]? = some C → c < B →
    ∀ (k : ℕ) (A : Tm), C.args[k]? = some (.point A) →
    HasTy (S0 ++ [.data (({ D with ctors := X } : DataDecl).truncate 0)]) 0 .one
      (({ D with ctors := X } : DataDecl).argCtx S0.length C k) A (.univ D.level) := by
  intro c C hC hcB k A hA
  rw [show ({ D with ctors := X } : DataDecl).ctors = X from rfl, hXB c hcB] at hC
  exact ((hWf.2.2 c C hC).1 k A hA).2.2.2

include hS0 hWf hXB hXr in
theorem argTysOK_X (hok0 : 0 < B → SigOK (S0 ++ [.data (D.truncate 0)])) :
    ArgTysOK S0 { D with ctors := X } := by
  intro c C hC j A hA m ps hps n g pre hjp hpre
  by_cases hcB : c < B
  · exact argTy_univ S0 { D with ctors := X } (dataSyn_X S0 hS0 D hWf X B hXB hXr hok0) hC hps (hok0 (by omega))
      (fun k A' hA' => hck_X S0 D hWf X B hXB c C hC hcB k A' hA')
      j A hA n g pre hjp hpre
  · have := hXr c (by omega) C hC
    subst this; simp at hA

include hS0 hWf hXB hXr hokB hB in
theorem bnd_X (hok0 : 0 < B → SigOK (S0 ++ [.data (D.truncate 0)])) (m : ℕ) (ps : RV m)
    (hps : ParamsOK (sigV S0) { D with ctors := X } m ps) :
    ∀ c C, (dataSD (sigV S0) { D with ctors := X } S0.length m ps).ctors[c]? = some C → ∀ ψ b, (ψ, b) ∈ C.bnd →
      ∀ n (rs : List (DM n)), (ival (renv rs) ψ).holds →
        BTy (dataSD (sigV S0) { D with ctors := X } S0.length m ps) c C b := by
  intro c C hC ψ b hb n rs hh
  by_cases hcB : c < B
  · have hCD : D.ctors[c]? = some C := by rw [← hXB c hcB]; exact hC
    have hsynD : DataSyn S0.length D :=
      dataSyn_X S0 hS0 D hWf D.ctors D.ctors.length (fun _ _ => rfl)
        (fun c' h C' hC' => by rw [List.getElem?_eq_none (by omega)] at hC'; cases hC') (fun _ => hok0 (by omega))
    have hckD : ∀ (c : ℕ) (C : Ctor), D.ctors[c]? = some C → ∀ (k : ℕ) (A : Tm), C.args[k]? = some (.point A) →
        HasTy (S0 ++ [.data (D.truncate 0)]) 0 .one (D.argCtx S0.length C k) A (.univ D.level) :=
      fun c C hC k A hA => ((hWf.2.2 c C hC).1 k A hA).2.2.2
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hb
    obtain ⟨-, -, hsimple, -, hbt⟩ := (hWf.2.2 c C hCD).2.1 k ψ b hk
    exact ((bty_of_wf S0 D hsynD hCD hps (hok0 (by omega)) hckD hS0
      (by have := (List.getElem?_eq_some_iff.1 hCD).1; omega) hh (E := { D with ctors := X }) rfl
      (fun c' hc' => hXB c' (by omega)) b).1 hsimple hbt).2
  · have := hXr c (by omega) C hC
    subst this; simp at hb

include hS0 hWf hXB hXr hokB hB in
theorem ovl_X (hok0 : 0 < B → SigOK (S0 ++ [.data (D.truncate 0)])) (m : ℕ) (ps : RV m)
    (hps : ParamsOK (sigV S0) { D with ctors := X } m ps) :
    ∀ c C, (dataSD (sigV S0) { D with ctors := X } S0.length m ps).ctors[c]? = some C → ∀ ψ b ψ' b',
      (ψ, b) ∈ C.bnd → (ψ', b') ∈ C.bnd → ∀ n (g : Hom n m) args (rs : List (DM n)),
        (dataSD (sigV S0) { D with ctors := X } S0.length m ps).ArgsTyped c C n g args → rs.length = C.dims →
        (ival (renv rs) ψ).holds → (ival (renv rs) ψ').holds →
        evalBnd (conBefore (dataSD (sigV S0) { D with ctors := X } S0.length m ps).ctors c n) args rs b =
          evalBnd (conBefore (dataSD (sigV S0) { D with ctors := X } S0.length m ps).ctors c n) args rs b' := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c IH =>
  intro C hC ψ b ψ' b' hmem hmem' n g args rs hat hrs hψ hψ'
  by_cases hcB : c < B
  swap
  · have := hXr c (by omega) C hC
    subst this; simp at hmem
  set E : DataDecl := { D with ctors := X } with hE
  have hsynX := dataSyn_X S0 hS0 D hWf X B hXB hXr hok0
  have hUX := argTysOK_X S0 hS0 D hWf X B hXB hXr hok0
  have hbX := dataSD_basic S0 E hsynX hUX hps
  have hrcX := dataSD_resClosed S0 E hsynX hUX hps
  have hCD : D.ctors[c]? = some C := by rw [← hXB c hcB]; exact hC
  have hcD : c < D.ctors.length := (List.getElem?_eq_some_iff.1 hCD).1
  -- the truncated declaration
  have hokc := hokB c hcB
  have hdT : DataOK (S0 ++ [.data (D.truncate c)]) S0.length (D.truncate c) := hokc.2 S0.length _ (entry_ext S0 _)
  have hpT : ParamsOK (sigV S0) (D.truncate c) n (fun k f => ps k (g.comp f)) := hps.restr g
  have hgT : (dataSD (sigV S0) (D.truncate c) S0.length n (fun k f => ps k (g.comp f))).Good := by
    have := (hdT.2 n _ (by rw [sigUpTo_ext]; exact hpT)).1; rwa [sigUpTo_ext] at this
  have hctO : ∀ k < c, (dataSD (sigV S0) (D.truncate c) S0.length n (fun k f => ps k (g.comp f))).ctors[k]? =
      (dataSD (sigV S0) E S0.length m ps).ctors[k]? := by
    intro k hk
    show (D.ctors.take c ++ [genCtor])[k]? = X[k]?
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hk, hXB k (by omega)]
  have hct : ∀ k < c, (dataSD (sigV S0) (D.truncate c) S0.length n (fun k f => ps k (g.comp f))).ctors.getD k default =
      (dataSD (sigV S0) E S0.length m ps).ctors.getD k default := by
    intro k hk; rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hctO k hk]
  have hty : ∀ k < c, ∀ j pre, (dataSD (sigV S0) (D.truncate c) S0.length n (fun k f => ps k (g.comp f))).ty k j n
      (Hom.id n) pre = (dataSD (sigV S0) E S0.length m ps).ty k j n g pre := by
    intro k hk j pre
    show argTySem (sigV S0) (D.truncate c) S0.length k j n (ps n (g.comp (Hom.id n))) pre =
      argTySem (sigV S0) E S0.length k j n (ps n g) pre
    rw [argTySem_congr (E := D.truncate c) (D := E) rfl (hct k hk), Hom.comp_id]
  -- generic atoms
  have ha0 : DElem (dataSD (sigV S0) (D.truncate c) S0.length n (fun k f => ps k (g.comp f))) n (Hom.id n)
      (genV c n (D.truncate c).ctors) := mem_El_dataC.1 (genV_mem hcD.le)
  have hb0 : bndAtMap ((D.truncate c).ctors.getD c default) ([] : List (DM n)) (Hom.id n) = none := by
    rw [getD_ctors (truncate_gen D hcD.le)]; rfl
  have ha0ne : ∀ (ψ0 : Cof n) u a, ¬ ψ0.holds → genV c n (D.truncate c).ctors ≠ hcV n ψ0 u a :=
    fun ψ0 u a hn => conV_ne_hcV hb0 hn
  set gf : ℕ → V := fun i => atomV n (genV c n (D.truncate c).ctors) (i + 1) with hgf
  set P : ℕ → Prop := fun i => i < C.args.length ∧ C.isRec i = true with hP
  set act : ℕ → V := fun i => args.getD i ∅ with hact
  have hinj : ∀ i j, P i → P j → gf i = gf j → i = j := fun i j _ _ h => by
    have := atomV_inj ha0.kv ha0ne (i + 1) (j + 1) h; omega
  have hne : ∀ i, P i → ∀ k vs (rs' : List (DM n)),
      bndAtMap ((dataSD (sigV S0) E S0.length m ps).ctors.getD k default) rs' (Hom.id n) = none →
      gf i ≠ conV (dataSD (sigV S0) E S0.length m ps).ctors n k vs rs' :=
    fun i _ k vs rs' hb h => conV_ne_hcV hb (not_bot_holds n) h.symm
  -- the corresponding constructor values
  have hQ : ∀ k < c, ∀ C', (dataSD (sigV S0) E S0.length m ps).ctors[k]? = some C' → ∀ (vT vX : List V)
      (rs' : List (DM n)), (dataSD (sigV S0) E S0.length m ps).ArgsTyped k C' n g vX →
      (dataSD (sigV S0) (D.truncate c) S0.length n (fun k f => ps k (g.comp f))).ArgsTyped k C' n (Hom.id n) vT →
      vT.length = vX.length →
      (∀ j (hj : j < vT.length) (hj' : j < vX.length), C'.isRec j = true →
        Corr (dataSD (sigV S0) E S0.length m ps).ctors n gf act P vT[j] vX[j]) →
      (∀ j (hj : j < vT.length) (hj' : j < vX.length), C'.isRec j = false → vT[j] = vX[j]) →
      rs'.length = C'.dims →
      Corr (dataSD (sigV S0) E S0.length m ps).ctors n gf act P
        (conV (dataSD (sigV S0) E S0.length m ps).ctors n k vT rs')
        (conV (dataSD (sigV S0) E S0.length m ps).ctors n k vX rs') := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k IHk =>
    intro hk C' hC' vT vX rs' hX hT hl hrec hpt hrs'
    have hC'T : (dataSD (sigV S0) (D.truncate c) S0.length n (fun k f => ps k (g.comp f))).ctors[k]? = some C' := by
      rw [hctO k hk]; exact hC'
    have hPVX : (dataSD (sigV S0) E S0.length m ps).PtValid k n g vX := by
      have := SData.ptValid_take hC' hX.2.2 vX.length; rwa [List.take_length] at this
    have hPVT : (dataSD (sigV S0) (D.truncate c) S0.length n (fun k f => ps k (g.comp f))).PtValid k n (Hom.id n) vT := by
      have := SData.ptValid_take hC'T hT.2.2 vT.length; rwa [List.take_length] at this
    have hkvX : ∀ a ∈ vX, IsKV n a := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      cases hr : C'.isRec j
      · exact hbX.pt_kv hPVX hj (by rw [getD_ctors hC']; exact hr)
      · exact (hX.2.1 j _ (List.getElem?_eq_getElem hj) hr).kv
    have hkvT : ∀ a ∈ vT, IsKV n a := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      cases hr : C'.isRec j
      · exact hgT.pt_kv hPVT hj (by rw [getD_ctors hC'T]; exact hr)
      · exact (hT.2.1 j _ (List.getElem?_eq_getElem hj) hr).kv
    cases hb : bndAtMap C' rs' (Hom.id n) with
    | none =>
      exact Corr.con (by rw [getD_ctors hC']; exact hb) hkvT hkvX hl
        (fun j hj hj' hr => hrec j hj hj' (by rwa [getD_ctors hC'] at hr))
        (fun j hj hj' hr => hpt j hj hj' (by rwa [getD_ctors hC'] at hr))
    | some cl =>
      obtain ⟨ψk, bk⟩ := cl
      obtain ⟨hmemk, hhk⟩ := bndAtMap_some hb
      have hXv := conV_eq_bnd_of hrcX hC' (IH k (by omega) C' hC') hX hrs' hb
      have hTv := conV_eq_bnd hgT hC'T hT hrs' hb
      have hcongr : (dataSD (sigV S0) (D.truncate c) S0.length n (fun k f => ps k (g.comp f))).ctors = (D.truncate c).ctors := rfl
      rw [conV_congr_ctors n k fun k'' hk'' => hct k'' (by omega),
        conBefore_congr_ctors (fun k'' hk'' => hct k'' (by omega))] at hTv
      rw [hTv, hXv]
      have hbty := bnd_X S0 hS0 D hWf X B hB hXB hXr hokB hok0 m ps hps k C' hC' ψk bk hmemk n rs' (by simpa using hhk)
      exact ((ovl_tree hbX hC' (fun k'' hk'' => hct k'' (by omega)) (fun k'' hk'' => hctO k'' (by omega))
        (fun k'' hk'' => hty k'' (by omega)) (fun k'' hk'' => IHk k'' hk'' (by omega)) hX (by rw [hl]; exact hX.1)
        (fun j hj hj' hr => ⟨hrec j hj hj' hr, hT.2.1 j _ (List.getElem?_eq_getElem hj) hr⟩) hpt hkvT rs' bk).1 hbty).1
  -- the generic arguments
  have hlA : args.length = C.args.length := hat.1
  have hPVA : (dataSD (sigV S0) E S0.length m ps).PtValid c n g args := by
    have := SData.ptValid_take hC hat.2.2 args.length; rwa [List.take_length] at this
  have hkvA : ∀ a ∈ args, IsKV n a := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    cases hr : C.isRec j
    · exact hbX.pt_kv hPVA hj (by rw [getD_ctors hC]; exact hr)
    · exact (hat.2.1 j _ (List.getElem?_eq_getElem hj) hr).kv
  set aT := genPre C gf args with haT
  have hlT : aT.length = C.args.length := by simp [aT, genPre_length, hlA]
  have hrecT : ∀ j (hj : j < aT.length) (hj' : j < args.length), C.isRec j = true →
      Corr (dataSD (sigV S0) E S0.length m ps).ctors n gf act P aT[j] args[j] ∧
        DElem (dataSD (sigV S0) (D.truncate c) S0.length n (fun k f => ps k (g.comp f))) n (Hom.id n) aT[j] := by
    intro j hj hj' hr
    simp only [aT, genPre_getElem, hr, if_true]
    refine ⟨?_, atomV_DElem ha0 (j + 1)⟩
    have := Corr.atom (ctors := (dataSD (sigV S0) E S0.length m ps).ctors) (n := n) (gen := gf) (act := act)
      (P := P) (i := j) ⟨by omega, hr⟩
    simpa [act, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] using this
  have hptT : ∀ j (hj : j < aT.length) (hj' : j < args.length), C.isRec j = false → aT[j] = args[j] := by
    intro j hj hj' hr
    simp [aT, genPre_getElem, hr]
  have hkvT : ∀ a ∈ aT, IsKV n a := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    cases hr : C.isRec j
    · rw [hptT j hj (by omega) hr]; exact hkvA _ (List.getElem_mem _)
    · exact (hrecT j hj (by omega) hr).2.kv
  have htop : ∀ bb, BTy (dataSD (sigV S0) E S0.length m ps) c C bb →
      Corr (dataSD (sigV S0) E S0.length m ps).ctors n gf act P
        (evalBnd (conBefore (dataSD (sigV S0) E S0.length m ps).ctors c n) aT rs bb)
        (evalBnd (conBefore (dataSD (sigV S0) E S0.length m ps).ctors c n) args rs bb) :=
    fun bb hbb => ((ovl_tree hbX hC hct hctO hty hQ hat hlT hrecT hptT hkvT rs bb).1 hbb).1
  -- the judgmental overlap, at the generic arguments
  obtain ⟨k1, hk1⟩ := List.getElem?_of_mem hmem
  obtain ⟨k2, hk2⟩ := List.getElem?_of_mem hmem'
  obtain ⟨-, hcl1, hs1, hhas1, -⟩ := (hWf.2.2 c C hCD).2.1 k1 ψ b hk1
  obtain ⟨-, hcl2, hs2, hhas2, -⟩ := (hWf.2.2 c C hCD).2.1 k2 ψ' b' hk2
  have heq := (hWf.2.2 c C hCD).2.2 k1 k2 ψ ψ' b b' hk1 hk2
  have hsynD : DataSyn S0.length D :=
    dataSyn_X S0 hS0 D hWf D.ctors D.ctors.length (fun _ _ => rfl)
      (fun c' h C' hC' => by rw [List.getElem?_eq_none (by omega)] at hC'; cases hC') (fun _ => hok0 (by omega))
  have hCE : E.ctors[c]? = some C := hC
  have hgetC : E.ctors.getD c default = D.ctors.getD c default := by
    rw [getD_ctors hCE, getD_ctors hCD]
  have hptD : ∀ i (hi : i < C.args.length), C.isRec i = false →
      args[i]'(by omega) ∈ El (argTyRaw (sigV S0) D S0.length c i n (ps n g) args) (Hom.id n) ∧
        IsKV n (args[i]'(by omega)) := by
    intro i hi hr
    refine ⟨?_, hkvA _ (List.getElem_mem _)⟩
    have hm := hat.2.2 i _ (List.getElem?_eq_getElem (by omega)) hr
    change _ ∈ El (argTySem (sigV S0) E S0.length c i n (ps n g) (args.take i)) _ at hm
    rw [argTySem_eq, if_pos ⟨by rw [getD_ctors hCE]; omega, by rw [getD_ctors hCE]; exact hr,
      ptValid_argPreValid (hPVA.take i) (j := i) (by simp; omega)⟩] at hm
    have e : argTyRaw (sigV S0) E S0.length c i n (ps n g) (args.take i) =
        argTyRaw (sigV S0) D S0.length c i n (ps n g) args := by
      simp only [argTyRaw, hgetC, List.take_take, Nat.min_self]; rfl
    rwa [e] at hm
  have hgfm : ∀ i, C.isRec i = true →
      gf i ∈ El (dataC (dataSD (sigV S0) (D.truncate c) S0.length n fun k f => ps k (g.comp f))) (Hom.id n) :=
    fun i _ => mem_El_dataC.2 (atomV_DElem ha0 (i + 1))
  have htk : genPre C gf (args.take C.args.length) = aT := by rw [List.take_of_length_le (by omega)]
  have hp1 := isPoint_argCtx S0 D hsynD hCD hps c g (renv rs) hψ gf hgfm (j := C.args.length) (pre := args)
    (by omega) le_rfl hptD
  have hp2 := isPoint_argCtx S0 D hsynD hCD hps c g (renv rs) hψ' gf hgfm (j := C.args.length) (pre := args)
    (by omega) le_rfl hptD
  have hp12 := isPoint_argCtx S0 D hsynD hCD hps c g (renv rs) (Φ := .and ψ ψ') (holds_and.2 ⟨hψ, hψ'⟩) gf hgfm
    (j := C.args.length) (pre := args) (by omega) le_rfl hptD
  rw [htk] at hp1 hp2 hp12
  have hargs : ∀ x (hx : x < C.args.length),
      argEnvKV n (plist (ps n g) D.params.length) aT x = aT.reverse[x]'(by simp; omega) := by
    intro x hx
    rw [argEnvKV_eq_of_lt (by simp [plist]; omega), List.getElem_append_left (by simp; omega)]
  have hsimp : ∀ bb, Ctor.simpleB D.ctors S0.length D.params.length c C.args.length C bb = true →
      Ctor.simpleB (D.truncate c).ctors S0.length (D.truncate c).params.length c C.args.length C bb = true := by
    intro bb h
    rw [← (simpleB_congr (fun c' hc' => ?_) bb).1]; exact h
    show D.ctors[c']? = (D.ctors.take c ++ [genCtor])[c']?
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hc']
  have hev := fun bb => (sem_simple_eval (S := S0 ++ [.data (D.truncate c)]) (entry_ext S0 _) (c := c) (C := C) hp12.kv aT hlT
    hargs rs (fun i _ => rfl) bb).1
  have hne1 : sem (S0 ++ [.data (D.truncate c)]) b n (renv rs) (argEnvKV n (plist (ps n g) D.params.length) aT) ≠ ∅ := by
    obtain ⟨hm, -, hty1, -⟩ := (sound_ty hokc hhas1).2.2.2 n _ _ hp1
    exact hty1.ne_empty hm
  have hne2 : sem (S0 ++ [.data (D.truncate c)]) b' n (renv rs) (argEnvKV n (plist (ps n g) D.params.length) aT) ≠ ∅ := by
    obtain ⟨hm, -, hty1, -⟩ := (sound_ty hokc hhas2).2.2.2 n _ _ hp2
    exact hty1.ne_empty hm
  have hE := (sound_eq hokc heq).2.2 n _ _ hp12
  rw [hev b (hsimp b hs1) hcl1 hne1, hev b' (hsimp b' hs2) hcl2 hne2] at hE
  rw [conBefore_congr_ctors (ctors1 := (D.truncate c).ctors) (ctors2 := (dataSD (sigV S0) E S0.length m ps).ctors)
    (fun k hk => hct k hk)] at hE
  have h1 := htop b (bnd_X S0 hS0 D hWf X B hB hXB hXr hokB hok0 m ps hps c C hC ψ b hmem n rs hψ)
  have h2 := htop b' (bnd_X S0 hS0 D hWf X B hB hXB hXr hokB hok0 m ps hps c C hC ψ' b' hmem' n rs hψ')
  rw [← hE] at h2
  exact Corr.unique hinj hne h1 h2

include hS0 hWf hXB hXr hokB hB in
theorem dataOK_X (hok0 : 0 < B → SigOK (S0 ++ [.data (D.truncate 0)])) :
    DataOK (S0 ++ [.data { D with ctors := X }]) S0.length { D with ctors := X } :=
  dataOK_of S0 _ (dataSyn_X S0 hS0 D hWf X B hXB hXr hok0) (argTysOK_X S0 hS0 D hWf X B hXB hXr hok0)
    fun m ps hps => ⟨bnd_X S0 hS0 D hWf X B hB hXB hXr hokB hok0 m ps hps,
      ovl_X S0 hS0 D hWf X B hB hXB hXr hokB hok0 m ps hps⟩

end assembly

theorem sigOK_trunc (S0 : Sig) (hS0 : SigOK S0) (D : DataDecl) (hWf : D.Wf S0 S0.length) :
    ∀ c ≤ D.ctors.length, SigOK (S0 ++ [.data (D.truncate c)]) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc
    have hX : D.truncate c = { D with ctors := D.ctors.take c ++ [genCtor] } := rfl
    rw [hX]
    refine sigOK_ext hS0 (dataOK_X S0 hS0 D hWf _ c hc (fun c' hc' => ?_) (fun c' hc' C' hC' => ?_)
      (fun c' hc' => ih c' hc' (by omega)) (fun h0 => ih 0 h0 (by omega)))
    · simp [List.getElem?_append_left (by simp; omega : c' < (D.ctors.take c).length), hc']
    · rw [List.getElem?_append_right (by simp; omega)] at hC'
      simp only [List.length_take, Nat.min_eq_left hc] at hC'
      rcases Nat.lt_or_ge (c' - c) 1 with h | h
      · rw [show c' - c = 0 by omega] at hC'; simp at hC'; exact hC'.symm
      · rw [List.getElem?_eq_none (by simp; omega)] at hC'; cases hC'

theorem dataOK_decl (S0 : Sig) (hS0 : SigOK S0) (D : DataDecl) (hWf : D.Wf S0 S0.length) :
    DataOK (S0 ++ [.data D]) S0.length D := by
  have := dataOK_X S0 hS0 D hWf D.ctors D.ctors.length le_rfl (fun _ _ => rfl)
    (fun c' hc' C' hC' => by rw [List.getElem?_eq_none (by omega)] at hC'; cases hC')
    (fun c' hc' => sigOK_trunc S0 hS0 D hWf c' hc'.le) (fun _ => sigOK_trunc S0 hS0 D hWf 0 (Nat.zero_le _))
  exact this

end

end Model
