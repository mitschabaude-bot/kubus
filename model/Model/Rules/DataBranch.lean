import Model.Rules.DataLemmas
import Model.Rules.CompLemmas

/-!
# Branches of the eliminator: iterated applications

Peeling the Π- and interval-Π-types of a branch type by applying to arguments.
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

/-- Extend a term environment by a list of values, the first one innermost. -/
def TEnv.consL (γ : ℕ → V) (as : List V) : ℕ → V := as.foldl TEnv.cons γ

/-- Extend an interval environment by a list of points, the first one innermost. -/
def IEnv.consL (ρ : IEnv m) (rs : List (DM m)) : IEnv m := rs.foldl IEnv.cons ρ

theorem TEnv.consL_kv {γ : ℕ → V} (hγ : ∀ x, IsKV m (γ x)) : ∀ {as : List V}, (∀ a ∈ as, IsKV m a) →
    ∀ x, IsKV m (TEnv.consL γ as x)
  | [], _, x => hγ x
  | a :: as, h, x => by
    simp only [TEnv.consL, List.foldl_cons]
    exact TEnv.consL_kv (γ := TEnv.cons γ a) (fun y => by cases y <;> simp [TEnv.cons, hγ, h a List.mem_cons_self])
      (fun b hb => h b (List.mem_cons_of_mem _ hb)) x

theorem TEnv.consL_ge (γ : ℕ → V) : ∀ (as : List V) (x : ℕ), as.length ≤ x → TEnv.consL γ as x = γ (x - as.length)
  | [], x, _ => by simp [TEnv.consL]
  | a :: as, x, hx => by
    simp only [TEnv.consL, List.foldl_cons]
    rw [show List.foldl TEnv.cons (TEnv.cons γ a) as = TEnv.consL (TEnv.cons γ a) as from rfl,
      TEnv.consL_ge _ as x (by simp at hx; omega)]
    simp at hx
    rw [show x - as.length = (x - (as.length + 1)) + 1 by omega]
    rfl

theorem TEnv.consL_lt (γ : ℕ → V) : ∀ (as : List V) (x : ℕ) (hx : x < as.length),
    TEnv.consL γ as x = as.reverse[x]'(by simpa using hx)
  | a :: as, x, hx => by
    simp only [TEnv.consL, List.foldl_cons]
    by_cases h : x < as.length
    · rw [show List.foldl TEnv.cons (TEnv.cons γ a) as = TEnv.consL (TEnv.cons γ a) as from rfl,
        TEnv.consL_lt _ as x h]
      rw [List.getElem_of_eq (List.reverse_cons (a := a) (as := as)), List.getElem_append_left (by simpa using h)]
    · have hx' : x = as.length := by simp at hx; omega
      subst hx'
      rw [show List.foldl TEnv.cons (TEnv.cons γ a) as = TEnv.consL (TEnv.cons γ a) as from rfl,
        TEnv.consL_ge _ as _ le_rfl]
      simp [List.reverse_cons]
/-- Applying a function of a Π-type to arguments of the domains. -/
theorem apps_foldr_pi {ρ : IEnv m} : ∀ (Ts : List Tm) (inner : Tm) (γ : ℕ → V) (f : V) (as : List V),
    (∀ x, IsKV m (γ x)) → TyOK S (Ts.foldr Tm.pi inner) m ρ γ →
    f ∈ El (sem S (Ts.foldr Tm.pi inner) m ρ γ) (Hom.id m) → ∀ (hl : as.length = Ts.length),
    (∀ i (hi : i < as.length), as[i] ∈ El (sem S (Ts[i]'(by omega)) m ρ (TEnv.consL γ (as.take i))) (Hom.id m)) →
    TyOK S inner m ρ (TEnv.consL γ as) ∧ appsV m f as ∈ El (sem S inner m ρ (TEnv.consL γ as)) (Hom.id m)
  | [], inner, γ, f, as, _, hty, hf, hl, _ => by
    cases as with
    | nil => exact ⟨hty, hf⟩
    | cons => simp at hl
  | T :: Ts, inner, γ, f, as, hγ, hty, hf, hl, has => by
    cases as with
    | nil => simp at hl
    | cons a as =>
      simp only [List.foldr_cons] at hty hf
      obtain ⟨hAkv, l, hl', hV, hWF⟩ := hty.pi_at
      rw [sem_pi hAkv] at hV hWF hf
      obtain ⟨-, hfam, -⟩ := WF.pi_inv hAkv (isKV_famV _ _) hWF
      have ha : a ∈ El (sem S T m ρ γ) (Hom.id m) := by simpa using has 0 (by simp)
      have hρ : ρ.restr (Hom.id m) = ρ := IEnv.restr_id ρ
      have hγ' : TEnv.restr γ (Hom.id m) = γ := TEnv.restr_id_of_kv hγ
      have hfa : appV m f a ∈ El (sem S (Ts.foldr Tm.pi inner) m ρ (TEnv.cons γ a)) (Hom.id m) := by
        rw [El_piC, res_id hAkv, res_id (isKV_famV _ _)] at hf
        have := appV_mem_piElSet hf ha
        rwa [apZ_dat_famV _ _ _ ha, hρ, hγ'] at this
      have hty' : TyOK S (Ts.foldr Tm.pi inner) m ρ (TEnv.cons γ a) := by
        have hw := hfam m (Hom.id m) a ha
        rw [apZ_dat_famV _ _ _ ha, hρ, hγ'] at hw
        refine ⟨l, hl', Or.inl ⟨hw, ?_⟩⟩
        have := Vt_below (below_piC_fam _ _ (isKV_famV _ _) a ⟨_, by rw [dat_famV]; exact mem_fnZ.2 ⟨_, ha, rfl⟩⟩) hV
        rwa [apZ_dat_famV _ _ _ ha, hρ, hγ'] at this
      have hakv : IsKV m a := (WF.pi_inv hAkv (isKV_famV _ _) hWF).1.fib.elKV _ _ _ ha
      have := apps_foldr_pi Ts inner (TEnv.cons γ a) (appV m f a) as
        (fun y => by cases y <;> simp [TEnv.cons, hγ, hakv]) hty' hfa (by simpa using hl)
        (fun i hi => by simpa [TEnv.consL] using has (i + 1) (by simp; omega))
      simpa [TEnv.consL, appsV] using this

theorem recPos_lt {C : Ctor} {s : ℕ} (hs : s < C.recPos.length) : C.recPos.getD s 0 < C.args.length := by
  have hm : C.recPos.getD s 0 ∈ C.recPos := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]; exact List.getElem_mem _
  simp only [Ctor.recPos, List.mem_filter, List.mem_range] at hm
  exact hm.1

theorem sem_branchIhTy (C : Ctor) (P : Tm) {s : ℕ} (hs : s < C.recPos.length) (ρ' : IEnv n) (γ' : ℕ → V)
    (args ihs : List V) (hl : args.length = C.args.length) (hsl : ihs.length = s) :
    sem S (DataDecl.branchIhTy C P s) n ρ' (TEnv.consL γ' (args ++ ihs)) =
      sem S P n ρ' (TEnv.cons γ' (args[C.recPos.getD s 0]'(by have := recPos_lt hs; omega))) := by
  have hrp := recPos_lt hs
  unfold DataDecl.branchIhTy
  rw [sem_subst S P n ρ' _ _ _ (fun x => by cases x <;> (intro k f; rfl))]
  congr 1
  funext x
  cases x with
  | zero =>
    simp only [sem_var, TEnv.cons_zero]
    rw [TEnv.consL_lt _ _ _ (by simp; omega), List.getElem_reverse]
    simp only [List.length_append, hl, hsl]
    rw [List.getElem_append_left (by omega)]
    congr 1; omega
  | succ j =>
    simp only [sem_var]
    rw [TEnv.consL_ge γ' (args ++ ihs) (j + C.args.length + s) (by simp; omega)]
    simp only [List.length_append, hl, hsl]
    rw [show j + C.args.length + s - (C.args.length + s) = j by omega]
    rfl

theorem consL_shift (γ' : ℕ → V) (args : List V) : (fun x => TEnv.consL γ' args (x + args.length)) = γ' := by
  funext x; rw [TEnv.consL_ge _ _ _ (by omega)]; simp

theorem sem_wkN_consL (t : Tm) (ρ' : IEnv n) (γ' : ℕ → V) (args : List V) :
    sem S (t.wkN args.length 0) n ρ' (TEnv.consL γ' args) = sem S t n ρ' γ' := by
  rw [Tm.wkN, sem_ren]
  congr 1
  exact consL_shift γ' args

theorem natural_wkN_consL {t : Tm} {ρ' : IEnv n} {γ' : ℕ → V} (h : Natural S t n ρ' γ') (args : List V) :
    Natural S (t.wkN args.length 0) n ρ' (TEnv.consL γ' args) := by
  intro k f
  rw [sem_wkN_consL, Tm.wkN, sem_ren, ← h k f]
  congr 1
  funext x
  simp only [TEnv.restr]
  rw [TEnv.consL_ge _ _ _ (by omega)]; simp

theorem sem_vars_consL (γ' : ℕ → V) (args : List V) (ρ' : IEnv n) :
    (((List.range args.length).map Tm.var).reverse.map fun t => sem S t n ρ' (TEnv.consL γ' args)) = args := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_map, List.length_range, sem_var]
  rw [TEnv.consL_lt _ _ _ (by omega), List.getElem_reverse]
  congr 1; omega

theorem sem_branchArgTy_point {d : ℕ} {D : DataDecl} (hd : S[d]? = some (.data D)) (hsyn : DataSyn d D) {c : ℕ}
    {C : Ctor} (hC : D.ctors[c]? = some C) {k : ℕ} {A : Tm} (hA : C.args[k]? = some (.point A)) (ps : Tm)
    (hpl : ps = Tm.ofList ps.toList) (hpsl : ps.toList.length = D.params.length) (ρ' : IEnv n) (γ' : ℕ → V)
    (args : List V) (hk : args.length = k) (hnat : ∀ t ∈ ps.toList, Natural S t n ρ' γ') :
    sem S (DataDecl.branchArgTy d D.params.length C ps k) n ρ' (TEnv.consL γ' args) =
      argTyRaw (sigUpTo S d) D d c k n (sem S ps n ρ' γ') args := by
  subst hk
  have harg : C.argTy d D.params.length args.length = A := by simp [Ctor.argTy, hA]
  unfold DataDecl.branchArgTy
  rw [harg, List.map_reverse]
  rw [sem_argTy_subst hd hsyn hC hA ((List.range args.length).map Tm.var) (ps.toList.map (·.wkN args.length 0))
    (by simp) (by simp [hpsl]) (fun t ht => ?_)]
  · rw [sem_vars_consL, sem_ofList_vlist, List.map_map]
    conv_rhs => rw [hpl, sem_ofList_vlist]
    have e : List.map ((fun t => sem S t n ρ' (TEnv.consL γ' args)) ∘ fun x => Tm.wkN args.length 0 x) ps.toList =
        List.map (fun t => sem S t n ρ' γ') ps.toList :=
      List.map_congr_left fun t _ => sem_wkN_consL (S := S) t ρ' γ' args
    rw [e]
  · rcases List.mem_append.1 ht with ht | ht
    · obtain ⟨x, -, rfl⟩ := List.mem_map.1 ht; intro k' f; rfl
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 ht)
      exact natural_wkN_consL (hnat p hp) args

/-- `n` interval-Π-types around `inner`. -/
def ipiN (k : ℕ) (inner : Tm) : Tm := (List.range k).foldl (fun acc _ => Tm.ipi acc) inner

theorem ipiN_succ (k : ℕ) (inner : Tm) : ipiN (k + 1) inner = Tm.ipi (ipiN k inner) := by
  simp [ipiN, List.range_succ, List.foldl_append]

/-- Applying an element of interval-Π-types to points. -/
theorem papps_ipiN : ∀ (rs : List (DM m)) (inner : Tm) (ρ : IEnv m) (γ : ℕ → V) (f : V),
    (∀ x, IsKV m (γ x)) → TyOK S (ipiN rs.length inner) m ρ γ →
    f ∈ El (sem S (ipiN rs.length inner) m ρ γ) (Hom.id m) →
    TyOK S inner m (IEnv.consL ρ rs) γ ∧ pappsV m f rs ∈ El (sem S inner m (IEnv.consL ρ rs) γ) (Hom.id m)
  | [], inner, ρ, γ, f, _, hty, hf => ⟨hty, hf⟩
  | r :: rs, inner, ρ, γ, f, hγ, hty, hf => by
    simp only [List.length_cons] at hty hf
    rw [ipiN_succ] at hty hf
    obtain ⟨hN, hL, hsem, l, hl, hV, hW⟩ := hty.ipi_at
    rw [hsem, mem_El_ipiC hL] at hf
    obtain ⟨p, hp, rfl⟩ := hf
    have hfr : pappV m (pathOfLine m p) r ∈ El (sem S (ipiN rs.length inner) m (ρ.cons r) γ) (Hom.id m) := by
      rw [pappV_pathOfLine, line_endpt hγ hN r, El_res, Hom.comp_id]
      have := hW.fib.elRes _ _ _ hp m (Hom.endpt m r)
      rwa [Hom.id_comp] at this
    have hty' : TyOK S (ipiN rs.length inner) m (ρ.cons r) γ := by
      refine ⟨l, hl, Or.inl ⟨?_, ?_⟩⟩
      · rw [line_endpt hγ hN r]; exact hW.res _
      · rw [line_endpt hγ hN r]; exact res_mem_Vt hV _
    have := papps_ipiN rs inner (ρ.cons r) γ _ hγ hty' hfr
    simpa [IEnv.consL, pappsV] using this

end

end Model
