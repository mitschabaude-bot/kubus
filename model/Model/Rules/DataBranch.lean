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

theorem sem_wkN_consL_restr (t : Tm) (γ' : ℕ → V) (args : List V) {k' : ℕ} (ρ'' : IEnv k') (f : Hom k' n) :
    sem S (t.wkN args.length 0) k' ρ'' (TEnv.restr (TEnv.consL γ' args) f) = sem S t k' ρ'' (TEnv.restr γ' f) := by
  rw [Tm.wkN, sem_ren]
  congr 1
  funext x
  simp only [TEnv.restr]
  rw [TEnv.consL_ge _ _ _ (by omega)]; simp

theorem sem_branchArgTy_rec {d : ℕ} {D : DataDecl} {C : Ctor} {k : ℕ}
    (hr : C.argTy d D.params.length k = .data d (Ctor.paramVars D.params.length k)) (ps : Tm)
    (hpl : ps = Tm.ofList ps.toList) (hpsl : ps.toList.length = D.params.length) (ρ' : IEnv n) (γ' : ℕ → V)
    (args : List V) (hk : args.length = k) :
    sem S (DataDecl.branchArgTy d D.params.length C ps k) n ρ' (TEnv.consL γ' args) =
      sem S (.data d ps) n ρ' γ' := by
  subst hk
  unfold DataDecl.branchArgTy
  rw [hr, List.map_reverse]
  have e := paramVars_substList (ps.toList.map (·.wkN args.length 0)) ((List.range args.length).map Tm.var)
  simp only [List.length_map, List.length_range, hpsl] at e
  rw [Tm.substList, show (Tm.data d (Ctor.paramVars D.params.length args.length)).subst _ I.var =
    Tm.data d ((Ctor.paramVars D.params.length args.length).substList
      ((List.range args.length).map Tm.var ++ (ps.toList.map (·.wkN args.length 0)).reverse)) from rfl, e]
  show (sigV S).dat n d _ = (sigV S).dat n d _
  congr 1
  funext k' f
  conv_rhs => rw [hpl]
  show sem S _ _ _ _ = sem S _ _ _ _
  rw [sem_ofList_vlist, sem_ofList_vlist, List.map_map]
  exact congrArg vlist (List.map_congr_left fun t _ => sem_wkN_consL_restr t γ' args _ f)

theorem listLen_vlist' : ∀ (L : List V), ListLen (vlist L) L.length
  | [] => rfl
  | a :: L => ⟨⟨_, _, rfl⟩, by simpa [vlist] using listLen_vlist' L⟩

theorem plist_vlist : ∀ (L : List V), plist (vlist L) L.length = L
  | [] => rfl
  | a :: L => by
    rw [List.length_cons, vlist, plist_pair, plist_vlist L]

/-- A constructor term with variable arguments denotes the constructor value. -/
theorem sem_con_vars {d : ℕ} {D : DataDecl} (hS : SigOK S) (hd : S[d]? = some (.data D)) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) (ps' : Tm) (xs : List Tm) (is : List I) {ρ : IEnv m} {γ : ℕ → V}
    (hγ : ∀ x, IsKV m (γ x)) (PSv : RV m) (hPS : psRV S ps' m ρ γ = PSv)
    (hpok : ParamsOK (sigUpTo S d) D m PSv) (args : List V)
    (hxs : xs.map (fun t => sem S t m ρ γ) = args) (hxv : ∀ t ∈ xs, ∃ y, t = .var y)
    (rs : List (DM m)) (his : is.map (ival ρ) = rs) (hlen : args.length = C.args.length) (hrs : rs.length = C.dims)
    (hat : (dataSD (sigUpTo S d) D d m PSv).ArgsTyped c C m (Hom.id m) args) :
    sem S (.con d c ps' (Tm.ofList xs) is) m ρ γ = conV D.ctors m c args rs ∧
      Natural S (.con d c ps' (Tm.ofList xs) is) m ρ γ := by
  have hgood := ((hS.2 d D hd).2 m PSv hpok).1
  have hxnat : ∀ t ∈ xs, ∀ k (f : Hom k m), sem S t k (ρ.restr f) (TEnv.restr γ f) = res f (sem S t m ρ γ) := by
    intro t ht k f; obtain ⟨y, rfl⟩ := hxv t ht; rfl
  have hguard : ∀ k (f : Hom k m), ConGuard (sigUpTo S d) D d k (psRV S ps' k (ρ.restr f) (TEnv.restr γ f)) c
      (psRV S (Tm.ofList xs) k (ρ.restr f) (TEnv.restr γ f)) (is.map (ival (ρ.restr f))) ∧
      sem S (Tm.ofList xs) k (ρ.restr f) (TEnv.restr γ f) = vlist (args.map (res f)) := by
    intro k f
    have hxsk : sem S (Tm.ofList xs) k (ρ.restr f) (TEnv.restr γ f) = vlist (args.map (res f)) := by
      rw [sem_ofList_vlist, ← hxs, List.map_map]
      exact congrArg vlist (List.map_congr_left fun t ht => hxnat t ht k f)
    have hisl : is.length = C.dims := by rw [← hrs, ← his, List.length_map]
    refine ⟨⟨C, hC, by simp [hisl], ?_, ?_, ?_⟩, hxsk⟩
    · simp only [psRV, Hom.comp_id, IEnv.restr_restr, TEnv.restr_restr]
      rw [hxsk]
      simpa [hlen] using listLen_vlist' (args.map (res f))
    · have : psRV S ps' k (ρ.restr f) (TEnv.restr γ f) = fun k' f' => PSv k' (f.comp f') := by
        rw [← hPS]; funext k' f'; simp only [psRV, IEnv.restr_restr, TEnv.restr_restr]
      rw [this]; exact hpok.restr f
    · have hpsr : psRV S ps' k (ρ.restr f) (TEnv.restr γ f) = fun k' f' => PSv k' (f.comp f') := by
        rw [← hPS]; funext k' f'; simp only [psRV, IEnv.restr_restr, TEnv.restr_restr]
      rw [hpsr]
      simp only [psRV, Hom.comp_id, IEnv.restr_restr, TEnv.restr_restr]
      rw [hxsk, show C.args.length = (args.map (res f)).length by simp [hlen], plist_vlist]
      have := hgood.argsTyped_res hC hat k f
      exact (argsTyped_restr_iff (dataSD (sigUpTo S d) D d m PSv) f (Hom.id k) _).2 (by simpa using this)
  have hval : ∀ k (f : Hom k m), sem S (.con d c ps' (Tm.ofList xs) is) k (ρ.restr f) (TEnv.restr γ f) =
      conV D.ctors k c (args.map (res f)) (rs.map (·.restr f)) := by
    intro k f
    rw [sem_con_of hd (hguard k f).1, IEnv.restr_restr, TEnv.restr_restr, Hom.comp_id, (hguard k f).2,
      getD_ctors hC, show C.args.length = (args.map (res f)).length by simp [hlen], plist_vlist, ← his,
      List.map_map]
    congr 1
  have h0 := hval m (Hom.id m)
  rw [IEnv.restr_id, TEnv.restr_id_of_kv hγ] at h0
  have hargkv : ∀ a ∈ args, IsKV m a := by
    intro a ha; rw [← hxs] at ha; obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha
    obtain ⟨y, rfl⟩ := hxv t ht; exact hγ y
  rw [map_res_id_of_kv hargkv, show rs.map (·.restr (Hom.id m)) = rs by simp] at h0
  refine ⟨h0, fun k f => ?_⟩
  rw [hval k f, h0, res_conV]

theorem IEnv.consL_ge (ρ : IEnv m) : ∀ (rs : List (DM m)) (x : ℕ), rs.length ≤ x → IEnv.consL ρ rs x = ρ (x - rs.length)
  | [], x, _ => by simp [IEnv.consL]
  | r :: rs, x, hx => by
    simp only [IEnv.consL, List.foldl_cons]
    rw [show List.foldl IEnv.cons (IEnv.cons ρ r) rs = IEnv.consL (IEnv.cons ρ r) rs from rfl,
      IEnv.consL_ge _ rs x (by simp at hx; omega)]
    simp at hx
    rw [show x - rs.length = (x - (rs.length + 1)) + 1 by omega]
    rfl

theorem IEnv.consL_lt (ρ : IEnv m) : ∀ (rs : List (DM m)) (x : ℕ) (hx : x < rs.length),
    IEnv.consL ρ rs x = rs.reverse[x]'(by simpa using hx)
  | r :: rs, x, hx => by
    simp only [IEnv.consL, List.foldl_cons]
    by_cases h : x < rs.length
    · rw [show List.foldl IEnv.cons (IEnv.cons ρ r) rs = IEnv.consL (IEnv.cons ρ r) rs from rfl,
        IEnv.consL_lt _ rs x h]
      rw [List.getElem_of_eq (List.reverse_cons (a := r) (as := rs)), List.getElem_append_left (by simpa using h)]
    · have hx' : x = rs.length := by simp at hx; omega
      subst hx'
      rw [show List.foldl IEnv.cons (IEnv.cons ρ r) rs = IEnv.consL (IEnv.cons ρ r) rs from rfl,
        IEnv.consL_ge _ rs _ le_rfl]
      simp [List.reverse_cons]
      rfl

theorem sem_branchBody {d : ℕ} {D : DataDecl} (hS : SigOK S) (hd : S[d]? = some (.data D)) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) (ps : Tm) (P : Tm) (ρ' : IEnv n) (γ' : ℕ → V) (hγ : ∀ x, IsKV n (γ' x))
    (args ihs : List V) (rs : List (DM n)) (hl : args.length = C.args.length) (hil : ihs.length = C.recPos.length)
    (hrs : rs.length = C.dims) (hkv : ∀ a ∈ args ++ ihs, IsKV n a)
    (hpok : ParamsOK (sigUpTo S d) D n (psRV S ps n ρ' γ'))
    (hat : (dataSD (sigUpTo S d) D d n (psRV S ps n ρ' γ')).ArgsTyped c C n (Hom.id n) args) :
    sem S (DataDecl.branchBody d c C ps P) n (IEnv.consL ρ' rs) (TEnv.consL γ' (args ++ ihs)) =
      sem S P n ρ' (TEnv.cons γ' (conV D.ctors n c args rs)) := by
  have hγB : ∀ x, IsKV n ((TEnv.consL γ' (args ++ ihs)) x) := TEnv.consL_kv hγ hkv
  set xs : List Tm := (List.range C.args.length).map fun k => Tm.var (C.recPos.length + C.args.length - 1 - k)
  set is : List I := (List.range C.dims).map fun l => I.var (C.dims - 1 - l)
  have hPS : psRV S (ps.wkN (C.args.length + C.recPos.length) C.dims) n (IEnv.consL ρ' rs) (TEnv.consL γ' (args ++ ihs)) = psRV S ps n ρ' γ' := by
    funext k f
    simp only [psRV, Tm.wkN, sem_ren]
    congr 1
    · funext i; simp only [IEnv.restr]; rw [IEnv.consL_ge _ _ _ (by omega)]; simp [hrs]
    · funext x; simp only [TEnv.restr]; rw [TEnv.consL_ge _ _ _ (by simp; omega)]; simp [hl, hil]
  have hxs : xs.map (fun t => sem S t n (IEnv.consL ρ' rs) (TEnv.consL γ' (args ++ ihs))) = args := by
    apply List.ext_getElem (by simp [xs, hl])
    intro i h1 h2
    simp only [xs, List.getElem_map, List.getElem_range, sem_var]
    rw [TEnv.consL_lt _ _ _ (by simp; omega), List.getElem_reverse]
    simp only [List.length_append, hl, hil]
    rw [List.getElem_append_left (by omega)]
    congr 1; omega
  have his : is.map (ival (IEnv.consL ρ' rs)) = rs := by
    apply List.ext_getElem (by simp [is, hrs])
    intro i h1 h2
    simp only [is, List.getElem_map, List.getElem_range, ival.var]
    rw [IEnv.consL_lt _ _ _ (by omega), List.getElem_reverse]
    congr 1; omega
  obtain ⟨hcv, hcn⟩ := sem_con_vars hS hd hC _ xs is hγB _ hPS hpok args hxs
    (fun t ht => by obtain ⟨k, -, rfl⟩ := List.mem_map.1 ht; exact ⟨_, rfl⟩) rs his hl hrs hat
  unfold DataDecl.branchBody
  rw [sem_subst S P n (IEnv.consL ρ' rs) (TEnv.consL γ' (args ++ ihs)) _ _ (fun x => by cases x with
    | zero => exact hcn
    | succ j => intro k f; rfl)]
  congr 1
  · funext i; simp only [ival.var]; rw [IEnv.consL_ge _ _ _ (by omega)]; simp [hrs]
  · funext x
    cases x with
    | zero => exact hcv
    | succ j =>
      simp only [sem_var]
      rw [TEnv.consL_ge _ _ _ (by simp; omega)]
      simp only [List.length_append, hl, hil]
      rw [show j + C.args.length + C.recPos.length - (C.args.length + C.recPos.length) = j by omega]
      rfl

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

theorem psnat_of_paramsOK {d : ℕ} {D : DataDecl} {ps : Tm} (hpl : ps = Tm.ofList ps.toList)
    (hpsl : ps.toList.length = D.params.length) {ρ' : IEnv n} {γ' : ℕ → V} (hγ : ∀ x, IsKV n (γ' x))
    (hpok : ParamsOK (sigUpTo S d) D n (psRV S ps n ρ' γ')) : ∀ t ∈ ps.toList, Natural S t n ρ' γ' := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  intro k f
  have e := (hpok n (Hom.id n)).2.2 k f i (by omega)
  simp only [psRV, Hom.id_comp, IEnv.restr_id, TEnv.restr_id_of_kv hγ] at e
  rw [sem_vnth ps _ _ i hi, sem_vnth ps _ _ i hi] at e
  exact e

theorem branchTy_eq (D : DataDecl) (d c : ℕ) (C : Ctor) (ps P : Tm) :
    D.branchTy d c C ps P = (((List.range C.args.length).map (DataDecl.branchArgTy d D.params.length C ps)) ++
      ((List.range C.recPos.length).map (DataDecl.branchIhTy C P))).foldr Tm.pi
      (ipiN C.dims (DataDecl.branchBody d c C ps P)) := by
  simp [DataDecl.branchTy, List.foldr_append, List.foldr_map, ipiN]

/-- **Branch application**: a branch applied to typed arguments, hypotheses and interval
arguments is an element of the motive at the constructor value. -/
theorem branch_app_mem {d : ℕ} {D : DataDecl} (hS : SigOK S) (hd : S[d]? = some (.data D)) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) (ps : Tm) (hpl : ps = Tm.ofList ps.toList)
    (P : Tm) (ρ' : IEnv n) (γ' : ℕ → V) (hγ : ∀ x, IsKV n (γ' x))
    (hpok : ParamsOK (sigUpTo S d) D n (psRV S ps n ρ' γ')) (bv : V)
    (hty : TyOK S (D.branchTy d c C ps P) n ρ' γ') (hbv : bv ∈ El (sem S (D.branchTy d c C ps P) n ρ' γ') (Hom.id n))
    (args ihs : List V) (rs : List (DM n))
    (hat : (dataSD (sigUpTo S d) D d n (psRV S ps n ρ' γ')).ArgsTyped c C n (Hom.id n) args)
    (hil : ihs.length = C.recPos.length)
    (hih : ∀ s (hs : s < C.recPos.length), ihs[s]'(by omega) ∈
      El (sem S P n ρ' (TEnv.cons γ' (args[C.recPos.getD s 0]'(by have := recPos_lt hs; have := hat.1; omega))))
        (Hom.id n))
    (hihkv : ∀ a ∈ ihs, IsKV n a) (hrs : rs.length = C.dims) :
    pappsV n (appsV n bv (args ++ ihs)) rs ∈ El (sem S P n ρ' (TEnv.cons γ' (conV D.ctors n c args rs))) (Hom.id n) := by
  have hok := hS.2 d D hd
  have hgood := (hok.2 n _ hpok).1
  have hl : args.length = C.args.length := hat.1
  have hPS : psRV S ps n ρ' γ' n (Hom.id n) = sem S ps n ρ' γ' := by
    simp only [psRV, IEnv.restr_id, TEnv.restr_id_of_kv hγ]
  have hpsl : ps.toList.length = D.params.length := by
    have h1 := (hpok n (Hom.id n)).1
    rw [hPS, hpl] at h1
    exact listLen_unique (listLen_sem_ofList _ _ _) h1
  have hpsnat := psnat_of_paramsOK hpl hpsl hγ hpok
  have hPV : (dataSD (sigUpTo S d) D d n (psRV S ps n ρ' γ')).PtValid c n (Hom.id n) args := by
    have := SData.ptValid_take hC hat.2.2 args.length; rwa [List.take_length] at this
  have hakv : ∀ a ∈ args, IsKV n a := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    cases hr : C.isRec j
    · have hct : (dataSD (sigUpTo S d) D d n (psRV S ps n ρ' γ')).ctors = D.ctors := rfl
      exact hgood.pt_kv hPV hj (by rw [hct, getD_ctors hC]; exact hr)
    · exact (hat.2.1 j _ (List.getElem?_eq_getElem hj) hr).kv
  rw [branchTy_eq] at hty hbv
  have hidx : ∀ i (hi : i < (args ++ ihs).length), (args ++ ihs)[i] ∈ El (sem S
      ((((List.range C.args.length).map (DataDecl.branchArgTy d D.params.length C ps)) ++
        ((List.range C.recPos.length).map (DataDecl.branchIhTy C P)))[i]'(by simp at hi ⊢; omega))
      n ρ' (TEnv.consL γ' ((args ++ ihs).take i))) (Hom.id n) := by
    intro i hi
    by_cases hin : i < C.args.length
    · simp only [List.getElem_append_left (by simp; omega : i < (List.map _ (List.range C.args.length)).length),
        List.getElem_map, List.getElem_range]
      rw [List.getElem_append_left (by omega), List.take_append_of_le_length (by omega)]
      cases hr : C.isRec i
      · obtain ⟨A, hA⟩ : ∃ A, C.args[i]? = some (.point A) := by
          cases h' : C.args[i]'hin with
          | point A => exact ⟨A, by rw [List.getElem?_eq_getElem hin, h']⟩
          | recur => simp [Ctor.isRec, List.getElem?_eq_getElem hin, h'] at hr
        rw [sem_branchArgTy_point hd hok.1 hC hA ps hpl hpsl ρ' γ' _ (by simp; omega) hpsnat]
        have := hat.2.2 i _ (List.getElem?_eq_getElem (by omega)) hr
        show _ ∈ El (argTyRaw (sigUpTo S d) D d c i n (sem S ps n ρ' γ') (args.take i)) _
        change _ ∈ El (argTySem (sigUpTo S d) D d c i n (psRV S ps n ρ' γ' n (Hom.id n)) (args.take i)) _ at this
        rw [hPS, argTySem_eq] at this
        split at this
        · exact this
        · simp at this
      · have harg : C.argTy d D.params.length i = .data d (Ctor.paramVars D.params.length i) := by
          cases h' : C.args[i]'hin with
          | point A => simp [Ctor.isRec, List.getElem?_eq_getElem hin, h'] at hr
          | recur => simp [Ctor.argTy, List.getElem?_eq_getElem hin, h']
        rw [sem_branchArgTy_rec harg ps hpl hpsl ρ' γ' _ (by simp; omega), sem_data_of hd hpok, mem_El_dataC]
        exact hat.2.1 i _ (List.getElem?_eq_getElem (by omega)) hr
    · have hs : i - C.args.length < C.recPos.length := by simp at hi; omega
      simp only [List.getElem_append_right (by simp; omega : (List.map _ (List.range C.args.length)).length ≤ i),
        List.getElem_map, List.getElem_range, List.length_map, List.length_range]
      rw [List.getElem_append_right (by omega)]
      rw [show (args ++ ihs).take i = args ++ ihs.take (i - C.args.length) by
        rw [List.take_append]; simp [hl, List.take_of_length_le (by omega : args.length ≤ i)]]
      rw [sem_branchIhTy C P hs ρ' γ' args _ hl (by simp; omega)]
      simp only [hl]
      exact hih _ hs
  obtain ⟨hty2, hmem2⟩ := apps_foldr_pi _ _ γ' bv (args ++ ihs) hγ hty hbv (by simp [hl, hil]) hidx
  rw [← hrs] at hty2 hmem2
  obtain ⟨-, hmem3⟩ := papps_ipiN rs _ ρ' _ _ (TEnv.consL_kv hγ (fun a ha => by
    rcases List.mem_append.1 ha with h | h
    · exact hakv a h
    · exact hihkv a h)) hty2 hmem2
  rw [sem_branchBody hS hd hC ps P ρ' γ' hγ args ihs rs hl hil hrs (fun a ha => by
    rcases List.mem_append.1 ha with h | h
    · exact hakv a h
    · exact hihkv a h) hpok hat] at hmem3
  exact hmem3

end

end Model
