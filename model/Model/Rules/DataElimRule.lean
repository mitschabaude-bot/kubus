import Model.Rules.DataSimple
import Model.DataElimTy

/-!
# The eliminator rule

At a point of the context, the eliminator's guard holds: the branch equations (`h6` of the rule)
give the constructor equations of the semantic eliminator (`ElimConEq`), by strong induction on
the constructor, since the eliminator on a simple boundary term is computed by `bndElim`.
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

/-- The motive at the point `(ρ, γ)`, at all restrictions and elements. -/
def motV (S : Sig) (P : Tm) (ρ : IEnv m) (γ : ℕ → V) : (n : ℕ) → Hom n m → V → V :=
  fun k f a => sem S P k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)

theorem motV_restr (P : Tm) (ρ : IEnv m) (γ : ℕ → V) (f : Hom k m) :
    motV S P (ρ.restr f) (TEnv.restr γ f) = fun n g => motV S P ρ γ n (f.comp g) := by
  funext n g a; simp only [motV, IEnv.restr_restr, TEnv.restr_restr]

theorem psRV_restr (t : Tm) (ρ : IEnv m) (γ : ℕ → V) (f : Hom k m) :
    psRV S t k (ρ.restr f) (TEnv.restr γ f) = fun n g => psRV S t m ρ γ n (f.comp g) := by
  funext n g; simp only [psRV, IEnv.restr_restr, TEnv.restr_restr]

theorem dataSD_restr (σ : SigV) (D : DataDecl) (d : ℕ) (ps : Tm) (ρ : IEnv m) (γ : ℕ → V) (f : Hom k m) :
    dataSD σ D d k (psRV S ps k (ρ.restr f) (TEnv.restr γ f)) = (dataSD σ D d m (psRV S ps m ρ γ)).restr f := by
  simp only [dataSD, SData.restr, psRV, IEnv.restr_restr, TEnv.restr_restr]


theorem sem_apps_of_nat {ρ : IEnv m} {γ : ℕ → V} : ∀ (ts : List Tm) (f : Tm), (∀ t ∈ ts, Natural S t m ρ γ) →
    sem S (Tm.apps f ts) m ρ γ = appsV m (sem S f m ρ γ) (ts.map fun t => sem S t m ρ γ)
  | [], f, _ => rfl
  | t :: ts, f, h => by
    simp only [Tm.apps, List.foldl_cons, List.map_cons, appsV]
    rw [show List.foldl Tm.app (f.app t) ts = Tm.apps (f.app t) ts from rfl,
      sem_apps_of_nat ts _ fun u hu => h u (List.mem_cons_of_mem _ hu),
      sem_app_of_nat (h t List.mem_cons_self)]

theorem sem_papps {ρ : IEnv m} {γ : ℕ → V} : ∀ (is : List I) (f : Tm),
    sem S (Tm.papps f is) m ρ γ = pappsV m (sem S f m ρ γ) (is.map (ival ρ))
  | [], f => rfl
  | r :: is, f => by
    simp only [Tm.papps, List.foldl_cons, List.map_cons, pappsV]
    rw [show List.foldl Tm.papp (f.papp r) is = Tm.papps (f.papp r) is from rfl, sem_papps is, sem_papp]

theorem sem_wkN_consL2 (t : Tm) (ρ : IEnv m) (γ : ℕ → V) (L : List V) (rs : List (DM m)) {N : ℕ}
    (hN : L.length = N) :
    sem S (t.wkN N rs.length) m (IEnv.consL ρ rs) (TEnv.consL γ L) = sem S t m ρ γ := by
  subst hN
  rw [Tm.wkN, sem_ren]
  congr 1
  · funext i; rw [IEnv.consL_ge _ _ _ (by omega)]; congr 1; omega
  · funext x; rw [TEnv.consL_ge _ _ _ (by omega)]; congr 1; omega

/-- The branch application at a branch point. -/
theorem sem_branchApp (C : Ctor) (b : Tm) (ρ : IEnv m) (γ : ℕ → V) (args ihs : List V) (rs : List (DM m))
    (hl : args.length = C.args.length) (hil : ihs.length = C.recPos.length) (hrs : rs.length = C.dims) :
    sem S (DataDecl.branchApp C b) m (IEnv.consL ρ rs) (TEnv.consL γ (args ++ ihs)) =
      pappsV m (appsV m (sem S b m ρ γ) (args ++ ihs)) rs := by
  unfold DataDecl.branchApp
  rw [sem_papps, sem_apps_of_nat _ _ (fun t ht => by
    rcases List.mem_append.1 ht with ht | ht <;>
    · obtain ⟨_, -, rfl⟩ := List.mem_map.1 ht; exact natural_var S _ _ _)]
  rw [← hrs, sem_wkN_consL2 b ρ γ (args ++ ihs) rs (by simp [hl, hil])]
  congr 1
  · congr 1
    apply List.ext_getElem (by simp [hl, hil])
    intro i h1 h2
    simp only [List.map_append, List.map_map]
    simp only [List.length_append, List.length_map, List.length_range] at h1
    by_cases hi : i < C.args.length
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by omega)]
      simp only [Function.comp, List.getElem_map, List.getElem_range, sem_var]
      rw [TEnv.consL_lt _ _ _ (by simp; omega), List.getElem_reverse]
      simp only [List.length_append, hl, hil]
      rw [List.getElem_append_left (by omega)]
      congr 1; omega
    · rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by omega)]
      simp only [Function.comp, List.getElem_map, List.getElem_range, sem_var, List.length_map, List.length_range]
      rw [TEnv.consL_lt _ _ _ (by simp; omega), List.getElem_reverse]
      simp only [List.length_append, hl, hil]
      rw [List.getElem_append_right (by omega)]
      congr 1; omega
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, ival.var]
    rw [IEnv.consL_lt _ _ _ (by simp at h1; omega), List.getElem_reverse]
    congr 1; simp at h1 ⊢; omega


/-! ### Branch environments -/

/-- `(ρ', γ')` extends the point `(ρ, γ)` by the arguments, hypotheses and interval arguments of
a branch (in the order of the branch context). -/
structure BrEnv (C : Ctor) (ρ : IEnv m) (γ : ℕ → V) (args ihs : List V) (rs : List (DM m))
    (ρ' : IEnv m) (γ' : ℕ → V) : Prop where
  shiftI : ∀ i, ρ' (i + C.dims) = ρ i
  shiftT : ∀ x, γ' (x + (C.args.length + C.recPos.length)) = γ x
  arg : ∀ j (hj : j < args.length), γ' (j + C.recPos.length) = args.reverse[j]'(by simpa using hj)
  ih : ∀ s (hs : s < ihs.length), γ' s = ihs.reverse[s]'(by simpa using hs)
  int : ∀ i < C.dims, ρ' i = renv rs i
  kv : ∀ x, IsKV m (γ' x)

theorem BrEnv.consL {C : Ctor} {ρ : IEnv m} {γ : ℕ → V} (hγ : ∀ x, IsKV m (γ x)) {args ihs : List V}
    {rs : List (DM m)} (hl : args.length = C.args.length) (hil : ihs.length = C.recPos.length)
    (hrs : rs.length = C.dims) (hkv : ∀ a ∈ args ++ ihs, IsKV m a) :
    BrEnv C ρ γ args ihs rs (IEnv.consL ρ rs) (TEnv.consL γ (args ++ ihs)) where
  shiftI i := by rw [IEnv.consL_ge _ _ _ (by omega)]; congr 1; omega
  shiftT x := by rw [TEnv.consL_ge _ _ _ (by simp; omega)]; congr 1; simp; omega
  arg j hj := by
    rw [TEnv.consL_lt _ _ _ (by simp; omega)]
    simp only [List.reverse_append]
    rw [List.getElem_append_right (by simp; omega)]
    congr 1; simp [hil]
  ih s hs := by
    rw [TEnv.consL_lt _ _ _ (by simp; omega)]
    simp only [List.reverse_append]
    rw [List.getElem_append_left (by simp; omega)]
  int i hi := by
    rw [IEnv.consL_lt _ _ _ (by omega)]
    simp only [renv]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
    rfl
  kv := TEnv.consL_kv hγ hkv

theorem BrEnv.restr {C : Ctor} {ρ : IEnv m} {γ : ℕ → V} {args ihs : List V} {rs : List (DM m)}
    {ρ' : IEnv m} {γ' : ℕ → V} (h : BrEnv C ρ γ args ihs rs ρ' γ') (f : Hom k m) :
    BrEnv C (ρ.restr f) (TEnv.restr γ f) (args.map (res f)) (ihs.map (res f)) (rs.map (·.restr f))
      (ρ'.restr f) (TEnv.restr γ' f) where
  shiftI i := by simp only [IEnv.restr]; rw [h.shiftI]
  shiftT x := by simp only [TEnv.restr]; rw [h.shiftT]
  arg j hj := by
    simp only [TEnv.restr, List.length_map] at hj ⊢
    rw [h.arg j hj]; simp [List.getElem_reverse]
  ih s hs := by
    simp only [TEnv.restr, List.length_map] at hs ⊢
    rw [h.ih s hs]; simp [List.getElem_reverse]
  int i hi := by rw [renv_restr]; simp only [IEnv.restr]; rw [h.int i hi]
  kv x := isKV_res f _

theorem BrEnv.sem_wkN {C : Ctor} {ρ : IEnv m} {γ : ℕ → V} {args ihs : List V} {rs : List (DM m)}
    {ρ' : IEnv m} {γ' : ℕ → V} (h : BrEnv C ρ γ args ihs rs ρ' γ') (t : Tm) :
    sem S (t.wkN (C.args.length + C.recPos.length) C.dims) m ρ' γ' = sem S t m ρ γ := by
  rw [Tm.wkN, sem_ren]
  congr 1
  · funext i; exact h.shiftI i
  · funext x; exact h.shiftT x


theorem bndElimArgs_eq (D : DataDecl) (C : Ctor) (ps bs : Tm) (C' : Ctor) : ∀ (as : Tm) (j : ℕ),
    D.bndElimArgs C ps bs C' j as = ((List.range as.toList.length).filter (fun i => C'.isRec (j + i))).map
      (fun i => D.bndElim C ps bs (as.toList.getD i .abort)) := by
  intro as
  induction as with
  | tcons a as _ ih =>
    intro j
    rw [DataDecl.bndElimArgs, ih (j + 1)]
    simp only [Tm.toList, List.length_cons]
    rw [List.range_succ_eq_map, List.filter_cons, List.filter_map]
    have e2 : List.filter ((fun i => C'.isRec (j + i)) ∘ Nat.succ) (List.range as.toList.length) =
        List.filter (fun i => C'.isRec (j + 1 + i)) (List.range as.toList.length) :=
      List.filter_congr fun i _ => by
        show C'.isRec (j + (i + 1)) = C'.isRec (j + 1 + i); rw [show j + (i + 1) = j + 1 + i by omega]
    have e3 : ((fun i => D.bndElim C ps bs ((a :: as.toList).getD i .abort)) ∘ Nat.succ) =
        fun i => D.bndElim C ps bs (as.toList.getD i .abort) := by
      funext i; simp
    rw [e2]
    have e4 : ∀ L : List ℕ, List.map (fun i => D.bndElim C ps bs ((a :: as.toList).getD i .abort)) (L.map Nat.succ) =
        List.map (fun i => D.bndElim C ps bs (as.toList.getD i .abort)) L := by
      intro L; rw [List.map_map, e3]
    by_cases hr : C'.isRec j = true
    · rw [if_pos hr, if_pos (show C'.isRec (j + 0) = true from hr), List.map_cons, e4]; rfl
    · rw [if_neg hr, if_neg (show ¬ C'.isRec (j + 0) = true from hr), e4]; rfl
  | _ => intro j; simp [DataDecl.bndElimArgs, Tm.toList]


/-- The substitution of `bndPoint`. -/
def bpσ (C : Ctor) (ps : Tm) : ℕ → Tm := fun j =>
  if j < C.args.length then .var (j + C.recPos.length)
  else (ps.toList.reverse.getD (j - C.args.length) (.var 0)).wkN (C.args.length + C.recPos.length) C.dims

theorem bndPoint_eq (C : Ctor) (ps b : Tm) : DataDecl.bndPoint C ps b = b.subst (bpσ C ps) I.var := rfl

theorem btyArgs_rec {Θ : SData m} {c : ℕ} {C C' : Ctor} {c' : ℕ} : ∀ (t : Tm) (j : ℕ) (prev : List Tm),
    BTyArgs Θ c C C' c' j prev t → ∀ i (hi : i < t.toList.length), C'.isRec (j + i) = true →
      BTy Θ c C (t.toList[i])
  | .tcons a as, j, prev, h, i, hi, hr => by
    obtain ⟨h1, -, h3⟩ := h
    cases i with
    | zero => exact h1 hr
    | succ i =>
      simp only [Tm.toList, List.getElem_cons_succ]
      exact btyArgs_rec as (j + 1) (a :: prev) h3 i (by simp [Tm.toList] at hi; omega)
        (by rw [← hr]; congr 1; omega)
  | .var _, _, _, _, i, hi, _ | .const _, _, _, _, i, hi, _ | .univ _, _, _, _, i, hi, _
  | .pi _ _, _, _, _, i, hi, _ | .lam _ _, _, _, _, i, hi, _ | .app _ _, _, _, _, i, hi, _
  | .sigma _ _, _, _, _, i, hi, _ | .pair _ _, _, _, _, i, hi, _ | .fst _, _, _, _, i, hi, _
  | .snd _, _, _, _, i, hi, _ | .path _ _ _, _, _, _, i, hi, _ | .plam _, _, _, _, i, hi, _
  | .papp _ _, _, _, _, i, hi, _ | .ipi _, _, _, _, i, hi, _ | .abort, _, _, _, i, hi, _
  | .split _ _ _ _, _, _, _, i, hi, _ | .transp _ _ _, _, _, _, i, hi, _ | .hcomp _ _ _ _, _, _, _, i, hi, _
  | .glue _ _ _ _, _, _, _, i, hi, _ | .glueEl _ _ _ _, _, _, _, i, hi, _ | .unglue _ _ _, _, _, _, i, hi, _
  | .tnil, _, _, _, i, hi, _ | .data _ _, _, _, _, i, hi, _ | .con _ _ _ _ _, _, _, _, i, hi, _
  | .elim _ _ _ _ _, _, _, _, i, hi, _ => by simp [Tm.toList] at hi


/-- The eliminator is typed and natural on `v`. -/
def ElimTN (Θ : SData m) (P' : (n : ℕ) → Hom n m → V → V) (bs' : (k : ℕ) → Hom k m → V) (v : V) : Prop :=
  elimD Θ P' bs' m (Hom.id m) v ∈ El (P' m (Hom.id m) v) (Hom.id m) ∧
    ∀ n' (h : Hom n' m), res h (elimD Θ P' bs' m (Hom.id m) v) = elimD Θ P' bs' n' ((Hom.id m).comp h) (res h v)

/-- The constructor equations of the eliminator for the constructors before `c`, at every point. -/
def ECAll (S : Sig) (d : ℕ) (D : DataDecl) (ps P bs : Tm) (Φ : I) (Γ : Ctx) (c : ℕ) : Prop :=
  ∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ → ∀ c' < c, ∀ C', D.ctors[c']? = some C' →
    ElimConEq (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) (motV S P ρ γ) (psRV S bs m ρ γ) c' C'

/-- `bndElim` computes the eliminator on the boundary term `e` of constructor `c`, at every
point and branch environment. -/
def TreeQ (S : Sig) (d : ℕ) (D : DataDecl) (ps P bs : Tm) (Φ : I) (Γ : Ctx) (c : ℕ) (C : Ctor) (e : Tm) : Prop :=
  ∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ → ∀ args,
    (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)).ArgsTyped c C m (Hom.id m) args →
    (∀ j a, args[j]? = some a → C.isRec j = true →
      ElimTN (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) (motV S P ρ γ) (psRV S bs m ρ γ) a) →
    ∀ rs : List (DM m), rs.length = C.dims → ∀ (ρ' : IEnv m) (γ' : ℕ → V),
    BrEnv C ρ γ args (C.recPos.map fun j => elimD (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) (motV S P ρ γ)
      (psRV S bs m ρ γ) m (Hom.id m) (args.getD j ∅)) rs ρ' γ' →
    BTy (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) c C e →
    sem S (D.bndElim C ps bs e) m ρ' γ' = elimD (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) (motV S P ρ γ)
      (psRV S bs m ρ γ) m (Hom.id m) (evalBnd (conBefore D.ctors c m) args rs e) ∧
    ElimTN (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) (motV S P ρ γ) (psRV S bs m ρ γ)
      (evalBnd (conBefore D.ctors c m) args rs e)

theorem elimD_restr_pt (d : ℕ) (D : DataDecl) (ps P bs : Tm) (ρ : IEnv m) (γ : ℕ → V) (f : Hom k m) (v : V)
    {n : ℕ} (g : Hom n k) :
    elimD (dataSD (sigUpTo S d) D d k (psRV S ps k (ρ.restr f) (TEnv.restr γ f))) (motV S P (ρ.restr f) (TEnv.restr γ f))
      (psRV S bs k (ρ.restr f) (TEnv.restr γ f)) n g v =
    elimD (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) (motV S P ρ γ) (psRV S bs m ρ γ) n (f.comp g) v := by
  rw [dataSD_restr, motV_restr, psRV_restr]; exact elimD_restr _ _ _ f v g

/-- `ElimTN` is stable under restriction of the point. -/
theorem elimTN_restr_pt (d : ℕ) (D : DataDecl) (ps P bs : Tm) (ρ : IEnv m) (γ : ℕ → V) {a : V}
    (hPf : Fib (motV S P ρ γ m (Hom.id m) a) m)
    (hPn : ∀ n' (h : Hom n' m), res h (motV S P ρ γ m (Hom.id m) a) = motV S P ρ γ n' ((Hom.id m).comp h) (res h a))
    (h : ElimTN (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) (motV S P ρ γ) (psRV S bs m ρ γ) a) (f : Hom k m) :
    ElimTN (dataSD (sigUpTo S d) D d k (psRV S ps k (ρ.restr f) (TEnv.restr γ f))) (motV S P (ρ.restr f) (TEnv.restr γ f))
      (psRV S bs k (ρ.restr f) (TEnv.restr γ f)) (res f a) ∧
    res f (elimD (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) (motV S P ρ γ) (psRV S bs m ρ γ) m (Hom.id m) a) =
      elimD (dataSD (sigUpTo S d) D d k (psRV S ps k (ρ.restr f) (TEnv.restr γ f))) (motV S P (ρ.restr f) (TEnv.restr γ f))
        (psRV S bs k (ρ.restr f) (TEnv.restr γ f)) k (Hom.id k) (res f a) := by
  have e2 : res f (elimD (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) (motV S P ρ γ) (psRV S bs m ρ γ) m (Hom.id m) a) =
      elimD (dataSD (sigUpTo S d) D d k (psRV S ps k (ρ.restr f) (TEnv.restr γ f))) (motV S P (ρ.restr f) (TEnv.restr γ f))
        (psRV S bs k (ρ.restr f) (TEnv.restr γ f)) k (Hom.id k) (res f a) := by
    rw [elimD_restr_pt, Hom.comp_id, h.2 k f, Hom.id_comp]
  refine ⟨⟨?_, fun n' h' => ?_⟩, e2⟩
  · rw [← e2, motV_restr]
    show _ ∈ El (motV S P ρ γ k (f.comp (Hom.id k)) (res f a)) (Hom.id k)
    rw [Hom.comp_id]
    have := hPf.elRes m (Hom.id m) _ h.1 k f
    rw [Hom.id_comp, show El (motV S P ρ γ m (Hom.id m) a) f = El (res f (motV S P ρ γ m (Hom.id m) a)) (Hom.id k) by
      rw [El_res, Hom.comp_id], hPn k f, Hom.id_comp] at this
    exact this
  · rw [← e2, res_res, elimD_restr_pt, h.2 n' (f.comp h'), res_res]
    simp only [Hom.id_comp]

section

variable (hS : SigOK S) {d : ℕ} {D : DataDecl} (hd : S[d]? = some (.data D)) {Ψ : ℕ} {Φ : I} {Γ : Ctx}
  {ps P : Tm} {lv : ℕ} (hpl : ps = Tm.ofList ps.toList)
  (h1 : SemTy S Ψ Φ Γ (.data d ps) (.univ D.level)) (h2 : SemTy S Ψ Φ (.data d ps :: Γ) P (.univ lv))

include hd h1 in
theorem elimPt_pok {ρ : IEnv m} {γ : ℕ → V} (hp : IsPoint S Φ Γ m ρ γ) :
    ParamsOK (sigUpTo S d) D m (psRV S ps m ρ γ) := by
  obtain ⟨hmemU, -, hTyU, -⟩ := h1.2.2.2 m ρ γ hp
  exact paramsOK_of_sem_data hd (TyOK.ne_empty hTyU hmemU)

include hd h1 hpl in
theorem elimPt_psl {ρ : IEnv m} {γ : ℕ → V} (hp : IsPoint S Φ Γ m ρ γ) : ps.toList.length = D.params.length := by
  have h := ((elimPt_pok hd h1 hp) m (Hom.id m)).1
  simp only [psRV, IEnv.restr_id, TEnv.restr_id_of_kv hp.kv] at h
  rw [hpl] at h
  exact listLen_unique (listLen_sem_ofList _ _ _) h

include hd h1 in
/-- Elements of the inductive type at a point extend it to a point of `data d ps :: Γ`. -/
theorem elimPt_cons {ρ : IEnv m} {γ : ℕ → V} (hp : IsPoint S Φ Γ m ρ γ) {n : ℕ} (g : Hom n m) {v : V}
    (hv : DElem (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) n g v) :
    IsPoint S Φ (.data d ps :: Γ) n (ρ.restr g) (TEnv.cons (TEnv.restr γ g) v) := by
  have hp' := hp.restr h1.1 g
  have hpok' := elimPt_pok hd h1 hp'
  refine hp'.cons ?_ hv.kv
  rw [sem_data_of hd hpok', mem_El_dataC, dataSD_restr, delem_restr_iff, Hom.comp_id]
  exact hv

include hd h1 h2 in
theorem elimPt_motive {ρ : IEnv m} {γ : ℕ → V} (hp : IsPoint S Φ Γ m ρ γ) :
    (∀ n (g : Hom n m) v, DElem (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) n g v → Fib (motV S P ρ γ n g v) n) ∧
    (∀ n (g : Hom n m) v, DElem (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) n g v → ∀ n' (h : Hom n' n),
      res h (motV S P ρ γ n g v) = motV S P ρ γ n' (g.comp h) (res h v)) := by
  refine ⟨fun n g v hv => ?_, fun n g v hv n' h => ?_⟩
  · obtain ⟨hmem, -, hty, -⟩ := h2.2.2.2 n _ _ (elimPt_cons hd h1 hp g hv)
    exact (TyCode.of_mem_univ hty hmem).fib
  · obtain ⟨-, hnat, -, -⟩ := h2.2.2.2 n _ _ (elimPt_cons hd h1 hp g hv)
    have := hnat n' h
    simp only [motV]
    rw [← this, TEnv.restr_cons, IEnv.restr_restr, TEnv.restr_restr]


theorem TEnv.consL_shift (γ : ℕ → V) (L : List V) {j : ℕ} (hj : j ≤ L.length) :
    (fun y => TEnv.consL γ L (y + j)) = TEnv.consL γ (L.take (L.length - j)) := by
  funext y
  by_cases hy : y + j < L.length
  · rw [TEnv.consL_lt _ _ _ hy, TEnv.consL_lt _ _ _ (by simp; omega), List.getElem_reverse, List.getElem_reverse,
      List.getElem_take]
    congr 1; simp; omega
  · rw [TEnv.consL_ge _ _ _ (by omega), TEnv.consL_ge _ _ _ (by simp; omega)]
    congr 1; simp; omega

include hS hd h1 hpl in
/-- The point of the branch context given by arguments, hypotheses and interval arguments at
which the boundary holds. -/
theorem elimPt_branch {ρ : IEnv m} {γ : ℕ → V} (hp : IsPoint S Φ Γ m ρ γ) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) {ψ : I} {b : Tm} (hmem : (ψ, b) ∈ C.bnd) (args ihs : List V) (rs : List (DM m))
    (hat : (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)).ArgsTyped c C m (Hom.id m) args)
    (hil : ihs.length = C.recPos.length)
    (hih : ∀ s (hs : s < C.recPos.length), ihs[s]'(by omega) ∈
      El (sem S P m ρ (TEnv.cons γ (args[C.recPos.getD s 0]'(by have := recPos_lt hs; have := hat.1; omega))))
        (Hom.id m))
    (hihkv : ∀ a ∈ ihs, IsKV m a) (hrs : rs.length = C.dims) (hψ : (ival (renv rs) ψ).holds) :
    IsPoint S (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ) m (IEnv.consL ρ rs)
      (TEnv.consL γ (args ++ ihs)) := by
  have hok := hS.2 d D hd
  have hpok := elimPt_pok hd h1 hp
  have hgood := (hok.2 m _ hpok).1
  have hl : args.length = C.args.length := hat.1
  have hPV : (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)).PtValid c m (Hom.id m) args := by
    have := SData.ptValid_take hC hat.2.2 args.length; rwa [List.take_length] at this
  have hakv : ∀ a ∈ args, IsKV m a := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    cases hr : C.isRec j
    · have hct : (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)).ctors = D.ctors := rfl
      exact hgood.pt_kv hPV hj (by rw [hct, getD_ctors hC]; exact hr)
    · exact (hat.2.1 j _ (List.getElem?_eq_getElem hj) hr).kv
  have hkvL : ∀ a ∈ args ++ ihs, IsKV m a := fun a ha => by
    rcases List.mem_append.1 ha with h | h
    · exact hakv a h
    · exact hihkv a h
  have hρs : (fun i => IEnv.consL ρ rs (i + C.dims)) = ρ := by
    funext i; rw [IEnv.consL_ge _ _ _ (by omega)]; congr 1; omega
  refine isPoint_cof_iff.2 ⟨⟨?_, fun x B hB => ?_, TEnv.consL_kv hp.kv hkvL⟩, ?_⟩
  · rw [ival_ren, hρs]; exact hp.cof
  · rw [Ctx.lookup_eq] at hB
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.1 hB
    unfold DataDecl.branchCtx at hT
    rw [List.getElem?_map] at hT
    obtain ⟨T0, hT0, rfl⟩ := Option.map_eq_some_iff.1 hT
    rw [sem_ren, sem_ren]
    simp only [id]
    rw [hρs]
    have hN : (args ++ ihs).length = C.args.length + C.recPos.length := by simp [hl, hil]
    by_cases hx : x < C.args.length + C.recPos.length
    · have hidx := branch_args_mem hS hd hC ps hpl P ρ γ hp.kv hpok args ihs hat hil hih
        (C.args.length + C.recPos.length - 1 - x) (by omega)
      rw [TEnv.consL_lt _ _ _ (by omega), List.getElem_reverse]
      have e1 : (fun y => TEnv.consL γ (args ++ ihs) (y + (x + 1))) =
          TEnv.consL γ ((args ++ ihs).take (C.args.length + C.recPos.length - 1 - x)) := by
        rw [TEnv.consL_shift _ _ (by omega), hN]; congr 2; omega
      rw [e1]
      have e2 : T0 = ((List.map (DataDecl.branchArgTy d D.params.length C ps) (List.range C.args.length) ++
          List.map (DataDecl.branchIhTy C P) (List.range C.recPos.length)))[C.args.length + C.recPos.length - 1 - x]'
          (by simp; omega) := by
        rw [List.getElem?_append_left (by simp; omega)] at hT0
        have : ((List.range C.recPos.length).reverse.map (DataDecl.branchIhTy C P) ++
            (List.range C.args.length).reverse.map (DataDecl.branchArgTy d D.params.length C ps)) =
            (List.map (DataDecl.branchArgTy d D.params.length C ps) (List.range C.args.length) ++
              List.map (DataDecl.branchIhTy C P) (List.range C.recPos.length)).reverse := by
          simp [List.map_reverse]
        rw [this, List.getElem?_reverse (by simp; omega)] at hT0
        simp only [List.length_append, List.length_map, List.length_range] at hT0
        rw [List.getElem?_eq_getElem (by simp; omega)] at hT0
        exact (Option.some.inj hT0).symm
      rw [e2]
      convert hidx using 3
      rw [hN]
    · rw [List.getElem?_append_right (by simp; omega)] at hT0
      have hT1 : Γ[x - (C.args.length + C.recPos.length)]? = some T0 := by
        rw [← hT0]; congr 1; simp; omega
      rw [TEnv.consL_ge _ _ _ (by omega), hN]
      have := hp.typ (x - (C.args.length + C.recPos.length)) _ (by rw [Ctx.lookup_eq, hT1]; rfl)
      rw [sem_ren] at this
      convert this using 3
      funext y; rw [TEnv.consL_ge _ _ _ (by omega), hN]; congr 1; omega
  · rw [ival_congr_scoped ((hok.1.2.2.2 c C hC ψ b hmem).1) (ρ' := renv rs) fun i hi => ?_]
    · exact hψ
    · rw [IEnv.consL_lt _ _ _ (by omega)]
      simp only [renv]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
      rfl


include hS hd h1 hpl in
/-- The branches at a point satisfy the branch hypothesis of `elimD_typed`. -/
theorem elimPt_hB {bs : Tm} (hbsl : bs.toList.length = D.ctors.length)
    (h5 : ∀ (c : Nat) (C : Ctor) (b : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      SemTy S Ψ Φ Γ b (D.branchTy d c C ps P))
    {ρ : IEnv m} {γ : ℕ → V} (hp : IsPoint S Φ Γ m ρ γ) :
    ∀ n (g : Hom n m) c C, (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)).ctors[c]? = some C → ∀ args,
      (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)).ArgsTyped c C n g args →
    ∀ ihs : List V, ∀ (hil : ihs.length = C.recPos.length),
    (∀ s (hs : s < C.recPos.length), ihs[s]'(by omega) ∈
      El (motV S P ρ γ n g (args.getD (C.recPos.getD s 0) ∅)) (Hom.id n)) →
    (∀ a ∈ ihs, IsKV n a) → ∀ rs : List (DM n), rs.length = C.dims →
    pappsV n (appsV n (vnth (psRV S bs m ρ γ n g) c) (args ++ ihs)) rs ∈
      El (motV S P ρ γ n g (conV D.ctors n c args rs)) (Hom.id n) ∧
    ∀ n' (h : Hom n' n), res h (pappsV n (appsV n (vnth (psRV S bs m ρ γ n g) c) (args ++ ihs)) rs) =
      pappsV n' (appsV n' (vnth (psRV S bs m ρ γ n' (g.comp h)) c) ((args ++ ihs).map (res h))) (rs.map (·.restr h)) := by
  intro n g c C hC args hat ihs hil hih hihkv rs hrs
  have hC' : D.ctors[c]? = some C := hC
  have hp' := hp.restr h1.1 g
  have hpok' := elimPt_pok hd h1 hp'
  have hc : c < bs.toList.length := by rw [hbsl]; exact (List.getElem?_eq_some_iff.1 hC').1
  have hb : bs.toList[c]? = some (bs.toList[c]) := List.getElem?_eq_getElem hc
  obtain ⟨hbv, hbnat, hty, -⟩ := (h5 c C _ hC' hb).2.2.2 n _ _ hp'
  have hBS : ∀ n' (h : Hom n' n), vnth (psRV S bs m ρ γ n' (g.comp h)) c =
      sem S (bs.toList[c]) n' ((ρ.restr g).restr h) (TEnv.restr (TEnv.restr γ g) h) := by
    intro n' h
    simp only [psRV]
    rw [sem_vnth bs _ _ c hc, IEnv.restr_restr, TEnv.restr_restr]
  have hBS0 : vnth (psRV S bs m ρ γ n g) c = sem S (bs.toList[c]) n (ρ.restr g) (TEnv.restr γ g) := by
    have := hBS n (Hom.id n)
    rwa [Hom.comp_id, IEnv.restr_id, TEnv.restr_id_of_kv hp'.kv] at this
  have hat' : (dataSD (sigUpTo S d) D d n (psRV S ps n (ρ.restr g) (TEnv.restr γ g))).ArgsTyped c C n (Hom.id n) args := by
    rw [dataSD_restr, argsTyped_restr_iff, Hom.comp_id]; exact hat
  have hih' : ∀ s (hs : s < C.recPos.length), ihs[s]'(by omega) ∈
      El (sem S P n (ρ.restr g) (TEnv.cons (TEnv.restr γ g)
        (args[C.recPos.getD s 0]'(by have := recPos_lt hs; have := hat'.1; omega)))) (Hom.id n) := by
    intro s hs
    have := hih s hs
    simp only [motV] at this
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by have := recPos_lt hs; have := hat'.1; omega),
      Option.getD_some] at this
  obtain ⟨hm, hn⟩ := branch_app_mem hS hd hC' ps hpl P (ρ.restr g) (TEnv.restr γ g) hp'.kv hpok' _ hty hbv args ihs rs
    hat' hil hih' hihkv hrs
  rw [hBS0]
  refine ⟨?_, fun n' h => ?_⟩
  · simpa [motV] using hm
  · rw [hn n' h, hBS n' h, hbnat n' h]


include hS hd h1 hpl in
/-- `bndPoint` at a branch environment denotes the boundary value. -/
theorem elimPt_bndPoint {ρ : IEnv m} {γ : ℕ → V} (hp : IsPoint S Φ Γ m ρ γ) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) {args : List V}
    (hat : (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)).ArgsTyped c C m (Hom.id m) args) {ihs : List V}
    {rs : List (DM m)} {ρ' : IEnv m} {γ' : ℕ → V} (hbe : BrEnv C ρ γ args ihs rs ρ' γ') : ∀ t : Tm,
    (BTy (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) c C t →
      Ctor.simpleB D.ctors d D.params.length c C.args.length C t = true →
      t.closedB (D.params.length + C.args.length) C.dims = true →
      sem S (t.subst (bpσ C ps) I.var) m ρ' γ' = evalBnd (conBefore D.ctors c m) args rs t) ∧
    (∀ C' c' j prev, BTyArgs (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) c C C' c' j prev t →
      Ctor.simpleArgs D.ctors d D.params.length c C.args.length C C' j t = true →
      t.closedB (D.params.length + C.args.length) C.dims = true →
      t.subst (bpσ C ps) I.var = Tm.ofList (t.toList.map (·.subst (bpσ C ps) I.var)) ∧
      ∀ i (hi : i < t.toList.length), sem S ((t.toList[i]).subst (bpσ C ps) I.var) m ρ' γ' =
        evalBnd (conBefore D.ctors c m) args rs (t.toList[i])) := by
  have hpok := elimPt_pok hd h1 hp
  have hpsl := elimPt_psl hd hpl h1 hp
  have hl : args.length = C.args.length := hat.1
  refine sem_simple_subst hS hd hC hbe.kv _ hpok args hat rs (bpσ C ps) I.var (fun j hj => ?_) ?_ (fun i hi => hbe.int i hi)
  · simp only [bpσ, if_pos hj, sem_var]
    exact hbe.arg j (by omega)
  · funext k f
    simp only [psRV]
    conv_rhs => rw [hpl, sem_ofList_vlist]
    unfold Ctor.paramVars
    rw [Tm.subst_ofList, sem_ofList_vlist]
    congr 1
    apply List.ext_getElem (by simp [hpsl])
    intro i h1' h2'
    simp only [List.map_map, List.getElem_map, List.getElem_range, Function.comp, Tm.subst, bpσ]
    simp only [List.length_map, List.length_range] at h1'
    rw [if_neg (by omega), List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega),
      List.getElem?_eq_getElem (by omega), Option.getD_some]
    have e := (hbe.restr f).sem_wkN (S := S) (ps.toList[ps.toList.length - 1 - (C.args.length + D.params.length - 1 - i - C.args.length)]'(by omega))
    rw [e]
    congr 2
    omega

end


section tree

variable (hS : SigOK S) {d : ℕ} {D : DataDecl} (hd : S[d]? = some (.data D)) {Ψ : ℕ} {Φ : I} {Γ : Ctx}
  {ps P bs : Tm} {lv : ℕ} (hpl : ps = Tm.ofList ps.toList)
  (h1 : SemTy S Ψ Φ Γ (.data d ps) (.univ D.level)) (h2 : SemTy S Ψ Φ (.data d ps :: Γ) P (.univ lv))
  (hbsl : bs.toList.length = D.ctors.length)
  (h5 : ∀ (c : Nat) (C : Ctor) (b : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      SemTy S Ψ Φ Γ b (D.branchTy d c C ps P))
include hS hd hpl h1 h2 hbsl h5

theorem elim_tree {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) (hIH : ECAll S d D ps P bs Φ Γ c) : ∀ e : Tm,
    (Ctor.simpleB D.ctors d D.params.length c C.args.length C e = true →
      e.closedB (D.params.length + C.args.length) C.dims = true → TreeQ S d D ps P bs Φ Γ c C e) ∧
    (∀ C' j, Ctor.simpleArgs D.ctors d D.params.length c C.args.length C C' j e = true →
      e.closedB (D.params.length + C.args.length) C.dims = true →
      ∀ i (hi : i < e.toList.length), C'.isRec (j + i) = true → TreeQ S d D ps P bs Φ Γ c C (e.toList[i])) := by
  intro e
  induction e with
  | var x =>
    refine ⟨fun hs _ => ?_, fun _ _ hs _ => by simp [Ctor.simpleArgs] at hs⟩
    simp only [Ctor.simpleB, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨hx, hr⟩ := hs
    intro m ρ γ hp args hat hrec rs hrs ρ' γ' hbe _
    have hl : args.length = C.args.length := hat.1
    have hmem : C.args.length - 1 - x ∈ C.recPos := by
      simp only [Ctor.recPos, List.mem_filter, List.mem_range]; exact ⟨by omega, hr⟩
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 (List.isSome_idxOf?.2 hmem)
    obtain ⟨hsl, hss, -⟩ := List.idxOf?_eq_some_iff.1 hs
    have hev : evalBnd (conBefore D.ctors c m) args rs (.var x) = args[C.args.length - 1 - x]'(by omega) := by
      simp only [evalBnd]
      rw [getD_reverse_eq (by omega), res_id (hat.2.1 _ _ (List.getElem?_eq_getElem _) (by rw [hl]; exact hr)).kv]
      congr 1; omega
    rw [hev]
    have hTN := hrec _ _ (List.getElem?_eq_getElem (by omega)) hr
    refine ⟨?_, hTN⟩
    simp only [DataDecl.bndElim, hs, sem_var]
    rw [hbe.ih _ (by simp; omega)]
    simp only [List.getElem_reverse, List.length_map, List.getElem_map]
    have e : C.recPos[C.recPos.length - 1 - (C.recPos.length - 1 - s)]'(by omega) = C.args.length - 1 - x := by
      rw [← hss]; congr 1; omega
    rw [e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  | con d' c' ps' as rs'' _ ihas =>
    refine ⟨fun hs hcl => ?_, fun _ _ hs _ => by simp [Ctor.simpleArgs] at hs⟩
    simp only [Ctor.simpleB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
    obtain ⟨⟨⟨hd', hc'⟩, hps'⟩, hrest⟩ := hs
    cases hC'0 : D.ctors[c']? with
    | none => rw [hC'0] at hrest; simp at hrest
    | some C' =>
    rw [hC'0] at hrest
    simp only [Bool.and_eq_true, beq_iff_eq] at hrest
    obtain ⟨-, hsa⟩ := hrest
    simp only [Tm.closedB, Bool.and_eq_true, List.all_eq_true] at hcl
    obtain ⟨⟨-, hcla⟩, hclr⟩ := hcl
    subst d' ps'
    have hc'b : c' < bs.toList.length := by rw [hbsl]; exact (List.getElem?_eq_some_iff.1 hC'0).1
    have hrecT := ihas.2 C' 0 hsa hcla
    intro m ρ γ hp args hat hrec rs hrs ρ' γ' hbe hb
    obtain ⟨-, C'', hC'', hlen'', hrs''', hargs⟩ := hb
    have hCC : C'' = C' := Option.some.inj ((hC''.symm.trans hC'0 : _))
    subst hCC
    have hok := hS.2 d D hd
    have hpok := elimPt_pok hd h1 hp
    have hgood := (hok.2 m _ hpok).1
    obtain ⟨hP, hPn⟩ := elimPt_motive hd h1 h2 hp
    have hB := elimPt_hB hS hd hpl h1 hbsl h5 hp
    have hev : evalBnd (conBefore D.ctors c m) args rs (.con d c' (Ctor.paramVars D.params.length C.args.length) as rs'') =
        conV D.ctors m c' (as.toList.map (evalBnd (conBefore D.ctors c m) args rs)) (rs''.map (ival (renv rs))) := by
      simp only [evalBnd, conBefore, dif_pos hc', evalBndList_eq]
    have hout := (bnd_delem_aux hgood hC hat.1 hat.2.1 hat.2.2 rs as).2 C'' c' 0 [] hargs
    have hta := nested_argsTyped hgood hC hat.1 hat.2.1 hat.2.2 rs hC'' hlen'' hout
    have hrecv : ∀ i (hi : i < as.toList.length), C''.isRec i = true →
        sem S (D.bndElim C ps bs (as.toList[i])) m ρ' γ' = elimD (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ))
          (motV S P ρ γ) (psRV S bs m ρ γ) m (Hom.id m) (evalBnd (conBefore D.ctors c m) args rs (as.toList[i])) ∧
        ElimTN (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) (motV S P ρ γ) (psRV S bs m ρ γ)
          (evalBnd (conBefore D.ctors c m) args rs (as.toList[i])) := fun i hi hr =>
      hrecT i hi (by simpa using hr) m ρ γ hp args hat hrec rs hrs ρ' γ' hbe
        (btyArgs_rec as 0 [] hargs i hi (by simpa using hr))
    have hEC := hIH m ρ γ hp c' hc' C'' hC'0
    have hrs'v : (rs''.map (ival (renv rs))).length = C''.dims := by simp [hrs''']
    have hrecvals : ∀ j a, (as.toList.map (evalBnd (conBefore D.ctors c m) args rs))[j]? = some a → C''.isRec j = true →
        ElimTN (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) (motV S P ρ γ) (psRV S bs m ρ γ) a := by
      intro j a ha hr
      obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 ha
      simp only [List.length_map] at hj
      simpa using (hrecv j hj hr).2
    have hconeq := hEC m (Hom.id m) _ hta _ hrs'v hrecvals
    have hprops := elimD_conV_props hgood (motV S P ρ γ) (psRV S bs m ρ γ) hP hPn hB hC'' hEC hta.1 hrs'v hta.2.1
      hta.2.2 hrecvals
    rw [hev]
    refine ⟨?_, hprops⟩
    refine Eq.trans ?_ (hconeq.trans (elimBranch_eq (Θ := dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) _ _ hC'' hta.1 _)).symm
    have hbp := (elimPt_bndPoint hS hd hpl h1 hp hC hat hbe as).2 C'' c' 0 [] hargs hsa hcla
    have hL1 : (as.toList.map (DataDecl.bndPoint C ps)).map (fun t => sem S t m ρ' γ') =
        as.toList.map (evalBnd (conBefore D.ctors c m) args rs) := by
      apply List.ext_getElem (by simp)
      intro i h1' h2'
      simp only [List.getElem_map, bndPoint_eq]
      exact hbp.2 i (by simpa using h1')
    have hL2 : (D.bndElimArgs C ps bs C'' 0 as).map (fun t => sem S t m ρ' γ') =
        C''.recPos.map (fun j => elimD (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) (motV S P ρ γ)
          (psRV S bs m ρ γ) m (Hom.id m) ((as.toList.map (evalBnd (conBefore D.ctors c m) args rs)).getD j ∅)) := by
      rw [bndElimArgs_eq, List.map_map, Ctor.recPos, ← hlen'']
      have hf : (List.range as.toList.length).filter (fun i => C''.isRec (0 + i)) =
          (List.range as.toList.length).filter C''.isRec := List.filter_congr fun i _ => by rw [Nat.zero_add]
      rw [hf]
      apply List.map_congr_left
      intro i hi
      simp only [List.mem_filter, List.mem_range] at hi
      simp only [Function.comp]
      rw [List.getD_eq_getElem?_getD (l := as.toList), List.getElem?_eq_getElem hi.1, Option.getD_some,
        (hrecv i hi.1 hi.2).1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi.1),
        Option.getD_some, List.getElem_map]
    have hrsv : rs''.map (ival ρ') = rs''.map (ival (renv rs)) :=
      List.map_congr_left fun r hr => ival_congr_scoped ((I.scopedB_iff _ _).1 (hclr r hr)) fun i hi => hbe.int i hi
    have hBSv : sem S (bs.toList[c']) m ρ γ = vnth (psRV S bs m ρ γ m (Hom.id m)) c' := by
      simp only [psRV, IEnv.restr_id, TEnv.restr_id_of_kv hp.kv]; rw [sem_vnth bs _ _ c' hc'b]
    have hat' : ∀ k (f : Hom k m), (dataSD (sigUpTo S d) D d k (psRV S ps k (ρ.restr f) (TEnv.restr γ f))).ArgsTyped
        c C k (Hom.id k) (args.map (res f)) := by
      intro k f
      rw [dataSD_restr, argsTyped_restr_iff, Hom.comp_id]
      simpa using hgood.argsTyped_res hC hat k f
    have hnat1 : ∀ i (hi : i < as.toList.length), Natural S ((as.toList[i]).subst (bpσ C ps) I.var) m ρ' γ' := by
      intro i hi k f
      have hp' := hp.restr h1.1 f
      have hargs' : BTyArgs (dataSD (sigUpTo S d) D d k (psRV S ps k (ρ.restr f) (TEnv.restr γ f))) c C C'' c' 0 [] as := by
        rw [dataSD_restr]; exact (bty_restr _ f c C as).2 _ _ _ _ hargs
      have e1 := (((elimPt_bndPoint hS hd hpl h1 hp' hC (hat' k f) (hbe.restr f)) as).2 C'' c' 0 [] hargs' hsa hcla).2 i hi
      rw [e1, hbp.2 i hi, res_evalBnd_conBefore]
    have hnat2 : ∀ i (hi : i < as.toList.length), C''.isRec i = true →
        Natural S (D.bndElim C ps bs (as.toList[i])) m ρ' γ' := by
      intro i hi hr k f
      have hp' := hp.restr h1.1 f
      have hrec' : ∀ j a, (args.map (res f))[j]? = some a → C.isRec j = true →
          ElimTN (dataSD (sigUpTo S d) D d k (psRV S ps k (ρ.restr f) (TEnv.restr γ f)))
            (motV S P (ρ.restr f) (TEnv.restr γ f)) (psRV S bs k (ρ.restr f) (TEnv.restr γ f)) a := by
        intro j a ha hrj
        rw [List.getElem?_map] at ha
        obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.1 ha
        have hde := hat.2.1 j a0 ha0 hrj
        exact (elimTN_restr_pt d D ps P bs ρ γ (hP m (Hom.id m) a0 hde) (hPn m (Hom.id m) a0 hde)
          (hrec j a0 ha0 hrj) f).1
      have hihs : (C.recPos.map fun j => elimD (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) (motV S P ρ γ)
            (psRV S bs m ρ γ) m (Hom.id m) (args.getD j ∅)).map (res f) =
          C.recPos.map fun j => elimD (dataSD (sigUpTo S d) D d k (psRV S ps k (ρ.restr f) (TEnv.restr γ f)))
            (motV S P (ρ.restr f) (TEnv.restr γ f)) (psRV S bs k (ρ.restr f) (TEnv.restr γ f)) k (Hom.id k)
            ((args.map (res f)).getD j ∅) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro j hj
        simp only [Ctor.recPos, List.mem_filter, List.mem_range] at hj
        have hjl : j < args.length := by rw [hat.1]; exact hj.1
        have hde := hat.2.1 j _ (List.getElem?_eq_getElem hjl) hj.2
        simp only [Function.comp]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some, List.getD_eq_getElem?_getD,
          List.getElem?_map, List.getElem?_eq_getElem hjl, Option.map_some, Option.getD_some]
        exact (elimTN_restr_pt d D ps P bs ρ γ (hP m (Hom.id m) _ hde) (hPn m (Hom.id m) _ hde)
          (hrec j _ (List.getElem?_eq_getElem hjl) hj.2) f).2
      have hbe' := hbe.restr f
      rw [hihs] at hbe'
      have hbty := btyArgs_rec as 0 [] hargs i hi (by simpa using hr)
      have hbty' : BTy (dataSD (sigUpTo S d) D d k (psRV S ps k (ρ.restr f) (TEnv.restr γ f))) c C (as.toList[i]) := by
        rw [dataSD_restr]; exact (bty_restr _ f c C _).1 hbty
      have e1 := (hrecT i hi (by simpa using hr) k _ _ hp' _ (hat' k f) hrec' _ (by simp [hrs]) _ _ hbe' hbty').1
      have hde_i := (hout i hi).1 (by simpa using hr)
      rw [e1, (hrecv i hi hr).1, ← res_evalBnd_conBefore]
      exact ((elimTN_restr_pt d D ps P bs ρ γ (hP m (Hom.id m) _ hde_i) (hPn m (Hom.id m) _ hde_i)
        (hrecv i hi hr).2 f).2).symm
    have hnat : ∀ t ∈ as.toList.map (DataDecl.bndPoint C ps) ++ D.bndElimArgs C ps bs C'' 0 as, Natural S t m ρ' γ' := by
      intro t ht
      rcases List.mem_append.1 ht with ht | ht
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
        simp only [List.getElem_map, bndPoint_eq]; exact hnat1 i (by simpa using hi)
      · rw [bndElimArgs_eq] at ht
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ht
        simp only [List.mem_filter, List.mem_range, Nat.zero_add] at hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi.1, Option.getD_some]
        exact hnat2 i hi.1 hi.2
    have hb' : bs.toList[c']? = some (bs.toList[c']) := List.getElem?_eq_getElem hc'b
    simp only [DataDecl.bndElim, hC'0, hb']
    rw [sem_papps, sem_apps_of_nat _ _ hnat, hbe.sem_wkN, List.map_append, hL1, hL2, hrsv, hBSv]
    rfl
  | tcons a as iha ihas =>
    refine ⟨fun hs => by simp [Ctor.simpleB] at hs, fun C' j hs hcl i hi hr => ?_⟩
    simp only [Ctor.simpleArgs, Bool.and_eq_true] at hs
    obtain ⟨hs1, hs2⟩ := hs
    simp only [Tm.closedB, Bool.and_eq_true] at hcl
    cases i with
    | zero =>
      simp only [Tm.toList, List.getElem_cons_zero]
      rw [Nat.add_zero] at hr
      rw [if_pos hr] at hs1
      exact iha.1 hs1 hcl.1
    | succ i =>
      simp only [Tm.toList, List.getElem_cons_succ]
      exact ihas.2 C' (j + 1) hs2 hcl.2 i (by simp [Tm.toList] at hi; omega) (by rw [← hr]; congr 1; omega)
  | tnil => exact ⟨fun hs => by simp [Ctor.simpleB] at hs, fun _ _ _ _ i hi => by simp [Tm.toList] at hi⟩
  | _ =>
    exact ⟨fun hs => by simp [Ctor.simpleB] at hs, fun _ _ hs => by simp [Ctor.simpleArgs] at hs⟩

end tree

end

end Model
