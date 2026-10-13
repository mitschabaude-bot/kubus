import Model.Rules.InterpFree
import Model.DataVt

/-!
# Denotations of the terms of inductive types
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

theorem sigV_entry_data {d : ℕ} {D : DataDecl} (h : S[d]? = some (.data D)) :
    (∀ m ps, (sigV S).dat m d ps =
      if ParamsOK (sigUpTo S d) D m ps then dataC (dataSD (sigUpTo S d) D d m ps) else ∅) ∧
    (∀ m c ps args rs, (sigV S).con m d c ps args rs = if ConGuard (sigUpTo S d) D d m ps c args rs then
      conV D.ctors m c (plist (args m (Hom.id m)) (D.ctors.getD c default).args.length) rs else ∅) ∧
    (∀ m ps P bs t, (sigV S).elim m d ps P bs t = if ElimGuard (sigUpTo S d) D d m ps P bs t then
      elimD (dataSD (sigUpTo S d) D d m ps) P bs m (Hom.id m) (t m (Hom.id m)) else ∅) := by
  obtain ⟨hk, -⟩ := List.getElem?_eq_some_iff.1 h
  have ha := sigUpTo_agree S S.length hk
  refine ⟨fun m ps => ?_, fun m c ps args rs => ?_, fun m ps P bs t => ?_⟩
  · rw [sigV, ← ha.2.1 m d ps (by omega)]
    simp only [sigUpTo, SigV.set, if_pos rfl, h, entrySem, dataSem, if_true]
  · rw [sigV, ← ha.2.2.1 m d c ps args rs (by omega)]
    simp only [sigUpTo, SigV.set, if_pos rfl, h, entrySem, dataSem, if_true]
  · rw [sigV, ← ha.2.2.2 m d ps P bs t (by omega)]
    simp only [sigUpTo, SigV.set, if_pos rfl, h, entrySem, dataSem, if_true]

/-- The parameters of `data d ps` etc. at a point, at all restrictions. -/
abbrev psRV (S : Sig) (ps : Tm) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V) : RV m :=
  fun k f => sem S ps k (ρ.restr f) (TEnv.restr γ f)

theorem sem_data {d : ℕ} {D : DataDecl} (h : S[d]? = some (.data D)) (ps : Tm) (ρ : IEnv m) (γ : ℕ → V) :
    sem S (.data d ps) m ρ γ = if ParamsOK (sigUpTo S d) D m (psRV S ps m ρ γ) then
      dataC (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) else ∅ :=
  (sigV_entry_data h).1 m _

theorem sem_data_of {d : ℕ} {D : DataDecl} (h : S[d]? = some (.data D)) {ps : Tm} {ρ : IEnv m} {γ : ℕ → V}
    (hp : ParamsOK (sigUpTo S d) D m (psRV S ps m ρ γ)) :
    sem S (.data d ps) m ρ γ = dataC (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ)) := by
  rw [sem_data h, if_pos hp]

/-- A type former that denotes a code has valid parameters. -/
theorem paramsOK_of_sem_data {d : ℕ} {D : DataDecl} (h : S[d]? = some (.data D)) {ps : Tm} {ρ : IEnv m}
    {γ : ℕ → V} (hne : sem S (.data d ps) m ρ γ ≠ ∅) : ParamsOK (sigUpTo S d) D m (psRV S ps m ρ γ) := by
  rw [sem_data h] at hne
  by_contra hc; exact hne (if_neg hc)

theorem sem_con {d : ℕ} {D : DataDecl} (h : S[d]? = some (.data D)) (c : ℕ) (ps args : Tm) (rs : List I)
    (ρ : IEnv m) (γ : ℕ → V) :
    sem S (.con d c ps args rs) m ρ γ =
      if ConGuard (sigUpTo S d) D d m (psRV S ps m ρ γ) c (psRV S args m ρ γ) (rs.map (ival ρ)) then
      conV D.ctors m c (plist (sem S args m (ρ.restr (Hom.id m)) (TEnv.restr γ (Hom.id m)))
        (D.ctors.getD c default).args.length) (rs.map (ival ρ)) else ∅ :=
  (sigV_entry_data h).2.1 m c _ _ _

theorem sem_con_of {d : ℕ} {D : DataDecl} (h : S[d]? = some (.data D)) {c : ℕ} {ps args : Tm} {rs : List I}
    {ρ : IEnv m} {γ : ℕ → V}
    (hg : ConGuard (sigUpTo S d) D d m (psRV S ps m ρ γ) c (psRV S args m ρ γ) (rs.map (ival ρ))) :
    sem S (.con d c ps args rs) m ρ γ =
      conV D.ctors m c (plist (sem S args m (ρ.restr (Hom.id m)) (TEnv.restr γ (Hom.id m)))
        (D.ctors.getD c default).args.length) (rs.map (ival ρ)) := by
  rw [sem_con h, if_pos hg]

theorem conGuard_of_sem {d : ℕ} {D : DataDecl} (h : S[d]? = some (.data D)) {c : ℕ} {ps args : Tm} {rs : List I}
    {ρ : IEnv m} {γ : ℕ → V} (hne : sem S (.con d c ps args rs) m ρ γ ≠ ∅) :
    ConGuard (sigUpTo S d) D d m (psRV S ps m ρ γ) c (psRV S args m ρ γ) (rs.map (ival ρ)) := by
  rw [sem_con h] at hne; by_contra hc; exact hne (if_neg hc)

theorem sem_elim {d : ℕ} {D : DataDecl} (h : S[d]? = some (.data D)) (ps P bs t : Tm) (ρ : IEnv m) (γ : ℕ → V) :
    sem S (.elim d ps P bs t) m ρ γ =
      if ElimGuard (sigUpTo S d) D d m (psRV S ps m ρ γ)
        (fun k f a => sem S P k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)) (psRV S bs m ρ γ) (psRV S t m ρ γ) then
      elimD (dataSD (sigUpTo S d) D d m (psRV S ps m ρ γ))
        (fun k f a => sem S P k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)) (psRV S bs m ρ γ) m (Hom.id m)
        (sem S t m (ρ.restr (Hom.id m)) (TEnv.restr γ (Hom.id m))) else ∅ :=
  (sigV_entry_data h).2.2 m _ _ _ _

/-! ### List terms and telescopes -/

theorem sem_vnth (ts : Tm) (ρ : IEnv m) (γ : ℕ → V) :
    ∀ i (hi : i < ts.toList.length), vnth (sem S ts m ρ γ) i = sem S (ts.toList[i]) m ρ γ := by
  induction ts with
  | tcons a as _ ihas =>
    intro i hi
    cases i with
    | zero => show π1 (ZFSet.pair _ _) = _; simp [Tm.toList]
    | succ i =>
      show vnth (π2 (ZFSet.pair _ _)) i = _
      simp only [π2_pair]
      simpa [Tm.toList] using ihas i (by simpa [Tm.toList] using hi)
  | _ => intro i hi; simp [Tm.toList] at hi

theorem plist_sem (ts : Tm) (ρ : IEnv m) (γ : ℕ → V) {n : ℕ} (hn : ts.toList.length = n) :
    plist (sem S ts m ρ γ) n = ts.toList.map (fun t => sem S t m ρ γ) := by
  subst hn
  apply List.ext_getElem (by simp [plist])
  intro i h1 h2
  simp only [plist, List.getElem_map, List.getElem_range]
  exact sem_vnth ts ρ γ i (by simpa using h2)

theorem SemTele.toList {Ψ : ℕ} {Φ : I} {Γ : Ctx} : ∀ {Δ : List Tm} {ts : Tm} {prev : List Tm},
    SemTele S Ψ Φ Γ ts Δ prev → ts.toList.length = Δ.length ∧ ts = Tm.ofList ts.toList ∧
      ∀ i (hi : i < Δ.length) (hi' : i < ts.toList.length),
        SemTy S Ψ Φ Γ (ts.toList[i]) (Δ[i].substList ((ts.toList.take i).reverse ++ prev))
  | [], ts, prev, h => by
    cases ts <;> simp_all [SemTele, Tm.toList, Tm.ofList]
  | A :: Δ, ts, prev, h => by
    cases ts with
    | tcons a as =>
      obtain ⟨h1, h2⟩ := h
      obtain ⟨e1, e2, e3⟩ := SemTele.toList h2
      refine ⟨by simp [Tm.toList, e1], by simp only [Tm.toList, Tm.ofList]; rw [← e2], fun i hi hi' => ?_⟩
      cases i with
      | zero => simpa [Tm.toList] using h1
      | succ i =>
        have := e3 i (by simpa using hi) (by simpa [Tm.toList] using hi')
        simpa [Tm.toList, List.take_succ_cons, List.reverse_cons, List.append_assoc] using this
    | _ => simp [SemTele] at h

theorem SemTele.wf {Ψ : ℕ} {Φ : I} {Γ : Ctx} : ∀ {Δ : List Tm} {ts : Tm} {prev : List Tm},
    SemTele S Ψ Φ Γ ts Δ prev → SemWf S Ψ Φ Γ
  | [], ts, prev, h => by cases ts <;> simp_all [SemTele]
  | A :: Δ, ts, prev, h => by
    cases ts with
    | tcons a as => exact h.1.1
    | _ => simp [SemTele] at h

/-- The value of a variable environment built from a list (most recent first). -/
theorem sem_substList_env (L : List Tm) (ρ : IEnv m) (γ : ℕ → V) (x : ℕ) (hx : x < L.length) :
    sem S ((fun j => L.getD j (.var (j - L.length))) x) m ρ γ = sem S (L[x]) m ρ γ := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx]

theorem natural_substList {L : List Tm} {ρ : IEnv m} {γ : ℕ → V} (hL : ∀ t ∈ L, Natural S t m ρ γ) :
    ∀ x, Natural S ((fun j => L.getD j (.var (j - L.length))) x) m ρ γ := by
  intro x
  by_cases hx : x < L.length
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx, Option.getD_some]
    exact hL _ (List.getElem_mem hx)
  · have e : L.getD x (.var (x - L.length)) = .var (x - L.length) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hx)]
    show Natural S (L.getD x _) m ρ γ
    rw [e]; intro k f; rfl

/-- **Parameters**: a well-typed parameter list gives valid semantic parameters. -/
theorem listLen_sem_ofList (L : List Tm) (ρ : IEnv m) (γ : ℕ → V) : ListLen (sem S (Tm.ofList L) m ρ γ) L.length := by
  induction L with
  | nil => rfl
  | cons t L ih => exact ⟨⟨_, _, rfl⟩, by simpa [Tm.ofList, sem, interp] using ih⟩

theorem paramsOK_of_tele {d : ℕ} {D : DataDecl} (hd : d ≤ S.length) (hsyn : DataSyn d D) {Ψ : ℕ} {Φ : I} {Γ : Ctx}
    {ps : Tm} (h : SemTele S Ψ Φ Γ ps D.params []) {m : ℕ} {ρ : IEnv m} {γ : ℕ → V} (hp : IsPoint S Φ Γ m ρ γ) :
    ParamsOK (sigUpTo S d) D m (psRV S ps m ρ γ) := by
  have hwf := h.wf
  obtain ⟨hlen, hofl, hty⟩ := h.toList
  intro n g
  have hpn := hp.restr hwf g
  refine ⟨?_, fun i hi => ?_, fun n' h' i hi => ?_⟩
  · show ListLen (sem S ps _ _ _) _
    rw [hofl, ← hlen]; exact listLen_sem_ofList _ _ _
  have hσ : interp (sigUpTo S d) univC TyCode (D.params[i]) = sem S (D.params[i]) :=
    interp_congr_cst _ _ (sigUpTo_agree S S.length hd) _ (hsyn.2.1 i _ (List.getElem?_eq_getElem hi)).2
  rw [hσ]
  · have hti := hty i hi (by omega)
    obtain ⟨hmem, -, htyok, -⟩ := hti.2.2.2 n _ _ hpn
    rw [sem_vnth ps _ _ i (by omega)]
    refine ⟨htyok.fib.elKV _ _ _ hmem, ?_⟩
    convert hmem using 2
    simp only [List.append_nil] at hti ⊢
    have hnat : ∀ t ∈ ps.toList, Natural S t n (ρ.restr g) (TEnv.restr γ g) := fun t ht => by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
      exact ((hty j (by omega) hj).2.2.2 n _ _ hpn).2.1
    rw [Tm.substList, sem_subst S _ n _ _ _ _ (natural_substList fun t ht =>
      hnat t (List.mem_of_mem_take (List.mem_reverse.1 ht)))]
    obtain ⟨hcl, -⟩ := hsyn.2.1 i _ (List.getElem?_eq_getElem hi)
    refine interp_congr_closed _ _ _ _ i 0 hcl n _ _ _ _ (fun _ h => absurd h (by omega)) (fun x hx => ?_)
    have hx' : x < ((ps.toList.take i).reverse).length := by simp; omega
    rw [sem_substList_env _ _ _ x hx']
    simp only [argEnv, List.reverse_nil, List.append_nil, plist]
    rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by simp; omega)]
    simp only [List.length_map, List.length_range, List.getElem?_map, List.getElem?_range (by omega : i - 1 - x < i),
      Option.map_some, Option.getD_some]
    rw [sem_vnth ps _ _ _ (by omega), List.getElem_reverse, List.getElem_take]
    congr 2; simp; omega
  · rw [sem_vnth ps _ _ i (by omega), sem_vnth ps _ _ i (by omega)]
    have := ((hty i hi (by omega)).2.2.2 n _ _ hpn).2.1 n' h'
    rw [← this, IEnv.restr_restr, TEnv.restr_restr]

end

end Model

namespace Model

open KubusCore

/-- Denotations agree for terms that only use the entries below `d`, constants at `d`, and do not
mention the inductive type `d`. -/
theorem interp_congr_md {cst cst' : SigV} (uc : ℕ → ℕ → V) (good : ℕ → V → Prop) {d : ℕ}
    (hc : SigV.AgreeLt d cst cst') (hcd : ∀ m, cst.cst m d = cst'.cst m d) :
    ∀ (t : Tm), t.ConstsLt (d + 1) → t.mentionsData d = false → interp cst uc good t = interp cst' uc good t := by
  intro t
  induction t with
  | const j =>
    intro h _; funext m ρ γ
    simp only [Tm.ConstsLt] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact hc.1 m j h
    · exact hcd m
  | var _ | univ _ | abort | tnil => intros; rfl
  | pi _ _ iA iB | sigma _ _ iA iB | lam _ _ iA iB | app _ _ iA iB | pair _ _ iA iB | tcons _ _ iA iB =>
    intro h hm; simp only [Tm.mentionsData, Bool.or_eq_false_iff] at hm
    funext m ρ γ; simp only [interp]; rw [iA h.1 hm.1, iB h.2 hm.2]
  | fst _ ip | snd _ ip | plam _ ip | ipi _ ip | papp _ _ ip =>
    intro h hm; simp only [Tm.mentionsData] at hm
    funext m ρ γ; simp only [interp]; rw [ip h hm]
  | unglue _ _ _ ie ig =>
    intro h hm; simp only [Tm.mentionsData, Bool.or_eq_false_iff] at hm
    funext m ρ γ; simp only [interp]; rw [ie h.1 hm.1, ig h.2 hm.2]
  | path _ _ _ iA ia ib | hcomp _ _ _ _ iA ia ib | glue _ _ _ _ iA ia ib | glueEl _ _ _ _ iA ia ib =>
    intro h hm; simp only [Tm.mentionsData, Bool.or_eq_false_iff] at hm
    funext m ρ γ; simp only [interp]; rw [iA h.1 hm.1.1, ia h.2.1 hm.1.2, ib h.2.2 hm.2]
  | split _ _ _ _ it iu | transp _ _ _ it iu =>
    intro h hm; simp only [Tm.mentionsData, Bool.or_eq_false_iff] at hm
    funext m ρ γ; simp only [interp]; rw [it h.1 hm.1, iu h.2 hm.2]
  | data j _ ip =>
    intro h hm; simp only [Tm.mentionsData, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hm
    funext m ρ γ; simp only [interp]; rw [ip h.2 hm.2]; exact hc.2.1 _ _ _ (by have := h.1; omega)
  | con j _ _ _ _ ip ia =>
    intro h hm; simp only [Tm.mentionsData, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hm
    funext m ρ γ; simp only [interp]; rw [ip h.2.1 hm.1.2, ia h.2.2 hm.2]
    exact hc.2.2.1 _ _ _ _ _ _ (by have := h.1; omega)
  | elim j _ _ _ _ ip iP ib it =>
    intro h hm; simp only [Tm.mentionsData, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hm
    funext m ρ γ; simp only [interp]
    rw [ip h.2.1 hm.1.1.1.2, iP h.2.2.1 hm.1.1.2, ib h.2.2.2.1 hm.1.2, it h.2.2.2.2 hm.2]
    exact hc.2.2.2 _ _ _ _ _ _ (by have := h.1; omega)

theorem sigUpTo_cst_ge (S : Sig) : ∀ k j m, k ≤ j → (sigUpTo S k).cst m j = ∅
  | 0, _, _, _ => rfl
  | k + 1, j, m, h => by
    simp only [sigUpTo, SigV.set, if_neg (show j ≠ k by omega)]
    exact sigUpTo_cst_ge S k j m (by omega)

theorem sigV_cst_data {S : Sig} {d : ℕ} {D : DataDecl} (h : S[d]? = some (.data D)) (m : ℕ) :
    (sigV S).cst m d = ∅ := by
  obtain ⟨hk, -⟩ := List.getElem?_eq_some_iff.1 h
  rw [sigV, ← (sigUpTo_agree S S.length hk).1 m d (by omega)]
  simp [sigUpTo, SigV.set, h, entrySem, dataSem]

end Model
