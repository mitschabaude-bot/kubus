import Model.Rules.DataLemmas

/-!
# Rules of inductive types (phase 2)

One lemma per rule of inductive types. Work in progress: the lemmas proved by `sorry` are the
rules not yet validated (the model of inductive types is being built).
-/

set_option autoImplicit false

namespace Model

open KubusCore KubusCore.Tm

noncomputable section

variable {S : Sig} {k m n : ℕ}

/-! ### Telescopes -/

theorem sem_HasTele_nil {Ψ Φ Γ prev} (h0 : SemWf S Ψ Φ Γ) : SemTele S Ψ Φ Γ .tnil [] prev := h0

theorem sem_HasTele_cons {Ψ Φ Γ a as A Δ prev} (h0 : SemTy S Ψ Φ Γ a (A.substList prev))
    (h1 : SemTele S Ψ Φ Γ as Δ (a :: prev)) : SemTele S Ψ Φ Γ (.tcons a as) (A :: Δ) prev := ⟨h0, h1⟩

theorem sem_EqTele_nil {Ψ Φ Γ prev} (h0 : SemWf S Ψ Φ Γ) : SemEqTele S Ψ Φ Γ .tnil .tnil [] prev := h0

theorem sem_EqTele_cons {Ψ Φ Γ a a' as as' A Δ prev} (h0 : SemEq S Ψ Φ Γ a a' (A.substList prev))
    (h1 : SemEqTele S Ψ Φ Γ as as' Δ (a :: prev)) :
    SemEqTele S Ψ Φ Γ (.tcons a as) (.tcons a' as') (A :: Δ) prev := ⟨h0, h1⟩

/-! ### Typing -/

theorem constsLt_ofList {n : ℕ} : ∀ {L : List Tm}, (∀ t ∈ L, t.ConstsLt n) → (Tm.ofList L).ConstsLt n
  | [], _ => trivial
  | t :: L, h => ⟨h t List.mem_cons_self, constsLt_ofList fun u hu => h u (List.mem_cons_of_mem _ hu)⟩

theorem SemTele.constsLt {Ψ Φ Γ ts Δ prev} (h : SemTele S Ψ Φ Γ ts Δ prev) : ts.ConstsLt S.length := by
  obtain ⟨hlen, he, hty⟩ := h.toList
  rw [he]
  refine constsLt_ofList fun t ht => ?_
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  exact (hty i (by omega) hi).2.1

theorem tyOK_univ {l : ℕ} (hl : l + 1 ≤ maxLevel) (ρ : IEnv m) (γ : ℕ → V) : TyOK S (.univ l) m ρ γ :=
  ⟨l, by omega, Or.inr rfl⟩

theorem natural_univ (l : ℕ) (ρ : IEnv m) (γ : ℕ → V) : Natural S (.univ l) m ρ γ := fun k f => by
  simp [res_univC]

theorem dataSD_restr (σ : SigV) (D : DataDecl) (d : ℕ) (ps : Tm) (ρ : IEnv m) (γ : ℕ → V) (f : Hom k m) :
    dataSD σ D d k (psRV S ps k (ρ.restr f) (TEnv.restr γ f)) = (dataSD σ D d m (psRV S ps m ρ γ)).restr f := by
  simp only [dataSD, SData.restr, psRV, IEnv.restr_restr, TEnv.restr_restr]

theorem sem_HasTy_data {Ψ Φ Γ d D ps} (hS : SigOK S) (h0 : S[d]? = some (.data D)) (h1 : D.level + 1 ≤ maxLevel)
    (h2 : SemTele S Ψ Φ Γ ps D.params []) : SemTy S Ψ Φ Γ (data d ps) (univ D.level) := by
  have hd : d < S.length := (List.getElem?_eq_some_iff.1 h0).1
  have hok := hS.2 d D h0
  refine ⟨h2.wf, ⟨hd, h2.constsLt⟩, trivial, fun m ρ γ hp => ⟨?_, fun k f => ?_, tyOK_univ h1 ρ γ, natural_univ _ ρ γ⟩⟩
  · obtain ⟨hgood, hty⟩ := hok.2 m _ (paramsOK_of_tele hd.le hok.1 h2 hp)
    rw [sem_data_of h0 (paramsOK_of_tele hd.le hok.1 h2 hp), sem_univ, mem_El_univ_iff]
    exact ⟨dataC_mem_Vt (by unfold maxLevel at h1; omega) fun c j n g pre => (hty c j n g pre).1,
      WFI.data _ hgood.toGoodCore fun c j n g pre hpv => (hty c j n g pre).2 hpv⟩
  · rw [sem_data_of h0 (paramsOK_of_tele hd.le hok.1 h2 (hp.restr h2.wf f)),
      sem_data_of h0 (paramsOK_of_tele hd.le hok.1 h2 hp), res_dataC, dataSD_restr]

theorem sem_HasTy_con {Ψ Φ Γ d D c C ps args rs} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : D.ctors[c]? = some C) (hpl : ps = Tm.ofList ps.toList) (h2 : SemTy S Ψ Φ Γ (data d ps) (univ D.level))
    (h3 : SemTele S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse)
    (h4 : rs.length = C.dims) (h5 : ∀ r ∈ rs, r.Scoped Ψ) :
    SemTy S Ψ Φ Γ (con d c ps args rs) (data d ps) := by
  have hd : d < S.length := (List.getElem?_eq_some_iff.1 h0).1
  have hok := hS.2 d D h0
  obtain ⟨hlen, hofl, hty⟩ := h3.toList
  simp only [Ctor.argTys, List.length_map, List.length_range] at hlen
  refine ⟨h3.wf, ⟨hd, h2.2.1.2, h3.constsLt⟩, h2.2.1, fun m ρ γ hp => ?_⟩
  obtain ⟨hmemU, hnatD, hTyU, -⟩ := h2.2.2.2 m ρ γ hp
  have hpok := paramsOK_of_sem_data h0 (TyOK.ne_empty hTyU hmemU)
  obtain ⟨hgood, -⟩ := hok.2 m _ hpok
  have hρ : ρ.restr (Hom.id m) = ρ := IEnv.restr_id ρ
  have hγ : TEnv.restr γ (Hom.id m) = γ := TEnv.restr_id_of_kv hp.kv
  -- the parameters
  have hPS : psRV S ps m ρ γ m (Hom.id m) = sem S ps m ρ γ := by simp only [psRV, hρ, hγ]
  have hpsl : ps.toList.length = D.params.length := by
    have h1 := (hpok m (Hom.id m)).1
    rw [hPS, hpl] at h1
    exact listLen_unique (listLen_sem_ofList _ _ _) h1
  have hpsnat : ∀ t ∈ ps.toList, Natural S t m ρ γ := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    intro k f
    have e := (hpok m (Hom.id m)).2.2 k f i (by omega)
    simp only [psRV, Hom.id_comp, hρ, hγ] at e
    rw [sem_vnth ps _ _ i hi, sem_vnth ps _ _ i hi] at e
    exact e
  -- the arguments
  have hargsel : ∀ i (hi : i < args.toList.length), SemTy S Ψ Φ Γ (args.toList[i])
      ((C.argTy d D.params.length i).substList ((args.toList.take i).reverse ++ ps.toList.reverse)) := by
    intro i hi
    have := hty i (by simp [Ctor.argTys]; omega) hi
    simpa [Ctor.argTys] using this
  set vals := args.toList.map fun t => sem S t m ρ γ with hvals
  have hsemcon : sem S (con d c ps args rs) m ρ γ = conV D.ctors m c vals (rs.map (ival ρ)) := by
    rw [sem_con h0, hρ, hγ, getD_ctors h1, plist_sem _ _ _ (by omega)]
  have hpt : ∀ i (hi : i < args.toList.length) (hA : ∃ A, C.args[i]? = some (.point A)),
      vals[i]'(by simp [vals]; omega) ∈ El (argTyRaw (sigUpTo S d) D d c i m (sem S ps m ρ γ) vals) (Hom.id m) := by
    intro i hi ⟨A, hA⟩
    have := ((hargsel i hi).2.2.2 m ρ γ hp).1
    have harg : C.argTy d D.params.length i = A := by simp [Ctor.argTy, hA]
    rw [harg] at this
    rw [sem_argTy_subst h0 hok.1 h1 hA _ _ (by simp; omega) hpsl (fun t ht => ?_), ← hpl] at this
    · simp only [List.reverse_reverse] at this
      rw [List.getElem_map]
      rw [show (List.map (fun t => sem S t m ρ γ) (List.take i args.toList)) = vals.take i by
        simp [vals, List.map_take]] at this
      have e : argTyRaw (sigUpTo S d) D d c i m (sem S ps m ρ γ) (vals.take i) =
          argTyRaw (sigUpTo S d) D d c i m (sem S ps m ρ γ) vals := argTyRaw_take_eq (by simp [List.take_take])
      rwa [e] at this
    · rcases List.mem_append.1 ht with ht | ht
      · obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_take (List.mem_reverse.1 ht))
        exact ((hargsel q hq).2.2.2 m ρ γ hp).2.1
      · exact hpsnat t (List.mem_reverse.1 ht)
  refine ⟨?_, fun k f => ?_, h2.ty_at hp⟩
  · rw [hsemcon, sem_data_of h0 hpok, mem_El_dataC]
    refine DElem.con h1 (by simp [vals]; omega) (by simp [h4]) (fun j a ha hr => ?_) (fun j a ha hr => ?_)
    · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 ha
      simp only [vals, List.length_map] at hj
      have := ((hargsel j hj).2.2.2 m ρ γ hp).1
      have harg : C.argTy d D.params.length j = .data d (Ctor.paramVars D.params.length j) := by
        have hjC : j < C.args.length := by omega
        cases h' : C.args[j]'hjC with
        | point A => simp [Ctor.isRec, List.getElem?_eq_getElem hjC, h'] at hr
        | recur => simp [Ctor.argTy, List.getElem?_eq_getElem hjC, h']
      rw [harg, Tm.substList, show (Tm.data d (Ctor.paramVars D.params.length j)).subst _ I.var =
          Tm.data d ((Ctor.paramVars D.params.length j).substList
            ((args.toList.take j).reverse ++ ps.toList.reverse)) from rfl] at this
      have e := paramVars_substList ps.toList (args.toList.take j).reverse
      rw [hpsl, show ((args.toList.take j).reverse).length = j by simp; omega] at e
      rw [e, ← hpl, sem_data_of h0 hpok, mem_El_dataC] at this
      simpa [vals] using this
    · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 ha
      simp only [vals, List.length_map] at hj
      have hjC : j < C.args.length := by omega
      obtain ⟨A, hA⟩ : ∃ A, C.args[j]? = some (.point A) := by
        cases h' : C.args[j]'hjC with
        | point A => exact ⟨A, by rw [List.getElem?_eq_getElem hjC, h']⟩
        | recur => simp [Ctor.isRec, List.getElem?_eq_getElem hjC, h'] at hr
      show _ ∈ El (argTySem (sigUpTo S d) D d c j m (psRV S ps m ρ γ m (Hom.id m)) (vals.take j)) _
      have hcond : j < (D.ctors.getD c default).args.length ∧ (D.ctors.getD c default).isRec j = false ∧
          argPreValid (sigUpTo S d) D d c j m (sem S ps m ρ γ) (vals.take j) := by
        refine ⟨by rw [getD_ctors h1]; omega, by rw [getD_ctors h1]; exact hr, by simp [vals]; omega,
          fun i hi hip hri => ?_⟩
        rw [argTyRaw_take_eq (pre' := vals) (by simp [List.take_take]; omega), List.getElem_take]
        rw [getD_ctors h1] at hri
        have hiC : i < C.args.length := by omega
        obtain ⟨Ai, hAi⟩ : ∃ A, C.args[i]? = some (.point A) := by
          cases h' : C.args[i]'hiC with
          | point A => exact ⟨A, by rw [List.getElem?_eq_getElem hiC, h']⟩
          | recur => simp [Ctor.isRec, List.getElem?_eq_getElem hiC, h'] at hri
        exact hpt i (by omega) ⟨Ai, hAi⟩
      rw [hPS, argTySem_eq, if_pos hcond, argTyRaw_take_eq (pre' := vals) (by simp [List.take_take])]
      exact hpt j hj ⟨A, hA⟩
  · rw [hsemcon, sem_con h0, res_conV, TEnv.restr_restr, Hom.comp_id, IEnv.restr_restr, Hom.comp_id,
      getD_ctors h1, plist_sem _ _ _ (by omega)]
    congr 1
    · simp only [vals, List.map_map]
      exact List.map_congr_left fun t ht => by
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
        exact ((hargsel i hi).2.2.2 m ρ γ hp).2.1 k f
    · simp only [List.map_map]
      exact List.map_congr_left fun r _ => (ival.restr ρ r f)

theorem sem_HasTy_elim {Ψ Φ Γ d D ps P bs t m} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (hpl : ps = Tm.ofList ps.toList) (h1 : SemTy S Ψ Φ Γ (data d ps) (univ D.level)) (h2 : SemTy S Ψ Φ (data d ps :: Γ) P (univ m))
    (h3 : bs = Tm.ofList bs.toList) (h4 : bs.toList.length = D.ctors.length)
    (h5 : ∀ (c : Nat) (C : Ctor) (b : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      SemTy S Ψ Φ Γ b (D.branchTy d c C ps P))
    (h6 : ∀ (c : Nat) (C : Ctor) (b : Tm) (k : Nat) (ψ : I) (e : Tm), D.ctors[c]? = some C →
      bs.toList[c]? = some b → C.bnd[k]? = some (ψ, e) →
      SemEq S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)
        (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps P))
    (h7 : SemTy S Ψ Φ Γ t (data d ps)) : SemTy S Ψ Φ Γ (elim d ps P bs t) (P.inst t) := by
  sorry

/-! ### Congruence -/

theorem sem_EqTm_data {Ψ Φ Γ d D ps ps'} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : SemTy S Ψ Φ Γ (data d ps) (univ D.level)) (h2 : SemTy S Ψ Φ Γ (data d ps') (univ D.level))
    (h3 : SemEqTele S Ψ Φ Γ ps ps' D.params []) : SemEq S Ψ Φ Γ (data d ps) (data d ps') (univ D.level) := by
  sorry

theorem sem_EqTm_con {Ψ Φ Γ d D c C ps ps' args args' rs rs'} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : D.ctors[c]? = some C) (h2 : SemTy S Ψ Φ Γ (con d c ps args rs) (data d ps))
    (h3 : SemTy S Ψ Φ Γ (con d c ps' args' rs') (data d ps)) (h4 : SemEqTele S Ψ Φ Γ ps ps' D.params [])
    (h5 : SemEqTele S Ψ Φ Γ args args' (C.argTys d D.params.length) ps.toList.reverse)
    (h6 : rs.length = rs'.length) (h7 : ∀ (k : Nat) (r r' : I), rs[k]? = some r → rs'[k]? = some r' → I.Eq r r') :
    SemEq S Ψ Φ Γ (con d c ps args rs) (con d c ps' args' rs') (data d ps) := by
  sorry

theorem sem_EqTm_elim {Ψ Φ Γ d D ps ps' P P' bs bs' t t' m} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : SemTy S Ψ Φ Γ (elim d ps P bs t) (P.inst t)) (h2 : SemTy S Ψ Φ Γ (elim d ps' P' bs' t') (P.inst t))
    (h3 : SemEqTele S Ψ Φ Γ ps ps' D.params []) (h4 : SemEq S Ψ Φ (data d ps :: Γ) P P' (univ m))
    (h5 : bs.toList.length = bs'.toList.length)
    (h6 : ∀ (c : Nat) (C : Ctor) (b b' : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      bs'.toList[c]? = some b' → SemEq S Ψ Φ Γ b b' (D.branchTy d c C ps P))
    (h7 : SemEq S Ψ Φ Γ t t' (data d ps)) :
    SemEq S Ψ Φ Γ (elim d ps P bs t) (elim d ps' P' bs' t') (P.inst t) := by
  sorry

/-! ### Computation -/

theorem sem_EqTm_conBnd {Ψ Φ Γ d D c C ps args rs} {k : Nat} {ψ b T} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : D.ctors[c]? = some C) (h2 : C.bnd[k]? = some (ψ, b)) (h3 : I.Entails Φ (Ctor.cofAt ψ rs))
    (hpl : ps = Tm.ofList ps.toList) (hal : args = Tm.ofList args.toList) (h4 : SemTy S Ψ Φ Γ (con d c ps args rs) T) :
    SemEq S Ψ Φ Γ (con d c ps args rs) (Ctor.bndAt b ps.toList args.toList rs) T := by
  sorry

theorem sem_EqTm_elimCon {Ψ Φ Γ d D c C ps P bs b qs args rs T} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : D.ctors[c]? = some C) (h2 : bs.toList[c]? = some b)
    (hal : args = Tm.ofList args.toList) (hbl : bs = Tm.ofList bs.toList) (h3 : SemTy S Ψ Φ Γ (elim d ps P bs (con d c qs args rs)) T) :
    SemEq S Ψ Φ Γ (elim d ps P bs (con d c qs args rs))
      (Tm.papps (Tm.apps b (args.toList ++
        C.recPos.map fun k => elim d ps P bs (args.toList.getD k .abort))) rs) T := by
  sorry

theorem sem_EqTm_elimHcomp {Ψ Φ Γ d D ps P bs qs φ u a T} (hS : SigOK S)
    (hd : S[d]? = some (.data D)) (h0 : SemTy S Ψ Φ Γ (elim d ps P bs (hcomp (data d qs) φ u a)) T) :
    SemEq S Ψ Φ Γ (elim d ps P bs (hcomp (data d qs) φ u a))
      (comp (P.subst (fun | 0 => hfill (data d ps) φ u a | j + 1 => var j) (fun i => .var (i + 1))) φ
        (elim d ps.dshift P.dshift bs.dshift u) (elim d ps P bs a)) T := by
  sorry

theorem sem_EqTm_transpData0 {Ψ Φ Γ d D ps φ a T} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : D.params = []) (h2 : SemTy S Ψ Φ Γ (transp (data d ps) φ a) T) :
    SemEq S Ψ Φ Γ (transp (data d ps) φ a) a T := by
  sorry

theorem sem_EqTm_transpCon {Ψ Φ Γ d D c C ps φ qs args rs T} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : D.params ≠ []) (h2 : D.ctors[c]? = some C)
    (hpl : ps = Tm.ofList ps.toList) (hal : args = Tm.ofList args.toList) (h3 : SemTy S Ψ Φ Γ (transp (data d ps) φ (con d c qs args rs)) T) :
    SemEq S Ψ Φ Γ (transp (data d ps) φ (con d c qs args rs))
      (con d c (ps.dinst .one)
        (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs) T := by
  sorry

theorem sem_EqTm_transpHcomp {Ψ Φ Γ d D ps φ qs ψ u a T} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : D.params ≠ []) (h2 : SemTy S Ψ Φ Γ (transp (data d ps) φ (hcomp (data d qs) ψ u a)) T) :
    SemEq S Ψ Φ Γ (transp (data d ps) φ (hcomp (data d qs) ψ u a))
      (hcomp (data d (ps.dinst .one)) ψ
        (transp ((data d ps).dsubst fun | 0 => .var 0 | n + 1 => .var (n + 2)) φ.shift u)
        (transp (data d ps) φ a)) T := by
  sorry

end

end Model
