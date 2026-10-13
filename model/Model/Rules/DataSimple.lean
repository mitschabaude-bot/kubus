import Model.Rules.DataBranch

/-!
# Simple boundary terms denote their boundary values
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

section

variable {d : ℕ} {D : DataDecl} (hS : SigOK S) (hd : S[d]? = some (.data D)) {c : ℕ} {C : Ctor}
  (hC : D.ctors[c]? = some C) {ρ : IEnv m} {γ : ℕ → V} (hγ : ∀ x, IsKV m (γ x)) (PS : RV m)
  (hpok : ParamsOK (sigUpTo S d) D m PS) (args : List V)
  (hat : (dataSD (sigUpTo S d) D d m PS).ArgsTyped c C m (Hom.id m) args) (rs : List (DM m))
  (σ : ℕ → Tm) (τ : ℕ → I)
  (hσa : ∀ j (hj : j < C.args.length), sem S (σ j) m ρ γ = args.reverse[j]'(by have := hat.1; simp; omega))
  (hσp : psRV S ((Ctor.paramVars D.params.length C.args.length).subst σ τ) m ρ γ = PS)
  (hτ : ∀ i < C.dims, ival ρ (τ i) = renv rs i)
include hS hd hC hγ hpok hat hσa hσp hτ

theorem sem_simple_subst : ∀ t : Tm,
    (BTy (dataSD (sigUpTo S d) D d m PS) c C t →
      Ctor.simpleB D.ctors d D.params.length c C.args.length C t = true →
      t.closedB (D.params.length + C.args.length) C.dims = true →
      sem S (t.subst σ τ) m ρ γ = evalBnd (conBefore D.ctors c m) args rs t) ∧
    (∀ C' c' j prev, BTyArgs (dataSD (sigUpTo S d) D d m PS) c C C' c' j prev t →
      Ctor.simpleArgs D.ctors d D.params.length c C.args.length C C' j t = true →
      t.closedB (D.params.length + C.args.length) C.dims = true →
      t.subst σ τ = Tm.ofList (t.toList.map (·.subst σ τ)) ∧
      ∀ i (hi : i < t.toList.length), sem S ((t.toList[i]).subst σ τ) m ρ γ =
        evalBnd (conBefore D.ctors c m) args rs (t.toList[i])) := by
  have hgood := ((hS.2 d D hd).2 m PS hpok).1
  have hl : args.length = C.args.length := hat.1
  have hPV : (dataSD (sigUpTo S d) D d m PS).PtValid c m (Hom.id m) args := by
    have := SData.ptValid_take hC hat.2.2 args.length; rwa [List.take_length] at this
  have hkv : ∀ a ∈ args, IsKV m a := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    cases hr : C.isRec j
    · have hct : (dataSD (sigUpTo S d) D d m PS).ctors = D.ctors := rfl
      exact hgood.pt_kv hPV hj (by rw [hct, getD_ctors hC]; exact hr)
    · exact (hat.2.1 j _ (List.getElem?_eq_getElem hj) hr).kv
  have hvar : ∀ j (hj : j < C.args.length), sem S (σ j) m ρ γ = evalBnd (conBefore D.ctors c m) args rs (.var j) := by
    intro j hj
    rw [hσa j hj]
    simp only [evalBnd]
    rw [getD_reverse_eq (by omega), res_id (hkv _ (List.getElem_mem _)), List.getElem_reverse]
    try (congr 1; omega)
  intro t
  induction t with
  | var x =>
    refine ⟨fun _ hs _ => ?_, fun _ _ _ _ _ hs _ => by simp [Ctor.simpleArgs] at hs⟩
    simp only [Ctor.simpleB, Bool.and_eq_true, decide_eq_true_eq] at hs
    exact hvar x hs.1
  | con d' c' ps' as rs'' _ ihas =>
    refine ⟨fun hb hs hcl => ?_, fun _ _ _ _ _ hs _ => by simp [Ctor.simpleArgs] at hs⟩
    obtain ⟨hc', C', hC', hlen', hrs', hargs⟩ := hb
    simp only [Ctor.simpleB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
    obtain ⟨⟨⟨hd', -⟩, hps'⟩, hrest⟩ := hs
    rw [show D.ctors[c']? = some C' from hC'] at hrest
    simp only [Bool.and_eq_true, beq_iff_eq] at hrest
    obtain ⟨-, hsa⟩ := hrest
    simp only [Tm.closedB, Bool.and_eq_true, List.all_eq_true] at hcl
    obtain ⟨⟨-, hcla⟩, hclr⟩ := hcl
    subst d' ps'
    have hout := (bnd_delem_aux hgood hC hat.1 hat.2.1 hat.2.2 rs as).2 C' c' 0 [] hargs
    have hta := nested_argsTyped hgood hC hat.1 hat.2.1 hat.2.2 rs hC' hlen' hout
    obtain ⟨hlit, helts⟩ := ihas.2 C' c' 0 [] hargs hsa hcla
    have hvals : (as.toList.map (·.subst σ τ)).map (fun t => sem S t m ρ γ) =
        as.toList.map (evalBnd (conBefore D.ctors c m) args rs) := by
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp only [List.getElem_map]
      exact helts i (by simpa using h1)
    have hsemas : sem S (as.subst σ τ) m ρ γ = vlist (as.toList.map (evalBnd (conBefore D.ctors c m) args rs)) := by
      rw [hlit, sem_ofList_vlist, hvals]
    have hrs3 : (rs''.map (·.subst τ)).map (ival ρ) = rs''.map (ival (renv rs)) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro r hr
      simp only [Function.comp, ival.subst]
      exact ival_congr_scoped ((I.scopedB_iff _ _).1 (hclr r hr)) fun i hi => hτ i hi
    have hguard : ConGuard (sigUpTo S d) D d m (psRV S ((Ctor.paramVars D.params.length C.args.length).subst σ τ) m ρ γ) c'
        (psRV S (as.subst σ τ) m ρ γ) ((rs''.map (·.subst τ)).map (ival ρ)) := by
      rw [hσp]
      refine ⟨C', hC', by simp [hrs'], ?_, hpok, ?_⟩
      · simp only [psRV, IEnv.restr_id, TEnv.restr_id_of_kv hγ]
        rw [hsemas, ← hlen']
        simpa using listLen_vlist' (as.toList.map (evalBnd (conBefore D.ctors c m) args rs))
      · simp only [psRV, IEnv.restr_id, TEnv.restr_id_of_kv hγ]
        rw [hsemas, ← hlen', show as.toList.length = (as.toList.map (evalBnd (conBefore D.ctors c m) args rs)).length
          by simp, plist_vlist]
        exact hta
    show sem S (.con d c' ((Ctor.paramVars D.params.length C.args.length).subst σ τ) (as.subst σ τ)
      (rs''.map (·.subst τ))) m ρ γ = _
    rw [sem_con_of hd hguard, IEnv.restr_id, TEnv.restr_id_of_kv hγ, hsemas,
      getD_ctors (show D.ctors[c']? = some C' from hC'),
      ← hlen', show as.toList.length = (as.toList.map (evalBnd (conBefore D.ctors c m) args rs)).length by simp,
      plist_vlist, hrs3]
    simp only [evalBnd, conBefore, dif_pos hc', evalBndList_eq]
  | tcons a as iha ihas =>
    refine ⟨fun hb => by simp [BTy] at hb, fun C' c' j prev hb hs hcl => ?_⟩
    obtain ⟨hb1, hb2, hb3⟩ := hb
    simp only [Ctor.simpleArgs, Bool.and_eq_true] at hs
    obtain ⟨hs1, hs2⟩ := hs
    simp only [Tm.closedB, Bool.and_eq_true] at hcl
    obtain ⟨ihl, ihe⟩ := ihas.2 C' c' (j + 1) (a :: prev) hb3 hs2 hcl.2
    refine ⟨by simp only [Tm.subst, Tm.toList, List.map_cons, Tm.ofList]; rw [ihl], fun i hi => ?_⟩
    cases i with
    | zero =>
      simp only [Tm.toList, List.getElem_cons_zero]
      by_cases hr : C'.isRec j = true
      · rw [if_pos hr] at hs1
        exact iha.1 (hb1 hr) hs1 hcl.1
      · rw [if_neg hr] at hs1
        cases a with
        | var x =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hs1
          exact hvar x hs1.1
        | _ => simp at hs1
    | succ i =>
      simp only [Tm.toList, List.getElem_cons_succ]
      exact ihe i (by simp [Tm.toList] at hi; omega)
  | tnil => exact ⟨fun hb => by simp [BTy] at hb, fun _ _ _ _ _ _ _ => ⟨rfl, fun i hi => by simp [Tm.toList] at hi⟩⟩
  | _ =>
    refine ⟨fun hb => by simp [BTy] at hb, fun _ _ _ _ _ hs _ => by simp [Ctor.simpleArgs] at hs⟩

end

end

end Model
