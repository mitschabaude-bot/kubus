import Model.DataConst

/-!
# Inductive types: transport of a constructor value whose boundary may hold

Transport of a constructor value is componentwise also where its boundary holds: the boundary is
simple, so transporting the boundary value transports the arguments of its nested constructors,
along their argument types, which are those of the outer constructor (`BTy`, from the spec's
`Ctor.bndTyped`).
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

/-- The variable index of a term (junk for other terms). -/
def varIdx : Tm → ℕ
  | .var x => x
  | _ => 0

variable {Θ : SData m} (hΘ : Θ.Good)
include hΘ

theorem tr_conV_any : ∀ c C, Θ.ctors[c]? = some C → ∀ n (f : Hom (n + 1) m) (φ : Cof n)
    (args outs fills : List V) (rs : List (DM n)),
    Θ.ArgsTyped c C n (f.comp (Hom.endpt n (DM.zero n))) args →
    Θ.ArgsTyped c C n (f.comp (Hom.endpt n (DM.one n))) outs →
    (∀ a ∈ args, IsKV n a) → rs.length = C.dims → outs.length = args.length → fills.length = args.length →
    Θ.PtValid c (n + 1) f fills →
    (∀ j (hj : j < args.length), C.isRec j = true → TR Θ n f φ args[j] (outs.getD j ∅)) →
    (∀ j (hj : j < args.length), C.isRec j = true →
      TR Θ (n + 1) (f.comp (tfLine n)) (fillFace φ) (res (Hom.wk n) args[j]) (fills.getD j ∅)) →
    (∀ j (hj : j < args.length), C.isRec j = false →
      outs.getD j ∅ = transpAt (Θ.ty c j (n + 1) f (fills.take j)) (Hom.id (n + 1)) φ args[j] ∧
      fills.getD j ∅ = transpFillF (Θ.ty c j (n + 1) f (fills.take j)) (Hom.id (n + 1)) φ args[j]) →
    TR Θ n f φ (conV Θ.ctors n c args rs) (conV Θ.ctors n c outs rs) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ihc =>
    intro C hC n f φ args outs fills rs hta hto hkv hrs hlo hlf hpv hro hrf hpt
    have hgC := getD_ctors hC
    cases hb : bndAtMap C rs (Hom.id n) with
    | none =>
      exact TR.con (by rw [hgC]; exact hb) hkv hlo hlf (by rw [hgC]; exact hro) (by rw [hgC]; exact hrf)
        (by rw [hgC]; exact hpt)
    | some cl =>
      obtain ⟨ψ, b⟩ := cl
      rw [conV_eq_bnd hΘ hC hta hrs hb, conV_eq_bnd hΘ hC hto hrs hb]
      have hbt := hΘ.bnd c C hC ψ b (bndAtMap_some hb).1 _ _ (by simpa using (bndAtMap_some hb).2)
      have hauxa := bnd_delem_aux hΘ hC hta.1 hta.2.1 hta.2.2 rs
      have hlen : args.length = C.args.length := hta.1
      have hkvo : ∀ j (hj : j < outs.length), C.isRec j = true → IsKV n outs[j] := fun j hj hr =>
        (hto.2.1 j _ (List.getElem?_eq_getElem hj) hr).kv
      suffices ∀ t : Tm, (BTy Θ c C t →
            TR Θ n f φ (evalBnd (conBefore Θ.ctors c n) args rs t) (evalBnd (conBefore Θ.ctors c n) outs rs t)) ∧
          (∀ C' c' k prev, BTyArgs Θ c C C' c' k prev t → ∀ i (hi : i < t.toList.length),
            C'.isRec (k + i) = true →
            TR Θ n f φ (evalBnd (conBefore Θ.ctors c n) args rs t.toList[i])
              (evalBnd (conBefore Θ.ctors c n) outs rs t.toList[i])) from (this b).1 hbt
      intro t
      induction t with
      | var x =>
        refine ⟨fun hb => ?_, fun _ _ _ _ _ i hi => by simp [Tm.toList] at hi⟩
        obtain ⟨hx, hr⟩ := hb
        simp only [evalBnd]
        rw [getD_reverse_eq (by omega), getD_reverse_eq (by omega)]
        have hj : args.length - 1 - x < args.length := by omega
        have hr' : C.isRec (args.length - 1 - x) = true := by rw [hlen]; exact hr
        have e : outs.length - 1 - x = args.length - 1 - x := by omega
        rw [res_id (hkv _ (List.getElem_mem hj)), res_id (hkvo _ (by omega) (by rw [e]; exact hr'))]
        have := hro _ hj hr'
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
        simpa [e] using this
      | con d c' ps as rs' _ ihas =>
        refine ⟨fun hb => ?_, fun _ _ _ _ _ i hi => by simp [Tm.toList] at hi⟩
        obtain ⟨hc', C', hC', hlen', hrs', hargs⟩ := hb
        have hout := (hauxa as).2 C' c' 0 [] hargs
        simp only [evalBnd, conBefore, dif_pos hc']
        rw [evalBndList_eq, evalBndList_eq]
        have hta' := nested_argsTyped hΘ hC hta.1 hta.2.1 hta.2.2 rs hC' hlen' hout
        have hauxo := bnd_delem_aux hΘ hC hto.1 hto.2.1 hto.2.2 rs
        have hto' := nested_argsTyped hΘ hC hto.1 hto.2.1 hto.2.2 rs hC' hlen' ((hauxo as).2 C' c' 0 [] hargs)
        set args2 := as.toList.map (evalBnd (conBefore Θ.ctors c n) args rs) with hargs2
        set outs2 := as.toList.map (evalBnd (conBefore Θ.ctors c n) outs rs) with houts2
        let fills2 : List V := (List.range as.toList.length).map fun i =>
          if C'.isRec i = true then
            (if h : ∃ w, TR Θ (n + 1) (f.comp (tfLine n)) (fillFace φ) (res (Hom.wk n) (args2.getD i ∅)) w
              then Classical.choose h else ∅)
          else fills.reverse.getD (varIdx (as.toList.getD i .abort)) ∅
        have hl2 : fills2.length = as.toList.length := by simp [fills2]
        have hf2 : ∀ i (hi : i < as.toList.length), fills2.getD i ∅ = if C'.isRec i = true then
            (if h : ∃ w, TR Θ (n + 1) (f.comp (tfLine n)) (fillFace φ) (res (Hom.wk n) (args2.getD i ∅)) w
              then Classical.choose h else ∅)
            else fills.reverse.getD (varIdx (as.toList.getD i .abort)) ∅ := by
          intro i hi
          simp [fills2, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
        -- point positions: the variable, the type equality
        have hpos : ∀ i (hi : i < as.toList.length), C'.isRec i = false →
            ∃ x, as.toList[i] = .var x ∧ x < C.args.length ∧ C.isRec (C.args.length - 1 - x) = false ∧
              Θ.ty c' i (n + 1) f (fills2.take i) =
                Θ.ty c (C.args.length - 1 - x) (n + 1) f (fills.take (C.args.length - 1 - x)) := by
          intro i hi hr
          obtain ⟨x, hxe, hx, hxr, hty⟩ := (hout i hi).2 (by simpa using hr)
          refine ⟨x, hxe, hx, hxr, ?_⟩
          have := hty (n + 1) f fills (by omega) hpv
          simp only [Nat.zero_add, List.append_nil] at this
          rw [← this]
          apply hΘ.recIrr
          · simp [nestPre, hl2] <;> omega
          · intro i' hi1 hi2 hr'
            simp only [List.length_take] at hi1
            have hr'' : C'.isRec i' = false := by rw [getD_ctors hC'] at hr'; exact hr'
            obtain ⟨y, hye, -, -, -⟩ := (hout i' (by omega)).2 (by simpa using hr'')
            have e1 : (fills2.take i)[i'] = fills2.getD i' ∅ := by
              rw [List.getElem_take, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
            rw [e1, hf2 i' (by omega), if_neg (by simp [hr''])]
            simp only [nestPre, List.reverse_reverse, List.getElem_map, List.getElem_take]
            rw [List.getD_eq_getElem?_getD (l := as.toList), List.getElem?_eq_getElem (by omega)]
            simp only [Option.getD_some, hye, varIdx, nestVal]
        refine ihc c' hc' C' hC' n f φ args2 outs2 fills2 _ hta' hto' (fun a ha => ?_) (by simp [hrs'])
          (by simp [args2, outs2]) (by simp [args2, hl2]) ?_ ?_ ?_ ?_
        · obtain ⟨t, -, rfl⟩ := List.mem_map.1 ha
          exact isKV_evalBnd (isKV_conBefore _ _ _) _ _ _
        · -- the fillers are valid
          intro i hi hr
          rw [getD_ctors hC'] at hr
          simp only [hl2] at hi
          obtain ⟨x, hxe, hx, hxr, hty⟩ := hpos i hi hr
          have e1 : fills2[i] = fills2.getD i ∅ := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
          have hxe' : as.toList.getD i .abort = .var x := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; simp [hxe]
          rw [e1, hf2 i hi, if_neg (by simp [hr]), hxe', varIdx, hty, getD_reverse_eq (by omega)]
          have := hpv (fills.length - 1 - x) (by omega) (by rw [hgC, hlf, hlen]; exact hxr)
          simpa [hlf, hlen] using this
        · intro j hj hr
          simp only [args2, List.length_map] at hj
          have := ihas.2 C' c' 0 [] hargs j hj (by simpa using hr)
          simpa [args2, outs2, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj] using this
        · intro j hj hr
          simp only [args2, List.length_map] at hj
          have hd := (hout j hj).1 (by simpa using hr)
          have hd' : DElem Θ n (f.comp (Hom.endpt n (DM.zero n))) (args2.getD j ∅) := by
            simpa [args2, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj] using hd
          have hex := DElem.tr_exists hΘ (f := f.comp (tfLine n)) (v := res (Hom.wk n) (args2.getD j ∅)) (by
            rw [Hom.comp_assoc, tfLine_endpt0, ← Hom.comp_assoc]; exact hd'.res hΘ.resClosed (n + 1) (Hom.wk n))
            (fillFace φ)
          rw [hf2 j hj, if_pos hr, dif_pos hex, List.getElem_eq_getD ∅]
          exact Classical.choose_spec hex
        · intro j hj hr
          simp only [args2, List.length_map] at hj
          obtain ⟨x, hxe, hx, hxr, hty⟩ := hpos j hj hr
          have hxe' : as.toList.getD j .abort = .var x := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; simp [hxe]
          have hp : args.length - 1 - x < args.length := by omega
          have hrp : C.isRec (args.length - 1 - x) = false := by rw [hlen]; exact hxr
          have hpo : Θ.PtValid c n (f.comp (Hom.endpt n (DM.one n))) outs := by
            have := SData.ptValid_take hC hto.2.2 outs.length; rwa [List.take_length] at this
          have hkvo' : IsKV n (outs[args.length - 1 - x]'(by omega)) :=
            hΘ.pt_kv hpo (by omega) (by rw [hgC]; exact hrp)
          have ea : args2[j] = args[args.length - 1 - x] := by
            simp only [args2, List.getElem_map, hxe, evalBnd]
            rw [getD_reverse_eq (by omega), res_id (hkv _ (List.getElem_mem _))]
          have eo : outs2.getD j ∅ = outs[args.length - 1 - x]'(by omega) := by
            have e2 : outs2.getD j ∅ = evalBnd (conBefore Θ.ctors c n) outs rs (.var x) := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [outs2]; exact hj)]
              simp [outs2, hxe]
            rw [e2, evalBnd, getD_reverse_eq (by omega)]
            have e3 : outs.length - 1 - x = args.length - 1 - x := by omega
            simp only [e3]
            exact res_id hkvo'
          have ef : fills2.getD j ∅ = fills[args.length - 1 - x]'(by omega) := by
            rw [hf2 j hj, if_neg (by simp [hr]), hxe', varIdx, getD_reverse_eq (by omega)]
            simp [hlf]
          rw [ea, eo, ef, hty]
          have := hpt _ hp hrp
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (by omega)] at this
          simpa [hlen] using this
      | tcons a as iha ihas =>
        refine ⟨fun hb => by simp [BTy] at hb, fun C' c' k prev hb => ?_⟩
        obtain ⟨hr, -, hrest⟩ := hb
        intro i hi hri
        cases i with
        | zero => simpa [Tm.toList] using iha.1 (hr (by simpa using hri))
        | succ i =>
          have hi' : i < as.toList.length := by simp [Tm.toList] at hi; omega
          simpa [Tm.toList] using ihas.2 C' c' (k + 1) (a :: prev) hrest i hi'
            (by rw [show k + 1 + i = k + (i + 1) by omega]; exact hri)
      | _ => exact ⟨fun hb => by simp [BTy] at hb, fun _ _ _ _ _ i hi => by simp [Tm.toList] at hi⟩

end

end Model
