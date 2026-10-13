import Model.DataInv

/-!
# Inductive types: transport is total on elements

Every element (and every restriction of an element) has a transport along every line through
its type, given componentwise by `TR`.
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

/-- The output and filler lists of a constructor transport exist once the recursive arguments
can be transported (with their fillers). -/
theorem exists_outs_fills (Θ : SData m) (c k : ℕ) (f : Hom (k + 1) m) (φ : Cof k) (args : List V)
    (hrec : ∀ j (hj : j < args.length), (Θ.ctors.getD c default).isRec j = true →
      (∃ w, TR Θ k f φ args[j] w) ∧ (∃ w, TR Θ (k + 1) (f.comp (tfLine k)) (fillFace φ) (res (Hom.wk k) args[j]) w)) :
    ∃ outs fills : List V, outs.length = args.length ∧ fills.length = args.length ∧
      (∀ j (hj : j < args.length), (Θ.ctors.getD c default).isRec j = true →
        TR Θ k f φ args[j] (outs.getD j ∅)) ∧
      (∀ j (hj : j < args.length), (Θ.ctors.getD c default).isRec j = true →
        TR Θ (k + 1) (f.comp (tfLine k)) (fillFace φ) (res (Hom.wk k) args[j]) (fills.getD j ∅)) ∧
      (∀ j (hj : j < args.length), (Θ.ctors.getD c default).isRec j = false →
        outs.getD j ∅ = transpAt (Θ.ty c j (k + 1) f (fills.take j)) (Hom.id (k + 1)) φ args[j] ∧
        fills.getD j ∅ = transpFillF (Θ.ty c j (k + 1) f (fills.take j)) (Hom.id (k + 1)) φ args[j]) := by
  suffices ∀ J (hJ : J ≤ args.length), ∃ outs fills : List V, outs.length = J ∧ fills.length = J ∧
      (∀ j (hj : j < J), (Θ.ctors.getD c default).isRec j = true →
        TR Θ k f φ (args[j]'(by omega)) (outs.getD j ∅)) ∧
      (∀ j (hj : j < J), (Θ.ctors.getD c default).isRec j = true →
        TR Θ (k + 1) (f.comp (tfLine k)) (fillFace φ) (res (Hom.wk k) (args[j]'(by omega))) (fills.getD j ∅)) ∧
      (∀ j (hj : j < J), (Θ.ctors.getD c default).isRec j = false →
        outs.getD j ∅ = transpAt (Θ.ty c j (k + 1) f (fills.take j)) (Hom.id (k + 1)) φ (args[j]'(by omega)) ∧
        fills.getD j ∅ = transpFillF (Θ.ty c j (k + 1) f (fills.take j)) (Hom.id (k + 1)) φ (args[j]'(by omega))) by
    obtain ⟨outs, fills, h1, h2, h3, h4, h5⟩ := this args.length le_rfl
    exact ⟨outs, fills, h1, h2, h3, h4, h5⟩
  intro J
  induction J with
  | zero => intro _; exact ⟨[], [], rfl, rfl, fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega)⟩
  | succ J ih =>
    intro hJ
    obtain ⟨outs, fills, h1, h2, h3, h4, h5⟩ := ih (by omega)
    have gl : ∀ (L : List V) (x : V) j, j < L.length → (L ++ [x]).getD j ∅ = L.getD j ∅ := by
      intro L x j hj
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    have gr : ∀ (L : List V) (x : V) j, L.length = j → (L ++ [x]).getD j ∅ = x := by
      intro L x j hj; subst hj; simp
    have tk : ∀ (L : List V) (x : V) j, j ≤ L.length → (L ++ [x]).take j = L.take j := by
      intro L x j hj; simp [List.take_append_of_le_length hj]
    by_cases hr : (Θ.ctors.getD c default).isRec J = true
    · obtain ⟨⟨o, ho⟩, ⟨fl, hfl⟩⟩ := hrec J (by omega) hr
      refine ⟨outs ++ [o], fills ++ [fl], by simp [h1], by simp [h2], fun j hj hjr => ?_, fun j hj hjr => ?_,
        fun j hj hjr => ?_⟩
      · by_cases hjJ : j < J
        · rw [gl _ _ _ (by omega)]; exact h3 j hjJ hjr
        · obtain rfl : j = J := by omega
          rw [gr _ _ _ h1]; exact ho
      · by_cases hjJ : j < J
        · rw [gl _ _ _ (by omega)]; exact h4 j hjJ hjr
        · obtain rfl : j = J := by omega
          rw [gr _ _ _ h2]; exact hfl
      · by_cases hjJ : j < J
        · rw [gl _ _ _ (by omega), gl _ _ _ (by omega), tk _ _ _ (by omega)]; exact h5 j hjJ hjr
        · obtain rfl : j = J := by omega
          rw [hjr] at hr; exact absurd hr (by decide)
    · have hr' : (Θ.ctors.getD c default).isRec J = false := by simpa using hr
      refine ⟨outs ++ [transpAt (Θ.ty c J (k + 1) f fills) (Hom.id (k + 1)) φ (args[J]'(by omega))],
        fills ++ [transpFillF (Θ.ty c J (k + 1) f fills) (Hom.id (k + 1)) φ (args[J]'(by omega))],
        by simp [h1], by simp [h2], fun j hj hjr => ?_, fun j hj hjr => ?_, fun j hj hjr => ?_⟩
      · by_cases hjJ : j < J
        · rw [gl _ _ _ (by omega)]; exact h3 j hjJ hjr
        · obtain rfl : j = J := by omega
          rw [hr'] at hjr; exact absurd hjr (by decide)
      · by_cases hjJ : j < J
        · rw [gl _ _ _ (by omega)]; exact h4 j hjJ hjr
        · obtain rfl : j = J := by omega
          rw [hr'] at hjr; exact absurd hjr (by decide)
      · by_cases hjJ : j < J
        · rw [gl _ _ _ (by omega), gl _ _ _ (by omega), tk _ _ _ (by omega)]; exact h5 j hjJ hjr
        · obtain rfl : j = J := by omega
          have htk : fills.take j = fills := by rw [← h2, List.take_length]
          rw [gr _ _ _ h1, gr _ _ _ h2, tk _ _ _ (by omega), htk]
          exact ⟨rfl, rfl⟩

section

variable (Θ : SData m)

/-- `v` (at the restriction `g` of the stage) can be transported, after any restriction, along
any line through its type. -/
def TrAll (n : ℕ) (g : Hom n m) (v : V) : Prop :=
  ∀ n' (h : Hom n' n) (f : Hom (n' + 1) m) (φ : Cof n'), f.comp (Hom.endpt n' (DM.zero n')) = g.comp h →
    ∃ w, TR Θ n' f φ (res h v) w

end

variable {Θ : SData m} (hΘ : Θ.Good)
include hΘ

theorem TrAll.res {n : ℕ} {g : Hom n m} {v : V} (hv : TrAll Θ n g v) (k : ℕ) (h : Hom k n) :
    TrAll Θ k (g.comp h) (res h v) := by
  intro n' h' f φ hf
  rw [res_res]; exact hv n' (h.comp h') f φ hf

theorem trAll_conV : ∀ c C, Θ.ctors[c]? = some C → ∀ n (g : Hom n m) args (rs : List (DM n)),
    Θ.ArgsTyped c C n g args → rs.length = C.dims →
    (∀ j a, args[j]? = some a → C.isRec j = true → TrAll Θ n g a) →
    TrAll Θ n g (conV Θ.ctors n c args rs) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ihc =>
    intro C hC n g args rs ht hrs hrec n' h f φ hf
    rw [res_conV]
    have ht' := hΘ.argsTyped_res hC ht n' h
    have hrs' : (rs.map (·.restr h)).length = C.dims := by simp [hrs]
    have hrec' : ∀ j a, (args.map (res h))[j]? = some a → C.isRec j = true → TrAll Θ n' (g.comp h) a := by
      intro j a ha hj
      rw [List.getElem?_map] at ha
      obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.1 ha
      exact (hrec j a0 ha0 hj).res hΘ n' h
    have hPV : Θ.PtValid c n' (g.comp h) (args.map (res h)) := by
      have := SData.ptValid_take hC ht'.2.2 (args.map (res h)).length; rwa [List.take_length] at this
    have hkv : ∀ a ∈ args.map (res h), IsKV n' a := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      cases hr : C.isRec j
      · exact hΘ.pt_kv hPV hj (by rw [getD_ctors hC]; exact hr)
      · exact (ht'.2.1 j _ (List.getElem?_eq_getElem hj) hr).kv
    cases hb : bndAtMap C (rs.map (·.restr h)) (Hom.id n') with
    | none =>
      obtain ⟨outs, fills, h1, h2, h3, h4, h5⟩ := exists_outs_fills Θ c n' f φ (args.map (res h))
        (fun j hj hjr => by
          rw [getD_ctors hC] at hjr
          have := hrec' j _ (List.getElem?_eq_getElem hj) hjr
          refine ⟨?_, ?_⟩
          · have := this n' (Hom.id n') f φ (by rw [Hom.comp_id]; exact hf)
            rwa [res_id (hkv _ (List.getElem_mem hj))] at this
          · refine this (n' + 1) (Hom.wk n') (f.comp (tfLine n')) (fillFace φ) ?_
            rw [Hom.comp_assoc, tfLine_endpt0, ← Hom.comp_assoc, hf])
      exact ⟨_, TR.con (by rw [getD_ctors hC]; exact hb) hkv h1 h2 h3 h4 h5⟩
    | some cl =>
      obtain ⟨ψ, b⟩ := cl
      rw [conV_eq_bnd hΘ hC ht' hrs' hb]
      have hbt := hΘ.bnd c C hC ψ b (bndAtMap_some hb).1
      have haux := bnd_delem_aux hΘ hC ht'.1 ht'.2.1 ht'.2.2 (rs.map (·.restr h))
      suffices ∀ t : Tm, (BTy Θ c C t →
            TrAll Θ n' (g.comp h) (evalBnd (conBefore Θ.ctors c n') (args.map (res h)) (rs.map (·.restr h)) t)) ∧
          (∀ C' c' k prev, BTyArgs Θ c C C' c' k prev t → ∀ i (hi : i < t.toList.length),
            C'.isRec (k + i) = true →
            TrAll Θ n' (g.comp h) (evalBnd (conBefore Θ.ctors c n') (args.map (res h)) (rs.map (·.restr h)) t.toList[i])) by
        have := (this b).1 hbt n' (Hom.id n') f φ (by rw [Hom.comp_id]; exact hf)
        rwa [res_id (isKV_evalBnd (isKV_conBefore _ _ _) _ _ _)] at this
      intro t
      induction t with
      | var x =>
        refine ⟨fun hb => ?_, fun _ _ _ _ _ i hi => by simp [Tm.toList] at hi⟩
        obtain ⟨hx, hr⟩ := hb
        have hl : (args.map (res h)).length = C.args.length := ht'.1
        simp only [evalBnd]
        rw [getD_reverse_eq (by omega)]
        have hj : (args.map (res h)).length - 1 - x < (args.map (res h)).length := by omega
        have hr' : C.isRec ((args.map (res h)).length - 1 - x) = true := by rw [hl]; exact hr
        rw [res_id (hkv _ (List.getElem_mem hj))]
        exact hrec' _ _ (List.getElem?_eq_getElem hj) hr'
      | con d c' ps as rs' _ ihas =>
        refine ⟨fun hb => ?_, fun _ _ _ _ _ i hi => by simp [Tm.toList] at hi⟩
        obtain ⟨hc', C', hC', hlen', hrs'', hargs⟩ := hb
        have hout := (haux as).2 C' c' 0 [] hargs
        simp only [evalBnd, conBefore, dif_pos hc']
        rw [evalBndList_eq]
        refine ihc c' hc' C' hC' n' (g.comp h) _ _
          (nested_argsTyped hΘ hC ht'.1 ht'.2.1 ht'.2.2 _ hC' hlen' hout) (by simp [hrs'']) (fun j a ha hj => ?_)
        rw [List.getElem?_map] at ha
        obtain ⟨t, ht'', rfl⟩ := Option.map_eq_some_iff.1 ha
        obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 ht''
        exact ihas.2 C' c' 0 [] hargs j hj' (by simpa using hj)
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

theorem DElem.trAll {n : ℕ} {g : Hom n m} {v : V} (hv : DElem Θ n g v) : TrAll Θ n g v := by
  induction hv with
  | @con n g c C args rs hC hlen hrs hrec hpt ih =>
    exact trAll_conV hΘ c C hC n g args rs ⟨hlen, hrec, hpt⟩ hrs ih
  | @hcomp n g φ u a hφ ha hu hcoh hbase iha ihu =>
    intro n' h f ψ hf
    rw [res_hcV]
    by_cases hh : (φ.restr h).holds
    · have hh' : ((φ.restr h).restr (Hom.id n')).holds := (hφ.restr h).holds_restr hh _
      have hkv := (hu n' h (DM.one n') hh).kv
      rw [hcV_eq_of_holds _ (hφ.restr h) hh (by simpa [Tube.restr] using hkv) (fun n₁ h₁ r hh₁ n₂ h₂ => by
        rw [Cof.restr_restr] at hh₁; exact hcoh n₁ (h.comp h₁) r hh₁ n₂ h₂)]
      have := ihu n' h (DM.one n') hh n' (Hom.id n') f ψ (by rw [Hom.comp_id]; exact hf)
      rw [res_id hkv] at this
      simpa [Tube.restr] using this
    · obtain ⟨a', ha'⟩ := iha n' h f ψ hf
      have hx : ∀ n₁ (h₁ : Hom n₁ n') r, ((φ.restr h).restr h₁).holds →
          ∃ w, TR Θ n₁ (f.comp (Hom.lift h₁)) (ψ.restr h₁) (u n₁ (h.comp h₁) r) w := by
        intro n₁ h₁ r hh₁
        rw [Cof.restr_restr] at hh₁
        have := ihu n₁ (h.comp h₁) r hh₁ n₁ (Hom.id n₁) (f.comp (Hom.lift h₁)) (ψ.restr h₁) (by
          rw [Hom.comp_assoc, TranspPi.lift_comp_endpt0, ← Hom.comp_assoc, hf, Hom.comp_id]; rfl)
        rwa [res_id (hu n₁ (h.comp h₁) r hh₁).kv] at this
      refine ⟨hcV n' (φ.restr h) (fun n₁ h₁ r => if hh₁ : ((φ.restr h).restr h₁).holds then
        Classical.choose (hx n₁ h₁ r hh₁) else ∅) a', TR.hc (hφ.restr h) hh (isKV_res _ _) ha' (fun n₁ h₁ r hh₁ => ?_)⟩
      rw [dif_pos hh₁]
      exact Classical.choose_spec (hx n₁ h₁ r hh₁)

/-- **Totality** of transport on elements. -/
theorem DElem.tr_exists {k : ℕ} {f : Hom (k + 1) m} {v : V}
    (hv : DElem Θ k (f.comp (Hom.endpt k (DM.zero k))) v) (φ : Cof k) : ∃ w, TR Θ k f φ v w := by
  have := hv.trAll hΘ k (Hom.id k) f φ (by rw [Hom.comp_id])
  rwa [res_id hv.kv] at this

end

end Model
