import Model.DataWF

/-!
# Inductive types: boundary values are elements
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

theorem getD_reverse_eq {args : List V} {x : ℕ} (hx : x < args.length) :
    args.reverse.getD x ∅ = args[args.length - 1 - x] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse hx, List.getElem?_eq_getElem (by omega)]; rfl

theorem getD_ctors {ctors : List Ctor} {c : ℕ} {C : Ctor} (hC : ctors[c]? = some C) : ctors.getD c default = C := by
  rw [List.getD_eq_getElem?_getD, hC]; rfl

section

variable {Θ : SData m} (hΘ : Θ.Good) {c : ℕ} {C : Ctor} (hC : Θ.ctors[c]? = some C) {g : Hom n m}
  {args : List V} (hlen : args.length = C.args.length)
  (hrec : ∀ j a, args[j]? = some a → C.isRec j = true → DElem Θ n g a)
  (hpt : ∀ j a, args[j]? = some a → C.isRec j = false → a ∈ El (Θ.ty c j n g (args.take j)) (Hom.id n))
  (rs : List (DM n))
include hΘ hC hlen hrec hpt

/-- The list statement used in the induction. -/
def BArgsOut (Θ : SData m) (c : ℕ) (C C' : Ctor) (c' : ℕ) (g : Hom n m) (args : List V) (rs : List (DM n))
    (k : ℕ) (prev : List Tm) (t : Tm) : Prop :=
  ∀ i (hi : i < t.toList.length),
    (C'.isRec (k + i) = true → DElem Θ n g (evalBnd (conBefore Θ.ctors c n) args rs t.toList[i])) ∧
    (C'.isRec (k + i) = false → ∃ x, t.toList[i] = .var x ∧ x < C.args.length ∧
      C.isRec (C.args.length - 1 - x) = false ∧
      ∀ n (g : Hom n m) (pre : List V), pre.length = C.args.length → Θ.PtValid c n g pre →
        Θ.ty c' (k + i) n g (nestPre pre ((t.toList.take i).reverse ++ prev)) =
          Θ.ty c (C.args.length - 1 - x) n g (pre.take (C.args.length - 1 - x)))

theorem nested_argsTyped {C' : Ctor} {c' : ℕ} {as : Tm} (hC' : Θ.ctors[c']? = some C')
    (hlen' : as.toList.length = C'.args.length) (hout : BArgsOut Θ c C C' c' g args rs 0 [] as) :
    Θ.ArgsTyped c' C' n g (as.toList.map (evalBnd (conBefore Θ.ctors c n) args rs)) := by
  have hPV : Θ.PtValid c n g args := by
    have := SData.ptValid_take hC hpt args.length; rwa [List.take_length] at this
  refine ⟨by simp [hlen'], fun j a ha hj => ?_, fun j a ha hj => ?_⟩
  · rw [List.getElem?_map] at ha
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 ha
    obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 ht
    exact (hout j hj').1 (by simpa using hj)
  · rw [List.getElem?_map] at ha
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 ha
    obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 ht
    obtain ⟨x, hxe, hx, hxr, hty⟩ := (hout j hj').2 (by simpa using hj)
    rw [hxe]
    simp only [evalBnd]
    rw [getD_reverse_eq (by omega)]
    have hkv := hΘ.pt_kv hPV (i := args.length - 1 - x) (by omega) (by rw [getD_ctors hC, hlen]; exact hxr)
    rw [res_id hkv]
    have e1 : Θ.ty c' j n g ((as.toList.map (evalBnd (conBefore Θ.ctors c n) args rs)).take j) =
        Θ.ty c' j n g (nestPre args ((as.toList.take j).reverse ++ [])) := by
      apply hΘ.recIrr
      · simp [nestPre]
      · intro i hi hi' hr
        simp only [List.length_take, List.length_map] at hi
        have hiC : C'.isRec (0 + i) = false := by rw [getD_ctors hC'] at hr; simpa using hr
        obtain ⟨y, hye, hy, hyr, -⟩ := (hout i (by omega)).2 hiC
        simp only [List.getElem_take, List.getElem_map, nestPre, List.append_nil, List.reverse_reverse]
        rw [hye]
        simp only [evalBnd]
        rw [getD_reverse_eq (by omega)]
        have hkv' := hΘ.pt_kv hPV (i := args.length - 1 - y) (by omega) (by
          rw [getD_ctors hC, hlen]; exact hyr)
        rw [res_id hkv']
    rw [e1, show (0 : ℕ) + j = j from by omega] at *
    have := hty n g args hlen hPV
    rw [this]
    have hp := hpt (args.length - 1 - x) _ (List.getElem?_eq_getElem (by omega)) (by rw [hlen]; exact hxr)
    simpa only [hlen] using hp

theorem bnd_delem_aux : ∀ t : Tm,
    (BTy Θ c C t → DElem Θ n g (evalBnd (conBefore Θ.ctors c n) args rs t)) ∧
    (∀ C' c' k prev, BTyArgs Θ c C C' c' k prev t → BArgsOut Θ c C C' c' g args rs k prev t) := by
  have hPV : Θ.PtValid c n g args := by
    have := SData.ptValid_take hC hpt args.length; rwa [List.take_length] at this
  intro t
  induction t with
  | var x =>
    refine ⟨fun hb => ?_, fun _ _ _ _ _ i hi => by simp [Tm.toList] at hi⟩
    obtain ⟨hx, hr⟩ := hb
    simp only [evalBnd]
    rw [getD_reverse_eq (by omega)]
    have hrec' := hrec (args.length - 1 - x) _ (List.getElem?_eq_getElem (by omega)) (by rw [hlen]; exact hr)
    rw [res_id hrec'.kv]; exact hrec'
  | con d c' ps as rs' _ ihas =>
    refine ⟨fun hb => ?_, fun _ _ _ _ _ i hi => by simp [Tm.toList] at hi⟩
    obtain ⟨hc', C', hC', hlen', hrs', hargs⟩ := hb
    have hout := ihas.2 C' c' 0 [] hargs
    simp only [evalBnd, conBefore, dif_pos hc']
    rw [evalBndList_eq]
    have ht := nested_argsTyped hΘ hC hlen hrec hpt rs hC' hlen' hout
    exact DElem.con hC' ht.1 (by simp [hrs']) ht.2.1 ht.2.2
  | tcons a as iha ihas =>
    refine ⟨fun hb => by simp [BTy] at hb, fun C' c' k prev hb => ?_⟩
    obtain ⟨hr, hp, hrest⟩ := hb
    intro i hi
    cases i with
    | zero =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simpa [Tm.toList] using iha.1 (hr (by simpa using h))
      · obtain ⟨x, hxe, hx, hxr, hty⟩ := hp (by simpa using h)
        exact ⟨x, by simpa [Tm.toList] using hxe, hx, hxr, by simpa [Tm.toList] using hty⟩
    | succ i =>
      have hi' : i < as.toList.length := by simp [Tm.toList] at hi; omega
      obtain ⟨h1, h2⟩ := ihas.2 C' c' (k + 1) (a :: prev) hrest i hi'
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simpa [Tm.toList] using h1 (by rw [show k + 1 + i = k + (i + 1) by omega]; exact h)
      · obtain ⟨x, hxe, hx, hxr, hty⟩ := h2 (by rw [show k + 1 + i = k + (i + 1) by omega]; exact h)
        refine ⟨x, by simpa [Tm.toList] using hxe, hx, hxr, fun n g pre hl hpv => ?_⟩
        have := hty n g pre hl hpv
        rw [show k + 1 + i = k + (i + 1) by omega] at this
        simpa [Tm.toList, List.take_succ_cons, List.reverse_cons, List.append_assoc] using this
  | _ => exact ⟨fun hb => by simp [BTy] at hb, fun _ _ _ _ _ i hi => by simp [Tm.toList] at hi⟩

end

end

end Model
