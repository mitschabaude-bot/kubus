import Model.DataBnd

/-!
# Inductive types: inversion of elements

Every element is a constructor value without boundary at its own stage, with typed arguments, or
a formal composition whose face does not hold, with an element base and an element tube.
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

theorem isKV_evalBnd {conF : ℕ → List V → List (DM n) → V} (hc : ∀ c as rs, IsKV n (conF c as rs))
    (args : List V) (rs : List (DM n)) (t : Tm) : IsKV n (evalBnd conF args rs t) := by
  cases t with
  | var j => rw [evalBnd]; exact isKV_res _ _
  | con d c ps as rs' => rw [evalBnd]; exact hc _ _ _
  | _ => rw [evalBnd] <;> first | exact isKV_junkV | (intros; simp_all)

theorem isKV_conBefore (ctors : List Ctor) (c n : ℕ) (c' : ℕ) (as : List V) (rs : List (DM n)) :
    IsKV n (conBefore ctors c n c' as rs) := by
  unfold conBefore; split
  · exact isKV_conV _ _ _ _
  · exact isKV_junkV

theorem res_conBefore (ctors : List Ctor) (c : ℕ) (h : Hom k n) (c' : ℕ) (as : List V) (rs : List (DM n)) :
    res h (conBefore ctors c n c' as rs) = conBefore ctors c k c' (as.map (res h)) (rs.map (·.restr h)) := by
  unfold conBefore; split
  · exact res_conV _ _ _ _ _
  · exact res_junkV h

theorem res_evalBnd_conBefore (ctors : List Ctor) (c : ℕ) (h : Hom k n) (args : List V) (rs : List (DM n)) (t : Tm) :
    res h (evalBnd (conBefore ctors c n) args rs t) =
      evalBnd (conBefore ctors c k) (args.map (res h)) (rs.map (·.restr h)) t :=
  (res_evalBnd h (res_conBefore ctors c h) args rs t).1

theorem bndAtMap_some {C : Ctor} {rs : List (DM n)} {f : Hom k n} {cl : I × Tm}
    (h : bndAtMap C rs f = some cl) : cl ∈ C.bnd ∧ ((ival (renv rs) cl.1).restr f).holds := by
  unfold bndAtMap at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem bndAtMap_isSome {C : Ctor} {rs : List (DM n)} {f : Hom k n} {cl : I × Tm} (hcl : cl ∈ C.bnd)
    (hh : ((ival (renv rs) cl.1).restr f).holds) : ∃ cl', bndAtMap C rs f = some cl' := by
  unfold bndAtMap
  cases hf : C.bnd.find? (fun cl => decide ((ival (renv rs) cl.1).restr f).holds) with
  | some cl' => exact ⟨cl', rfl⟩
  | none =>
    have := List.find?_eq_none.1 hf cl hcl
    simp only [decide_eq_true_eq] at this
    exact absurd hh this

section

variable {Θ : SData m}

theorem SData.argsTyped_res_of (hrc : Θ.ResClosed) {c : ℕ} {C : Ctor} (hC : Θ.ctors[c]? = some C) {g : Hom n m}
    {args : List V} (ht : Θ.ArgsTyped c C n g args) (k : ℕ) (h : Hom k n) :
    Θ.ArgsTyped c C k (g.comp h) (args.map (res h)) := by
  obtain ⟨hlen, hrec, hpt⟩ := ht
  refine ⟨by simp [hlen], fun j a ha hj => ?_, fun j a ha hj => ?_⟩
  · rw [List.getElem?_map] at ha
    obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.1 ha
    exact (hrec j a0 ha0 hj).res hrc k h
  · rw [List.getElem?_map] at ha
    obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.1 ha
    rw [← List.map_take]
    exact hrc c j n g _ a0 (SData.ptValid_take hC hpt j) (hpt j a0 ha0 hj) k h

theorem SData.Good.argsTyped_res (hΘ : Θ.Good) {c : ℕ} {C : Ctor} (hC : Θ.ctors[c]? = some C) {g : Hom n m}
    {args : List V} (ht : Θ.ArgsTyped c C n g args) (k : ℕ) (h : Hom k n) :
    Θ.ArgsTyped c C k (g.comp h) (args.map (res h)) :=
  SData.argsTyped_res_of hΘ.resClosed hC ht k h

/-- A constructor value whose boundary holds at its own stage is its boundary value, given the
agreement of its overlapping boundary clauses. -/
theorem conV_eq_bnd_of (hrc : Θ.ResClosed) {c : ℕ} {C : Ctor} (hC : Θ.ctors[c]? = some C)
    (hovl : ∀ ψ b ψ' b', (ψ, b) ∈ C.bnd → (ψ', b') ∈ C.bnd → ∀ n (g : Hom n m) args (rs : List (DM n)),
      Θ.ArgsTyped c C n g args → rs.length = C.dims → (ival (renv rs) ψ).holds → (ival (renv rs) ψ').holds →
      evalBnd (conBefore Θ.ctors c n) args rs b = evalBnd (conBefore Θ.ctors c n) args rs b')
    {g : Hom n m} {args : List V}
    (ht : Θ.ArgsTyped c C n g args) {rs : List (DM n)} (hrs : rs.length = C.dims) {ψ : I} {b : Tm}
    (hb : bndAtMap C rs (Hom.id n) = some (ψ, b)) :
    conV Θ.ctors n c args rs = evalBnd (conBefore Θ.ctors c n) args rs b := by
  obtain ⟨hmem, hh⟩ := bndAtMap_some hb
  have hh' : (ival (renv rs) ψ).holds := by simpa using hh
  apply (isKV_conV _ _ _ _).ext (isKV_evalBnd (isKV_conBefore _ _ _) _ _ _)
  intro k f
  rw [conV_eq, dat_mkKV, getD_ctors hC]
  have hf : ((ival (renv rs) ψ).restr f).holds := hh'.restr f
  obtain ⟨⟨ψ', b'⟩, hb'⟩ := bndAtMap_isSome hmem hf
  rw [hb']
  obtain ⟨hmem', hh2⟩ := bndAtMap_some hb'
  show dat (evalBnd (conBefore Θ.ctors c n) args rs b') k f = _
  rw [← here_res, ← here_res, res_evalBnd_conBefore, res_evalBnd_conBefore]
  congr 1
  refine (hovl ψ' b' ψ b hmem' hmem k (g.comp f) _ _ (SData.argsTyped_res_of hrc hC ht k f)
    (by simp [hrs]) ?_ ?_)
  · rw [← ival_renv_restr]; exact hh2
  · rw [← ival_renv_restr]; exact hf

theorem conV_eq_bnd (hΘ : Θ.Good) {c : ℕ} {C : Ctor} (hC : Θ.ctors[c]? = some C) {g : Hom n m} {args : List V}
    (ht : Θ.ArgsTyped c C n g args) {rs : List (DM n)} (hrs : rs.length = C.dims) {ψ : I} {b : Tm}
    (hb : bndAtMap C rs (Hom.id n) = some (ψ, b)) :
    conV Θ.ctors n c args rs = evalBnd (conBefore Θ.ctors c n) args rs b :=
  conV_eq_bnd_of hΘ.resClosed hC (hΘ.ovl c C hC) ht hrs hb

end

end

end Model

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

theorem hcV_eq_of_holds {φ : Cof n} {u : Tube n} (a : V) (hφ : φ.IsCof) (hh : φ.holds)
    (hkv : IsKV n (u n (Hom.id n) (DM.one n)))
    (hcoh : ∀ n' (h : Hom n' n) r, (φ.restr h).holds → ∀ n'' (h' : Hom n'' n'),
      res h' (u n' h r) = u n'' (h.comp h') (r.restr h')) :
    hcV n φ u a = u n (Hom.id n) (DM.one n) := by
  rw [hkv.eq, hcV]
  congr 1; funext k g
  rw [if_pos (hφ.holds_restr hh g)]
  have := hcoh n (Hom.id n) (DM.one n) (hφ.holds_restr hh _) k g
  rw [Hom.id_comp, DM.one_restr] at this
  rw [← this, here_res]

section

variable (Θ : SData m)

/-- A constructor value without boundary at its stage, with typed (Kripke-value) arguments. -/
def RepConOK (n : ℕ) (g : Hom n m) (v : V) : Prop :=
  ∃ c C args rs, Θ.ctors[c]? = some C ∧ v = conV Θ.ctors n c args rs ∧ bndAtMap C rs (Hom.id n) = none ∧
    (∀ a ∈ args, IsKV n a) ∧ Θ.ArgsTyped c C n g args ∧ rs.length = C.dims

/-- A formal composition whose face does not hold, with element base and tube. -/
def RepHcOK (n : ℕ) (g : Hom n m) (v : V) : Prop :=
  ∃ ψ u a, v = hcV n ψ u a ∧ ψ.IsCof ∧ ¬ ψ.holds ∧ DElem Θ n g a ∧
    (∀ n' (h : Hom n' n) r, (ψ.restr h).holds → DElem Θ n' (g.comp h) (u n' h r)) ∧
    (∀ n' (h : Hom n' n) r, (ψ.restr h).holds → ∀ n'' (h' : Hom n'' n'),
      res h' (u n' h r) = u n'' (h.comp h') (r.restr h')) ∧
    (∀ n' (h : Hom n' n), (ψ.restr h).holds → u n' h (DM.zero n') = res h a)

def HasRep (n : ℕ) (g : Hom n m) (v : V) : Prop := RepConOK Θ n g v ∨ RepHcOK Θ n g v

end

variable {Θ : SData m} (hΘ : Θ.Good)
include hΘ

theorem hasRep_conV : ∀ c C, Θ.ctors[c]? = some C → ∀ n (g : Hom n m) args (rs : List (DM n)),
    Θ.ArgsTyped c C n g args → rs.length = C.dims →
    (∀ j a, args[j]? = some a → C.isRec j = true → HasRep Θ n g a) →
    HasRep Θ n g (conV Θ.ctors n c args rs) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ihc =>
    intro C hC n g args rs ht hrs hrep
    have hPV : Θ.PtValid c n g args := by
      have := SData.ptValid_take hC ht.2.2 args.length; rwa [List.take_length] at this
    have hkv : ∀ a ∈ args, IsKV n a := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      cases hr : C.isRec j
      · exact hΘ.pt_kv hPV hj (by rw [getD_ctors hC]; exact hr)
      · exact (ht.2.1 j _ (List.getElem?_eq_getElem hj) hr).kv
    cases hb : bndAtMap C rs (Hom.id n) with
    | none => exact Or.inl ⟨c, C, args, rs, hC, rfl, hb, hkv, ht, hrs⟩
    | some cl =>
      obtain ⟨ψ, b⟩ := cl
      rw [conV_eq_bnd hΘ hC ht hrs hb]
      have hbt := hΘ.bnd c C hC ψ b (bndAtMap_some hb).1 _ _ (by simpa using (bndAtMap_some hb).2)
      have haux := bnd_delem_aux hΘ.basic hC ht.1 ht.2.1 ht.2.2 rs
      suffices ∀ t : Tm, (BTy Θ c C t → HasRep Θ n g (evalBnd (conBefore Θ.ctors c n) args rs t)) ∧
          (∀ C' c' k prev, BTyArgs Θ c C C' c' k prev t → ∀ i (hi : i < t.toList.length),
            C'.isRec (k + i) = true → HasRep Θ n g (evalBnd (conBefore Θ.ctors c n) args rs t.toList[i])) from
        (this b).1 hbt
      intro t
      induction t with
      | var x =>
        refine ⟨fun hb => ?_, fun _ _ _ _ _ i hi => by simp [Tm.toList] at hi⟩
        obtain ⟨hx, hr⟩ := hb
        have hl : args.length = C.args.length := ht.1
        simp only [evalBnd]
        rw [getD_reverse_eq (by omega)]
        have hj : args.length - 1 - x < args.length := by omega
        have hr' : C.isRec (args.length - 1 - x) = true := by rw [ht.1]; exact hr
        rw [res_id (hkv _ (List.getElem_mem hj))]
        exact hrep _ _ (List.getElem?_eq_getElem hj) hr'
      | con d c' ps as rs' _ ihas =>
        refine ⟨fun hb => ?_, fun _ _ _ _ _ i hi => by simp [Tm.toList] at hi⟩
        obtain ⟨hc', C', hC', hlen', hrs', hargs⟩ := hb
        have hout := (haux as).2 C' c' 0 [] hargs
        simp only [evalBnd, conBefore, dif_pos hc']
        rw [evalBndList_eq]
        refine ihc c' hc' C' hC' n g _ _ (nested_argsTyped hΘ.basic hC ht.1 ht.2.1 ht.2.2 rs hC' hlen' hout)
          (by simp [hrs']) (fun j a ha hj => ?_)
        rw [List.getElem?_map] at ha
        obtain ⟨t, ht', rfl⟩ := Option.map_eq_some_iff.1 ha
        obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 ht'
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

/-- **Inversion**: every element has a representation. -/
theorem DElem.hasRep {n : ℕ} {g : Hom n m} {v : V} (hv : DElem Θ n g v) : HasRep Θ n g v := by
  induction hv with
  | @con n g c C args rs hC hlen hrs hrec hpt ih =>
    exact hasRep_conV hΘ c C hC n g args rs ⟨hlen, hrec, hpt⟩ hrs ih
  | @hcomp n g φ u a hφ ha hu hcoh hbase iha ihu =>
    by_cases hh : φ.holds
    · have hh' : (φ.restr (Hom.id n)).holds := hφ.holds_restr hh _
      have hkv := (hu n (Hom.id n) (DM.one n) hh').kv
      rw [hcV_eq_of_holds a hφ hh hkv hcoh]
      have := ihu n (Hom.id n) (DM.one n) hh'
      rwa [Hom.comp_id] at this
    · exact Or.inr ⟨φ, u, a, rfl, hφ, hh, ha, hu, hcoh, hbase⟩

end

end Model
