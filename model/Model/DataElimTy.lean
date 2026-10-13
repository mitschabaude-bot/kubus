import Model.DataVt
import Model.DataElim

/-!
# Inductive types: the eliminator is typed and natural

For a motive (a fibrant family over the elements) and branches typed by their branch types and
satisfying the boundary conditions, the eliminator lands in the motive and commutes with
restriction (by induction on elements).
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

section

variable {Θ : SData m} (hΘ : Θ.Good) (P : (n : ℕ) → Hom n m → V → V) (bs : (k : ℕ) → Hom k m → V)
include hΘ

/-- The eliminator on a typed constructor value is the branch, also where its boundary holds. -/
theorem elimD_conV_typed (hBO : BranchesOK Θ P bs) {g : Hom n m} {c : ℕ} {C : Ctor} (hC : Θ.ctors[c]? = some C)
    {args : List V} (hat : Θ.ArgsTyped c C n g args) {rs : List (DM n)} (hrs : rs.length = C.dims) :
    elimD Θ P bs n g (conV Θ.ctors n c args rs) = elimBranch Θ P bs n g c args rs := by
  have hPV : Θ.PtValid c n g args := by
    have := SData.ptValid_take hC hat.2.2 args.length; rwa [List.take_length] at this
  have hkv : ∀ a ∈ args, IsKV n a := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    cases hr : C.isRec j
    · exact hΘ.pt_kv hPV hj (by rw [getD_ctors hC]; exact hr)
    · exact (hat.2.1 j _ (List.getElem?_eq_getElem hj) hr).kv
  cases hb : bndAtMap C rs (Hom.id n) with
  | none => exact elimD_conV Θ P bs g (by rw [getD_ctors hC]; exact hb) hkv
  | some cl =>
    obtain ⟨ψ, b⟩ := cl
    obtain ⟨hmem, hh⟩ := bndAtMap_some hb
    rw [conV_eq_bnd hΘ hC hat hrs hb]
    exact (hBO n g c C hC ψ b hmem args rs hat hrs (by simpa using hh)).symm

end

section typed

variable {Θ : SData m} (hΘ : Θ.Good) (P : (n : ℕ) → Hom n m → V → V) (bs : (k : ℕ) → Hom k m → V)
  (hP : ∀ n (g : Hom n m) v, DElem Θ n g v → Fib (P n g v) n)
  (hPn : ∀ n (g : Hom n m) v, DElem Θ n g v → ∀ n' (h : Hom n' n), res h (P n g v) = P n' (g.comp h) (res h v))
  (hB : ∀ n (g : Hom n m) c C, Θ.ctors[c]? = some C → ∀ args, Θ.ArgsTyped c C n g args →
    ∀ ihs : List V, ∀ (hil : ihs.length = C.recPos.length),
    (∀ s (hs : s < C.recPos.length), ihs[s]'(by omega) ∈
      El (P n g (args.getD (C.recPos.getD s 0) ∅)) (Hom.id n)) →
    (∀ a ∈ ihs, IsKV n a) → ∀ rs : List (DM n), rs.length = C.dims →
    pappsV n (appsV n (vnth (bs n g) c) (args ++ ihs)) rs ∈ El (P n g (conV Θ.ctors n c args rs)) (Hom.id n) ∧
    ∀ n' (h : Hom n' n), res h (pappsV n (appsV n (vnth (bs n g) c) (args ++ ihs)) rs) =
      pappsV n' (appsV n' (vnth (bs n' (g.comp h)) c) ((args ++ ihs).map (res h))) (rs.map (·.restr h)))
include hΘ hP hPn hB

/-- The constructor equation of the eliminator for constructor `c` (at arguments on which the
eliminator is typed). -/
def ElimConEq (Θ : SData m) (P : (n : ℕ) → Hom n m → V → V) (bs : (k : ℕ) → Hom k m → V) (c : ℕ) (C : Ctor) : Prop :=
  ∀ n (g : Hom n m) args, Θ.ArgsTyped c C n g args → ∀ rs : List (DM n), rs.length = C.dims →
    (∀ j a, args[j]? = some a → C.isRec j = true → elimD Θ P bs n g a ∈ El (P n g a) (Hom.id n) ∧
      ∀ n' (h : Hom n' n), res h (elimD Θ P bs n g a) = elimD Θ P bs n' (g.comp h) (res h a)) →
    elimD Θ P bs n g (conV Θ.ctors n c args rs) = elimBranch Θ P bs n g c args rs

omit hΘ hP hPn hB in
theorem elimBranch_eq {n : ℕ} {g : Hom n m} {c : ℕ} {C : Ctor} (hC : Θ.ctors[c]? = some C) {args : List V}
    (hlen : args.length = C.args.length) (rs : List (DM n)) :
    elimBranch Θ P bs n g c args rs = pappsV n (appsV n (vnth (bs n g) c)
      (args ++ C.recPos.map fun j => elimD Θ P bs n g (args.getD j ∅))) rs := by
  unfold elimBranch; rw [getD_ctors hC, hlen]; rfl

/-- The eliminator on a constructor value is typed and natural, given its constructor equation and
typed natural recursive arguments. -/
theorem elimD_conV_props {c : ℕ} {C : Ctor} (hC : Θ.ctors[c]? = some C) (hGc : ElimConEq Θ P bs c C)
    {n : ℕ} {g : Hom n m} {args : List V} {rs : List (DM n)} (hlen : args.length = C.args.length)
    (hrs : rs.length = C.dims) (hrec : ∀ j a, args[j]? = some a → C.isRec j = true → DElem Θ n g a)
    (hpt : ∀ j a, args[j]? = some a → C.isRec j = false → a ∈ El (Θ.ty c j n g (args.take j)) (Hom.id n))
    (ih : ∀ j a, args[j]? = some a → C.isRec j = true → elimD Θ P bs n g a ∈ El (P n g a) (Hom.id n) ∧
      ∀ n' (h : Hom n' n), res h (elimD Θ P bs n g a) = elimD Θ P bs n' (g.comp h) (res h a)) :
    elimD Θ P bs n g (conV Θ.ctors n c args rs) ∈ El (P n g (conV Θ.ctors n c args rs)) (Hom.id n) ∧
      ∀ n' (h : Hom n' n), res h (elimD Θ P bs n g (conV Θ.ctors n c args rs)) =
        elimD Θ P bs n' (g.comp h) (res h (conV Θ.ctors n c args rs)) := by
  have hat : Θ.ArgsTyped c C n g args := ⟨hlen, hrec, hpt⟩
  rw [hGc n g args hat rs hrs ih, elimBranch_eq (Θ := Θ) P bs hC hlen]
  have hrp : ∀ s (hs : s < C.recPos.length), ∃ a, args[C.recPos.getD s 0]? = some a ∧ C.isRec (C.recPos.getD s 0) = true := by
    intro s hs
    have hm : C.recPos.getD s 0 ∈ C.recPos := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]; exact List.getElem_mem _
    simp only [Ctor.recPos, List.mem_filter, List.mem_range] at hm
    exact ⟨_, List.getElem?_eq_getElem (by rw [hlen]; exact hm.1), hm.2⟩
  have hgetD : ∀ s (hs : s < C.recPos.length), args.getD (C.recPos.getD s 0) ∅ =
      (args[C.recPos.getD s 0]?).getD ∅ := fun s hs => by rw [List.getD_eq_getElem?_getD]
  have hih : ∀ s (hs : s < C.recPos.length), elimD Θ P bs n g (args.getD (C.recPos.getD s 0) ∅) ∈
      El (P n g (args.getD (C.recPos.getD s 0) ∅)) (Hom.id n) ∧
      ∀ n' (h : Hom n' n), res h (elimD Θ P bs n g (args.getD (C.recPos.getD s 0) ∅)) =
        elimD Θ P bs n' (g.comp h) (res h (args.getD (C.recPos.getD s 0) ∅)) := by
    intro s hs
    obtain ⟨a, ha, hr⟩ := hrp s hs
    rw [hgetD s hs, ha]
    exact ih _ a ha hr
  have hihs := hB n g c C hC args hat (C.recPos.map fun j => elimD Θ P bs n g (args.getD j ∅)) (by simp)
    (fun s hs => by
      have hs' : s < C.recPos.length := by simpa using hs
      have := (hih s hs').1
      rw [show C.recPos.getD s 0 = C.recPos[s] by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs']; rfl]
        at this
      simp only [List.getElem_map]
      rw [show C.recPos.getD s 0 = C.recPos[s] by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs']; rfl]
      exact this)
    (fun a ha => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
      obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hj
      have := (hih s hs).1
      have hd : DElem Θ n g (args.getD (C.recPos.getD s 0) ∅) := by
        obtain ⟨a, ha, hr⟩ := hrp s hs
        rw [hgetD s hs, ha]; exact hrec _ a ha hr
      rw [show C.recPos.getD s 0 = C.recPos[s] by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]; rfl]
        at this hd
      exact (hP n g _ hd).elKV _ _ _ this) rs hrs
  refine ⟨hihs.1, fun n' h => ?_⟩
  rw [hihs.2 n' h, res_conV, List.map_append, List.map_map]
  have hat' := hΘ.argsTyped_res hC hat n' h
  rw [hGc n' (g.comp h) _ hat' _ (by simp [hrs]) (fun j a ha hr => by
      rw [List.getElem?_map] at ha
      obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.1 ha
      obtain ⟨h1, h2⟩ := ih j a0 ha0 hr
      have hd : DElem Θ n g a0 := hrec j a0 ha0 hr
      refine ⟨?_, fun n'' h' => ?_⟩
      · rw [← h2 n' h]
        have := (hP n g a0 hd).elRes n (Hom.id n) _ h1 n' h
        rwa [El_eq_res_id, Hom.id_comp, hPn n g a0 hd n' h] at this
      · rw [← h2 n' h, res_res, h2 n'' (h.comp h'), res_res]; rfl),
    elimBranch_eq (Θ := Θ) P bs hC (by simp [hlen])]
  congr 3
  apply List.map_congr_left
  intro j hj
  obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hj
  have e := (hih s hs).2 n' h
  rw [show C.recPos.getD s 0 = C.recPos[s] by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]; rfl]
    at e
  simp only [Function.comp]
  rw [e]
  congr 1
  have hjl : C.recPos[s] < args.length := by
    have hm : C.recPos[s] ∈ (List.range C.args.length).filter C.isRec := List.getElem_mem hs
    rw [List.mem_filter, List.mem_range] at hm
    omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hjl]

/-- **The eliminator is typed and natural** on elements. -/
theorem elimD_typed (hG : ∀ c C, Θ.ctors[c]? = some C → ElimConEq Θ P bs c C) : ∀ {n : ℕ} {g : Hom n m} {v : V}, DElem Θ n g v →
    elimD Θ P bs n g v ∈ El (P n g v) (Hom.id n) ∧
      ∀ n' (h : Hom n' n), res h (elimD Θ P bs n g v) = elimD Θ P bs n' (g.comp h) (res h v) := by
  intro n g v hv
  induction hv with
  | @con n g c C args rs hC hlen hrs hrec hpt ih =>
    exact elimD_conV_props hΘ P bs hP hPn hB hC (hG c C hC) hlen hrs hrec hpt ih
  | @hcomp n g φ u a hφ ha hu hcoh hbase iha ihu =>
    have hfib := fib_dataC hΘ
    have hu0 : a ∈ El (dataC Θ) g := mem_El_dataC.2 ha
    have hut : TubeOK (dataC Θ) g φ u a :=
      ⟨fun n' h r hh => mem_El_dataC.2 (hu n' h r hh), hcoh, hbase⟩
    by_cases hh : φ.holds
    · have hid : (φ.restr (Hom.id n)).holds := hφ.holds_restr hh _
      have hkv := (hu n (Hom.id n) (DM.one n) hid).kv
      have hv : hcV n φ u a = u n (Hom.id n) (DM.one n) := hcV_eq_of_holds a hφ hh hkv hcoh
      rw [hv]
      have := ihu n (Hom.id n) (DM.one n) hid
      simp only [Hom.comp_id] at this
      exact this
    · -- the hfill of the composition
      set W := hfillF (dataC Θ) g φ u a with hW
      have hWv : hcV (n + 1) (fillFace φ) (fillTube φ u a) (res (Hom.wk n) a) = W := by
        rw [hW, hfillF, hcompAt_dataC (fillTube_ok hfib hφ hu0 hut) (hfib.elRes _ _ a hu0 _ _)]
        exact hcV_congr _ fun n' h r hh' => by simp [Tube.canon, hh']
      have hWd : DElem Θ (n + 1) (g.comp (Hom.wk n)) W := mem_El_dataC.1 (hfillF_mem hfib hφ hu0 hut)
      have hka : IsKV n a := ha.kv
      rw [elimD_hcV Θ P bs g hφ hh hka, hWv]
      have hL := hP _ _ W hWd
      have hLres : ∀ n' (x : Hom n' (n + 1)), El (P (n + 1) (g.comp (Hom.wk n)) W) ((Hom.id (n + 1)).comp x) =
          El (P n' (g.comp ((Hom.wk n).comp x)) (res x W)) (Hom.id n') := by
        intro n' x
        rw [Hom.id_comp, El_eq_res_id, hPn _ _ W hWd n' x]; rfl
      have hb0 : elimD Θ P bs n g a ∈ El (P (n + 1) (g.comp (Hom.wk n)) W)
          ((Hom.id (n + 1)).comp (Hom.endpt n (DM.zero n))) := by
        rw [hLres, Hom.wk_comp_endpt, Hom.comp_id, hW, hfillF_endpt0 hfib hφ hu0 hut]
        exact iha.1
      have htube : LineTubeOK (P (n + 1) (g.comp (Hom.wk n)) W) (Hom.id (n + 1)) φ
          (fun n' g' r => elimD Θ P bs n' (g.comp g') (u n' g' r)) (elimD Θ P bs n g a) := by
        refine ⟨fun n' g' r hg => ?_, fun n' g' r hg n'' g'' => ?_, fun n' g' hg => ?_⟩
        · rw [hLres, Hom.wk_comp_snoc, hW, hfillF_face hfib hφ hu0 hut g' hg r]
          exact (ihu n' g' r hg).1
        · exact (ihu n' g' r hg).2 n'' g'' ▸ by rw [hcoh n' g' r hg n'' g'']; rfl
        · show elimD Θ P bs n' (g.comp g') (u n' g' (DM.zero n')) = res g' (elimD Θ P bs n g a)
          rw [hbase n' g' hg, iha.2 n' g']
      refine ⟨?_, fun n' h => ?_⟩
      · have := compF_mem hL hφ hb0 htube
        rw [hLres, Hom.wk_comp_endpt, Hom.comp_id, hW, hfillF_endpt1 hfib hφ hu0 hut,
          hcompAt_dataC hut hu0] at this
        rwa [show hcV n φ (Tube.canon φ u) a = hcV n φ u a from
          hcV_congr a (fun n' h r hh' => by simp [Tube.canon, hh'])] at this
      · rw [compF_res hL hφ hb0 htube h, res_hcV]
        by_cases hh' : (φ.restr h).holds
        · have hid : ((φ.restr h).restr (Hom.id n')).holds := (hφ.restr h).holds_restr hh' _
          have hkv := (hu n' h (DM.one n') hh').kv
          rw [hcV_eq_of_holds _ (hφ.restr h) hh' (by simpa [Tube.restr] using hkv) (fun n₁ h₁ r hh₁ n₂ h₂ => by
            rw [Cof.restr_restr] at hh₁; exact hcoh n₁ (h.comp h₁) r hh₁ n₂ h₂)]
          rw [compF_face hL (hφ.restr h) (hL.transp_base_restr hb0 h) (htube.restr h) hh']
          simp [Tube.restr]
        · have hka' : IsKV n' (res h a) := isKV_res _ _
          rw [elimD_hcV Θ P bs (g.comp h) (hφ.restr h) hh' hka', ← compF_res_id, iha.2 n' h]
          have hW' : hcV (n' + 1) (fillFace (φ.restr h)) (fillTube (φ.restr h) (u.restr h) (res h a))
              (res (Hom.wk n') (res h a)) = res (Hom.lift h) W := by
            have hu0' : res h a ∈ El (dataC Θ) (g.comp h) := hfib.elRes _ _ a hu0 _ h
            rw [hW, hfillF_natural hfib hφ hu0 hut h, hfillF,
              hcompAt_dataC (fillTube_ok hfib (hφ.restr h) hu0' (hut.restr h)) (hfib.elRes _ _ _ hu0' _ _)]
            exact (hcV_congr _ fun n'' h'' r hh'' => by simp [Tube.canon, hh'']).symm
          rw [hW', Hom.id_comp, hPn _ _ W hWd (n' + 1) (Hom.lift h), Hom.comp_assoc, Hom.wk_comp_lift]
          rfl

end typed

end

end Model
