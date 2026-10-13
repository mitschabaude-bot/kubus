import Model.DataNB

/-!
# Inductive types: transport is lawful

Along a line of inductive types constant on `φ`, transport (`TR`) lands in the inductive type at
the end, is the identity where `φ` holds, and commutes with restriction.
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

theorem endpt0_comp (h : Hom n k) : (Hom.endpt k (DM.zero k)).comp h = Hom.snoc h (DM.zero n) := by
  rw [Hom.endpt, Hom.snoc_comp, Hom.id_comp, DM.zero_restr]

theorem constOn_tfLine' {c : V} {f : Hom (k + 1) m} {φ : Cof k} (hcon : ConstOn c f φ) :
    ConstOn c (f.comp (tfLine k)) (fillFace φ) := by
  intro n h hh r
  rw [Hom.comp_assoc, Hom.comp_assoc, tfLine_snoc, tfLine_snoc]
  rw [fillFace, Cof.or_restr, Cof.holds_or] at hh
  rcases hh with hh | hh
  · rw [Cof.restr_restr] at hh
    rw [hcon _ _ hh (DM.min _ r), hcon _ _ hh (DM.min _ (DM.zero n))]
  · rw [Cof.eq0_restr] at hh
    rw [DM.eq_zero_of_holds_eq0 hh, DM.min_zero_left, DM.min_zero_left]

theorem fillFace_restr_lift (φ : Cof k) (h : Hom n k) : (fillFace φ).restr (Hom.lift h) = fillFace (φ.restr h) := by
  rw [fillFace, fillFace, Cof.or_restr, Cof.eq0_restr, lastVar_restr_lift, Cof.restr_restr,
    Cof.restr_restr, Hom.wk_comp_lift]

theorem fillFace_endpt0 (φ : Cof k) : ((fillFace φ).restr (Hom.endpt k (DM.zero k))).holds := by
  rw [fillFace, Cof.or_restr, Cof.eq0_restr, lastVar_restr_endpt, Cof.eq0_zero]; exact Cof.or_top _

theorem fillFace_endpt1 {φ : Cof k} (hφ : φ.IsCof) : (fillFace φ).restr (Hom.endpt k (DM.one k)) = φ := by
  rw [fillFace, Cof.or_restr, Cof.eq0_restr, lastVar_restr_endpt, Cof.eq0_one, Cof.or_bot,
    Cof.restr_restr, Hom.wk_comp_endpt, hφ.restr_id]

theorem fillFace_snoc {φ : Cof k} {h : Hom n k} (hh : (φ.restr h).holds) (r : DM n) :
    ((fillFace φ).restr (Hom.snoc h r)).holds := by
  rw [fillFace, Cof.or_restr, Cof.holds_or]; left
  rw [Cof.restr_restr, Hom.wk_comp_snoc]; exact hh

/-- The properties of a transport derivation along a constant line. -/
def TRProps (Θ : SData m) (k : ℕ) (f : Hom (k + 1) m) (φ : Cof k) (v w : V) : Prop :=
  φ.IsCof → ConstOn (dataC Θ) f φ → DElem Θ k (f.comp (Hom.endpt k (DM.zero k))) v →
    DElem Θ k (f.comp (Hom.endpt k (DM.one k))) w ∧
    (∀ n' (h : Hom n' k), (φ.restr h).holds → res h w = res h v) ∧
    (∀ n' (h : Hom n' k), TR Θ n' (f.comp (Hom.lift h)) (φ.restr h) (res h v) (res h w))

theorem SData.PtValid.take {Θ : SData m} {c n : ℕ} {g : Hom n m} {L : List V} (hp : Θ.PtValid c n g L) (j : ℕ) :
    Θ.PtValid c n g (L.take j) := by
  intro i hi hr
  simp only [List.length_take] at hi
  have := hp i (by omega) hr
  simpa [List.getElem_take, List.take_take, Nat.min_eq_left (by omega : i ≤ j)] using this

theorem ptValid_take_succ {Θ : SData m} {c n : ℕ} {g : Hom n m} {L : List V} {j : ℕ} (hj : j < L.length)
    (hp : Θ.PtValid c n g (L.take j))
    (hl : (Θ.ctors.getD c default).isRec j = false → L[j] ∈ El (Θ.ty c j n g (L.take j)) (Hom.id n)) :
    Θ.PtValid c n g (L.take (j + 1)) := by
  intro i hi hr
  simp only [List.length_take] at hi
  by_cases hij : i < j
  · have := hp i (by simp; omega) hr
    simpa [List.getElem_take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hij),
      Nat.min_eq_left (by omega : i ≤ j + 1)] using this
  · obtain rfl : i = j := by omega
    simp only [List.getElem_take, List.take_take, Nat.min_eq_left (Nat.le_succ i)]
    exact hl hr

section con

variable {Θ : SData m} (hΘ : Θ.Good) {k : ℕ} {f : Hom (k + 1) m} {φ : Cof k} {c : ℕ} {args : List V}
  {rs : List (DM k)} {outs fills : List V}
  (hb : bndAtMap (Θ.ctors.getD c default) rs (Hom.id k) = none) (hkv : ∀ a ∈ args, IsKV k a)
  (hlo : outs.length = args.length) (hlf : fills.length = args.length)
  (hro : ∀ j (hj : j < args.length), (Θ.ctors.getD c default).isRec j = true → TR Θ k f φ args[j] (outs.getD j ∅))
  (hpt : ∀ j (hj : j < args.length), (Θ.ctors.getD c default).isRec j = false →
    outs.getD j ∅ = transpAt (Θ.ty c j (k + 1) f (fills.take j)) (Hom.id (k + 1)) φ args[j] ∧
    fills.getD j ∅ = transpFillF (Θ.ty c j (k + 1) f (fills.take j)) (Hom.id (k + 1)) φ args[j])
  (iho : ∀ j (hj : j < args.length), (Θ.ctors.getD c default).isRec j = true →
    TRProps Θ k f φ args[j] (outs.getD j ∅))
  (ihf : ∀ j (hj : j < args.length), (Θ.ctors.getD c default).isRec j = true →
    TRProps Θ (k + 1) (f.comp (tfLine k)) (fillFace φ) (res (Hom.wk k) args[j]) (fills.getD j ∅))
  (hφ : φ.IsCof) (hc : ConstOn (dataC Θ) f φ) {C : Ctor} (hC : Θ.ctors[c]? = some C)
  (hta : Θ.ArgsTyped c C k (f.comp (Hom.endpt k (DM.zero k))) args)
include hΘ hkv hlo hlf hro hpt iho ihf hφ hc hC hta

/-- The invariants of the fillers, for the first `j` arguments. -/
def FillInv (Θ : SData m) (k : ℕ) (f : Hom (k + 1) m) (φ : Cof k) (c : ℕ) (args outs fills : List V) (j : ℕ) : Prop :=
  Θ.PtValid c (k + 1) f (fills.take j) ∧ ∀ i (hi : i < j) (hia : i < args.length),
    res (Hom.endpt k (DM.zero k)) (fills.getD i ∅) = args[i] ∧
    res (Hom.endpt k (DM.one k)) (fills.getD i ∅) = outs.getD i ∅ ∧
    ∀ n' (h : Hom n' k), (φ.restr h).holds → ∀ r, res (Hom.snoc h r) (fills.getD i ∅) = res h args[i]

theorem fillInv_ty_facts {i : ℕ} (hi : i < args.length) (hinv : FillInv Θ k f φ c args outs fills i) :
    Fib (Θ.ty c i (k + 1) f (fills.take i)) (k + 1) ∧
    ConstOn (Θ.ty c i (k + 1) f (fills.take i)) (Hom.id (k + 1)) φ ∧
    (C.isRec i = false → args[i] ∈ El (Θ.ty c i (k + 1) f (fills.take i)) ((Hom.id (k + 1)).comp (Hom.endpt k (DM.zero k)))) := by
  have hpv := hinv.1
  have hlen : args.length = C.args.length := hta.1
  refine ⟨hΘ.fib c i (k + 1) f _ hpv, fun n' h hh r => ?_, fun hr => ?_⟩
  · rw [Hom.id_comp, Hom.id_comp, hΘ.nat c i (k + 1) f _ hpv n' (Hom.snoc h r),
      hΘ.nat c i (k + 1) f _ hpv n' (Hom.snoc h (DM.zero n'))]
    have hm : ∀ r', (fills.take i).map (res (Hom.snoc h r')) = (args.take i).map (res h) := by
      intro r'
      apply List.ext_getElem (by simp [hlf])
      intro i' h1 h2
      simp only [List.length_map, List.length_take] at h1
      simp only [List.getElem_map, List.getElem_take]
      have := (hinv.2 i' (by omega) (by omega)).2.2 n' h hh r'
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
      exact this
    rw [hm r, hm (DM.zero n')]
    have hta' := hΘ.argsTyped_res hC hta n' h
    rw [Hom.comp_assoc, endpt0_comp] at hta'
    refine ty_const hc hh r hC (by omega) (by simp; omega) ⟨?_, fun i' hi' hr' => ?_⟩
    · rw [List.map_take]; exact SData.ptValid_take hC hta'.2.2 i
    · simp only [List.length_map, List.length_take] at hi'
      rw [getD_ctors hC] at hr'
      simp only [List.getElem_map, List.getElem_take]
      exact hta'.2.1 i' _ (by rw [List.getElem?_map, List.getElem?_eq_getElem (by omega)]; rfl) hr'
  · rw [El_eq_res_id, Hom.id_comp, hΘ.nat c i (k + 1) f _ hpv k (Hom.endpt k (DM.zero k))]
    have hm : (fills.take i).map (res (Hom.endpt k (DM.zero k))) = args.take i := by
      apply List.ext_getElem (by simp [hlf])
      intro i' h1 h2
      simp only [List.length_map, List.length_take] at h1
      simp only [List.getElem_map, List.getElem_take]
      have := (hinv.2 i' (by omega) (by omega)).1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
      exact this
    rw [hm]
    exact hta.2.2 i _ (List.getElem?_eq_getElem hi) hr

theorem fillInv_all : ∀ j ≤ args.length, FillInv Θ k f φ c args outs fills j := by
  intro j
  induction j with
  | zero => intro _; exact ⟨fun i hi => by simp at hi, fun i hi => absurd hi (by omega)⟩
  | succ j ih =>
    intro hj
    have hinv := ih (by omega)
    have hjl : j < args.length := by omega
    have hgC := getD_ctors hC
    have hfj : fills.getD j ∅ = fills[j]'(by omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    by_cases hr : C.isRec j = true
    · have hr' : (Θ.ctors.getD c default).isRec j = true := by rw [hgC]; exact hr
      have hd : DElem Θ k (f.comp (Hom.endpt k (DM.zero k))) args[j] := hta.2.1 j _ (List.getElem?_eq_getElem hjl) hr
      obtain ⟨-, hF, hR⟩ := ihf j hjl hr' (isCof_fillFace hφ) (constOn_tfLine' hc) (by
        rw [Hom.comp_assoc, tfLine_endpt0, ← Hom.comp_assoc]; exact hd.res hΘ.resClosed (k + 1) (Hom.wk k))
      refine ⟨ptValid_take_succ (by omega) hinv.1 (fun h => absurd (hr'.symm.trans h) (by decide)), fun i hi hia => ?_⟩
      by_cases hij : i < j
      · exact hinv.2 i hij hia
      obtain rfl : i = j := by omega
      refine ⟨?_, ?_, fun n' h hh r => ?_⟩
      · rw [hF k (Hom.endpt k (DM.zero k)) (fillFace_endpt0 φ), res_res, Hom.wk_comp_endpt, res_id hd.kv]
      · have := hR k (Hom.endpt k (DM.one k))
        rw [Hom.comp_assoc, tfLine_lift_endpt1, Hom.comp_id, fillFace_endpt1 hφ, res_res, Hom.wk_comp_endpt,
          res_id hd.kv] at this
        exact ((hro i hjl hr').unique this rfl).symm
      · rw [hF n' (Hom.snoc h r) (fillFace_snoc hh r), res_res, Hom.wk_comp_snoc]
    · have hr' : C.isRec j = false := by simpa using hr
      have hr'' : (Θ.ctors.getD c default).isRec j = false := by rw [hgC]; exact hr'
      obtain ⟨hfib, hcon, hbase⟩ := fillInv_ty_facts hΘ hkv hlo hlf hro hpt iho ihf hφ hc hC hta hjl hinv
      have hbase := hbase hr'
      have hfill := (hpt j hjl hr'').2
      refine ⟨ptValid_take_succ (by omega) hinv.1 (fun _ => ?_), fun i hi hia => ?_⟩
      · rw [← hfj, hfill]; exact transpFillF_mem hfib hφ hcon hbase
      by_cases hij : i < j
      · exact hinv.2 i hij hia
      obtain rfl : i = j := by omega
      refine ⟨?_, ?_, fun n' h hh r => ?_⟩
      · rw [hfill]; exact transpFillF_endpt0 hfib hφ hcon hbase
      · rw [hfill, transpFillF_endpt1 hfib hφ hcon hbase, (hpt i hjl hr'').1]
      · rw [hfill]; exact transpFillF_face hfib hφ hcon hbase h hh r

theorem fills_ptValid : Θ.PtValid c (k + 1) f fills := by
  have := (fillInv_all hΘ hkv hlo hlf hro hpt iho ihf hφ hc hC hta args.length le_rfl).1
  rwa [← hlf, List.take_length] at this

theorem con_point_facts {j : ℕ} (hj : j < args.length) :
    Fib (Θ.ty c j (k + 1) f (fills.take j)) (k + 1) ∧
    ConstOn (Θ.ty c j (k + 1) f (fills.take j)) (Hom.id (k + 1)) φ ∧
    (C.isRec j = false → args[j] ∈ El (Θ.ty c j (k + 1) f (fills.take j)) ((Hom.id (k + 1)).comp (Hom.endpt k (DM.zero k)))) :=
  fillInv_ty_facts hΘ hkv hlo hlf hro hpt iho ihf hφ hc hC hta hj
    (fillInv_all hΘ hkv hlo hlf hro hpt iho ihf hφ hc hC hta j (by omega))

theorem con_outs_typed : Θ.ArgsTyped c C k (f.comp (Hom.endpt k (DM.one k))) outs := by
  have hgC := getD_ctors hC
  have hinv := fillInv_all hΘ hkv hlo hlf hro hpt iho ihf hφ hc hC hta args.length le_rfl
  refine ⟨by rw [hlo]; exact hta.1, fun j a ha hr => ?_, fun j a ha hr => ?_⟩
  · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 ha
    have hd : DElem Θ k (f.comp (Hom.endpt k (DM.zero k))) (args[j]'(by omega)) :=
      hta.2.1 j _ (List.getElem?_eq_getElem (by omega)) hr
    have := (iho j (by omega) (by rw [hgC]; exact hr) hφ hc hd).1
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] at this
  · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 ha
    have hj' : j < args.length := by omega
    obtain ⟨hfib, hcon, hbase⟩ := con_point_facts hΘ hkv hlo hlf hro hpt iho ihf hφ hc hC hta hj'
    have e := (hpt j hj' (by rw [hgC]; exact hr)).1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] at e
    simp only [Option.getD_some] at e
    rw [e]
    have := hfib.trMem k (Hom.id (k + 1)) φ _ hφ hcon (hbase hr)
    rw [El_eq_res_id, Hom.id_comp, hΘ.nat c j (k + 1) f _ ((fills_ptValid hΘ hkv hlo hlf hro hpt iho ihf hφ hc hC hta).take j) k _] at this
    have hm : (fills.take j).map (res (Hom.endpt k (DM.one k))) = outs.take j := by
      apply List.ext_getElem (by simp [hlf, hlo])
      intro i h1 h2
      simp only [List.length_map, List.length_take] at h1
      simp only [List.getElem_map, List.getElem_take]
      have := (hinv.2 i (by omega) (by omega)).2.1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)] at this
      exact this
    rwa [hm] at this

theorem con_face (n' : ℕ) (h : Hom n' k) (hh : (φ.restr h).holds) :
    res h (conV Θ.ctors k c outs rs) = res h (conV Θ.ctors k c args rs) := by
  have hgC := getD_ctors hC
  rw [res_conV, res_conV]
  congr 1
  apply List.ext_getElem (by simp [hlo])
  intro j h1 h2
  simp only [List.length_map] at h2
  simp only [List.getElem_map]
  have eo : outs[j]'(by omega) = outs.getD j ∅ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  rw [eo]
  by_cases hr : C.isRec j = true
  · have hd : DElem Θ k (f.comp (Hom.endpt k (DM.zero k))) args[j] := hta.2.1 j _ (List.getElem?_eq_getElem h2) hr
    exact (iho j h2 (by rw [hgC]; exact hr) hφ hc hd).2.1 n' h hh
  · have hr' : C.isRec j = false := by simpa using hr
    obtain ⟨hfib, hcon, hbase⟩ := con_point_facts hΘ hkv hlo hlf hro hpt iho ihf hφ hc hC hta h2
    rw [(hpt j h2 (by rw [hgC]; exact hr')).1]
    exact hfib.transp_restr_face hφ hcon (hbase hr') h hh

theorem con_res (hrs : rs.length = C.dims) (n' : ℕ) (h : Hom n' k) :
    TR Θ n' (f.comp (Hom.lift h)) (φ.restr h) (res h (conV Θ.ctors k c args rs)) (res h (conV Θ.ctors k c outs rs)) := by
  have hgC := getD_ctors hC
  have hpv := fills_ptValid hΘ hkv hlo hlf hro hpt iho ihf hφ hc hC hta
  have hto := con_outs_typed hΘ hkv hlo hlf hro hpt iho ihf hφ hc hC hta
  rw [res_conV, res_conV]
  have e0 : (f.comp (Hom.lift h)).comp (Hom.endpt n' (DM.zero n')) = (f.comp (Hom.endpt k (DM.zero k))).comp h := by
    rw [Hom.comp_assoc, TranspPi.lift_comp_endpt0]; rfl
  have e1 : (f.comp (Hom.lift h)).comp (Hom.endpt n' (DM.one n')) = (f.comp (Hom.endpt k (DM.one k))).comp h := by
    rw [Hom.comp_assoc, TranspPi.lift_comp_endpt1]; rfl
  have gd : ∀ (L : List V) (g : V → V) j, j < L.length → (L.map g).getD j ∅ = g (L.getD j ∅) := by
    intro L g j hj
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  refine tr_conV_any hΘ c C hC n' (f.comp (Hom.lift h)) (φ.restr h) (args.map (res h)) (outs.map (res h))
    (fills.map (res (Hom.lift h))) (rs.map (·.restr h)) (by rw [e0]; exact hΘ.argsTyped_res hC hta n' h)
    (by rw [e1]; exact hΘ.argsTyped_res hC hto n' h) (fun a ha => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha; exact isKV_res _ _) (by simp [hrs]) (by simp [hlo]) (by simp [hlf])
    (hΘ.ptValid_res hpv (n' + 1) (Hom.lift h)) (fun j hj hr => ?_) (fun j hj hr => ?_) (fun j hj hr => ?_)
  · simp only [List.length_map] at hj
    have hd : DElem Θ k (f.comp (Hom.endpt k (DM.zero k))) args[j] := hta.2.1 j _ (List.getElem?_eq_getElem hj) hr
    rw [gd _ _ _ (by omega), List.getElem_map]
    exact (iho j hj (by rw [hgC]; exact hr) hφ hc hd).2.2 n' h
  · simp only [List.length_map] at hj
    have hd : DElem Θ k (f.comp (Hom.endpt k (DM.zero k))) args[j] := hta.2.1 j _ (List.getElem?_eq_getElem hj) hr
    rw [gd _ _ _ (by omega), List.getElem_map]
    have := (ihf j hj (by rw [hgC]; exact hr) (isCof_fillFace hφ) (constOn_tfLine' hc) (by
      rw [Hom.comp_assoc, tfLine_endpt0, ← Hom.comp_assoc]; exact hd.res hΘ.resClosed (k + 1) (Hom.wk k))).2.2
      (n' + 1) (Hom.lift h)
    rw [Hom.comp_assoc, tfLine_lift_lift, ← Hom.comp_assoc, fillFace_restr_lift, res_res, Hom.wk_comp_lift,
      ← res_res] at this
    exact this
  · simp only [List.length_map] at hj
    have hr' : C.isRec j = false := hr
    obtain ⟨hfib, hcon, hbase⟩ := con_point_facts hΘ hkv hlo hlf hro hpt iho ihf hφ hc hC hta hj
    have hpj := hpt j hj (by rw [hgC]; exact hr')
    have hT : res (Hom.lift h) (Θ.ty c j (k + 1) f (fills.take j)) =
        Θ.ty c j (n' + 1) (f.comp (Hom.lift h)) ((fills.map (res (Hom.lift h))).take j) := by
      rw [hΘ.nat c j (k + 1) f _ (hpv.take j) (n' + 1) (Hom.lift h), List.map_take]
    rw [gd _ _ _ (by omega), gd _ _ _ (by omega), hpj.1, hpj.2, List.getElem_map, ← hT,
      transpAt_res_id', transpFillF_res_id]
    refine ⟨?_, ?_⟩
    · rw [hfib.trRes k (Hom.id (k + 1)) φ _ hφ hcon (hbase hr') n' h, Hom.id_comp]
    · rw [transpFillF_natural hfib hφ hcon (hbase hr') h, Hom.id_comp]

end con

variable {Θ : SData m} (hΘ : Θ.Good)
include hΘ

theorem TR.props {k : ℕ} {f : Hom (k + 1) m} {φ : Cof k} {v w : V} (htr : TR Θ k f φ v w) :
    TRProps Θ k f φ v w := by
  induction htr with
  | @con k f φ c args rs outs fills hb hkv hlo hlf hro hrf hpt iho ihf =>
    intro hφ hc hv
    rcases hv.hasRep hΘ with ⟨c', C, args', rs', hC, heq, hb', hkv', hta, hrs⟩ | ⟨ψ, u, a, heq, -, hn, -⟩
    · obtain ⟨rfl, rfl, rfl⟩ := conV_inj hb (by rw [getD_ctors hC]; exact hb') hkv hkv' heq
      have hto := con_outs_typed hΘ hkv hlo hlf hro hpt iho ihf hφ hc hC hta
      exact ⟨DElem.con hC hto.1 hrs hto.2.1 hto.2.2, con_face hΘ hkv hlo hlf hro hpt iho ihf hφ hc hC hta,
        con_res hΘ hkv hlo hlf hro hpt iho ihf hφ hc hC hta hrs⟩
    · exact absurd heq (conV_ne_hcV hb hn)
  | @hc k f φ ψ u u' a a' hψ hn hka ha htu iha ihu =>
    intro hφ hc hv
    rcases hv.hasRep hΘ with ⟨c', C, args', rs', hC', heq, hb', -⟩ | ⟨ψ2, u2, a2, heq, hψ2, hn2, ha2, hu2, hcoh2, hbase2⟩
    · exact absurd heq.symm (conV_ne_hcV (by rw [getD_ctors hC']; exact hb') hn)
    obtain ⟨rfl, hueq, rfl⟩ := hcV_inj hψ hψ2 hn hn2 hka ha2.kv heq
    have hu : ∀ n (g : Hom n k) r, (ψ.restr g).holds → DElem Θ n ((f.comp (Hom.endpt k (DM.zero k))).comp g) (u n g r) :=
      fun n g r hh => by rw [hueq n g r hh]; exact hu2 n g r hh
    have hcoh : ∀ n (g : Hom n k) r, (ψ.restr g).holds → ∀ n'' (h' : Hom n'' n),
        res h' (u n g r) = u n'' (g.comp h') (r.restr h') := by
      intro n g r hh n'' h'
      have hh' : (ψ.restr (g.comp h')).holds := by rw [← Cof.restr_restr]; exact (hψ.restr g).holds_restr hh h'
      rw [hueq n g r hh, hueq n'' (g.comp h') _ hh']; exact hcoh2 n g r hh n'' h'
    have hbase : ∀ n (g : Hom n k), (ψ.restr g).holds → u n g (DM.zero n) = res g a := fun n g hh => by
      rw [hueq n g _ hh]; exact hbase2 n g hh
    have eline : ∀ n (g : Hom n k), (f.comp (Hom.lift g)).comp (Hom.endpt n (DM.zero n)) =
        (f.comp (Hom.endpt k (DM.zero k))).comp g := fun n g => by
      rw [Hom.comp_assoc, TranspPi.lift_comp_endpt0]; rfl
    have ihu' : ∀ n (g : Hom n k) r (hh : (ψ.restr g).holds), _ := fun n g r hh =>
      ihu n g r hh (hφ.restr g) (hc.restr g) (by rw [eline]; exact hu n g r hh)
    have iha' := iha hφ hc ha2
    have hcoh' : ∀ n (g : Hom n k) r, (ψ.restr g).holds → ∀ n'' (h' : Hom n'' n),
        res h' (u' n g r) = u' n'' (g.comp h') (r.restr h') := by
      intro n g r hh n'' h'
      have hh' : (ψ.restr (g.comp h')).holds := by rw [← Cof.restr_restr]; exact (hψ.restr g).holds_restr hh h'
      have h1 := (ihu' n g r hh).2.2 n'' h'
      rw [hcoh n g r hh n'' h', Hom.comp_assoc, Hom.lift_comp, Cof.restr_restr] at h1
      exact (htu n'' (g.comp h') _ hh').unique h1 rfl |>.symm
    have hbase' : ∀ n (g : Hom n k), (ψ.restr g).holds → u' n g (DM.zero n) = res g a' := by
      intro n g hh
      have h1 := iha'.2.2 n g
      have h2 := htu n g (DM.zero n) hh
      rw [hbase n g hh] at h2
      exact h2.unique h1 rfl
    refine ⟨DElem.hcomp hψ iha'.1 (fun n g r hh => ?_) hcoh' hbase', fun n' h hh => ?_, fun n' h => ?_⟩
    · have := (ihu' n g r hh).1
      rwa [Hom.comp_assoc, TranspPi.lift_comp_endpt1, ← Hom.comp_assoc] at this
    · rw [res_hcV, res_hcV, iha'.2.1 n' h hh]
      refine hcV_congr _ fun n₁ g₁ r hh₁ => ?_
      rw [Cof.restr_restr] at hh₁
      simp only [Tube.restr]
      have H : (φ.restr (h.comp g₁)).holds := by rw [← Cof.restr_restr]; exact (hφ.restr h).holds_restr hh g₁
      have := (ihu' n₁ (h.comp g₁) r hh₁).2.1 n₁ (Hom.id n₁) ((hφ.restr _).holds_restr H _)
      rwa [res_id (htu n₁ (h.comp g₁) r hh₁).out_kv, res_id (hu n₁ (h.comp g₁) r hh₁).kv] at this
    · rw [res_hcV, res_hcV]
      by_cases hh : (ψ.restr h).holds
      · have hkv1 : IsKV n' ((u.restr h) n' (Hom.id n') (DM.one n')) := by
          simpa [Tube.restr] using (hu n' h (DM.one n') hh).kv
        have hkv2 : IsKV n' ((u'.restr h) n' (Hom.id n') (DM.one n')) := by
          simpa [Tube.restr] using (htu n' h (DM.one n') hh).out_kv
        have hc1 : ∀ n₁ (h₁ : Hom n₁ n') r, ((ψ.restr h).restr h₁).holds → ∀ n₂ (h₂ : Hom n₂ n₁),
            res h₂ ((u.restr h) n₁ h₁ r) = (u.restr h) n₂ (h₁.comp h₂) (r.restr h₂) := fun n₁ h₁ r hh₁ n₂ h₂ => by
          rw [Cof.restr_restr] at hh₁; exact hcoh n₁ (h.comp h₁) r hh₁ n₂ h₂
        have hc2 : ∀ n₁ (h₁ : Hom n₁ n') r, ((ψ.restr h).restr h₁).holds → ∀ n₂ (h₂ : Hom n₂ n₁),
            res h₂ ((u'.restr h) n₁ h₁ r) = (u'.restr h) n₂ (h₁.comp h₂) (r.restr h₂) := fun n₁ h₁ r hh₁ n₂ h₂ => by
          rw [Cof.restr_restr] at hh₁; exact hcoh' n₁ (h.comp h₁) r hh₁ n₂ h₂
        rw [hcV_eq_of_holds _ (hψ.restr h) hh hkv1 hc1, hcV_eq_of_holds _ (hψ.restr h) hh hkv2 hc2]
        simp only [Tube.restr, Hom.comp_id]
        exact htu n' h (DM.one n') hh
      · refine TR.hc (hψ.restr h) hh (isKV_res _ _) (iha'.2.2 n' h) (fun n₁ g₁ r hh₁ => ?_)
        rw [Cof.restr_restr] at hh₁
        have := htu n₁ (h.comp g₁) r hh₁
        rwa [← Hom.lift_comp, ← Hom.comp_assoc, ← Cof.restr_restr] at this

end

end Model
