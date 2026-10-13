import Model.DataTrFib

/-!
# Inductive types without path constructors: componentwise composition

`hcD` composes componentwise (`HR`) when the type has no path constructors. Here: existence,
uniqueness and the Kan laws of `HR`, i.e. the composition fields of `fib_dataC`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

theorem bndAtMap_of_nil {C : Ctor} (hb : C.bnd = []) {n k : ℕ} (rs : List (DM n)) (f : Hom k n) :
    bndAtMap C rs f = none := by simp [bndAtMap, hb]

section basic

variable {Λ : SData m}

theorem HR.out_kv {k : ℕ} {g : Hom k m} {φ : Cof k} {u : Tube k} {v w : V} (h : HR Λ k g φ u v w) :
    IsKV k w := by
  cases h; exact isKV_conV _ _ _ _

/-- `HR` only depends on the tube on its face. -/
theorem HR.congr_tube {k : ℕ} {g : Hom k m} {φ : Cof k} {u u' : Tube k} {v w : V} (h : HR Λ k g φ u v w)
    (hu : ∀ n (h : Hom n k) r, (φ.restr h).holds → u n h r = u' n h r) : HR Λ k g φ u' v w := by
  cases h with
  | con hb hkv htu hlo hlf hro hpt =>
    exact HR.con hb hkv (fun n h r hh => by rw [← hu n h r hh]; exact htu n h r hh) hlo hlf hro hpt

theorem hr_restr (h : Hom k m) {n : ℕ} {g : Hom n k} {φ : Cof n} {u : Tube n} {v w : V}
    (hr : HR Λ n (h.comp g) φ u v w) : HR (Λ.restr h) n g φ u v w := by
  induction hr with
  | con hb hkv htu hlo hlf hro hpt iho =>
    refine HR.con hb hkv htu hlo hlf (fun j hj hjr => iho j hj hjr) (fun j hj hjr => ?_)
    have := hpt j hj hjr
    rw [Hom.comp_assoc] at this
    exact this

/-- **Uniqueness** of componentwise composition (on tubes agreeing on the face). -/
theorem HR.unique (hrI : ∀ c j n (g : Hom n m) pre pre', pre.length = pre'.length →
      (∀ i (hi : i < pre.length) (hi' : i < pre'.length), (Λ.ctors.getD c default).isRec i = false →
        pre[i] = pre'[i]) → Λ.ty c j n g pre = Λ.ty c j n g pre')
    {k : ℕ} {g : Hom k m} {φ : Cof k} {u : Tube k} {v w : V} (h : HR Λ k g φ u v w) :
    ∀ {u' v' w'}, HR Λ k g φ u' v' w' → v = v' →
      (∀ n (h : Hom n k) r, (φ.restr h).holds → u n h r = u' n h r) → w = w' := by
  induction h with
  | @con u c args outs fills ua hb hkv htu hlo hlf hro hpt iho =>
    intro u' v' w' h' hv hu
    cases h' with
    | @con _ c2 args2 outs2 fills2 ua2 hb2 hkv2 htu2 hlo2 hlf2 hro2 hpt2 =>
      obtain ⟨rfl, rfl, -⟩ := conV_inj (bndAtMap_of_nil hb _ _) (bndAtMap_of_nil hb2 _ _) hkv hkv2 hv
      have hua : ∀ n (h : Hom n k) r, (φ.restr h).holds → ua n h r = ua2 n h r := by
        intro n h r hh
        obtain ⟨e1, -, k1⟩ := htu n h r hh
        obtain ⟨e2, -, k2⟩ := htu2 n h r hh
        rw [hu n h r hh, e2] at e1
        exact (conV_inj (bndAtMap_of_nil hb _ _) (bndAtMap_of_nil hb _ _) k2 k1 e1).2.1.symm
      have hT : ∀ j, j ≤ args.length →
          (∀ i, i < j → (Λ.ctors.getD c default).isRec i = false → fills.getD i ∅ = fills2.getD i ∅) →
          ∀ j', Λ.ty c j' (k + 1) (g.comp (Hom.wk k)) (fills.take j) =
            Λ.ty c j' (k + 1) (g.comp (Hom.wk k)) (fills2.take j) := by
        intro j hj he j'
        refine hrI _ _ _ _ _ _ (by simp [hlf, hlf2]) fun i hi hi' hr => ?_
        simp only [List.length_take] at hi hi'
        rw [List.getElem_take, List.getElem_take, List.getElem_eq_getD ∅, List.getElem_eq_getD ∅]
        exact he i (by omega) hr
      have hfl : ∀ j, j ≤ args.length →
          ∀ i, i < j → (Λ.ctors.getD c default).isRec i = false → fills.getD i ∅ = fills2.getD i ∅ := by
        intro j
        induction j with
        | zero => intro _ i hi; omega
        | succ j ih =>
          intro hj i hi hr
          by_cases hij : i < j
          · exact ih (by omega) i hij hr
          obtain rfl : i = j := by omega
          rw [(hpt i (by omega) hr).2, (hpt2 i (by omega) hr).2, hT i (by omega) (ih (by omega)), fillF, fillF,
            fillTube_congr (u' := fun n h r => (ua2 n h r).getD i ∅) _ fun n h r hh => by simp only [hua n h r hh]]
      congr 1
      apply List.ext_getElem (by omega)
      intro j h1 h2
      rw [List.getElem_eq_getD ∅, List.getElem_eq_getD ∅]
      cases hr : (Λ.ctors.getD c default).isRec j
      · rw [(hpt j (by omega) hr).1, (hpt2 j (by omega) hr).1, hT j (by omega) (hfl j (by omega))]
        exact compF_congr fun n h r hh => by simp only [hua n h r hh]
      · exact iho j (by omega) hr (hro2 j (by omega) hr) rfl fun n h r hh => by simp only [hua n h r hh]

end basic

theorem gd_map {L : List V} {j : ℕ} (f : V → V) (hj : j < L.length) : (L.map f).getD j ∅ = f (L.getD j ∅) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl

theorem gd_eq {L : List V} {j : ℕ} (hj : j < L.length) : L.getD j ∅ = L[j] := (List.getElem_eq_getD ∅).symm

section inv

variable {Λ : SData m} (hΛ : Λ.Good) (hH : Λ.hit = false)
include hΛ hH

theorem bnd_nil {c : ℕ} {C : Ctor} (hC : Λ.ctors[c]? = some C) : (Λ.ctors.getD c default).bnd = [] := by
  rw [getD_ctors hC]; exact (hΛ.nonhit hH c C hC).2

/-- Without path constructors, elements are constructor values. -/
theorem DElem.nonhit_inv {n : ℕ} {g : Hom n m} {v : V} (hv : DElem Λ n g v) :
    ∃ c C args, Λ.ctors[c]? = some C ∧ v = conV Λ.ctors n c args [] ∧ Λ.ArgsTyped c C n g args := by
  cases hv with
  | @con _ _ c C args rs hC hlen hrs hrec hpt =>
    obtain rfl : rs = [] := List.eq_nil_of_length_eq_zero (by rw [hrs, (hΛ.nonhit hH c C hC).1])
    exact ⟨c, C, args, hC, rfl, hlen, hrec, hpt⟩
  | hcomp hH' => rw [hH] at hH'; cases hH'

omit hH in
theorem argsTyped_kv {c : ℕ} {C : Ctor} (hC : Λ.ctors[c]? = some C) {n : ℕ} {g : Hom n m} {args : List V}
    (ht : Λ.ArgsTyped c C n g args) : ∀ a ∈ args, IsKV n a := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  have hPV : Λ.PtValid c n g args := by
    have := SData.ptValid_take hC ht.2.2 args.length; rwa [List.take_length] at this
  cases hr : C.isRec j
  · exact hΛ.pt_kv hPV hj (by rw [getD_ctors hC]; exact hr)
  · exact (ht.2.1 j _ (List.getElem?_eq_getElem hj) hr).kv

/-- On a tube over a constructor value, every value is a constructor value with the same
constructor (the endpoints of the generic line through it are). -/
theorem tube_con {k : ℕ} {g : Hom k m} {φ : Cof k} (hφ : φ.IsCof) {u : Tube k} {c : ℕ} {C : Ctor}
    {args : List V} (hC : Λ.ctors[c]? = some C) (hkv : ∀ a ∈ args, IsKV k a)
    (hu : TubeOK (dataC Λ) g φ u (conV Λ.ctors k c args [])) {n : ℕ} (h : Hom n k) (r : DM n)
    (hh : (φ.restr h).holds) :
    ∃ as, u n h r = conV Λ.ctors n c as [] ∧ Λ.ArgsTyped c C n (g.comp h) as := by
  have hh1 : (φ.restr (h.comp (Hom.wk n))).holds := by
    rw [← Cof.restr_restr]; exact (hφ.restr h).holds_restr hh _
  obtain ⟨c1, C1, as1, hC1, e1, ht1⟩ := (mem_El_dataC.1 (hu.mem _ _ (lastVar n) hh1)).nonhit_inv hΛ hH
  have hr : ∀ s : DM n, u n h s = res (Hom.snoc (Hom.id n) s) (u (n + 1) (h.comp (Hom.wk n)) (lastVar n)) := by
    intro s
    rw [hu.coh _ _ _ hh1, Hom.comp_assoc, Hom.wk_comp_snoc, Hom.comp_id, lastVar_restr_snoc]
  have h0 := hr (DM.zero n)
  rw [hu.base n h hh, e1, res_conV, res_conV, List.map_nil] at h0
  obtain ⟨rfl, -, -⟩ := conV_inj (bndAtMap_of_nil (bnd_nil hΛ hH hC) _ _) (bndAtMap_of_nil (bnd_nil hΛ hH hC1) _ _)
    (fun a ha => by obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha; exact isKV_res _ _)
    (fun a ha => by obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha; exact isKV_res _ _) h0
  obtain ⟨c2, C2, as2, hC2, e2, ht2⟩ := (mem_El_dataC.1 (hu.mem n h r hh)).nonhit_inv hΛ hH
  have h1 := hr r
  rw [e1, res_conV, e2, List.map_nil] at h1
  obtain ⟨rfl, -, -⟩ := conV_inj (bndAtMap_of_nil (bnd_nil hΛ hH hC2) _ _) (bndAtMap_of_nil (bnd_nil hΛ hH hC1) _ _)
    (argsTyped_kv hΛ hC2 ht2) (fun a ha => by obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha; exact isKV_res _ _) h1
  rw [hC] at hC2; cases hC2
  exact ⟨as2, e2, ht2⟩

/-- The arguments of the tube values of an `HR` derivation: typed, coherent, and the base's at
`0`. -/
theorem tube_args_facts {k : ℕ} {g : Hom k m} {φ : Cof k} (hφ : φ.IsCof) {u : Tube k} {c : ℕ} {C : Ctor}
    {args : List V} {ua : (n : ℕ) → Hom n k → DM n → List V} (hC : Λ.ctors[c]? = some C)
    (hta : Λ.ArgsTyped c C k g args)
    (hu : TubeOK (dataC Λ) g φ u (conV Λ.ctors k c args []))
    (htu : ∀ n (h : Hom n k) r, (φ.restr h).holds →
        u n h r = conV Λ.ctors n c (ua n h r) [] ∧ (ua n h r).length = args.length ∧
          ∀ a ∈ ua n h r, IsKV n a) :
    (∀ n (h : Hom n k) r, (φ.restr h).holds → Λ.ArgsTyped c C n (g.comp h) (ua n h r)) ∧
    (∀ n (h : Hom n k) r, (φ.restr h).holds → ∀ n' (h' : Hom n' n),
      (ua n h r).map (res h') = ua n' (h.comp h') (r.restr h')) ∧
    (∀ n (h : Hom n k), (φ.restr h).holds → ua n h (DM.zero n) = args.map (res h)) := by
  have hb := bnd_nil hΛ hH hC
  have hkv := argsTyped_kv hΛ hC hta
  have hmkv : ∀ {n n'} (h : Hom n' n) (L : List V), ∀ a ∈ L.map (res h), IsKV n' a := fun h L a ha => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha; exact isKV_res _ _
  refine ⟨fun n h r hh => ?_, fun n h r hh n' h' => ?_, fun n h hh => ?_⟩
  · obtain ⟨as, e, ht⟩ := tube_con hΛ hH hφ hC hkv hu h r hh
    obtain ⟨e', -, hk⟩ := htu n h r hh
    rw [e'] at e
    obtain ⟨-, rfl, -⟩ := conV_inj (bndAtMap_of_nil hb _ _) (bndAtMap_of_nil hb _ _) hk (argsTyped_kv hΛ hC ht) e
    exact ht
  · have hh' : (φ.restr (h.comp h')).holds := by
      rw [← Cof.restr_restr]; exact (hφ.restr h).holds_restr hh h'
    have e := hu.coh n h r hh n' h'
    rw [(htu n h r hh).1, (htu n' (h.comp h') _ hh').1, res_conV, List.map_nil] at e
    exact (conV_inj (bndAtMap_of_nil hb _ _) (bndAtMap_of_nil hb _ _) (hmkv _ _) (htu n' _ _ hh').2.2 e).2.1
  · have e := hu.base n h hh
    rw [(htu n h _ hh).1, res_conV, List.map_nil] at e
    exact (conV_inj (bndAtMap_of_nil hb _ _) (bndAtMap_of_nil hb _ _) (htu n h _ hh).2.2 (hmkv _ _) e).2.1

end inv

theorem ty_take_eq {Λ : SData m} (hΛ : Λ.Good) {c j' n : ℕ} {g : Hom n m} {L L' : List V} {j : ℕ}
    (hL : j ≤ L.length) (hL' : j ≤ L'.length)
    (he : ∀ i, i < j → (Λ.ctors.getD c default).isRec i = false → L.getD i ∅ = L'.getD i ∅) :
    Λ.ty c j' n g (L.take j) = Λ.ty c j' n g (L'.take j) := by
  refine hΛ.recIrr _ _ _ _ _ _ (by simp; omega) fun i hi hi' hr => ?_
  simp only [List.length_take] at hi hi'
  rw [List.getElem_take, List.getElem_take, ← gd_eq, ← gd_eq]
  exact he i (by omega) hr

/-- The properties of a componentwise composition. -/
def HRProps (Λ : SData m) (k : ℕ) (g : Hom k m) (φ : Cof k) (u : Tube k) (v w : V) : Prop :=
  φ.IsCof → DElem Λ k g v → TubeOK (dataC Λ) g φ u v →
    DElem Λ k g w ∧
    (∀ n (h : Hom n k), (φ.restr h).holds → res h w = u n h (DM.one n)) ∧
    (∀ n (h : Hom n k), HR Λ n (g.comp h) (φ.restr h) (u.restr h) (res h v) (res h w))

section con

variable {Λ : SData m} (hΛ : Λ.Good) (hH : Λ.hit = false) {k : ℕ} {g : Hom k m} {φ : Cof k} {c : ℕ} {C : Ctor}
  {args outs fills : List V} {ua : (n : ℕ) → Hom n k → DM n → List V}
  (hC : Λ.ctors[c]? = some C) (hta : Λ.ArgsTyped c C k g args) (hφ : φ.IsCof)
  (hlo : outs.length = args.length) (hlf : fills.length = args.length)
  (hut : ∀ n (h : Hom n k) r, (φ.restr h).holds → Λ.ArgsTyped c C n (g.comp h) (ua n h r))
  (huc : ∀ n (h : Hom n k) r, (φ.restr h).holds → ∀ n' (h' : Hom n' n),
    (ua n h r).map (res h') = ua n' (h.comp h') (r.restr h'))
  (hub : ∀ n (h : Hom n k), (φ.restr h).holds → ua n h (DM.zero n) = args.map (res h))
  (hpt : ∀ j (hj : j < args.length), (Λ.ctors.getD c default).isRec j = false →
    outs.getD j ∅ = compF (Λ.ty c j (k + 1) (g.comp (Hom.wk k)) (fills.take j)) (Hom.id (k + 1)) φ
      (fun n h r => (ua n h r).getD j ∅) args[j] ∧
    fills.getD j ∅ = fillF (Λ.ty c j (k + 1) (g.comp (Hom.wk k)) (fills.take j)) (Hom.id (k + 1)) φ
      (fun n h r => (ua n h r).getD j ∅) args[j])
include hΛ hC hta hφ hlo hlf hut huc hub hpt

/-- The invariants of the fillers, for the point arguments among the first `j`. -/
def HFillInv (Λ : SData m) (k : ℕ) (g : Hom k m) (φ : Cof k) (c : ℕ) (args outs fills : List V)
    (ua : (n : ℕ) → Hom n k → DM n → List V) (j : ℕ) : Prop :=
  Λ.PtValid c (k + 1) (g.comp (Hom.wk k)) (fills.take j) ∧ ∀ i (hi : i < j) (hia : i < args.length),
    (Λ.ctors.getD c default).isRec i = false →
    res (Hom.endpt k (DM.zero k)) (fills.getD i ∅) = args[i] ∧
    res (Hom.endpt k (DM.one k)) (fills.getD i ∅) = outs.getD i ∅ ∧
    ∀ n (h : Hom n k), (φ.restr h).holds → ∀ r, res (Hom.snoc h r) (fills.getD i ∅) = (ua n h r).getD i ∅

omit hΛ hC hφ hlo hlf hpt in
theorem comp_tube_coh {j : ℕ} (hj : j < args.length) (n : ℕ) (h : Hom n k) (r : DM n) (hh : (φ.restr h).holds)
    (n' : ℕ) (h' : Hom n' n) :
    res h' ((ua n h r).getD j ∅) = (ua n' (h.comp h') (r.restr h')).getD j ∅ := by
  rw [← huc n h r hh n' h', gd_map _ (by rw [(hut n h r hh).1, ← hta.1]; exact hj)]

omit hΛ hC hφ hlo hlf hpt in
theorem comp_tube_base {j : ℕ} (hj : j < args.length) (n : ℕ) (h : Hom n k) (hh : (φ.restr h).holds) :
    (ua n h (DM.zero n)).getD j ∅ = res h args[j] := by
  rw [hub n h hh, gd_map _ hj, gd_eq hj]

theorem hfill_ty_facts {i : ℕ} (hi : i < args.length) (hr : (Λ.ctors.getD c default).isRec i = false)
    (hinv : HFillInv Λ k g φ c args outs fills ua i) :
    Fib (Λ.ty c i (k + 1) (g.comp (Hom.wk k)) (fills.take i)) (k + 1) ∧
    args[i] ∈ El (Λ.ty c i (k + 1) (g.comp (Hom.wk k)) (fills.take i)) ((Hom.id (k + 1)).comp (Hom.endpt k (DM.zero k))) ∧
    LineTubeOK (Λ.ty c i (k + 1) (g.comp (Hom.wk k)) (fills.take i)) (Hom.id (k + 1)) φ
      (fun n h r => (ua n h r).getD i ∅) args[i] := by
  have hpv := hinv.1
  have hr' : C.isRec i = false := by rw [← getD_ctors hC]; exact hr
  refine ⟨hΛ.fib c i (k + 1) _ _ hpv, ?_, ⟨fun n h r hh => ?_, fun n h r hh n' h' => comp_tube_coh hta hut huc hub hi n h r hh n' h',
    fun n h hh => comp_tube_base hta hut huc hub hi n h hh⟩⟩
  · rw [El_eq_res_id, Hom.id_comp, hΛ.nat c i (k + 1) _ _ hpv k _, Hom.comp_assoc, Hom.wk_comp_endpt, Hom.comp_id,
      List.map_take, ty_take_eq hΛ (L' := args) (by simp [hlf]; omega) (by omega) (fun i' hi' hr'' => by
        rw [gd_map _ (by omega)]; exact ((hinv.2 i' hi' (by omega) hr'').1).trans (gd_eq (by omega)).symm)]
    exact hta.2.2 i _ (List.getElem?_eq_getElem hi) hr'
  · have hl : (ua n h r).length = args.length := by rw [(hut n h r hh).1, ← hta.1]
    rw [El_eq_res_id, Hom.id_comp, hΛ.nat c i (k + 1) _ _ hpv n _, Hom.comp_assoc, Hom.wk_comp_snoc,
      List.map_take, ty_take_eq hΛ (L' := ua n h r) (by simp [hlf]; omega) (by omega) (fun i' hi' hr'' => by
        rw [gd_map _ (by omega)]; exact (hinv.2 i' hi' (by omega) hr'').2.2 n h hh r), gd_eq (by omega)]
    exact (hut n h r hh).2.2 i _ (List.getElem?_eq_getElem (by omega)) hr'

theorem hfillInv_all : ∀ j ≤ args.length, HFillInv Λ k g φ c args outs fills ua j := by
  intro j
  induction j with
  | zero => intro _; exact ⟨fun i hi => by simp at hi, fun i hi => absurd hi (by omega)⟩
  | succ j ih =>
    intro hj
    have hinv := ih (by omega)
    have hjl : j < args.length := by omega
    by_cases hr : (Λ.ctors.getD c default).isRec j = true
    · refine ⟨ptValid_take_succ (by omega) hinv.1 (fun h => absurd (hr.symm.trans h) (by decide)), fun i hi hia hri => ?_⟩
      by_cases hij : i < j
      · exact hinv.2 i hij hia hri
      obtain rfl : i = j := by omega
      exact absurd (hr.symm.trans hri) (by decide)
    · have hr' : (Λ.ctors.getD c default).isRec j = false := by simpa using hr
      obtain ⟨hfib, hbase, htube⟩ := hfill_ty_facts hΛ hC hta hφ hlo hlf hut huc hub hpt hjl hr' hinv
      have hfill := (hpt j hjl hr').2
      refine ⟨ptValid_take_succ (by omega) hinv.1 (fun _ => ?_), fun i hi hia hri => ?_⟩
      · rw [← gd_eq (by omega), hfill]; exact fillF_mem hfib hφ hbase htube
      by_cases hij : i < j
      · exact hinv.2 i hij hia hri
      obtain rfl : i = j := by omega
      refine ⟨?_, ?_, fun n h hh r => ?_⟩
      · rw [hfill]; exact fillF_endpt0 hfib hφ hbase htube
      · rw [hfill, fillF_endpt1 hfib hφ hbase htube, (hpt i hjl hr').1]
      · rw [hfill]; exact fillF_face hfib hφ hbase htube h hh r

theorem hfills_ptValid : Λ.PtValid c (k + 1) (g.comp (Hom.wk k)) fills := by
  have := (hfillInv_all hΛ hC hta hφ hlo hlf hut huc hub hpt args.length le_rfl).1
  rwa [← hlf, List.take_length] at this

theorem hcon_point_facts {j : ℕ} (hj : j < args.length) (hr : (Λ.ctors.getD c default).isRec j = false) :
    Fib (Λ.ty c j (k + 1) (g.comp (Hom.wk k)) (fills.take j)) (k + 1) ∧
    args[j] ∈ El (Λ.ty c j (k + 1) (g.comp (Hom.wk k)) (fills.take j)) ((Hom.id (k + 1)).comp (Hom.endpt k (DM.zero k))) ∧
    LineTubeOK (Λ.ty c j (k + 1) (g.comp (Hom.wk k)) (fills.take j)) (Hom.id (k + 1)) φ
      (fun n h r => (ua n h r).getD j ∅) args[j] :=
  hfill_ty_facts hΛ hC hta hφ hlo hlf hut huc hub hpt hj hr
    (hfillInv_all hΛ hC hta hφ hlo hlf hut huc hub hpt j (by omega))

omit hΛ hC hφ hlo hlf hpt in
theorem comp_tube_ok {j : ℕ} (hj : j < args.length) (hr : C.isRec j = true) :
    TubeOK (dataC Λ) g φ (fun n h r => (ua n h r).getD j ∅) args[j] where
  mem n h r hh := by
    rw [mem_El_dataC, gd_eq (by rw [(hut n h r hh).1, ← hta.1]; exact hj)]
    exact (hut n h r hh).2.1 j _ (List.getElem?_eq_getElem _) hr
  coh n h r hh n' h' := comp_tube_coh hta hut huc hub hj n h r hh n' h'
  base n h hh := comp_tube_base hta hut huc hub hj n h hh

variable (iho : ∀ j (hj : j < args.length), (Λ.ctors.getD c default).isRec j = true →
    HRProps Λ k g φ (fun n h r => (ua n h r).getD j ∅) args[j] (outs.getD j ∅))
include iho

theorem hcon_rec {j : ℕ} (hj : j < args.length) (hr : C.isRec j = true) :
    DElem Λ k g (outs.getD j ∅) ∧
    (∀ n (h : Hom n k), (φ.restr h).holds → res h (outs.getD j ∅) = (ua n h (DM.one n)).getD j ∅) ∧
    (∀ n (h : Hom n k), HR Λ n (g.comp h) (φ.restr h) (fun n' h' r => (ua n' (h.comp h') r).getD j ∅)
      (res h args[j]) (res h (outs.getD j ∅))) :=
  iho j hj (by rw [getD_ctors hC]; exact hr) hφ (hta.2.1 j _ (List.getElem?_eq_getElem hj) hr)
    (comp_tube_ok hta hut huc hub hj hr)

theorem hcon_outs_typed : Λ.ArgsTyped c C k g outs := by
  have hinv := hfillInv_all hΛ hC hta hφ hlo hlf hut huc hub hpt args.length le_rfl
  refine ⟨by rw [hlo]; exact hta.1, fun j a ha hr => ?_, fun j a ha hr => ?_⟩
  · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 ha
    rw [← gd_eq hj]
    exact (hcon_rec hΛ hC hta hφ hlo hlf hut huc hub hpt iho (by omega) hr).1
  · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 ha
    have hj' : j < args.length := by omega
    have hr' : (Λ.ctors.getD c default).isRec j = false := by rw [getD_ctors hC]; exact hr
    obtain ⟨hfib, hbase, htube⟩ := hcon_point_facts hΛ hC hta hφ hlo hlf hut huc hub hpt hj' hr'
    rw [← gd_eq hj, (hpt j hj' hr').1]
    have := compF_mem hfib hφ hbase htube
    rw [El_eq_res_id, Hom.id_comp, hΛ.nat c j (k + 1) _ _ ((hfills_ptValid hΛ hC hta hφ hlo hlf hut huc hub hpt).take j) k _,
      Hom.comp_assoc, Hom.wk_comp_endpt, Hom.comp_id, List.map_take,
      ty_take_eq hΛ (L' := outs) (by simp [hlf]; omega) (by omega) (fun i' hi' hr'' => by
        rw [gd_map _ (by omega)]; exact (hinv.2 i' (by omega) (by omega) hr'').2.1)] at this
    exact this

theorem hcon_face (u : Tube k) (htu : ∀ n (h : Hom n k) r, (φ.restr h).holds → u n h r = conV Λ.ctors n c (ua n h r) [])
    (n : ℕ) (h : Hom n k) (hh : (φ.restr h).holds) :
    res h (conV Λ.ctors k c outs []) = u n h (DM.one n) := by
  rw [res_conV, List.map_nil, htu n h _ hh]
  congr 1
  have hl : (ua n h (DM.one n)).length = args.length := by rw [(hut n h _ hh).1, ← hta.1]
  apply List.ext_getElem (by simp [hlo, hl])
  intro j h1 h2
  simp only [List.length_map] at h1
  rw [List.getElem_map, ← gd_eq h1, ← gd_eq h2]
  cases hr : C.isRec j
  · have hr' : (Λ.ctors.getD c default).isRec j = false := by rw [getD_ctors hC]; exact hr
    obtain ⟨hfib, hbase, htube⟩ := hcon_point_facts hΛ hC hta hφ hlo hlf hut huc hub hpt (by omega) hr'
    rw [(hpt j (by omega) hr').1, compF_restr_face hfib hφ hbase htube h hh]
  · exact (hcon_rec hΛ hC hta hφ hlo hlf hut huc hub hpt iho (by omega) hr).2.1 n h hh

theorem hcon_res (u : Tube k) (hb : (Λ.ctors.getD c default).bnd = [])
    (htu : ∀ n (h : Hom n k) r, (φ.restr h).holds →
        u n h r = conV Λ.ctors n c (ua n h r) [] ∧ (ua n h r).length = args.length ∧
          ∀ a ∈ ua n h r, IsKV n a)
    (n : ℕ) (h : Hom n k) :
    HR Λ n (g.comp h) (φ.restr h) (u.restr h) (res h (conV Λ.ctors k c args [])) (res h (conV Λ.ctors k c outs [])) := by
  have hpv := hfills_ptValid hΛ hC hta hφ hlo hlf hut huc hub hpt
  rw [res_conV, res_conV, List.map_nil]
  refine HR.con (ua := fun n' h' r => ua n' (h.comp h') r) (fills := fills.map (res (Hom.lift h))) hb
    (fun a ha => by obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha; exact isKV_res _ _)
    (fun n' h' r hh => by
      rw [Cof.restr_restr] at hh
      obtain ⟨e, hl, hk⟩ := htu n' (h.comp h') r hh
      exact ⟨e, by simp [hl], hk⟩) (by simp [hlo]) (by simp [hlf]) (fun j hj hr => ?_) (fun j hj hr => ?_)
  · simp only [List.length_map] at hj
    rw [gd_map _ (by omega), List.getElem_map]
    exact (hcon_rec hΛ hC hta hφ hlo hlf hut huc hub hpt iho hj (by rw [← getD_ctors hC]; exact hr)).2.2 n h
  · simp only [List.length_map] at hj
    obtain ⟨hfib, hbase, htube⟩ := hcon_point_facts hΛ hC hta hφ hlo hlf hut huc hub hpt hj hr
    have hpj := hpt j hj hr
    have hT : res (Hom.lift h) (Λ.ty c j (k + 1) (g.comp (Hom.wk k)) (fills.take j)) =
        Λ.ty c j (n + 1) ((g.comp h).comp (Hom.wk n)) ((fills.map (res (Hom.lift h))).take j) := by
      rw [hΛ.nat c j (k + 1) _ _ (hpv.take j) (n + 1) (Hom.lift h), List.map_take, Hom.comp_assoc,
        Hom.wk_comp_lift, ← Hom.comp_assoc]
    rw [gd_map _ (by omega), gd_map _ (by omega), hpj.1, hpj.2, List.getElem_map, ← hT, compF_res_id, fillF_res_id,
      compF_res hfib hφ hbase htube h, fillF_natural hfib hφ hbase htube h, Hom.id_comp]
    exact ⟨rfl, rfl⟩

end con

section props

variable {Λ : SData m} (hΛ : Λ.Good) (hH : Λ.hit = false)
include hΛ hH

theorem HR.props {k : ℕ} {g : Hom k m} {φ : Cof k} {u : Tube k} {v w : V} (hr : HR Λ k g φ u v w) :
    HRProps Λ k g φ u v w := by
  induction hr with
  | @con u c args outs fills ua hb hkv htu hlo hlf hro hpt iho =>
    intro hφ hv hu
    obtain ⟨c', C, args', hC, e, hta⟩ := hv.nonhit_inv hΛ hH
    obtain ⟨rfl, rfl, -⟩ := conV_inj (bndAtMap_of_nil hb _ _) (bndAtMap_of_nil (bnd_nil hΛ hH hC) _ _) hkv
      (argsTyped_kv hΛ hC hta) e
    obtain ⟨hut, huc, hub⟩ := tube_args_facts hΛ hH hφ hC hta hu htu
    have hto := hcon_outs_typed hΛ hC hta hφ hlo hlf hut huc hub hpt iho
    exact ⟨DElem.con hC hto.1 (by rw [(hΛ.nonhit hH c C hC).1]; rfl) hto.2.1 hto.2.2,
      hcon_face hΛ hC hta hφ hlo hlf hut huc hub hpt iho u (fun n h r hh => (htu n h r hh).1),
      hcon_res hΛ hC hta hφ hlo hlf hut huc hub hpt iho u hb htu⟩

end props


section exist

variable {Λ : SData m}

/-- The output and filler lists of a componentwise composition exist once the recursive
arguments can be composed. -/
theorem exists_outs_fills_hr (c k : ℕ) (g : Hom k m) (φ : Cof k) (args : List V)
    (ua : (n : ℕ) → Hom n k → DM n → List V)
    (hrec : ∀ j (hj : j < args.length), (Λ.ctors.getD c default).isRec j = true →
      ∃ w, HR Λ k g φ (fun n h r => (ua n h r).getD j ∅) args[j] w) :
    ∃ outs fills : List V, outs.length = args.length ∧ fills.length = args.length ∧
      (∀ j (hj : j < args.length), (Λ.ctors.getD c default).isRec j = true →
        HR Λ k g φ (fun n h r => (ua n h r).getD j ∅) args[j] (outs.getD j ∅)) ∧
      (∀ j (hj : j < args.length), (Λ.ctors.getD c default).isRec j = false →
        outs.getD j ∅ = compF (Λ.ty c j (k + 1) (g.comp (Hom.wk k)) (fills.take j)) (Hom.id (k + 1)) φ
          (fun n h r => (ua n h r).getD j ∅) args[j] ∧
        fills.getD j ∅ = fillF (Λ.ty c j (k + 1) (g.comp (Hom.wk k)) (fills.take j)) (Hom.id (k + 1)) φ
          (fun n h r => (ua n h r).getD j ∅) args[j]) := by
  suffices ∀ J (hJ : J ≤ args.length), ∃ outs fills : List V, outs.length = J ∧ fills.length = J ∧
      (∀ j (hj : j < J), (Λ.ctors.getD c default).isRec j = true →
        HR Λ k g φ (fun n h r => (ua n h r).getD j ∅) (args[j]'(by omega)) (outs.getD j ∅)) ∧
      (∀ j (hj : j < J), (Λ.ctors.getD c default).isRec j = false →
        outs.getD j ∅ = compF (Λ.ty c j (k + 1) (g.comp (Hom.wk k)) (fills.take j)) (Hom.id (k + 1)) φ
          (fun n h r => (ua n h r).getD j ∅) (args[j]'(by omega)) ∧
        fills.getD j ∅ = fillF (Λ.ty c j (k + 1) (g.comp (Hom.wk k)) (fills.take j)) (Hom.id (k + 1)) φ
          (fun n h r => (ua n h r).getD j ∅) (args[j]'(by omega))) by
    obtain ⟨outs, fills, h1, h2, h3, h4⟩ := this args.length le_rfl
    exact ⟨outs, fills, h1, h2, h3, h4⟩
  intro J
  induction J with
  | zero => intro _; exact ⟨[], [], rfl, rfl, fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega)⟩
  | succ J ih =>
    intro hJ
    obtain ⟨outs, fills, h1, h2, h3, h4⟩ := ih (by omega)
    have gl : ∀ (L : List V) (x : V) j, j < L.length → (L ++ [x]).getD j ∅ = L.getD j ∅ := by
      intro L x j hj
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    have gr : ∀ (L : List V) (x : V) j, L.length = j → (L ++ [x]).getD j ∅ = x := by
      intro L x j hj; subst hj; simp
    have tk : ∀ (L : List V) (x : V) j, j ≤ L.length → (L ++ [x]).take j = L.take j := by
      intro L x j hj; simp [List.take_append_of_le_length hj]
    by_cases hr : (Λ.ctors.getD c default).isRec J = true
    · obtain ⟨o, ho⟩ := hrec J (by omega) hr
      refine ⟨outs ++ [o], fills ++ [∅], by simp [h1], by simp [h2], fun j hj hjr => ?_, fun j hj hjr => ?_⟩
      · by_cases hjJ : j < J
        · rw [gl _ _ _ (by omega)]; exact h3 j hjJ hjr
        · obtain rfl : j = J := by omega
          rw [gr _ _ _ h1]; exact ho
      · by_cases hjJ : j < J
        · rw [gl _ _ _ (by omega), gl _ _ _ (by omega), tk _ _ _ (by omega)]; exact h4 j hjJ hjr
        · obtain rfl : j = J := by omega
          rw [hjr] at hr; exact absurd hr (by decide)
    · have hr' : (Λ.ctors.getD c default).isRec J = false := by simpa using hr
      refine ⟨outs ++ [compF (Λ.ty c J (k + 1) (g.comp (Hom.wk k)) fills) (Hom.id (k + 1)) φ
          (fun n h r => (ua n h r).getD J ∅) (args[J]'(by omega))],
        fills ++ [fillF (Λ.ty c J (k + 1) (g.comp (Hom.wk k)) fills) (Hom.id (k + 1)) φ
          (fun n h r => (ua n h r).getD J ∅) (args[J]'(by omega))],
        by simp [h1], by simp [h2], fun j hj hjr => ?_, fun j hj hjr => ?_⟩
      · by_cases hjJ : j < J
        · rw [gl _ _ _ (by omega)]; exact h3 j hjJ hjr
        · obtain rfl : j = J := by omega
          rw [hr'] at hjr; exact absurd hjr (by decide)
      · by_cases hjJ : j < J
        · rw [gl _ _ _ (by omega), gl _ _ _ (by omega), tk _ _ _ (by omega)]; exact h4 j hjJ hjr
        · obtain rfl : j = J := by omega
          have htk : fills.take j = fills := by rw [← h2, List.take_length]
          rw [gr _ _ _ h1, gr _ _ _ h2, tk _ _ _ (by omega), htk]
          exact ⟨rfl, rfl⟩

variable (hΛ : Λ.Good) (hH : Λ.hit = false)
include hΛ hH

/-- **Existence** of componentwise composition on elements. -/
theorem hr_exists {k : ℕ} {g : Hom k m} {v : V} (hv : DElem Λ k g v) :
    ∀ (φ : Cof k) (u : Tube k), φ.IsCof → TubeOK (dataC Λ) g φ u v → ∃ w, HR Λ k g φ u v w := by
  induction hv with
  | @con n g c C args rs hC hlen hrs hrec hpt ih =>
    intro φ u hφ hu
    obtain rfl : rs = [] := List.eq_nil_of_length_eq_zero (by rw [hrs, (hΛ.nonhit hH c C hC).1])
    have hta : Λ.ArgsTyped c C n g args := ⟨hlen, hrec, hpt⟩
    have hkv := argsTyped_kv hΛ hC hta
    have hx : ∀ n' (h : Hom n' n) r, (φ.restr h).holds →
        ∃ as, u n' h r = conV Λ.ctors n' c as [] ∧ Λ.ArgsTyped c C n' (g.comp h) as :=
      fun n' h r hh => tube_con hΛ hH hφ hC hkv hu h r hh
    let ua : (n' : ℕ) → Hom n' n → DM n' → List V := fun n' h r =>
      if hh : (φ.restr h).holds then Classical.choose (hx n' h r hh) else []
    have hua : ∀ n' (h : Hom n' n) r (hh : (φ.restr h).holds),
        u n' h r = conV Λ.ctors n' c (ua n' h r) [] ∧ Λ.ArgsTyped c C n' (g.comp h) (ua n' h r) := by
      intro n' h r hh
      simp only [ua, dif_pos hh]
      exact Classical.choose_spec (hx n' h r hh)
    have htu : ∀ n' (h : Hom n' n) r, (φ.restr h).holds →
        u n' h r = conV Λ.ctors n' c (ua n' h r) [] ∧ (ua n' h r).length = args.length ∧
          ∀ a ∈ ua n' h r, IsKV n' a := fun n' h r hh =>
      ⟨(hua n' h r hh).1, by rw [(hua n' h r hh).2.1, hlen], argsTyped_kv hΛ hC (hua n' h r hh).2⟩
    obtain ⟨hut, huc, hub⟩ := tube_args_facts hΛ hH hφ hC hta hu htu
    obtain ⟨outs, fills, h1, h2, h3, h4⟩ := exists_outs_fills_hr c n g φ args ua (fun j hj hr => by
      have hr' : C.isRec j = true := by rwa [getD_ctors hC] at hr
      exact ih j _ (List.getElem?_eq_getElem hj) hr' φ _ hφ (comp_tube_ok hta hut huc hub hj hr'))
    exact ⟨_, HR.con (bnd_nil hΛ hH hC) hkv htu h1 h2 h3 h4⟩
  | hcomp hH' => rw [hH] at hH'; cases hH'

theorem hcD_eq {k : ℕ} {g : Hom k m} {φ : Cof k} {u : Tube k} {v w : V} (hr : HR Λ k g φ u v w) :
    hcD Λ k g φ u v = w := by
  have hex : ∃ w, HR Λ k g φ u v w := ⟨w, hr⟩
  rw [hcD, if_neg (by simp [hH]), dif_pos hex]
  exact (Classical.choose_spec hex).unique hΛ.recIrr hr rfl fun _ _ _ _ => rfl

end exist

section

variable {Θ : SData m} (hΘ : Θ.Good) (hH : Θ.hit = false)
include hΘ hH

variable {f : Hom k m} {φ : Cof k} {u : Tube k} {u0 : V}

omit hΘ hH in
theorem tubeOK_restr_canon (hφ : φ.IsCof) (hu : TubeOK (dataC Θ) f φ u u0) :
    TubeOK (dataC (Θ.restr f)) (Hom.id k) φ (Tube.canon φ u) u0 where
  mem n h r hh := by
    rw [mem_El_dataC, delem_restr_iff, Hom.id_comp, ← mem_El_dataC]
    simp only [Tube.canon, if_pos hh]; exact hu.mem n h r hh
  coh n h r hh n' h' := by
    have hh' : (φ.restr (h.comp h')).holds := by
      rw [← Cof.restr_restr]; exact (hφ.restr h).holds_restr hh h'
    simp only [Tube.canon, if_pos hh, if_pos hh']; exact hu.coh n h r hh n' h'
  base n h hh := by simp only [Tube.canon, if_pos hh]; exact hu.base n h hh

/-- The composition of `dataC Θ` (without path constructors) as a componentwise composition. -/
theorem hcompAt_dataC_HR (hφ : φ.IsCof) (hu0 : u0 ∈ El (dataC Θ) f) (hu : TubeOK (dataC Θ) f φ u u0) :
    HR (Θ.restr f) k (Hom.id k) φ (Tube.canon φ u) u0 (hcompAt (dataC Θ) f φ u u0) ∧
    DElem (Θ.restr f) k (Hom.id k) u0 := by
  have hv : DElem (Θ.restr f) k (Hom.id k) u0 := by
    rw [delem_restr_iff, Hom.comp_id]; exact mem_El_dataC.1 hu0
  obtain ⟨w, hw⟩ := hr_exists (hΘ.restr f) hH hv φ _ hφ (tubeOK_restr_canon hφ hu)
  rw [hcompAt_dataC_gen hu hu0, hcD_eq (hΘ.restr f) hH hw]
  exact ⟨hw, hv⟩

theorem dataC_hcMem_nonHIT (hφ : φ.IsCof) (hu0 : u0 ∈ El (dataC Θ) f) (hu : TubeOK (dataC Θ) f φ u u0) :
    hcompAt (dataC Θ) f φ u u0 ∈ El (dataC Θ) f := by
  obtain ⟨hw, hv⟩ := hcompAt_dataC_HR hΘ hH hφ hu0 hu
  have := (hw.props (hΘ.restr f) hH hφ hv (tubeOK_restr_canon hφ hu)).1
  rw [delem_restr_iff, Hom.comp_id] at this
  exact mem_El_dataC.2 this

theorem dataC_hcFace_nonHIT (hφ : φ.IsCof) (hu0 : u0 ∈ El (dataC Θ) f) (hu : TubeOK (dataC Θ) f φ u u0)
    (hh : φ.holds) : hcompAt (dataC Θ) f φ u u0 = u k (Hom.id k) (DM.one k) := by
  obtain ⟨hw, hv⟩ := hcompAt_dataC_HR hΘ hH hφ hu0 hu
  have hh' : (φ.restr (Hom.id k)).holds := hφ.holds_restr hh _
  have := (hw.props (hΘ.restr f) hH hφ hv (tubeOK_restr_canon hφ hu)).2.1 k (Hom.id k) hh'
  rw [res_id hw.out_kv] at this
  rw [this]; simp only [Tube.canon, if_pos hh']

theorem dataC_hcRes_nonHIT (hφ : φ.IsCof) (hu0 : u0 ∈ El (dataC Θ) f)
    (hu : TubeOK (dataC Θ) f φ u u0) (n : ℕ) (h : Hom n k) :
    res h (hcompAt (dataC Θ) f φ u u0) =
      hcompAt (dataC Θ) (f.comp h) (φ.restr h) (u.restr h) (res h u0) := by
  obtain ⟨hw, hv⟩ := hcompAt_dataC_HR hΘ hH hφ hu0 hu
  have hu0' : res h u0 ∈ El (dataC Θ) (f.comp h) := dataC_elRes hΘ.resClosed f u0 hu0 n h
  have hr := (hw.props (hΘ.restr f) hH hφ hv (tubeOK_restr_canon hφ hu)).2.2 n h
  rw [Hom.id_comp] at hr
  have hr' : HR (Θ.restr (f.comp h)) n (Hom.id n) _ _ _ _ := hr_restr h (by rwa [Hom.comp_id])
  rw [(hcompAt_dataC_HR hΘ hH (hφ.restr h) hu0' (hu.restr h)).1.unique (hΘ.restr (f.comp h)).recIrr hr' rfl]
  intro n' h' r hh
  have hh' : (φ.restr (h.comp h')).holds := by rw [← Cof.restr_restr]; exact hh
  simp only [Tube.canon, Tube.restr, if_pos hh, if_pos hh']

end

end

end Model
