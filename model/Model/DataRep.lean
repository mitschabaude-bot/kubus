import Model.DataFib

/-!
# Inductive types: representations are unique; transport is functional

A constructor value without boundary at its own stage determines its constructor, (Kripke-value)
arguments and interval arguments; a formal composition whose face does not hold determines its
face, its tube on the face and its (Kripke-value) base; and the two kinds are distinct. Hence the
transport relation `TR` is functional.
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

theorem pair_ne_empty (a b : V) : ZFSet.pair a b ≠ ∅ := by
  intro h
  have : ({a} : V) ∈ ZFSet.pair a b := by simp [ZFSet.pair]
  rw [h] at this; exact ZFSet.notMem_empty _ this

theorem vlist_injective : Function.Injective vlist := by
  intro as bs h
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => rfl
    | cons b bs => exact absurd h.symm (by simp only [vlist]; exact pair_ne_empty _ _)
  | cons a as ih =>
    cases bs with
    | nil => exact absurd h (by simp only [vlist]; exact pair_ne_empty _ _)
    | cons b bs =>
      simp only [vlist, pair_inj'] at h
      rw [h.1, ih h.2]

theorem here_conV {ctors : List Ctor} {c : ℕ} {args : List V} {rs : List (DM k)}
    (hb : bndAtMap (ctors.getD c default) rs (Hom.id k) = none) :
    here k (conV ctors k c args rs) =
      tagZ tCon (ZFSet.pair (natZ c) (ZFSet.pair (vlist (args.map (res (Hom.id k))))
        (vlist (rs.map fun r => enc (r.restr (Hom.id k)))))) := by
  rw [conV_eq, here_mkKV, hb]

theorem here_hcV {ψ : Cof k} {u : Tube k} {a : V} (hψ : ¬ ψ.holds) :
    here k (hcV k ψ u a) =
      tagZ tHc (ZFSet.pair (enc (ψ.restr (Hom.id k))) (ZFSet.pair (tubeZ (ψ.restr (Hom.id k)) (u.restr (Hom.id k)))
        (res (Hom.id k) a))) := by
  have : ¬ (ψ.restr (Hom.id k)).holds := by
    intro h; apply hψ
    have := (Cof.holds_restr_iff ψ (Hom.id k)).1 h
    rwa [Hom.app_id] at this
  rw [hcV, here_mkKV, if_neg this]

theorem map_res_id_of_kv {as : List V} (h : ∀ a ∈ as, IsKV k a) : as.map (res (Hom.id k)) = as := by
  conv_rhs => rw [← List.map_id as]
  exact List.map_congr_left fun a ha => res_id (h a ha)

theorem conV_inj {ctors : List Ctor} {c c' : ℕ} {args args' : List V} {rs rs' : List (DM k)}
    (hb : bndAtMap (ctors.getD c default) rs (Hom.id k) = none)
    (hb' : bndAtMap (ctors.getD c' default) rs' (Hom.id k) = none)
    (ha : ∀ a ∈ args, IsKV k a) (ha' : ∀ a ∈ args', IsKV k a)
    (h : conV ctors k c args rs = conV ctors k c' args' rs') : c = c' ∧ args = args' ∧ rs = rs' := by
  have := congrArg (here k) h
  rw [here_conV hb, here_conV hb', tagZ_inj] at this
  simp only [pair_inj', natZ_inj] at this
  obtain ⟨-, h1, h2, h3⟩ := this
  refine ⟨h1, ?_, ?_⟩
  · have := vlist_injective h2
    rwa [map_res_id_of_kv ha, map_res_id_of_kv ha'] at this
  · have := vlist_injective h3
    simp only [DM.restr_id] at this
    exact List.map_injective_iff.2 (fun x y hxy => enc_injective hxy) this

theorem hcV_inj {ψ ψ' : Cof k} {u u' : Tube k} {a a' : V} (hψ : ψ.IsCof) (hψ' : ψ'.IsCof)
    (hn : ¬ ψ.holds) (hn' : ¬ ψ'.holds) (ha : IsKV k a) (ha' : IsKV k a')
    (h : hcV k ψ u a = hcV k ψ' u' a') :
    ψ = ψ' ∧ (∀ n (g : Hom n k) r, (ψ.restr g).holds → u n g r = u' n g r) ∧ a = a' := by
  have := congrArg (here k) h
  rw [here_hcV hn, here_hcV hn', tagZ_inj] at this
  simp only [pair_inj', enc_inj, hψ.restr_id, hψ'.restr_id] at this
  obtain ⟨-, h1, h2, h3⟩ := this
  subst h1
  refine ⟨rfl, fun n g r hg => ?_, by rwa [res_id ha, res_id ha'] at h3⟩
  rw [tubeZ_eq_iff] at h2
  have := congrFun (congrFun (congrFun h2 n) g) r
  simp only [Tube.canon, Tube.restr, Hom.id_comp, if_pos hg] at this
  exact this

theorem conV_ne_hcV {ctors : List Ctor} {c : ℕ} {args : List V} {rs : List (DM k)}
    {ψ : Cof k} {u : Tube k} {a : V}
    (hb : bndAtMap (ctors.getD c default) rs (Hom.id k) = none) (hn : ¬ ψ.holds) :
    conV ctors k c args rs ≠ hcV k ψ u a := by
  intro h
  have := congrArg (here k) h
  rw [here_conV hb, here_hcV hn, tagZ_inj] at this
  exact absurd this.1 (by decide)

/-! ### Transport is functional -/

theorem TR.out_kv {Θ : SData m} {k : ℕ} {f : Hom (k + 1) m} {φ : Cof k} {v w : V}
    (h : TR Θ k f φ v w) : IsKV k w := by
  cases h with
  | con => exact isKV_conV _ _ _ _
  | hc => exact isKV_hcV _ _ _

theorem TR.unique {Θ : SData m} {k : ℕ} {f : Hom (k + 1) m} {φ : Cof k} {v w : V}
    (h : TR Θ k f φ v w) : ∀ {v' w'}, TR Θ k f φ v' w' → v = v' → w = w' := by
  induction h with
  | @con k f φ c args rs outs fills hb hkv hlo hlf hro hrf hpt iho ihf =>
    intro v' w' h' hv
    cases h' with
    | @con _ _ _ c2 args2 rs2 outs2 fills2 hb2 hkv2 hlo2 hlf2 hro2 hrf2 hpt2 =>
      obtain ⟨rfl, rfl, rfl⟩ := conV_inj hb hb2 hkv hkv2 hv
      have hfills : ∀ j ≤ args.length, fills.take j = fills2.take j := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          intro hj
          rw [List.take_succ, List.take_succ, ihj (by omega)]
          congr 1
          rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
          congr 1
          have e1 : fills[j]'(by omega) = fills.getD j ∅ := List.getElem_eq_getD ∅
          have e2 : fills2[j]'(by omega) = fills2.getD j ∅ := List.getElem_eq_getD ∅
          rw [e1, e2]
          by_cases hr : (Θ.ctors.getD c default).isRec j = true
          · exact congrArg some (ihf j (by omega) hr (hrf2 j (by omega) hr) rfl)
          · have hr' : (Θ.ctors.getD c default).isRec j = false := by simpa using hr
            rw [(hpt j (by omega) hr').2, (hpt2 j (by omega) hr').2, ihj (by omega)]
      congr 1
      apply List.ext_getElem (by omega)
      intro j h1 h2
      have e1 : outs[j]'h1 = outs.getD j ∅ := List.getElem_eq_getD ∅
      have e2 : outs2[j]'h2 = outs2.getD j ∅ := List.getElem_eq_getD ∅
      rw [e1, e2]
      by_cases hr : (Θ.ctors.getD c default).isRec j = true
      · exact iho j (by omega) hr (hro2 j (by omega) hr) rfl
      · have hr' : (Θ.ctors.getD c default).isRec j = false := by simpa using hr
        rw [(hpt j (by omega) hr').1, (hpt2 j (by omega) hr').1, hfills j (by omega)]
    | hc _ hn2 _ _ _ => exact absurd hv (conV_ne_hcV hb hn2)
  | @hc k f φ ψ u u' a a' hψ hn hka _ _ iha ihu =>
    intro v' w' h' hv
    cases h' with
    | con hb2 _ _ _ _ _ _ => exact absurd hv.symm (conV_ne_hcV hb2 hn)
    | @hc _ _ _ ψ2 u2 u2' a2 a2' hψ2 hn2 hka2 ha2 hu2 =>
      obtain ⟨rfl, hu, rfl⟩ := hcV_inj hψ hψ2 hn hn2 hka hka2 hv
      rw [iha ha2 rfl]
      exact hcV_congr _ fun n g r hg => ihu n g r hg (hu2 n g r hg) (hu n g r hg)

theorem transpD_of_TR {Θ : SData m} (hp : Θ.params = true) {k : ℕ} {f : Hom (k + 1) m} {φ : Cof k} {v w : V}
    (h : TR Θ k f φ v w) : transpD Θ k f φ v = w := by
  have hex : ∃ w, TR Θ k f φ v w := ⟨w, h⟩
  rw [transpD, if_neg (by simp [hp]), dif_pos hex]
  exact (Classical.choose_spec hex).unique h rfl

end

end Model
