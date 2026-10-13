import Model.DataRestr
import Mathlib.SetTheory.ZFC.Rank

/-!
# Inductive types: the eliminator on representations
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

theorem Below.rank_lt {x y : V} (h : Below x y) : ZFSet.rank x < ZFSet.rank y := by
  induction h with
  | single h => exact ZFSet.rank_lt_of_mem h
  | tail _ h ih => exact ih.trans (ZFSet.rank_lt_of_mem h)

theorem below_vlist : ∀ {as : List V} {a : V}, a ∈ as → Below a (vlist as)
  | b :: as, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact below_pair_left _ _
    · exact (below_vlist h).trans (below_pair_right _ _)

theorem below_conV_arg {ctors : List Ctor} {c : ℕ} {args : List V} {rs : List (DM k)}
    (hb : bndAtMap (ctors.getD c default) rs (Hom.id k) = none) (hkv : ∀ a ∈ args, IsKV k a) {a : V}
    (ha : a ∈ args) : Below a (conV ctors k c args rs) := by
  have h1 : Below (here k (conV ctors k c args rs)) (conV ctors k c args rs) := below_dat (isKV_conV _ _ _ _) _
  rw [here_conV hb, map_res_id_of_kv hkv] at h1
  exact (((below_vlist ha).trans (below_pair_left _ _)).trans (below_pair_right _ _)).trans
    ((below_tagZ _ _).trans h1)

theorem below_hcV_base {ψ : Cof k} {u : Tube k} {a : V} (hψ : ψ.IsCof) (hn : ¬ ψ.holds) (hka : IsKV k a) :
    Below a (hcV k ψ u a) := by
  have h1 : Below (here k (hcV k ψ u a)) (hcV k ψ u a) := below_dat (isKV_hcV _ _ _) _
  rw [here_hcV hn, res_id hka] at h1
  exact ((below_pair_right _ _).trans (below_pair_right _ _)).trans ((below_tagZ _ _).trans h1)

theorem below_hcV_tube {ψ : Cof k} {u : Tube k} {a : V} (hψ : ψ.IsCof) (hn : ¬ ψ.holds) {n : ℕ} {g : Hom n k}
    {r : DM n} (hg : (ψ.restr g).holds) : Below (u n g r) (hcV k ψ u a) := by
  have h1 : Below (here k (hcV k ψ u a)) (hcV k ψ u a) := below_dat (isKV_hcV _ _ _) _
  rw [here_hcV hn, hψ.restr_id] at h1
  have h2 : Below (Tube.canon ψ (u.restr (Hom.id k)) n g r) (tubeZ ψ (u.restr (Hom.id k))) :=
    below_fnC (fun x : TubeDom k => Tube.canon ψ (u.restr (Hom.id k)) x.1 x.2.1 x.2.2) ⟨n, g, r⟩
  simp only [Tube.canon, Tube.restr, Hom.id_comp, if_pos hg] at h2
  exact ((h2.trans (below_pair_left _ _)).trans (below_pair_right _ _)).trans ((below_tagZ _ _).trans h1)

/-- The branch for constructor `c` applied to the arguments, the eliminator on the recursive ones,
and the interval arguments. -/
def elimBranch (Θ : SData m) (P : (n : ℕ) → Hom n m → V → V) (bs : (k : ℕ) → Hom k m → V) (k : ℕ)
    (g : Hom k m) (c : ℕ) (args : List V) (rs : List (DM k)) : V :=
  pappsV k (appsV k (vnth (bs k g) c) (args ++ ((List.range args.length).filter
    (Θ.ctors.getD c default).isRec).map fun j => elimD Θ P bs k g (args.getD j ∅))) rs

theorem elimD_repCon (Θ : SData m) (P : (n : ℕ) → Hom n m → V → V) (bs : (k : ℕ) → Hom k m → V) (g : Hom k m)
    {v : V} (h : RepCon Θ k v) :
    elimD Θ P bs k g v = elimBranch Θ P bs k g (Classical.choose h) (Classical.choose (Classical.choose_spec h))
      (Classical.choose (Classical.choose_spec (Classical.choose_spec h))) := by
  rw [elimD, dif_pos h]
  obtain ⟨e1, e3, e4⟩ := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))
  unfold elimBranch
  congr 3
  apply List.map_congr_left
  intro j hj
  rw [dif_pos]
  simp only [List.mem_filter, List.mem_range] at hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj.1, Option.getD_some]
  conv_rhs => rw [e1]
  exact (below_conV_arg e3 e4 (List.getElem_mem _)).rank_lt

theorem elimD_conV (Θ : SData m) (P : (n : ℕ) → Hom n m → V → V) (bs : (k : ℕ) → Hom k m → V) (g : Hom k m)
    {c : ℕ} {args : List V} {rs : List (DM k)}
    (hb : bndAtMap (Θ.ctors.getD c default) rs (Hom.id k) = none) (hkv : ∀ a ∈ args, IsKV k a) :
    elimD Θ P bs k g (conV Θ.ctors k c args rs) = elimBranch Θ P bs k g c args rs := by
  have hrep : RepCon Θ k (conV Θ.ctors k c args rs) := ⟨c, args, rs, rfl, hb, hkv⟩
  rw [elimD_repCon Θ P bs g hrep]
  obtain ⟨e1, e3, e4⟩ := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hrep))
  obtain ⟨hc, ha, hr⟩ := conV_inj hb e3 hkv e4 e1
  exact (congr (congr (congrArg (elimBranch Θ P bs k g) hc) ha) hr).symm

theorem not_repCon_hcV (Θ : SData m) {ψ : Cof k} {u : Tube k} {a : V} (hn : ¬ ψ.holds) :
    ¬ RepCon Θ k (hcV k ψ u a) := by
  rintro ⟨c, args, rs, h, hb, -⟩
  exact conV_ne_hcV hb hn h.symm

theorem fillTube_congr {ψ : Cof k} {u u' : Tube k} (a : V)
    (h : ∀ n (g : Hom n k) r, (ψ.restr g).holds → u n g r = u' n g r) : fillTube ψ u a = fillTube ψ u' a := by
  funext n g r
  simp only [fillTube]
  split
  · rename_i hh; rw [h _ _ _ hh]
  · rfl

theorem elimD_hcV (Θ : SData m) (P : (n : ℕ) → Hom n m → V → V) (bs : (k : ℕ) → Hom k m → V) (g : Hom k m)
    {ψ : Cof k} {u : Tube k} {a : V} (hψ : ψ.IsCof) (hn : ¬ ψ.holds) (hka : IsKV k a) :
    elimD Θ P bs k g (hcV k ψ u a) =
      compF (P (k + 1) (g.comp (Hom.wk k)) (hcV (k + 1) (fillFace ψ) (fillTube ψ u a) (res (Hom.wk k) a)))
        (Hom.id (k + 1)) ψ (fun n' g' r => elimD Θ P bs n' (g.comp g') (u n' g' r)) (elimD Θ P bs k g a) := by
  have hrep : RepHc k (hcV k ψ u a) := ⟨ψ, u, a, rfl, hψ, hn, hka⟩
  rw [elimD, dif_neg (not_repCon_hcV Θ hn), dif_pos hrep]
  obtain ⟨e1, e2, e3, e4⟩ := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hrep))
  obtain ⟨hψ', hu', ha'⟩ := hcV_inj hψ e2 hn e3 hka e4 e1
  have hfill := fillTube_congr (a := Classical.choose (Classical.choose_spec (Classical.choose_spec hrep)))
    (ψ := Classical.choose hrep) (fun n g r hg => (hu' n g r (by rw [hψ']; exact hg)).symm)
  rw [hfill]
  have key : ∀ (ψ' : Cof k) (u' : Tube k) (a' : V), ψ = ψ' → (∀ n (g : Hom n k) r, (ψ.restr g).holds → u n g r = u' n g r) →
      a = a' → ∀ (T : Tube k) (b : V), (∀ n' (g' : Hom n' k) r, (ψ'.restr g').holds →
        T n' g' r = elimD Θ P bs n' (g.comp g') (u' n' g' r)) → b = elimD Θ P bs k g a' →
      compF (P (k + 1) (g.comp (Hom.wk k)) (hcV (k + 1) (fillFace ψ') (fillTube ψ' u a') (res (Hom.wk k) a')))
        (Hom.id (k + 1)) ψ' T b =
      compF (P (k + 1) (g.comp (Hom.wk k)) (hcV (k + 1) (fillFace ψ) (fillTube ψ u a) (res (Hom.wk k) a)))
        (Hom.id (k + 1)) ψ (fun n' g' r => elimD Θ P bs n' (g.comp g') (u n' g' r)) (elimD Θ P bs k g a) := by
    rintro ψ' u' a' rfl hu rfl T b hT rfl
    exact compF_congr fun n' g' r hg => by rw [hT n' g' r hg, ← hu n' g' r hg]
  refine key _ _ _ hψ' hu' ha' _ _ (fun n' g' r hg => ?_) ?_
  · rw [dif_pos]
    conv_rhs => rw [e1]
    exact (below_hcV_tube e2 e3 hg).rank_lt
  · rw [dif_pos]
    conv_rhs => rw [e1]
    exact (below_hcV_base e2 e3 e4).rank_lt

/-- The branches agree with the eliminator on the boundaries (the semantic boundary conditions of
the branches). -/
def BranchesOK (Θ : SData m) (P : (n : ℕ) → Hom n m → V → V) (bs : (k : ℕ) → Hom k m → V) : Prop :=
  ∀ n (g : Hom n m) c C, Θ.ctors[c]? = some C → ∀ ψ b, (ψ, b) ∈ C.bnd → ∀ args (rs : List (DM n)),
    Θ.ArgsTyped c C n g args → rs.length = C.dims → (ival (renv rs) ψ).holds →
    elimBranch Θ P bs n g c args rs = elimD Θ P bs n g (evalBnd (conBefore Θ.ctors c n) args rs b)

end

end Model
