import Model.Whnf.Kan2UnivH
import Model.Whnf.Kan2Codes
import Model.Whnf.Kan2DataCode

/-!
# The binary Kan operations at all codes

`kanP2_tyCode`: composition and transport relate related data at every pair of types related at a
restriction of a type code, by induction on codes (`tyCode_ind`), one case per type former. The
components of a normal form are related at restrictions of the components of the code
(`Comp2_piC`, …), so the induction hypotheses at the component codes give the Kan properties the
per-former lemmas need (`kanH2_of_code`, `khRel_of_code`). Composition in a universe of level `l`
uses transport along lines of level `l` only, which the induction hypothesis covers.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-! ### Universes -/

theorem kanP2_univC {m l : ℕ} (ih : ∀ m' X, WF l m' X → KanP2 S m' X) : KanP2 S m (univC m l) := by
  have hKT : KTAt S l := fun k X X' hXX hX => by
    have hm := mem_of_ty hW hX
    rw [show semK S (k + 1) (.univ l) = univC (k + 1) l from rfl, El_univC] at hm
    have hne := semK_ne hW hX
    exact kanT2_of_code (g := Hom.id (k + 1)) (ih (k + 1) _ (ZFSet.mem_sep.1 hm).2) hne
      (res_id (kv_semK_of_univ hW hX)).symm hXX
  refine ⟨fun k f A A' hT => ?_, fun k f A A' hT => ?_⟩
  · have hTT := Comp2_ty_RT2 hT
    have hb := Comp2_ty_base hT
    rw [Comp2_univC] at hT
    have hR := hT.2 k (ISub.id k)
    rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at hR
    exact kanH2_univ hW hKT hTT hR.1
  · have hTT := Comp2_ty_RT2 hT
    have hb := Comp2_ty_base hT
    rw [Comp2_univC] at hT
    have hR := hT.2 (k + 1) (ISub.id (k + 1))
    rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at hR
    exact kanT2_univ hW hTT hR.1


/-! ### Inductive types -/

theorem data_decl {m : ℕ} {Θ : SData m} {f : Hom k m} {A A' : Tm} (hT : (Comp2 S (dataC Θ) m k f).ty A A') :
    ∃ D, S[Θ.idx]? = some (.data D) := by
  have hb := Comp2_ty_base hT
  rw [Comp2_dataC] at hT
  obtain ⟨ps, -, hR, -⟩ := hT.2.1 k (ISub.id k)
  rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at hR
  obtain ⟨l, hd⟩ := ty_of_tyEq hW hb.2.1 hR.2 (fun l h => by cases h)
  obtain ⟨D, hD, -⟩ := gen_data (spec_to_minimal hW hd) rfl
  exact ⟨D, hD⟩

theorem kanP2_dataC' (hyp : HITHyp2 S) {m : ℕ} {Θ : SData m} (hKS : KanShape S m Θ) : KanP2 S m (dataC Θ) := by
  refine ⟨fun k f A A' hT => ?_, fun k f A A' hT => ?_⟩
  · obtain ⟨D, hD⟩ := data_decl hW hT
    exact kanH2_dataC hW hD hKS hT
  · obtain ⟨D, hD⟩ := data_decl hW hT
    exact kanT2_dataC hW hD hKS hyp hT

/-! ### All codes -/

theorem kanP2_tyCode (hyp : HITHyp2 S) {m : ℕ} {X : V} (hX : TyCode m X) : KanP2 S m X := by
  refine tyCode_ind (fun m X => KanP2 S m X) (fun m => kanP2_emptyC hW) ?_ ?_ ?_ ?_ ?_ ?_ ?_ m X hX
  · intro l m A B hA hB hBf hBw hBn ihA ihB
    exact kanP2_piC hW hA ihA fun k f A0 a a' ha => ihB k f _ (by
      have := (Comp2_el ha).2; rwa [El_res, Hom.comp_id] at this)
  · intro l m A B hA hB hBf hBw hBn ihA ihB
    exact kanP2_sigmaC hW hA ihA fun k f A0 a a' ha => ihB k f _ (by
      have := (Comp2_el ha).2; rwa [El_res, Hom.comp_id] at this)
  · intro l m L a0 a1 hL h0 h1 ihL
    exact kanP2_pathC hW (IsKV.ne_empty hL.fib.kv) ihL
  · intro l m L hL ihL
    exact kanP2_ipiC hW (IsKV.ne_empty hL.fib.kv) ihL
  · intro m l hl ih
    exact kanP2_univC hW ih
  · intro l m A φ Tp ep hl hAw hφ hn hTpE hepE hTw hTn hem hen ihA ihT
    exact kanP2_glueC hW hAw hφ hTn (fun k f hh => (hTw k f hh).fib.kv) ihA ihT
  · intro l m Θ hc hw hpw ih ihp
    exact kanP2_dataC' hW hyp (kanShape_of ih)

/-- **The binary Kan property of all related types.** -/
theorem kanOracle2 (hyp : HITHyp2 S) : KanOracle2 S := by
  have hKT : ∀ l, KTAt S l := fun l k X X' hXX hX =>
    (kanP2_tyCode hW hyp (tyCode_of_univ hW hX)).2 k (Hom.id (k + 1)) X X' (by unfold RT2 at hXX; exact hXX)
  refine ⟨fun k A A' h => ?_, fun k A A' h => ?_⟩
  · obtain ⟨l, hA | rfl⟩ := (Comp2_ty_base h).2.1
    · exact (kanP2_tyCode hW hyp (tyCode_of_univ hW hA)).1 k (Hom.id k) A A' (by unfold RT2 at h; exact h)
    · exact kanH2_univ hW (hKT l) h ⟨redW_self rfl, TyEq.refl _⟩
  · obtain ⟨l, hA | rfl⟩ := (Comp2_ty_base h).2.1
    · exact (kanP2_tyCode hW hyp (tyCode_of_univ hW hA)).2 k (Hom.id (k + 1)) A A' (by unfold RT2 at h; exact h)
    · exact kanT2_univ hW h ⟨redW_self rfl, TyEq.refl _⟩

end

end Model.Whnf
