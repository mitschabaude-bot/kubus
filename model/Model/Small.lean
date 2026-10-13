import Model.Univ
import Model.SmallBasic

/-!
# Smallness of codes

`Vt l` (the embedded `ZFSet.{l}`) is closed under the constructions of the model: a set is in
`Vt l` iff its members are and it is `l`-small (`mem_Vt_of`, `isSmallAt_of_mem_Vt`). The Kan
operations of a code are lookups in its graphs, so their results lie below the code; the element
sets and graphs are built by pairing, ranges over small index types and separation.
-/

set_option autoImplicit false

universe w w'

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {l k m n : ℕ}

theorem emptyC_mem_Vt' (hl : l ≤ 4) : emptyC m ∈ Vt l :=
  mkKV_mem_Vt hl fun _ _ => quad_mem_Vt (tagZ_mem_Vt (empty_mem_Vt hl)) (empty_mem_Vt hl) (empty_mem_Vt hl)
    (empty_mem_Vt hl)


theorem univC_mem_Vt' {l : ℕ} (hl : l < 4) : univC m l ∈ Vt (l + 1) := by
  have hl' : l + 1 ≤ 4 := hl
  have hV := Vt_mem_succ l hl
  unfold univC univCode univDatum
  refine mkKV_mem_Vt hl' fun k f => ?_
  refine quad_mem_Vt (tagZ_mem_Vt (natZ_mem_Vt hl' _)) (sep_mem_Vt hV _) ?_
    (hcGraph_mem_Vt hl' (fun n _ => sep_mem_Vt hV _) fun φ u u0 hu hu0 => univHcF_mem_Vt hl' hu hu0)
  rcases k with _ | n
  · exact empty_mem_Vt hl'
  · unfold univTr
    exact trGraph_mem_Vt hl' (sep_mem_Vt hV _) fun φ a ha => Vt_trans _ (sep_mem_Vt hV _) ha

/-! ### Interpretations -/

theorem TEnv.cons_mem_Vt {γ : ℕ → V} (hγ : ∀ x, γ x ∈ Vt l) {a : V} (ha : a ∈ Vt l) :
    ∀ x, TEnv.cons γ a x ∈ Vt l
  | 0 => ha
  | x + 1 => hγ x

/-- All values of the signature semantics are small. -/
def SigV.Small (l : ℕ) (σ : SigV) : Prop :=
  (∀ m c, σ.cst m c ∈ Vt l) ∧ (∀ m d ps, σ.dat m d ps ∈ Vt l) ∧
  (∀ m d c ps args rs, σ.con m d c ps args rs ∈ Vt l) ∧ (∀ m d ps P bs t, σ.elim m d ps P bs t ∈ Vt l)

theorem SigV.small_empty (hl : l ≤ 4) : SigV.Small l SigV.empty :=
  ⟨fun _ _ => empty_mem_Vt hl, fun _ _ _ => empty_mem_Vt hl, fun _ _ _ _ _ _ => empty_mem_Vt hl,
    fun _ _ _ _ _ _ => empty_mem_Vt hl⟩

theorem interp_mem_Vt (hl : l ≤ 4) {cst : SigV} {uc : ℕ → ℕ → V} {good : (m : ℕ) → V → Prop}
    (hcst : SigV.Small l cst) (huc : ∀ m l', uc m l' ∈ Vt l) :
    ∀ (t : KubusCore.Tm) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V), (∀ x, γ x ∈ Vt l) →
      interp cst uc good t m ρ γ ∈ Vt l := by
  have hr : ∀ {m k : ℕ} {γ : ℕ → V}, (∀ x, γ x ∈ Vt l) → ∀ (f : Hom k m), ∀ x, TEnv.restr γ f x ∈ Vt l :=
    fun hγ f x => res_mem_Vt' hl (hγ x) f
  intro t
  induction t with
  | var x => intro m ρ γ hγ; exact hγ x
  | const c => intro m ρ γ hγ; exact hcst.1 m c
  | tnil => intro m ρ γ hγ; exact empty_mem_Vt hl
  | tcons t ts iht ihts => intro m ρ γ hγ; exact pair_mem_Vt (iht m ρ γ hγ) (ihts m ρ γ hγ)
  | data d ps _ => intro m ρ γ hγ; exact hcst.2.1 _ _ _
  | con d c ps args rs _ _ => intro m ρ γ hγ; exact hcst.2.2.1 _ _ _ _ _ _
  | elim d ps P bs t _ _ _ _ => intro m ρ γ hγ; exact hcst.2.2.2 _ _ _ _ _ _
  | univ l' => intro m ρ γ hγ; exact huc m l'
  | pi A B ihA ihB =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact piC_mem_Vt' hl (ihA m ρ γ hγ) (famV_mem_Vt hl (ihA m ρ γ hγ) fun k f a ha =>
        ihB _ _ _ (TEnv.cons_mem_Vt (hr hγ f) (Vt_trans l (El_mem_Vt hl (ihA m ρ γ hγ) f) ha)))
    · exact empty_mem_Vt hl
  | sigma A B ihA ihB =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact sigmaC_mem_Vt' hl (ihA m ρ γ hγ) (famV_mem_Vt hl (ihA m ρ γ hγ) fun k f a ha =>
        ihB _ _ _ (TEnv.cons_mem_Vt (hr hγ f) (Vt_trans l (El_mem_Vt hl (ihA m ρ γ hγ) f) ha)))
    · exact empty_mem_Vt hl
  | lam A t ihA iht =>
    intro m ρ γ hγ; simp only [interp]
    exact lamV_mem_Vt hl (fun _ f => El_mem_Vt hl (ihA m ρ γ hγ) f) fun k f a ha =>
      iht _ _ _ (TEnv.cons_mem_Vt (hr hγ f) (Vt_trans l (El_mem_Vt hl (ihA m ρ γ hγ) f) ha))
  | app f a ihf iha =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact appV_mem_Vt hl (ihf m ρ γ hγ) _
    · exact empty_mem_Vt hl
  | pair a b iha ihb =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact pairV_mem_Vt hl (iha m ρ γ hγ) (ihb m ρ γ hγ)
    · exact empty_mem_Vt hl
  | fst p ih => intro m ρ γ hγ; simp only [interp]; exact fstV_mem_Vt hl (ih m ρ γ hγ)
  | snd p ih => intro m ρ γ hγ; simp only [interp]; exact sndV_mem_Vt hl (ih m ρ γ hγ)
  | path A a b ihA iha ihb =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact pathC_mem_Vt' hl (ihA _ _ _ (hr hγ _)) (iha m ρ γ hγ) (ihb m ρ γ hγ)
    · exact empty_mem_Vt hl
  | plam t ih =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact pathOfLine_mem_Vt hl (ih _ _ _ (hr hγ _))
    · exact empty_mem_Vt hl
  | papp p r ih => intro m ρ γ hγ; simp only [interp]; exact pappV_mem_Vt hl (ih m ρ γ hγ) _
  | ipi A ih =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact ipiC_mem_Vt' hl (ih _ _ _ (hr hγ _))
    · exact empty_mem_Vt hl
  | split φ t ψ u iht ihu =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    all_goals first | exact iht m ρ γ hγ | exact ihu m ρ γ hγ | exact empty_mem_Vt hl
  | abort => intro m ρ γ hγ; simp only [interp]; exact empty_mem_Vt hl
  | transp A φ a ihA iha =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact transpAt_mem_Vt hl (ihA _ _ _ (hr hγ _)) _ _ _
    · exact empty_mem_Vt hl
  | hcomp A φ u a ihA ihu iha =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact hcompAt_mem_Vt hl (ihA m ρ γ hγ) _ _ _ _
    · exact empty_mem_Vt hl
  | glue A φ T e ihA ihT ihe =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact glueC_mem_Vt' hl (ihA m ρ γ hγ) (partialKV_mem_Vt hl fun k f _ => ihT _ _ _ (hr hγ f))
        (partialKV_mem_Vt hl fun k f _ => ihe _ _ _ (hr hγ f))
    · exact empty_mem_Vt hl
  | glueEl φ e t a ihe iht iha =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact iht m ρ γ hγ
    · exact empty_mem_Vt hl
    · exact glueV_mem_Vt hl (partialKV_mem_Vt hl fun k f _ => iht _ _ _ (hr hγ f)) (iha m ρ γ hγ) _
    · exact empty_mem_Vt hl
  | unglue φ e g ihe ihg =>
    intro m ρ γ hγ; simp only [interp]; exact ungAt_mem_Vt hl (ihe m ρ γ hγ) (ihg m ρ γ hγ) _

theorem equivCode_mem_Vt' {T A : V} (hT : T ∈ Vt l) (hA : A ∈ Vt l) : equivCode m T A ∈ Vt l := by
  have hl := le_of_mem_Vt hT
  exact interp_mem_Vt hl (SigV.small_empty hl) (fun _ _ => empty_mem_Vt hl) _ _ _ _
    (TEnv.cons_mem_Vt (TEnv.cons_mem_Vt (fun _ => empty_mem_Vt hl) hT) hA)

end

end Model
