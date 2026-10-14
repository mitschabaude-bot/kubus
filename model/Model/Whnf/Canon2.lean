import Model.Whnf.Kan2All
import Model.Canon.CanonForm

/-!
# Canonicity from the binary fundamental lemma

The binary fundamental lemma (`fund2`, with the Kan oracle `kanOracle2`) relates the two sides of every
judgmental equality of closed types. At an equality of Glue types whose face does not hold, the type
relation of Glue normal forms relates their bases and equivalences, which gives the compatibility of
Glue annotations (`glueCompat_of`), the hypothesis of `canonicity_of_glueCompat`.

The remaining obligations of the binary development are bundled in `Obl2`: transport along lines of
higher inductive types with parameters (`HITHyp2`: the boundaries of constructors, and the argument types of
their nested constructors), the rules of higher inductive types
(`DataHyp2`), and `glueBeta` (`GlueBetaHyp2`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig}

/-- The remaining obligations of the binary fundamental lemma and the binary Kan lemma. -/
structure Obl2 (S : Sig) : Prop where
  hit : HITHyp2 S
  data : ∀ n, DataHyp2 S (S.take n)
  glueBeta : GlueBetaHyp2 S

/-- **The compatibility of Glue annotations**, from the binary fundamental lemma. -/
theorem glueCompat_of (hW : WfSig S) (O : Obl2 S) : GlueCompat S := by
  intro k A A' T T' e e' φ φ' l h hn h12 h21
  obtain ⟨-, hr⟩ := fund2_closed hW (kanOracle2 hW O.hit) O.data O.glueBeta (spec_to_minimal_eq hW h)
  have hGG' := RE2_univ_ty hW hr
  have hG := HasTy.eqL h
  have hG' := HasTy.eqR h
  have hn' : ¬ I.Entails .one φ' := fun h' => hn (ent_trans h' h21)
  have inv := RT2_glueW_inv hW hG hG' hn hn' hGG' (redT_glue_self hn) (redT_glue_self hn')
  have ee := glue_ee hW hG hG' h12 inv.1 (fun k' σ hh => (inv.2 k' σ hh).1) (fun k' σ hh => (inv.2 k' σ hh).2)
  refine ⟨?_, ee.symm⟩
  obtain ⟨-, lA, hA, -⟩ := glue_data hW hG
  rcases (Comp2_ty_base inv.1).2.2.2.2.2 with rfl | ⟨l', eA⟩
  · exact ⟨lA, EqTm.refl hA⟩
  · exact ⟨l', eA⟩

/-- **Canonicity**, given the remaining obligations of the binary development. -/
theorem canonicity_of_obl2 (S : Sig) (d : Nat) (D : DataDecl) (t : Tm) (hW : WfSig S) (O : Obl2 S)
    (hD : S[d]? = some (.data D)) (hp : D.params = []) (ht : HasTy S 0 .one [] t (.data d .tnil)) :
    ∃ t', EqTm S 0 .one [] t t' (.data d .tnil) ∧ Canon S d t' :=
  canonicity_of_glueCompat S d D t hW (glueCompat_of hW O) hD hp ht

end

end Model.Whnf
