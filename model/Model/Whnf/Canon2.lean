import Model.Whnf.Fund2
import Model.Canon.CanonForm

/-!
# Unconditional canonicity from the binary fundamental lemma

The binary fundamental lemma (`fund2`, with Kan carried by the universe relation) relates the two sides of every
judgmental equality of closed types. At an equality of Glue types whose face does not hold, the type
relation of Glue normal forms relates their bases and equivalences, which gives the compatibility of
Glue annotations (`glueCompat`), discharging the hypothesis of the canonical form proof.

Constructor boundary expansion follows from the checked overlap agreement and boundary argument
typing derived by `hyps_take`. HIT elimination and its computation rules follow from the binary
relation induction. No additional model obligations are assumed.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig}

/-- **The compatibility of Glue annotations**, from the binary fundamental lemma. -/
theorem glueCompat (hW : WfSig S) : GlueCompat S := by
  intro k A A' T T' e e' φ φ' l h hn h12 h21
  obtain ⟨-, hr⟩ := fund2_closed hW (spec_to_minimal_eq hW h)
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

/-- **Canonicity** for closed elements of a parameter-free inductive type, including HITs. -/
theorem canonicity (S : Sig) (d : Nat) (D : DataDecl) (t : Tm) (hW : WfSig S)
    (hD : S[d]? = some (.data D)) (hp : D.params = []) (ht : HasTy S 0 .one [] t (.data d .tnil)) :
    ∃ t', EqTm S 0 .one [] t t' (.data d .tnil) ∧ Canon S d t' :=
  canonicity_of_glueCompat S d D t hW (glueCompat hW) hD hp ht

end

end Model.Whnf
