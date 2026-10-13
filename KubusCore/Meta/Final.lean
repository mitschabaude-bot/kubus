import KubusCore.Meta.SigWk
import KubusCore.Meta.ConBnd

/-!
# Metatheory: the spec and the minimal judgments agree on well-formed signatures

`ContractaTyped` (the boundary rule `conBnd`) holds for every well-formed signature, by strong
induction on the signature: a boundary's type equations are checked in the prefix before its
inductive type, where the spec's judgments are minimal ones by the induction hypothesis. Hence
`spec_to_minimal` needs no hypothesis beyond `WfSig`.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-- Generation for constructors: the premises of the `con` rule at the natural type
`data d ps`, followed by conversions. -/
theorem gen_conF {Ψ Φ Γ s T} (h : HasTy0 S Ψ Φ Γ s T) {d c ps args rs}
    (ht : s = .con d c ps args rs) :
    IntroTy S Ψ Φ Γ (con d c ps args rs) (data d ps) ∧ TyChainC S Ψ Φ Γ (data d ps) T :=
  match h with
  | .var _ _ => by cases ht
  | .conv h0 h1 => by
    obtain ⟨hI, ch⟩ := gen_conF h0 ht
    exact ⟨hI, ch.snoc h1⟩
  | .restrict hs he h2 => by
    obtain ⟨hI, ch⟩ := gen_conF h2 ht
    exact ⟨hI.restrict hs he, ch.restrict hs he⟩
  | .const _ _ => by cases ht
  | .univ _ _ => by cases ht
  | .cumul h0 h1 => by
    obtain ⟨hI, ch⟩ := gen_conF h1 ht
    exact ⟨hI, ch.cumul h0⟩
  | .pi _ _ => by cases ht
  | .lam _ _ => by cases ht
  | .app _ _ => by cases ht
  | .sigma _ _ => by cases ht
  | .pair _ _ _ => by cases ht
  | .fst _ => by cases ht
  | .snd _ => by cases ht
  | .path _ _ _ => by cases ht
  | .plam _ _ _ _ => by cases ht
  | .papp _ _ => by cases ht
  | .ipi _ _ => by cases ht
  | .ilam _ _ => by cases ht
  | .iapp _ _ => by cases ht
  | .split _ _ _ _ _ _ _ => by cases ht
  | .abort _ _ => by cases ht
  | .transp _ _ _ _ => by cases ht
  | .hcomp _ _ _ _ _ => by cases ht
  | .glue _ _ _ _ => by cases ht
  | .glueEl _ _ _ _ _ => by cases ht
  | .unglue _ _ _ _ => by cases ht
  | .data _ _ _ => by cases ht
  | .con h0 h1 h2 h3 h4 h5 h6 h7 => by cases ht; exact ⟨⟨rfl, _, _, h0, h1, h2, h3, h4, h5, h6, h7⟩, .refl _⟩
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases ht

theorem contractaTyped_of (hW : WfSig S)
    (htr : ∀ (d : Nat) (D : DataDecl), S[d]? = some (.data D) →
      ∀ {Ψ Φ Γ t u A}, EqTm (S.take d) Ψ Φ Γ t u A → EqTm0 S Ψ Φ Γ t u A) :
    ContractaTyped S where
  conBnd := fun hD hC hk hent hps hargs h => by
    obtain ⟨⟨_, D', C', hD', hC', _, hdata, hpt, hat, hrs, hrsc⟩, ch⟩ := gen_conF h rfl
    rw [hD] at hD'; cases hD'; rw [hC] at hC'; cases hC'
    exact ch.transport (conBnd_typed hW (htr _ _ hD) hD hC hk hent hps hargs hdata hpt hat hrs hrsc)

/-- Every well-formed signature has typed definitions and typed contracta. -/
theorem wf_typed : ∀ (n : Nat) (S : Sig), S.length = n → WfSig S → SigTyped0 S ∧ ContractaTyped S := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro S hn hS
    have hpre : ∀ k, k < S.length → SigTyped0 (S.take k) ∧ ContractaTyped (S.take k) := fun k hk =>
      ih k (by omega) (S.take k) (by simp [List.length_take]; omega) (wfSig_take hS k)
    have hC : ContractaTyped S := contractaTyped_of hS fun d D hD {Ψ Φ Γ t u A} e => by
      have hd : d < S.length := (List.getElem?_eq_some_iff.1 hD).1
      obtain ⟨hT', hC'⟩ := hpre d hd
      have hinc : ∀ (j : Nat) (e : Entry), (S.take d)[j]? = some e → S[j]? = some e :=
        fun j e h => (getElem?_take_some h).2
      exact sigwk_eq hinc (spec_to_minimal_eq_of (wfSig_take hS d) hT' hC' e)
    refine ⟨sigTyped0_of_wfSig n S hn hS fun k => ?_, hC⟩
    by_cases hk : k < S.length
    · exact (hpre k hk).2
    · rw [List.take_of_length_le (by omega)]; exact hC

/-- The spec's typing judgment adds nothing to the minimal one. -/
theorem spec_to_minimal (hS : WfSig S) {Ψ Φ Γ t A} (h : HasTy S Ψ Φ Γ t A) : HasTy0 S Ψ Φ Γ t A :=
  spec_to_minimal_of hS (wf_typed _ S rfl hS).1 (wf_typed _ S rfl hS).2 h

theorem spec_to_minimal_eq (hS : WfSig S) {Ψ Φ Γ t u A} (h : EqTm S Ψ Φ Γ t u A) : EqTm0 S Ψ Φ Γ t u A :=
  spec_to_minimal_eq_of hS (wf_typed _ S rfl hS).1 (wf_typed _ S rfl hS).2 h

end KubusCore.Meta
