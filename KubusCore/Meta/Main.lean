import KubusCore.Meta.Presup

/-!
# Metatheory: summary

The spec's primitive structural, presupposition and inversion rules over the minimal
judgments (`Meta/Minimal.lean`):

| spec rule | minimal judgments | assumption |
|---|---|---|
| `HasTy.wk`, `EqTm.wk`, `HasTy.dwk`, `EqTm.dwk` | `HasTy0.wk`, … (`Weaken.lean`) | `SigClosed` |
| `HasTy.subst`, `HasTy.dsubst`, `EqTm.dsubst` | `HasTy0.subst`, … (`Structural.lean`) | `SigClosed` |
| `EqTm.subst` | `EqTm0.subst` | right-hand sides typed |
| `piDom`, …, `glueFib` | `HasTy0.piDom`, … (`Inversion.lean`) | `SigClosed` |
| `eqL`, `eqR` | `presup0` (`Presup.lean`) | `ContractaTyped`, `SigTyped0` |

and the two inclusions between the spec and the minimal judgments.
-/

namespace KubusCore.Meta

variable {S : Sig}

/-- The spec's typing judgment adds nothing to the minimal one, given that the contracta of the
computation rules in `ContractaTyped` are typed and the signature's definitions are typed. -/
theorem spec_to_minimal (hS : WfSig S) (hT : SigTyped0 S) (hC : ContractaTyped S) {Ψ Φ Γ t A}
    (h : HasTy S Ψ Φ Γ t A) : HasTy0 S Ψ Φ Γ t A :=
  toMin_ty (sigClosed_of_wfSig hS) (presup0 (sigClosed_of_wfSig hS) hT hC) hT h

theorem spec_to_minimal_eq (hS : WfSig S) (hT : SigTyped0 S) (hC : ContractaTyped S) {Ψ Φ Γ t u A}
    (h : EqTm S Ψ Φ Γ t u A) : EqTm0 S Ψ Φ Γ t u A :=
  toMin_eq (sigClosed_of_wfSig hS) (presup0 (sigClosed_of_wfSig hS) hT hC) hT h

/-- The minimal judgments are derivable in the spec, given the generalizations M4 and M5. -/
theorem minimal_to_spec (hM4a : SpecM4glueEl S) (hM4b : SpecM4unglue S) (hM5 : SpecM5 S) {Ψ Φ Γ t A}
    (h : HasTy0 S Ψ Φ Γ t A) : HasTy S Ψ Φ Γ t A :=
  toFull_ty hM4a hM4b hM5 h

theorem minimal_to_spec_eq (hM4a : SpecM4glueEl S) (hM4b : SpecM4unglue S) (hM5 : SpecM5 S)
    {Ψ Φ Γ t u A} (h : EqTm0 S Ψ Φ Γ t u A) : EqTm S Ψ Φ Γ t u A :=
  toFull_eq hM4a hM4b hM5 h

end KubusCore.Meta
