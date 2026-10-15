import Model.Whnf.Kan2DataHC

/-!
# Composition of related constructors

The `hcompCon` contracta of compositions of related constructors along related tubes are related at
one stage (`HCC.hcompCon2`): recursive arguments by the composition of the base's arguments,
point arguments by `comp2` along their related type lines.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

namespace HCC

variable {d : ℕ} {D : DataDecl} {K : ℕ} {P Q Q' : Tm} {k1 : ℕ} {ρ : ISub k1 K} {c : ℕ} {C : Ctor}
  {qs qs' : Tm} {X X' : List Tm} {φ φ' : I} {u u' : Tm}
  (H : HCC S d D K P Q Q' k1 ρ c C qs qs' X X' φ φ' u u')
include H

/-- The `hcompCon` contracta of compositions of related constructors along related tubes are related
at one stage. -/
theorem hcompCon2 :
    DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k1 ρ.hom
      (.data d (P.isub ρ)) (.hcomp (.data d (Q.isub ρ)) φ u (.con d c qs (Tm.ofList X) []))
      (.hcomp (.data d (Q'.isub ρ)) φ' u' (.con d c qs' (Tm.ofList X') [])) := by
  obtain ⟨⟨e_hc, rL⟩, ⟨e_hc', rR⟩⟩ := H.contracta
  refine DR2At.expandR H.hW (DR2At.expand H.hW ?_ rL e_hc) rR e_hc'
  exact H.toHCG.conRel

end HCC

end

end Model.Whnf
