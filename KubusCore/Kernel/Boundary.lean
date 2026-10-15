import KubusCore.Kernel.Lemmas

/-! # Deciding syntactic boundary agreement -/

namespace KubusCore

namespace I

theorem eqB_complete {r s : I} (h : I.Eq r s) : eqB r s = true := by
  simp only [eqB, List.all_eq_true, beq_iff_eq]
  intro ρ _
  exact h ρ

instance decidableEqI (r s : I) : Decidable (I.Eq r s) :=
  decidable_of_iff (eqB r s = true) ⟨eqB_sound, eqB_complete⟩

end I

namespace Boundary

instance decidableINear : (rs ss : List I) → Decidable (INear rs ss)
  | [], [] => isTrue trivial
  | [], _ :: _ | _ :: _, [] => isFalse id
  | r :: rs, s :: ss =>
      show Decidable (I.Eq r s ∧ INear rs ss) from
        @instDecidableAnd _ _ (I.decidableEqI r s) (decidableINear rs ss)

def nearDec (t u : Tm) : Decidable (Near t u) := by
  cases t <;> cases u
  all_goals try exact isFalse id
  case var.var x y => exact inferInstanceAs (Decidable (x = y))
  case tnil.tnil => exact isTrue trivial
  case tcons.tcons a as b bs =>
    exact @instDecidableAnd _ _ (nearDec a b) (nearDec as bs)
  case con.con d c ps as rs d' c' ps' bs ss =>
    letI := nearDec as bs
    exact inferInstanceAs (Decidable (d = d' ∧ c = c' ∧ ps = ps' ∧ Near as bs ∧ INear rs ss))
termination_by t

instance decidableNear (t u : Tm) : Decidable (Near t u) := nearDec t u

instance decidableAgree (ctors : List Ctor) (d np n c : Nat) (φ : I) (b b' : Tm) :
    Decidable (Agree ctors d np n c φ b b') :=
  inferInstanceAs (Decidable (∀ α ∈ φ.faces, Near (nf ctors d np n c α b) (nf ctors d np n c α b')))

end Boundary

end KubusCore
