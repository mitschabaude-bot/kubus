import Model.DataFibFull

/-!
# Inductive types: well-formedness is stable under restriction
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

theorem argsTyped_restr_iff (Θ : SData m) (h : Hom k m) {c : ℕ} {C : Ctor} {n : ℕ} (g : Hom n k) (args : List V) :
    (Θ.restr h).ArgsTyped c C n g args ↔ Θ.ArgsTyped c C n (h.comp g) args := by
  unfold SData.ArgsTyped
  simp only [delem_restr_iff]
  rfl

theorem bty_restr (Θ : SData m) (h : Hom k m) (c : ℕ) (C : Ctor) : ∀ t : Tm,
    (BTy Θ c C t → BTy (Θ.restr h) c C t) ∧
    (∀ C' c' j prev, BTyArgs Θ c C C' c' j prev t → BTyArgs (Θ.restr h) c C C' c' j prev t) := by
  intro t
  induction t with
  | var x => exact ⟨fun hb => hb, fun _ _ _ _ hb => by simp [BTyArgs] at hb ⊢⟩
  | con d c' ps as rs' _ ihas =>
    refine ⟨fun hb => ?_, fun _ _ _ _ hb => by simp [BTyArgs] at hb ⊢⟩
    obtain ⟨h1, C', h2, h3, h4, h5⟩ := hb
    exact ⟨h1, C', h2, h3, h4, ihas.2 _ _ _ _ h5⟩
  | tcons a as iha ihas =>
    refine ⟨fun hb => by simp [BTy] at hb, fun C' c' j prev hb => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hb
    refine ⟨fun hr => iha.1 (h1 hr), fun hr => ?_, ihas.2 _ _ _ _ h3⟩
    obtain ⟨x, hx1, hx2, hx3, hx4⟩ := h2 hr
    exact ⟨x, hx1, hx2, hx3, fun n g pre hl hp => hx4 n (h.comp g) pre hl hp⟩
  | _ => exact ⟨fun hb => by simp [BTy] at hb, fun _ _ _ _ hb => by simp [BTyArgs] at hb ⊢⟩

theorem SData.GoodCore.restr {Θ : SData m} (hΘ : Θ.GoodCore) (h : Hom k m) : (Θ.restr h).GoodCore where
  nat c j n g pre hp n' h' := hΘ.nat c j n (h.comp g) pre hp n' h'
  recIrr c j n g pre pre' hl he := hΘ.recIrr c j n (h.comp g) pre pre' hl he
  bnd c C hC ψ b hb n rs hh := (bty_restr Θ h c C b).1 (hΘ.bnd c C hC ψ b hb n rs hh)
  const hp c j n g g' pre := hΘ.const hp c j n (h.comp g) (h.comp g') pre
  nonhit := hΘ.nonhit
  ovl c C hC ψ b ψ' b' hb hb' n g args rs ht hrs h1 h2 :=
    hΘ.ovl c C hC ψ b ψ' b' hb hb' n (h.comp g) args rs ((argsTyped_restr_iff Θ h g args).1 ht) hrs h1 h2

theorem SData.Good.restr {Θ : SData m} (hΘ : Θ.Good) (h : Hom k m) : (Θ.restr h).Good :=
  { hΘ.toGoodCore.restr h with fib := fun c j n g pre hp => hΘ.fib c j n (h.comp g) pre hp }

theorem shapeOf_dataC (Θ : SData m) : shapeOf (dataC Θ) (Hom.id m) =
    tagZ tData (ZFSet.pair (natZ Θ.idx) (ZFSet.pair (Θ.pv m (Hom.id m)) (shapeV (Θ.restr (Hom.id m))))) := by
  rw [dataC, shapeOf_mkKV, dataDatum, π1_quad]
  simp [SData.restr]

end

end Model
