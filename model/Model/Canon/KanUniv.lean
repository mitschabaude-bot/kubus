import Model.Canon.Fund

/-!
# Canonicity: composition in the universe

`hcomp U [φ ↦ u] u0` computes to a Glue type whose equivalence is `lineEquiv` of the reversed
tube. Its computability uses the fundamental lemma on Kan-free terms, with the Kan operations at
lines of types of the universe (covered by the induction hypothesis over codes of level `l`).
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

theorem I.scoped_subst_all {σ : ℕ → I} {k : ℕ} (hσ : ∀ j, (σ j).Scoped k) : ∀ r : I, (r.subst σ).Scoped k
  | .zero => trivial
  | .one => trivial
  | .var i => hσ i
  | .neg r => I.scoped_subst_all hσ r
  | .and r s => ⟨I.scoped_subst_all hσ r, I.scoped_subst_all hσ s⟩
  | .or r s => ⟨I.scoped_subst_all hσ r, I.scoped_subst_all hσ s⟩

theorem I.up_scoped_all {τ : ℕ → I} {k : ℕ} (hτ : ∀ i, (τ i).Scoped k) : ∀ i, (I.up τ i).Scoped (k + 1)
  | 0 => show (0 : ℕ) < k + 1 by omega
  | i + 1 => I.scoped_shift (hτ i)

/-- A term-closed instance of a closed type is one of its restrictions. -/
theorem subst_isub_ofFun {X : Tm} {n k' : ℕ} (hc : X.closedB 0 n = true) (γ : ℕ → Tm) (τ : ℕ → I)
    (hτ : ∀ i < n, (τ i).Scoped k') : X.subst γ τ = X.isub (ISub.ofFun n τ hτ) := by
  rw [isub_ofFun hc]
  exact closed_subst_eq X 0 n γ .var τ τ hc (fun x hx => absurd hx (Nat.not_lt_zero _)) (fun _ _ => rfl)

/-- The identity computable substitution at stage `k` (closed terms at stage `k`). -/
def CSub.idS (S : Sig) (k : ℕ) : CSub S k .one [] k where
  σ := ISub.id k
  γ := lsub [] 0
  face := ent_refl _
  nat _ := fun _ _ => rfl
  look x A h := by simp [Ctx.lookup] at h

theorem hyp_zero : Hyp S 0 := ⟨fun _ hi => absurd hi (Nat.not_lt_zero _), fun _ hd => absurd hd (Nat.not_lt_zero _)⟩

variable (hW : WfSig S) (hGC : GlueCompat S)
include hW

omit hW in
theorem CSub.idS_subst {t : Tm} (hc : t.closedB 0 k = true) : t.subst (CSub.idS S k).γ (CSub.idS S k).σ.τ = t :=
  closed_subst_id hc (fun x hx => absurd hx (Nat.not_lt_zero _)) (fun i hi => by simp [CSub.idS, ISub.id, hi])

include hGC in
/-- The fundamental lemma for a closed Kan-free term at stage `k`. -/
theorem fund_closed {t A : Tm} (ht : HasTy0 S k .one [] t A) (hK : KOK S 0 False t) : RE S k A t := by
  have h := fund_ty hW (O := False) False.elim hyp_zero hGC ht hK k (CSub.idS S k)
  have hs := minimal_to_spec ht
  rwa [CSub.idS_subst (closed_of_ty hW hs), CSub.idS_subst (closed_of_isTyK hW (isTyK_of_ty hW hs))] at h

variable {l : ℕ} (ih : ∀ m' X, WF l m' X → KR S m' X ∧ KanP S m' X)
include ih

theorem kanH_of_ty {X : Tm} (hX : HasTy S k .one [] X (.univ l)) (hR : RT S k X) : KanH S k X := by
  have hm := ((RE_univ_iff hW).1 (RE_univ_of hW hX hR)).2.1
  exact (ih k _ (ZFSet.mem_sep.1 hm).2).2.1 k (Hom.id k) X hR

theorem kanT_of_ty {X : Tm} (hX : HasTy S (k + 1) .one [] X (.univ l)) (hR : RT S (k + 1) X) : KanT S k X := by
  have hm := ((RE_univ_iff hW).1 (RE_univ_of hW hX hR)).2.1
  exact (ih (k + 1) _ (ZFSet.mem_sep.1 hm).2).2.2 k (Hom.id (k + 1)) X hR

/-- Transport along any instance of a computable line of types of level `l`. -/
theorem nkt_inst {n : ℕ} {B : Tm} (hB : HasTy S n .one [] B (.univ l)) (hR : ∀ k' (ρ : ISub k' n), RT S k' (B.isub ρ))
    (γ0 : ℕ → Tm) (τ0 : ℕ → I) : NKT S (B.subst γ0 τ0) := by
  intro k γ τ l' hτ _
  have hc := closed_of_ty hW hB
  have hsc : ∀ i < n, ((τ0 i).subst (I.up τ)).Scoped (k + 1) := fun i _ =>
    I.scoped_subst_all (I.up_scoped_all hτ) _
  rw [subst_subst, subst_isub_ofFun hc _ _ hsc]
  exact ⟨hR _ _, kanT_of_ty hW ih (HasTy.isubS hW hB _) (hR _ _)⟩

/-- Composition in any instance of a computable type of level `l`. -/
theorem nkh_inst {n : ℕ} {B : Tm} (hB : HasTy S n .one [] B (.univ l)) (hR : ∀ k' (ρ : ISub k' n), RT S k' (B.isub ρ))
    (γ0 : ℕ → Tm) (τ0 : ℕ → I) : NKH S (B.subst γ0 τ0) := by
  intro k γ τ l' hτ _
  have hc := closed_of_ty hW hB
  have hsc : ∀ i < n, ((τ0 i).subst τ).Scoped k := fun i _ => I.scoped_subst_all hτ _
  rw [subst_subst, subst_isub_ofFun hc _ _ hsc]
  exact ⟨hR _ _, kanH_of_ty hW ih (HasTy.isubS hW hB _) (hR _ _)⟩

end

end Model.Canon
