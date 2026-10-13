import Model.Canon.Proj

/-!
# Canonicity: projections and faces

Face substitutions (`face_all`), the commutation of projections with interval substitutions, and
the conversion of argument telescopes along equal arguments.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig}

/-- On a face, a term equals its instance at the face's endpoints. -/
theorem face_all (hW : WfSig S) {Ψ : ℕ} {Ξ : I} {Γ : Ctx} {t A : Tm} {l : ℕ}
    (hA : HasTy0 S Ψ Ξ Γ A (.univ l) ∨ A = .univ l) (ht : HasTy0 S Ψ Ξ Γ t A) :
    ∀ (α : I.Face), (∀ p ∈ α, p.1 < Ψ) → I.Entails Ξ (I.ofFace α) →
      EqTm0 S Ψ Ξ Γ t (t.subst Tm.var (faceSub α)) A
  | [], _, _ => by
    rw [show faceSub [] = I.var from funext fun _ => rfl, subst_var]; exact EqTm0.refl ht
  | (i, e) :: α, hsc, he => by
    obtain ⟨hT, hC⟩ := wf_typed _ S rfl hW
    have hS := sigClosed_of_wfSig hW
    have hlit : I.Entails Ξ (I.lit i e) := ent_trans he (ent_and_left _ _)
    have hrest : I.Entails Ξ (I.ofFace α) := ent_trans he (ent_and_right _ _)
    have hi : i < Ψ := hsc _ (List.mem_cons_self ..)
    have e1 : EqTm0 S Ψ Ξ Γ t (t.dset i (I.ofDir e)) A := by
      rcases hA with hA | rfl
      · exact EqTm0.face hi hlit hA ht
      · exact EqTm0.faceU hi hlit ht
    have ht1 := (pre_eq hS hT hC e1).2.1
    have e2 := face_all hW hA ht1 α (fun p hp => hsc p (List.mem_cons_of_mem _ hp)) hrest
    have hc : (t.dset i (I.ofDir e)).subst Tm.var (faceSub α) = t.subst Tm.var (faceSub ((i, e) :: α)) := by
      rw [Tm.dset, Tm.dsubst, subst_subst]
      congr 1
      funext x; exact faceSub_cons_comp i e α (.var x)
    rw [hc] at e2
    exact e1.trans e2


/-! ## Projections under interval substitutions -/

theorem upN_var : ∀ k, upN k Tm.var = Tm.var
  | 0 => rfl
  | k + 1 => by rw [upN, upN_var k, up_var]

theorem lams_dsubst (τ : ℕ → I) : ∀ (Ts : List Tm) (b : Tm),
    (lams Ts b).subst Tm.var τ = lams (Ts.map (·.subst Tm.var τ)) (b.subst Tm.var τ)
  | [], _ => rfl
  | T :: Ts, b => by
    show Tm.lam (T.subst Tm.var τ) ((lams Ts b).subst (Tm.up Tm.var) τ) = _
    rw [up_var, lams_dsubst τ Ts b]; rfl

theorem branchesOf_dsubst (hS : SigClosed S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) {ps P : Tm}
    (hps : IsList ps) (hpl : ps.toList.length = D.params.length) (body : ℕ → Ctor → Tm) (τ : ℕ → I) :
    (branchesOf D d ps P body).subst Tm.var τ =
      branchesOf D d (ps.subst Tm.var τ) (P.subst Tm.var τ) (fun c' C' => (body c' C').subst Tm.var τ) := by
  unfold branchesOf
  rw [ofList_subst]
  congr 1
  apply List.ext_getElem (by simp)
  intro c' h1 h2
  simp only [List.getElem_map, List.getElem_mapIdx]
  have hcl : c' < D.ctors.length := by simpa using h2
  have hc' : D.ctors[c']? = some D.ctors[c'] := List.getElem?_eq_getElem hcl
  rw [lams_dsubst, List.map_append, List.map_map, List.map_map]
  congr 2
  · apply List.map_congr_left; intro k hk
    simp only [Function.comp]
    have := branchArgTy_subst (σ := Tm.var) (τ := τ) (argTy_closed hS hD hc' k) hps hpl
    rwa [upN_var] at this
  · apply List.map_congr_left; intro s hs
    simp only [Function.comp]
    have := branchIhTy_subst (σ := Tm.var) (τ := τ) (List.mem_range.1 hs) P
    rwa [upN_var, up_var] at this

section
variable {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor} {j : ℕ}

theorem projQBody_dsubst (hS : SigClosed S) (hD : S[d]? = some (.data D)) (hcC : D.ctors[c]? = some C)
    (hj : j < C.args.length) {ps : Tm} (hps : IsList ps) (hpl : ps.toList.length = D.params.length)
    (τ : ℕ → I) (c' : ℕ) (C' : Ctor) :
    (projQBody d D.params.length C ps c j c' C').subst Tm.var τ = projQBody d D.params.length C (ps.subst Tm.var τ) c j c' C' := by
  unfold projQBody
  split
  · have hcl := argTy_closed hS hD hcC j
    rw [substList_subst (by simpa [argVarsE, Nat.min_eq_left hj.le, Nat.add_comm, hpl] using hcl), List.map_append]
    congr 2
    · conv => rhs; rw [← List.map_id (List.take j (argVarsE C.recPos.length C.args.length)).reverse]
      apply List.map_congr_left; intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_take (List.mem_reverse.1 hx))
      rfl
    · rw [toList_subst hps, List.map_reverse]
  · show Tm.pi _ ((Tm.data d ps).subst (Tm.up Tm.var) τ) = _
    rw [up_var]; rfl


theorem projBody_dsubst {ps : Tm} (τ : ℕ → I) (c' : ℕ) (C' : Ctor) :
    (projBody d C ps c j c' C').subst Tm.var τ = projBody d C (ps.subst Tm.var τ) c j c' C' := by
  unfold projBody
  split
  · rfl
  · show Tm.lam _ ((Tm.var 0).subst (Tm.up Tm.var) τ) = _
    rw [up_var]; rfl

theorem projQ_dsubst (hS : SigClosed S) (hD : S[d]? = some (.data D)) (hcC : D.ctors[c]? = some C)
    (hj : j < C.args.length) {ps : Tm} (hps : IsList ps) (hpl : ps.toList.length = D.params.length) (τ : ℕ → I) :
    (projQ d D ps c C j).subst Tm.var τ = projQ d D (ps.subst Tm.var τ) c C j := by
  unfold projQ
  show Tm.elim d (ps.subst Tm.var τ) ((Tm.univ D.level).subst (Tm.up Tm.var) τ)
    ((branchesOf D d ps (.univ D.level) (projQBody d D.params.length C ps c j)).subst Tm.var τ) (Tm.var 0) = _
  rw [branchesOf_dsubst hS hD hps hpl]
  congr 2
  funext c' C'
  exact projQBody_dsubst hS hD hcC hj hps hpl τ c' C'

theorem proj_dsubst (hS : SigClosed S) (hD : S[d]? = some (.data D)) (hcC : D.ctors[c]? = some C)
    (hj : j < C.args.length) {ps : Tm} (hps : IsList ps) (hpl : ps.toList.length = D.params.length) (τ : ℕ → I)
    (t : Tm) :
    (proj d D ps c C j t).subst Tm.var τ = proj d D (ps.subst Tm.var τ) c C j (t.subst Tm.var τ) := by
  unfold proj
  show Tm.elim d (ps.subst Tm.var τ) ((projQ d D ps c C j).subst (Tm.up Tm.var) τ)
    ((branchesOf D d ps (projQ d D ps c C j) (projBody d C ps c j)).subst Tm.var τ) (t.subst Tm.var τ) = _
  rw [up_var, branchesOf_dsubst hS hD hps hpl, projQ_dsubst hS hD hcC hj hps hpl]
  congr 2
  funext c' C'
  exact projBody_dsubst τ c' C'

end

end

end Model.Canon
