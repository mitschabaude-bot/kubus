import Model.Whnf.Valid2ElimH19

/-! # Normalization evidence for the raw higher inductive eliminator induction -/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' K : ℕ}

/-- The eliminator's contractum at a constructor or formal composition head. -/
def elimRedH (d : ℕ) (D : DataDecl) (ps M bs : Tm) : Tm → Tm
  | .con _ c _ args rs => match D.ctors[c]? with
    | some C => Tm.papps (ecTm d C c ps M bs args.toList) rs
    | none => .abort
  | .hcomp _ φ u a => elimHcompTm d ps M bs φ u a
  | _ => .abort

theorem elimRedH_con {d c : ℕ} {D : DataDecl} {C : Ctor} (hC : D.ctors[c]? = some C)
    (ps M bs q : Tm) (X : List Tm) (rs : List I) :
    elimRedH d D ps M bs (.con d c q (Tm.ofList X) rs) = Tm.papps (ecTm d C c ps M bs X) rs := by
  simp only [elimRedH, hC, toList_ofList]

theorem elimRedH_hcomp (d : ℕ) (D : DataDecl) (ps M bs q u a : Tm) (φ : I) :
    elimRedH d D ps M bs (.hcomp (.data d q) φ u a) = elimHcompTm d ps M bs φ u a := rfl

/-- Contracta commute with restrictions of heads, including restrictions exposing a boundary. -/
theorem elimRedH_isub {d : ℕ} {D : DataDecl} {ps M bs W : Tm} (hbs : IsList bs)
    (hWF : WhnfF d D W) (σ : ISub k' k) :
    (elimRedH d D ps M bs W).isub σ =
      elimRedH d D (ps.isub σ) (M.isub σ) (bs.isub σ) (W.isub σ) := by
  rcases hWF with ⟨c, C, q, X, rs, hC, rfl, -, -⟩ | ⟨q, φ, u, a, rfl, -⟩
  · rw [elimRedH_con hC, isub_conT, elimRedH_con hC, papps_isub2, ecTm_isub d C c hbs]
  · rw [elimRedH_hcomp, isub_hcomp]
    exact elimHcompTm_isub d ps M bs u a φ σ

/-- Computation to the contractum selected by each normal form, uniformly in restrictions. -/
def ElimNormH (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P M bs : Tm)
    (k : ℕ) (ρ : ISub k K) (x : Tm) : Prop :=
  ∀ k' (σ : ISub k' k) W, RedE S k' (.data d (P.isub (ρ.comp σ))) (x.isub σ) W →
    RE2 S k' ((M.isub (ρ.comp σ)).inst (x.isub σ))
      (.elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) (x.isub σ))
      (elimRedH d D (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) W)

theorem ElimNormH.isub {d : ℕ} {D : DataDecl} {P M bs x : Tm} {ρ : ISub k K}
    (N : ElimNormH S d D K P M bs k ρ x) (σ : ISub k' k) :
    ElimNormH S d D K P M bs k' (ρ.comp σ) (x.isub σ) := by
  intro k'' τ W hw
  have R := N k'' (σ.comp τ) W (by simpa only [Tm.isub_isub, ISub.comp_assoc] using hw)
  simpa only [Tm.isub_isub, ISub.comp_assoc] using R

/-- The relation induction also records normalization for its left element. -/
def EN1H (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P M bs : Tm)
    (k : ℕ) (g : Hom k K) (A x : Tm) : Prop :=
  ∀ (ρ : ISub k K), g = ρ.hom → A = .data d (P.isub ρ) → ElimNormH S d D K P M bs k ρ x

/-- The stage induction records normalization of its left normal form. -/
def EN2H (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P M bs : Tm)
    (k : ℕ) (g : Hom k K) (A x : Tm) : Prop :=
  ∀ (ρ : ISub k K), g = ρ.hom → A = .data d (P.isub ρ) →
  ∀ W, RedE S k A x W → ElimNormH S d D K P M bs k ρ W

/-- Paired contracta at a stage; the normal forms may be constructors or formal compositions. -/
def EMStageH (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P M bs : Tm)
    (k : ℕ) (g : Hom k K) (A x x' : Tm) : Prop :=
  ∀ (ρ : ISub k K), g = ρ.hom → A = .data d (P.isub ρ) →
  ∀ Q M' bs', ElimRelH S d D K P M bs Q M' bs' →
  ∀ W W', RedE S k A x W → RedE S k A x' W' →
    RE2 S k ((M.isub ρ).inst W)
      (elimRedH d D (P.isub ρ) (M.isub ρ) (bs.isub ρ) W)
      (elimRedH d D (Q.isub ρ) (M'.isub ρ) (bs'.isub ρ) W')

variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hW hD

/-- Elimination reduces to the contractum of the scrutinee's normal form. -/
theorem elimRedH_reduct {ps M bs : Tm} {m : ℕ} (E : ElimPrem S k .one [] d D ps M bs m)
    {x W : Tm} (hx : HasTy S k .one [] x (.data d ps))
    (hw : RedE S k (.data d ps) x W) (hWF : WhnfF d D W) (hH : D.isHIT = true) :
    Red S (.elim d ps M bs x) (elimRedH d D ps M bs W) ∧
      EqTm S k .one [] (.elim d ps M bs x) (elimRedH d D ps M bs W) (M.inst x) := by
  rcases hWF with ⟨c, C, q, X, rs, hC, rfl, -, hn⟩ | ⟨q, φ, u, a, rfl, hn⟩
  · rw [elimRedH_con hC]
    exact elim_reductH hW hD E hx hC hw hn
  · exact elim_hcomp_reductH hW hD hH E hx hw hn

/-- Normalization evidence supplies computability of the eliminator itself. -/
theorem ElimNormH.computable (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1)) {P M bs : Tm}
    (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (hPP : RT2 S K (.data d P) (.data d P))
    (H : ElimRelH S d D K P M bs P M bs) (ρ : ISub k K) {x x' : Tm}
    (hx : RE2 S k (.data d (P.isub ρ)) x x') (N : ElimNormH S d D K P M bs k ρ x) :
    RE2 S k ((M.isub ρ).inst x) (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) x)
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) x) := by
  obtain ⟨W, hw, -, -, -⟩ := whnf_data hW hD hH hyp hP hPP ρ hx
  have hxc := closed_of_ty hW (RE2.typed hx).1
  have R := N k (ISub.id k) W (by rw [ISub.comp_id, isub_id_of_closed hxc]; exact hw)
  rw [ISub.comp_id, isub_id_of_closed hxc] at R
  have hA := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ
  have hxx := RE2.trans hW hA hx (RE2.symm hW hA hx)
  exact RE2.trans hW (H.mot k ρ _ _ hxx) R (RE2.symm hW (H.mot k ρ _ _ hxx) R)

end

end Model.Whnf
