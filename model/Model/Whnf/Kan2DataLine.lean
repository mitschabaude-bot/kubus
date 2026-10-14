import Model.Whnf.Kan2DataFace
import Model.Whnf.Kan2DataFillH

/-!
# Argument types of literal inductive types at related prefixes

The argument types of a constructor at related prefixes of arguments and related parameters are
related at the code of the inductive type (`argTy_code_rel`), for any parameter lists related to
those of a literal inductive type `data d P`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

section lit
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
  {K : ℕ} {P : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (hPP : RT2 S K (.data d P) (.data d P))
include hW hD hP

/-- Related elements of a type whose code is a restriction of that of a literal inductive type. -/
theorem RE2_dataT_iff {k3 : ℕ} (g : Hom k3 K) {T x y : Tm}
    (hsem : semK S k3 T = res g (dataC (ΘK S D d K P))) :
    RE2 S k3 T x y ↔ EB S k3 T x y ∧
      DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k3 g T x y := by
  unfold RE2
  rw [hsem, Comp2_res (show dataC (ΘK S D d K P) ≠ ∅ from mkKV_ne_empty _), Hom.comp_id, Comp2_dataC]
  simp only [show (ΘK S D d K P).idx = d from rfl]
  constructor
  · rintro ⟨hE, -, -, hdr⟩
    refine ⟨hE, ?_⟩
    have := DR2.unbase (Θ := ΘK S D d K P) (Hom.id K) (h := g) (g := Hom.id k3)
      (by rw [Hom.id_comp]; exact hdr)
    rwa [Hom.comp_id] at this
  · rintro ⟨hE, hdr⟩
    refine ⟨hE, ?_, hE, ?_⟩
    · have := mem_of_ty hW hE.1
      rwa [hsem] at this
    · have := DR2.rebase (Hom.id K) hdr g (Hom.id k3) (Hom.comp_id _).symm
      rwa [Hom.id_comp] at this

/-- The code of a restriction of a literal inductive type related to `data d P`. -/
theorem semK_dataQ {Q : Tm} (hQ : RT2 S K (.data d P) (.data d Q)) (σ : ISub k' K) :
    semK S k' (.data d (Q.isub σ)) = res σ.hom (dataC (ΘK S D d K P)) := by
  have hQT : IsTyK S K (.data d Q) := (Comp2_ty_base hQ).2.2.1
  rw [show Tm.data d (Q.isub σ) = (Tm.data d Q).isub σ from rfl, semK_isubTy hW hQT σ, RT2.semK_eq hW hQ,
    semK_dataT hW hD hP]

include hH

/-- The argument types at related prefixes of arguments and related parameters are related at the
code of the inductive type. -/
theorem argTy_code_rel {k3 : ℕ} (ρ3 : ISub k3 K) {R R' : Tm}
    (hRR' : argRelH (ΘK S D d K P) (Hom.id K) S k3 ρ3.hom R R')
    (hRsem : semK S k3 (.data d R) = res ρ3.hom (dataC (ΘK S D d K P)))
    (hRc : R.closedB 0 k3 = true) (hR'c : R'.closedB 0 k3 = true)
    {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {A A' : List Tm} (hl' : A'.length = A.length)
    (hrec : ∀ i (hi : i < A.length) (hi' : i < A'.length), C.isRec i = true → RE2 S k3 (.data d R) A[i] A'[i])
    (hpt : ∀ i (hi : i < A.length) (hi' : i < A'.length), C.isRec i = false →
      RE2 S k3 ((C.argTy d D.params.length i).substList ((A.take i).reverse ++ R.toList.reverse)) A[i] A'[i])
    (hr : A.length < C.args.length) (hrr : C.isRec A.length = false) :
    (Comp2 S (tyLook (shapeV ((ΘK S D d K P).restr ((Hom.id K).comp ρ3.hom))) c A.length (A.map (semK S k3)))
      k3 k3 (Hom.id k3)).ty
      ((C.argTy d D.params.length A.length).substList (A.reverse ++ R.toList.reverse))
      ((C.argTy d D.params.length A.length).substList (A'.reverse ++ R'.toList.reverse)) := by
  have hdD := dataD_eq hW hD
  have hC' : (dataD S (ΘK S D d K P).idx).ctors[c]? = some C := by
    show (dataD S d).ctors[c]? = some C; rw [hdD]; exact hC
  -- the relations of the prefix, at the code, by induction along it
  let Good : ℕ → Prop := fun j =>
    (∀ i (hi : i < A.length) (hi' : i < A'.length), i < j → C.isRec i = true →
      DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k3
        ρ3.hom (.data d R) A[i] A'[i]) ∧
    (∀ i (hi : i < A.length) (hi' : i < A'.length), i < j → C.isRec i = false →
      dataP2 S (ΘK S D d K P) (Hom.id K) k3 ρ3.hom c i ((A.take i).map (semK S k3))
        ((C.argTy d (dataD S d).params.length i).substList ((A.take i).reverse ++ R.toList.reverse))
        A[i] A'[i])
  have key : ∀ j, j ≤ A.length → Good j := by
    intro j
    induction j with
    | zero => intro _; exact ⟨fun i _ _ h => absurd h (Nat.not_lt_zero _), fun i _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ j ih =>
      intro hj
      obtain ⟨g1, g2⟩ := ih (by omega)
      refine ⟨fun i hi hi' hij hri => ?_, fun i hi hi' hij hri => ?_⟩
      · by_cases hlt : i < j
        · exact g1 i hi hi' hlt hri
        obtain rfl : i = j := by omega
        exact ((RE2_dataT_iff hW hD hP ρ3.hom hRsem).1 (hrec i hi hi' hri)).2
      · by_cases hlt : i < j
        · exact g2 i hi hi' hlt hri
        obtain rfl : i = j := by omega
        have hli : (A.take i).length = i := by simp; omega
        have hty := argRelH_id (Hom.id K) hRR' hRc hR'c hC' (args := A.take i) (args' := A'.take i)
          (by rw [hli]; omega) (by simp; omega) (by rw [hli]; exact hri)
          (fun i' h1 h2 hri' => by
            simp only [List.getElem_take]; exact g1 i' (by simp at h1; omega) (by simp at h2; omega)
              (by simp at h1; omega) hri')
          (fun i' h1 h2 hri' => by
            simp only [List.getElem_take, List.take_take]
            rw [Nat.min_eq_left (by simp at h1; omega)]
            exact g2 i' (by simp at h1; omega) (by simp at h2; omega) (by simp at h1; omega) hri')
        rw [hli] at hty
        have hb := Comp2_ty_base hty
        unfold dataP2
        simp only [show (ΘK S D d K P).idx = d from rfl, hdD] at hb ⊢
        exact (Comp2_el_iff hb.1 hb.2.2.2.1).2 (by simpa using hpt i hi hi' hri)
  obtain ⟨g1, g2⟩ := key A.length (Nat.le_refl _)
  have := argRelH_id (Hom.id K) hRR' hRc hR'c hC' (args := A) (args' := A') hr hl' hrr
    (fun i hi hi' hri => g1 i hi hi' hi hri) (fun i hi hi' hri => g2 i hi hi' hi hri)
  simpa only [show (ΘK S D d K P).idx = d from rfl, hdD] using this

omit hH in
/-- Parameters related to those of a literal inductive type are related to each other. -/
theorem argRelH_QQ {Q Q' : Tm} (hQ : RT2 S K (.data d P) (.data d Q)) (hQ' : RT2 S K (.data d P) (.data d Q'))
    (σ : ISub k' K) : argRelH (ΘK S D d K P) (Hom.id K) S k' σ.hom (Q.isub σ) (Q'.isub σ) := by
  obtain ⟨-, rQP, dP, dQ, -, hPl, hQl⟩ := dataLit_rel hW hD hP hQ σ
  obtain ⟨rPQ', -, -, -, -, -, -⟩ := dataLit_rel hW hD hP hQ' σ
  have hQT : IsTyK S k' (.data d (Q.isub σ)) := ((Comp2_ty_base hQ).2.2.1).isub hW σ
  have hPT : IsTyK S k' (.data d (P.isub σ)) := ((Comp2_ty_base hQ).2.1).isub hW σ
  have hQ'T : IsTyK S k' (.data d (Q'.isub σ)) := ((Comp2_ty_base hQ').2.2.1).isub hW σ
  have hdd : TyEq S k' (.data d (Q.isub σ)) (.data d (P.isub σ)) :=
    ((Comp2_ty_base hQ).2.2.2.2.2.isub hW σ).symm
  exact argRelH_comp hW (Hom.id K) (perP_ΘK hW hD hP) rQP dQ dP rPQ' hQT hPT hQ'T hPl hdd

end lit

end

end Model.Whnf
