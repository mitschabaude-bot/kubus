import KubusCore.Meta.SubDefs

/-!
# Metatheory: substitutions that agree on faces

Two interval substitutions that agree on every face of the restriction give judgmentally equal
results (`face_lemma`), provided the judgment is closed under substitution and under
substitutions that are equal in the free De Morgan algebra. The proof splits the restriction
into its faces (`EqTm.local`), substitutes the endpoints of a face with the face rule, and
then uses functionality. This is how the face rule (whose instances under an interval
substitution are not instances of the face rule) is shown to be stable under substitution.
-/

namespace KubusCore.Meta

open Tm
open I (Face)

variable {S : Sig}

/-! ## Faces as substitutions -/

/-- Set interval variable `k` to the endpoint `e`. -/
def dsetI (k : Nat) (e : Bool) : Nat → I := fun n => if n = k then I.ofDir e else .var n

theorem faceSub_cases (c : Face) (n : Nat) :
    (∃ e, (n, e) ∈ c ∧ faceSub c n = I.ofDir e) ∨ ((∀ e, (n, e) ∉ c) ∧ faceSub c n = .var n) := by
  induction c with
  | nil => right; simp [faceSub]
  | cons l c ih =>
    obtain ⟨k, d⟩ := l
    simp only [faceSub]
    by_cases h : n = k
    · subst h; left; exact ⟨d, List.mem_cons_self .., by simp⟩
    · simp only [h, if_false]
      rcases ih with ⟨e, he, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨e, List.mem_cons_of_mem _ he, h2⟩
      · right; refine ⟨fun e he => ?_, h2⟩
        rcases List.mem_cons.1 he with he | he
        · simp at he; exact h he.1
        · exact h1 e he

theorem faceSub_mem {c : Face} (hc : Face.consistent c = true) {n : Nat} {e : Bool} (h : (n, e) ∈ c) :
    faceSub c n = I.ofDir e := by
  rcases faceSub_cases c n with ⟨e', he', h2⟩ | ⟨h1, _⟩
  · rw [h2]
    by_cases hee : e' = e
    · rw [hee]
    · have : e' = !e := by cases e <;> cases e' <;> simp_all
      subst this
      exact absurd he' (consistent_iff.1 hc (n, e) h)
  · exact absurd h (h1 e)

theorem ofDir_subst (d : Bool) (τ : Nat → I) : (I.ofDir d).subst τ = I.ofDir d := by cases d <;> rfl

/-- A face extending `c` subsumes `c`'s substitution. -/
theorem faceSub_comp {c c' : Face} (hc' : Face.consistent c' = true) (hsub : ∀ l ∈ c, l ∈ c') (n : Nat) :
    (faceSub c n).subst (faceSub c') = faceSub c' n := by
  rcases faceSub_cases c n with ⟨e, he, h2⟩ | ⟨_, h2⟩
  · rw [h2, ofDir_subst, faceSub_mem hc' (hsub _ he)]
  · rw [h2]; rfl

theorem mem_of_ent_lit {c : Face} (hc : Face.consistent c = true) {k : Nat} {e : Bool}
    (h : I.Entails (I.ofFace c) (I.lit k e)) : (k, e) ∈ c := by
  have hs := faceAsg_sat hc
  have := entails_iff.1 h _ (faceAsg_k3 c) ((eval_ofFace _ c).2 hs)
  cases e <;> simp only [I.lit, I.eval] at this
  · have h0 := neg_one_iff.1 this
    simp only [faceAsg] at h0
    split at h0
    · cases h0
    · split at h0
      · rename_i h1; exact List.contains_iff_mem.1 h1
      · cases h0
  · simp only [faceAsg] at this
    split at this
    · rename_i h1; exact List.contains_iff_mem.1 h1
    · split at this <;> cases this

theorem subset_of_ent_ofFace {c c' : Face} (hc' : Face.consistent c' = true)
    (h : I.Entails (I.ofFace c') (I.ofFace c)) : ∀ l ∈ c, l ∈ c' := by
  intro l hl
  obtain ⟨k, e⟩ := l
  exact mem_of_ent_lit hc' (ent_trans h (ofFace_ent_lit hl))

/-! ## `FaceEq` -/

theorem faceEq_refl (Ψ : Nat) (Ξ : I) (τ : Nat → I) : FaceEq Ψ Ξ τ τ := fun _ _ _ _ => I_eq_refl _

theorem faceEq_symm {Ψ Ξ τ1 τ2} (h : FaceEq Ψ Ξ τ1 τ2) : FaceEq Ψ Ξ τ2 τ1 :=
  fun i hi α hα => I_eq_symm (h i hi α hα)

theorem faceEq_trans {Ψ Ξ τ1 τ2 τ3} (h1 : FaceEq Ψ Ξ τ1 τ2) (h2 : FaceEq Ψ Ξ τ2 τ3) : FaceEq Ψ Ξ τ1 τ3 :=
  fun i hi α hα => I_eq_trans (h1 i hi α hα) (h2 i hi α hα)

theorem faceEq_of_eq {Ψ Ξ τ1 τ2} (h : ∀ i < Ψ, I.Eq (τ1 i) (τ2 i)) : FaceEq Ψ Ξ τ1 τ2 :=
  fun i hi _ _ => I_eq_subst (h i hi) _

theorem faceEq_restrict {Ψ Ξ Ξ' τ1 τ2} (h : FaceEq Ψ Ξ τ1 τ2) (he : I.Entails Ξ' Ξ) :
    FaceEq Ψ Ξ' τ1 τ2 := by
  intro i hi β' hβ'
  simp only [I.Entails, I.entails, List.all_eq_true, List.any_eq_true] at he
  obtain ⟨β, hβ, hsub⟩ := he β' hβ'
  have hsub' : ∀ l ∈ β, l ∈ β' := fun l hl => by simpa using hsub l hl
  have hc := faces_consistent hβ'
  have key : ∀ r : I, (r.subst (faceSub β)).subst (faceSub β') = r.subst (faceSub β') := fun r => by
    rw [I_subst_subst]; exact I_subst_congr (faceSub_comp hc hsub') r
  have := I_eq_subst (h i hi β hβ) (faceSub β')
  rwa [key, key] at this

theorem eval_subst_faceSub {ρ : Nat → I.M4} {c : Face} (h : Sat ρ c) (r : I) :
    (r.subst (faceSub c)).eval ρ = r.eval ρ := by
  rw [eval_subst]; exact eval_congr (eval_faceSub h) r

theorem eval_scoped_congr {r : I} {n : Nat} (hr : r.Scoped n) {ρ ρ' : Nat → I.M4}
    (h : ∀ i < n, ρ i = ρ' i) : r.eval ρ = r.eval ρ' := by
  induction r with
  | zero | one => rfl
  | var i => exact h i hr
  | neg r ih => simp only [I.eval]; rw [ih hr]
  | and r s ihr ihs | or r s ihr ihs => simp only [I.eval]; rw [ihr hr.1, ihs hr.2]

theorem faceEq_ent {Ψ Ξ τ1 τ2} (h : FaceEq Ψ Ξ τ1 τ2) {φ : I} (hφ : φ.Scoped Ψ)
    (he : I.Entails Ξ (φ.subst τ1)) : I.Entails Ξ (φ.subst τ2) := by
  rw [entails_iff] at *
  intro ρ hρ hΞ
  have := he ρ hρ hΞ
  obtain ⟨β, hβ, hs⟩ := (faces_sem hρ Ξ).1 hΞ
  rw [eval_subst] at *
  rw [← this]
  apply eval_scoped_congr hφ
  intro i hi
  rw [← eval_subst_faceSub hs (τ2 i), ← eval_subst_faceSub hs (τ1 i)]
  exact (h i hi β hβ ρ).symm

theorem faceEq_lit {Ψ Ξ} {τ : Nat → I} {i : Nat} {d : Bool} (he : I.Entails Ξ ((I.lit i d).subst τ)) :
    FaceEq Ψ Ξ τ (fun j => if j = i then I.ofDir d else τ j) := by
  intro j _ β hβ
  by_cases hji : j = i
  · subst hji
    simp only [if_true, ofDir_subst]
    have hβe := ent_trans (ofFace_ent hβ) he
    cases d
    · exact faceSub_eq_zero (faces_consistent hβ) hβe
    · exact faceSub_eq_one (faces_consistent hβ) hβe
  · simp only [hji, if_false]; exact I_eq_refl _

theorem faceEq_faceSub {Ψ Ξ} {α : Face} (he : I.Entails Ξ (I.ofFace α)) (τ : Nat → I) :
    FaceEq Ψ Ξ τ (fun j => (τ j).subst (faceSub α)) := by
  intro j _ β hβ
  have hc := faces_consistent hβ
  have hsub := subset_of_ent_ofFace hc (ent_trans (ofFace_ent hβ) he)
  rw [I_subst_subst]
  rw [I_subst_congr (fun n => faceSub_comp hc hsub n)]
  exact I_eq_refl _

theorem dsetI_eq_faceSub (k : Nat) (e : Bool) : dsetI k e = faceSub [(k, e)] := by
  funext n; simp [dsetI, faceSub]

/-! ## Splitting a restriction into its faces -/

theorem eq_local_faces {Ψ Φ Γ X Y T} (hX : HasTy0 S Ψ Φ Γ X T) (hY : HasTy0 S Ψ Φ Γ Y T)
    (h : ∀ α ∈ Φ.faces, EqTm0 S Ψ (cof Φ (I.ofFace α)) Γ X Y T) : EqTm0 S Ψ Φ Γ X Y T := by
  have hΦ := scoped_of_ty hX
  have hsc : ∀ α ∈ Φ.faces, (I.ofFace α).Scoped Ψ := fun α hα =>
    scoped_ofFace (faces_scoped hΦ α hα)
  have aux : ∀ cs : List Face, (∀ α ∈ cs, α ∈ Φ.faces) → ∀ Ξ : I, Ξ.Scoped Ψ → I.Entails Ξ Φ →
      I.Entails Ξ (I.ofFaces cs) → EqTm0 S Ψ Ξ Γ X Y T := by
    intro cs
    induction cs with
    | nil =>
      intro _ Ξ hs he hcs
      exact EqTm0.absurd hcs (HasTy0.restrict hs he hX) (HasTy0.restrict hs he hY)
    | cons c cs ih =>
      intro hcs Ξ hs he hc
      have hc' := hcs c (List.mem_cons_self ..)
      have hsc' : (I.ofFaces cs).Scoped Ψ :=
        scoped_ofFaces fun α hα => faces_scoped hΦ α (hcs α (List.mem_cons_of_mem _ hα))
      refine EqTm0.local (hsc c hc') hsc' hc (HasTy0.restrict hs he hX) (HasTy0.restrict hs he hY) ?_ ?_
      · exact EqTm0.restrict ⟨hs, hsc c hc'⟩ (ent_and_mono he (ent_refl _)) (h c hc')
      · exact ih (fun α hα => hcs α (List.mem_cons_of_mem _ hα)) _ ⟨hs, hsc'⟩
          (ent_trans (ent_and_left _ _) he) (ent_and_right _ _)
  exact aux _ (fun _ h => h) Φ hΦ (ent_refl _) (ent_ofFaces Φ)

/-! ## Transfer of typed substitutions along `FaceEq` -/

theorem TySub.transfer {Ψ Φ Ψ' Ξ Δ σ τ1 τ2} (hΦ : Φ.Scoped Ψ) : ∀ {Γ : Ctx}, CtxSub S Ψ Φ Γ →
    TySub S Ψ Φ Γ Ψ' Ξ Δ σ τ1 → (∀ i < Ψ, (τ2 i).Scoped Ψ') → FaceEq Ψ Ξ τ1 τ2 →
    TySub S Ψ Φ Γ Ψ' Ξ Δ σ τ2
  | [], _, h, hb, hf => ⟨hb, h.hscoped, faceEq_ent hf hΦ h.ent, (fun x A hx => by cases hx), h.wf⟩
  | A :: Γ, ⟨hΓ, l, _, _, hface⟩, h, hb, hf => by
    have ht := TySub.transfer (σ := fun n => σ (n + 1)) hΦ hΓ h.tail hb hf
    refine ⟨hb, h.hscoped, faceEq_ent hf hΦ h.ent, fun x B hx => ?_, h.wf⟩
    cases x with
    | zero =>
      simp only [Ctx.lookup, Option.some.injEq] at hx; subst hx
      have h0 := h.look 0 _ rfl
      rw [shift_subst] at h0 ⊢
      exact HasTy0.conv h0 (hface h.tail ht hf)
    | succ x =>
      simp only [Ctx.lookup, Option.map_eq_some_iff] at hx
      obtain ⟨B0, hB0, rfl⟩ := hx
      rw [shift_subst]
      exact ht.look x B0 hB0

/-! ## The face lemma -/

/-- The type of a judgment: a universe, or a type that is closed under (face-)substitution. -/
def TyFace (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (T : Tm) : Prop :=
  (∃ l, T = univ l) ∨ (∃ l, SubP S Ψ Φ Γ T (univ l) ∧ FaceP S Ψ Φ Γ T (univ l))

theorem TyFace.conv {Ψ Φ Γ T} (hT : TyFace S Ψ Φ Γ T) {Ψ' Ξ Δ σ τ1 τ2 X Y}
    (h1 : TySub S Ψ Φ Γ Ψ' Ξ Δ σ τ1) (h2 : TySub S Ψ Φ Γ Ψ' Ξ Δ σ τ2) (hf : FaceEq Ψ Ξ τ1 τ2)
    (h : EqTm0 S Ψ' Ξ Δ X Y (T.subst σ τ2)) : EqTm0 S Ψ' Ξ Δ X Y (T.subst σ τ1) := by
  rcases hT with ⟨l, rfl⟩ | ⟨l, _, hface⟩
  · exact h
  · exact EqTm0.conv h (EqTm0.symm (hface h1 h2 hf))

theorem TyFace.convTy {Ψ Φ Γ T} (hT : TyFace S Ψ Φ Γ T) {Ψ' Ξ Δ σ τ1 τ2 X}
    (h1 : TySub S Ψ Φ Γ Ψ' Ξ Δ σ τ1) (h2 : TySub S Ψ Φ Γ Ψ' Ξ Δ σ τ2) (hf : FaceEq Ψ Ξ τ1 τ2)
    (h : HasTy0 S Ψ' Ξ Δ X (T.subst σ τ2)) : HasTy0 S Ψ' Ξ Δ X (T.subst σ τ1) := by
  rcases hT with ⟨l, rfl⟩ | ⟨l, _, hface⟩
  · exact h
  · exact HasTy0.conv h (EqTm0.symm (hface h1 h2 hf))

theorem dset_subst_comp (X : Tm) (σ : Nat → Tm) (τ : Nat → I) (k : Nat) (e : Bool) :
    (X.subst σ τ).dset k (I.ofDir e) =
      X.subst (fun n => (σ n).dset k (I.ofDir e)) (fun j => (τ j).subst (dsetI k e)) := by
  simp only [Tm.dset, Tm.dsubst, subst_subst]
  rfl

theorem dsetI_idem (k : Nat) (e : Bool) (r : I) : (r.subst (dsetI k e)).subst (dsetI k e) = r.subst (dsetI k e) := by
  rw [I_subst_subst]; apply I_subst_congr; intro n
  simp only [dsetI]; split
  · exact ofDir_subst _ _
  · rename_i h; simp only [I.subst, dsetI, if_neg h]

/-- One endpoint substitution, by the face rule on both sides. -/
theorem face_step {Ψ Φ Γ X T} (hΦ : Φ.Scoped Ψ) (hΓ : CtxSub S Ψ Φ Γ) (hsub : SubP S Ψ Φ Γ X T)
    (hT : TyFace S Ψ Φ Γ T) {Ψ' Ξ Δ σ τ} (h1 : TySub S Ψ Φ Γ Ψ' Ξ Δ σ τ) {k : Nat} {e : Bool}
    (hk : k < Ψ') (he : I.Entails Ξ (I.lit k e)) :
    EqTm0 S Ψ' Ξ Δ (X.subst σ τ) (X.subst σ (fun j => (τ j).subst (dsetI k e))) (T.subst σ τ) := by
  have hf : FaceEq Ψ Ξ τ (fun j => (τ j).subst (dsetI k e)) := by
    rw [dsetI_eq_faceSub]
    exact faceEq_faceSub (by simpa [I.ofFace] using ent_and_intro he (ent_one Ξ)) τ
  have hb : ∀ i < Ψ, ((τ i).subst (dsetI k e)).Scoped Ψ' := fun i hi =>
    scoped_subst (h1.bound i hi) fun n hn => by
      simp only [dsetI]; split
      · cases e <;> trivial
      · exact hn
  have h2 := h1.transfer hΦ hΓ hb hf
  have hX1 := hsub h1
  have hX2 := hsub h2
  have heq : (X.subst σ τ).dset k (I.ofDir e) =
      (X.subst σ (fun j => (τ j).subst (dsetI k e))).dset k (I.ofDir e) := by
    rw [dset_subst_comp, dset_subst_comp]
    congr 1; funext j; rw [dsetI_idem]
  have e1 : EqTm0 S Ψ' Ξ Δ (X.subst σ τ) ((X.subst σ τ).dset k (I.ofDir e)) (T.subst σ τ) := by
    rcases hT with ⟨l, rfl⟩ | ⟨l, hsT, _⟩
    · exact EqTm0.faceU hk he hX1
    · exact EqTm0.face hk he (hsT h1) hX1
  have e2 : EqTm0 S Ψ' Ξ Δ (X.subst σ (fun j => (τ j).subst (dsetI k e)))
      ((X.subst σ (fun j => (τ j).subst (dsetI k e))).dset k (I.ofDir e)) (T.subst σ τ) := by
    apply hT.conv h1 h2 hf
    rcases hT with ⟨l, rfl⟩ | ⟨l, hsT, _⟩
    · exact EqTm0.faceU hk he hX2
    · exact EqTm0.face hk he (hsT h2) hX2
  rw [heq] at e1
  exact EqTm0.trans e1 (EqTm0.symm e2)

theorem faceSub_cons_comp (k : Nat) (e : Bool) (c : Face) (r : I) :
    (r.subst (dsetI k e)).subst (faceSub c) = r.subst (faceSub ((k, e) :: c)) := by
  rw [I_subst_subst]; apply I_subst_congr; intro n
  simp only [dsetI, faceSub]; split
  · exact ofDir_subst _ _
  · rfl

/-- Substituting all endpoints of a face, by repeated face steps. -/
theorem face_chain {Ψ Φ Γ X T} (hΦ : Φ.Scoped Ψ) (hΓ : CtxSub S Ψ Φ Γ) (hsub : SubP S Ψ Φ Γ X T)
    (hT : TyFace S Ψ Φ Γ T) {Ψ' Ξ Δ σ} : ∀ (α : Face), (∀ l ∈ α, l.1 < Ψ') →
    I.Entails Ξ (I.ofFace α) → ∀ τ, TySub S Ψ Φ Γ Ψ' Ξ Δ σ τ →
    EqTm0 S Ψ' Ξ Δ (X.subst σ τ) (X.subst σ (fun j => (τ j).subst (faceSub α))) (T.subst σ τ)
  | [], _, _, τ, h1 => by
    have : (fun j => (τ j).subst (faceSub [])) = τ := by funext j; exact I_subst_var _
    rw [this]; exact EqTm0.refl (hsub h1)
  | (k, e) :: α, hsc, he, τ, h1 => by
    have hlit : I.Entails Ξ (I.lit k e) := ent_trans he (ent_and_left _ _)
    have hrest : I.Entails Ξ (I.ofFace α) := ent_trans he (ent_and_right _ _)
    have hk : k < Ψ' := hsc _ (List.mem_cons_self ..)
    have s1 := face_step hΦ hΓ hsub hT h1 hk hlit
    have hf : FaceEq Ψ Ξ τ (fun j => (τ j).subst (dsetI k e)) := by
      rw [dsetI_eq_faceSub]
      exact faceEq_faceSub (by simpa [I.ofFace] using ent_and_intro hlit (ent_one Ξ)) τ
    have hb : ∀ i < Ψ, ((τ i).subst (dsetI k e)).Scoped Ψ' := fun i hi =>
      scoped_subst (h1.bound i hi) fun n hn => by
        simp only [dsetI]; split
        · cases e <;> trivial
        · exact hn
    have h2 := h1.transfer hΦ hΓ hb hf
    have s2 := face_chain hΦ hΓ hsub hT α (fun l hl => hsc l (List.mem_cons_of_mem _ hl)) hrest _ h2
    have s2' := hT.conv h1 h2 hf s2
    have : (fun j => ((τ j).subst (dsetI k e)).subst (faceSub α)) =
        (fun j => (τ j).subst (faceSub ((k, e) :: α))) := by
      funext j; exact faceSub_cons_comp k e α (τ j)
    rw [this] at s2'
    exact EqTm0.trans s1 s2'

/-- Substitutions agreeing on the faces of the restriction give equal results. -/
theorem face_lemma {Ψ Φ Γ X T} (hΦ : Φ.Scoped Ψ) (hΓ : CtxSub S Ψ Φ Γ) (hsub : SubP S Ψ Φ Γ X T)
    (hfun : FunP S Ψ Φ Γ X T) (hT : TyFace S Ψ Φ Γ T) : FaceP S Ψ Φ Γ X T := by
  intro Ψ' Φ' Δ σ τ1 τ2 h1 h2 hf
  apply eq_local_faces (hsub h1) (hT.convTy h1 h2 hf (hsub h2))
  intro α hα
  have hc := faces_consistent hα
  have hsα : (I.ofFace α).Scoped Ψ' := scoped_ofFace (faces_scoped h1.hscoped α hα)
  have hΞ : (cof Φ' (I.ofFace α)).Scoped Ψ' := ⟨h1.hscoped, hsα⟩
  have h1' := h1.restrict hΞ (ent_and_left _ _)
  have h2' := h2.restrict hΞ (ent_and_left _ _)
  have he : I.Entails (cof Φ' (I.ofFace α)) (I.ofFace α) := ent_and_right _ _
  have hsc : ∀ l ∈ α, l.1 < Ψ' := faces_scoped h1.hscoped α hα
  have hf' := faceEq_restrict hf (ent_and_left Φ' (I.ofFace α))
  -- the face substituted on both sides
  have hb : ∀ τ : Nat → I, (∀ i < Ψ, (τ i).Scoped Ψ') → ∀ i < Ψ, ((τ i).subst (faceSub α)).Scoped Ψ' :=
    fun τ hτ i hi => scoped_subst (hτ i hi) fun n hn => by
      rcases faceSub_cases α n with ⟨e, _, h⟩ | ⟨_, h⟩
      · rw [h]; cases e <;> trivial
      · rw [h]; exact hn
  have hfa1 := faceEq_faceSub (Ψ := Ψ) he τ1
  have hfa2 := faceEq_faceSub (Ψ := Ψ) he τ2
  have k1 := h1'.transfer hΦ hΓ (hb τ1 h1.bound) hfa1
  have k2 := h2'.transfer hΦ hΓ (hb τ2 h2.bound) hfa2
  have c1 := face_chain hΦ hΓ hsub hT α hsc he τ1 h1'
  have c2 := face_chain hΦ hΓ hsub hT α hsc he τ2 h2'
  have hmid := hfun k1 k2 ⟨fun x A hx => EqTm0.refl (k1.look x A hx), fun i hi => hf i hi α hα⟩
  have hmid' := hT.conv h1' k1 hfa1 hmid
  have c2' := hT.conv h1' h2' hf' c2
  exact EqTm0.trans c1 (EqTm0.trans hmid' (EqTm0.symm c2'))

end KubusCore.Meta
