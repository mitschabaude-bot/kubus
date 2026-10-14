import Model.Whnf.Kan2DataHITInd

/-!
# Transport along lines of higher inductive types: contracta

The normal forms of elements of a literal higher inductive type (`WhnfF`: constructors where no boundary
holds, formal compositions whose face does not hold); the transport of an element reduces to the contractum
`tRedF` of the transport of its normal form (`tred_red`), which is a normal form, and contracta commute
with restrictions (`tRedF_isub`). Where the face of the transport holds, the contracta are related to the
normal forms (`TC.tcon_faceH`, `hcomp_faceH`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- The normal forms of a higher inductive type. -/
def WhnfF (d : ℕ) (D : DataDecl) (W : Tm) : Prop :=
  (∃ (c : ℕ) (C : Ctor) (q : Tm) (X : List Tm) (rs : List I), D.ctors[c]? = some C ∧
    W = .con d c q (Tm.ofList X) rs ∧ X.length = C.args.length ∧ firstBnd C.bnd rs = none) ∨
  (∃ (qs : Tm) (χ : I) (u a : Tm), W = .hcomp (.data d qs) χ u a ∧ ¬ I.Entails .one χ)

section red
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hp : D.params ≠ [])
  (hH : D.isHIT = true)
include hW hD hp hH

/-- The transport of an element reduces to the contractum of the transport of its normal form, a normal
form. -/
theorem tred_red {PL x W : Tm} {ψ : I} (hψ : ¬ I.Entails .one ψ) (hWF : WhnfF d D W) (hxW : RedW S x W)
    (hty : HasTy S k .one [] (.transp (.data d PL) ψ x) ((Tm.data d PL).dinst .one))
    (eW : EqTm S k .one [] x W ((Tm.data d PL).dinst .zero)) :
    Red S (.transp (.data d PL) ψ x) (tRedF d D PL ψ W) ∧
    EqTm S k .one [] (.transp (.data d PL) ψ x) (tRedF d D PL ψ W) ((Tm.data d PL).dinst .one) ∧
    IsWhnf S (tRedF d D PL ψ W) := by
  have rb := transp_rebase hW hty eW
  have r1 := red_transp_base hD hp (ps := PL) hψ hxW.1
  rcases hWF with ⟨c, C, q, X, rs, hC, rfl, hXl, hf⟩ | ⟨qs, χ, u, a, rfl, hχ⟩
  · rw [tRedF_con d D PL ψ hC]
    have hs := step_transp_conR hD hp hC (ps := PL) (qs := q) hψ hXl (step_con_none hD hC _ _ hf)
    exact ⟨r1.trans (.step hs (.refl _)), rb.2.trans (transpCon_eqR hW hD hp hC rb.1).1,
      step_con_none hD hC _ _ hf⟩
  · rw [tRedF_hcomp]
    have hs := step_transp_hcompH hD hp hH (ps := PL) (qs := qs) (u := u) (a := a) hψ hχ
    obtain ⟨_, ⟨hL, -, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
    obtain ⟨D', hD', hpt⟩ := gen_data_tele hL rfl
    rw [hD] at hD'; cases hD'
    have hd0 : HasTy S k .one [] (.data d (PL.dinst .zero)) (.univ D.level) := by
      have := HasTy.isubS hW (minimal_to_spec (HasTy0.data hD (hW.2 d D hD).1 hpt)) (ISub.cons .zero trivial (ISub.id k))
      rwa [show (Tm.data d PL).isub (ISub.cons .zero trivial (ISub.id k)) = .data d (PL.isub (ISub.cons .zero trivial
        (ISub.id k))) from rfl, isub_cons_id_of_closed (by simpa [Tm.closedB] using closed_ty hL)] at this
    have hb0 := (hcomp_data_retype hW (HasTy.eqR eW) hd0).1
    exact ⟨r1.trans (.step hs (.refl _)), rb.2.trans (transpHcomp_eq hD hp hH hb0 rb.1), step_hcomp_HIT hD hH hχ⟩

end red

/-- Contracta commute with restrictions. -/
theorem tRedF_isub (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) {PL W : Tm} {ψ : I}
    (hPl : IsList PL) (hPlen : PL.toList.length = D.params.length) (hWF : WhnfF d D W) (κ : ISub k' k) :
    (tRedF d D PL ψ W).isub κ = tRedF d D (PL.isub κ.up) (ψ.subst κ.τ) (W.isub κ) := by
  rcases hWF with ⟨c, C, q, X, rs, hC, rfl, hXl, -⟩ | ⟨qs, χ, u, a, rfl, -⟩
  · rw [tRedF_con d D PL ψ hC, isub_conT, tRedF_con d D _ _ hC, tConR_isub hW hD hC hPl hPlen hXl κ]
  · rw [tRedF_hcomp, tHc_isub]
    rfl

/-- The tube of the `transpHcomp` contractum at a point. -/
theorem transp_skip_dinst (L u : Tm) (φ r : I) :
    (Tm.transp (L.dsubst skipI) φ.shift u).dinst r = Tm.transp L φ (u.dinst r) := by
  simp only [Tm.dinst, Tm.dsubst, Tm.subst, subst_subst, I.shift, I_ren_subst]
  congr 1
  · conv_rhs => rw [← subst_var L]
    refine subst_congr (fun _ => rfl) (fun i => ?_) L
    rcases i with _ | i <;> rfl
  · conv_rhs => rw [← I_subst_var φ]
    rfl

namespace TC

variable {d : ℕ} {D : DataDecl} {PL : Tm} {φ : I} {c : ℕ} {C : Ctor} {q : Tm} {X : List Tm} {rs : List I}

/-- Where the face of a transport of a constructor holds, its `transpCon` contractum is related to the
constructor. -/
theorem tcon_faceH (H : TC S k d D PL PL φ φ c C q q X X rs rs) (hH : D.isHIT = true) (hyp : HITHyp2 S)
    (hφ : I.Entails .one φ) :
    RE2 S k (.data d (PL.dinst .one)) (tConR d D c C PL φ X rs) (.con d c q (Tm.ofList X) rs) := by
  have hW := H.hW
  obtain ⟨-, -, -, -, -, -, hPl, -, -, -, hPc, -⟩ := H.basic
  obtain ⟨hd1, s1, -, -, hc1⟩ := H.end_data
  have hP0 : PL.isub (ISub.cons .zero trivial (ISub.id k)) = PL.dinst .zero := isub_cons_id_of_closed hPc .zero trivial
  have hP1 : PL.isub (ISub.cons .one trivial (ISub.id k)) = PL.dinst .one := isub_cons_id_of_closed hPc .one trivial
  have hholds : (ival (idEnv k) (φ.subst (ISub.id k).τ)).holds := by
    rw [I_subst_id H.hφs]; exact (holds_iff_entails H.hφs).2 hφ
  have h10 := H.hLC k (ISub.id k) .one trivial hholds
  rw [show (Tm.data d PL).isub (ISub.cons .one trivial (ISub.id k)) = .data d (PL.dinst .one) by
      show Tm.data d (PL.isub _) = _; rw [hP1],
    show (Tm.data d PL).isub (ISub.cons .zero trivial (ISub.id k)) = .data d (PL.dinst .zero) by
      show Tm.data d (PL.isub _) = _; rw [hP0]] at h10
  have FA := H.face_args hφ
  obtain ⟨-, ⟨-, -, -, hb0⟩, -⟩ := gen_transpF (spec_to_minimal hW H.hty) rfl
  have hcb : HasTy S k .one [] (.con d c q (Tm.ofList X) rs) (.data d (PL.dinst .one)) :=
    (minimal_to_spec hb0 : HasTy S k .one [] _ (.data d (PL.dinst .zero))).tyConv (TyEq.symm (Comp2_ty_base h10).2.2.2.2.2)
  obtain ⟨eT, -⟩ := H.basic
  have R := con_rel hW H.hD hd1 s1 hH hyp c (ISub.id k) H.hC
    (by rw [isub_id_of_closed hc1]; exact (HasTy.eqR eT : HasTy S k .one [] (.con d c (PL.dinst .one)
      (Tm.ofList (tOuts d D C PL φ X)) rs) _))
    (by rw [isub_id_of_closed hc1]; exact hcb) (forall2_ieq_refl _) (fun i hi => by
      rw [isub_id_of_closed hc1]
      obtain ⟨T, R⟩ := FA i hi
      exact RE2.conv hW T (RE2.symm hW T R))
  rw [isub_id_of_closed hc1] at R
  exact R

end TC

section whnf
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = true)
  (hyp : HITHyp2 S) {K : ℕ} {P : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level))
  (hPP : RT2 S K (.data d P) (.data d P))
include hW hD hH hyp hP hPP

/-- The normal form of an element of a literal higher inductive type: related to itself and to the
element. -/
theorem whnf_data {k3 : ℕ} (ρ' : ISub k3 K) {x x' : Tm} (h : RE2 S k3 (.data d (P.isub ρ')) x x') :
    ∃ W, RedE S k3 (.data d (P.isub ρ')) x W ∧ WhnfF d D W ∧ RE2 S k3 (.data d (P.isub ρ')) W W ∧
      RE2 S k3 (.data d (P.isub ρ')) W x := by
  have hPρ := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ'
  have hdD := dataD_eq hW hD
  have hDR := DR2.at_id hW (Θ := ΘK S D d K P) ((RE2_dataLit_iff hW hD hP ρ').1 h).2
  rcases DR2At_cases hW hD hP hPP ρ' hDR with
    ⟨c, C, qs, Z, rs, qs', Z', rs', hC, hZl, hZ'l, hr, -, hrsl, hrsl', hreq, -, -, hZ⟩ |
    ⟨qs, χ, u, a, qs', χ', u', a', -, hr, hr', hχs, -, -, -, haa, hu⟩
  · have hf : firstBnd C.bnd rs = none := by
      have := hr.1.2; simp [IsWhnf, step, hD, hC] at this; exact this
    have hWW : RE2 S k3 (.data d (P.isub ρ')) (.con d c qs (Tm.ofList Z) rs) (.con d c qs (Tm.ofList Z) rs) :=
      con_rel hW hD hP hPP hH hyp c ρ' hC (HasTy.eqR hr.2) (HasTy.eqR hr.2) (forall2_ieq_refl _)
        (fun i hi => (args_self hW hD hP hPP ρ' hC hZl hZ'l hZ i hi).2.1)
    exact ⟨_, hr, .inl ⟨c, C, qs, Z, rs, hC, rfl, hZl, hf⟩, hWW, RE2_whnf hW hD hP hPP ρ' h hr hWW⟩
  · have hχ : ¬ I.Entails .one χ := by
      intro hc
      have := hr.1.2
      simp [IsWhnf, step, show I.entails .one χ = true from hc] at this
    have hty := HasTy.eqR hr.2
    have hPρ' : RT2 S k3 (.data d (P.isub ρ')) (.data d (P.isub ρ')) := hPρ
    have hT : ∀ {k4 : ℕ} (σ : ISub k4 k3), RT2 S k4 (.data d (P.isub (ρ'.comp σ))) (.data d (P.isub (ρ'.comp σ))) :=
      fun σ => RT2.isub hW (tyCode_of_univ hW hP) hPP _
    have tS : TubeD S k3 (.data d (P.isub ρ')) χ u u := by
      intro k4 σ r hr0 hh
      have h1 := hu k4 σ r hr0 hh
      rw [show (Tm.data d (P.isub ρ')).isub σ = .data d (P.isub (ρ'.comp σ)) by
        show Tm.data d ((P.isub ρ').isub σ) = _; rw [Tm.isub_isub]]
      exact RE2.trans hW (hT σ) h1 (RE2.symm hW (hT σ) h1)
    have hWW := hcomp_relD hW hD hH hP hPP ρ' hty hty (EqTm.refl hty) (ent_refl _) (ent_refl _) tS tS tS
      (RE2.trans hW hPρ haa (RE2.symm hW hPρ haa))
    exact ⟨_, hr, .inr ⟨qs, χ, u, a, rfl, hχ⟩, hWW, RE2_whnf hW hD hP hPP ρ' h hr hWW⟩

end whnf

section face
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = true)
  (hp : D.params ≠ []) {K : ℕ} {P : Tm} (hP : HasTy S (K + 1) .one [] (.data d P) (.univ D.level))
  (hArgK : KanShape S (K + 1) (ΘK S D d (K + 1) P))
  (hRL : Rob S d K P P)
include hW hD hH hp hP hArgK hRL

/-- Where the face of a transport of a formal composition holds, its `transpHcomp` contractum is related to
the composition. -/
theorem hcomp_faceH {k1 : ℕ} (ρ : ISub k1 K) (y : I) (hy : y.Scoped (k1 + 1)) {ψ χ : I} {qs u a : Tm}
    (hψs : ψ.Scoped k1) (hψ : I.Entails .one ψ)
    (LC : LineConst S k1 ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)) ψ)
    (hT : HasTy S k1 .one [] (.transp ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)) ψ (.hcomp (.data d qs) χ u a))
      (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one))
    (hU : ∀ k' (σ : ISub k' k1) (r : I), r.Scoped k' → (ival (idEnv k') (χ.subst σ.τ)).holds →
      RE2 S k' ((((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .zero).isub σ) ((u.isub σ.up).dinst r)
        ((u.isub σ.up).dinst r))
    (hA : RE2 S k1 (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .zero) a a) :
    RE2 S k1 (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one)
      (tHc d (P.isub (ISub.cons y hy ρ.up.tail)) ψ χ u a) (.hcomp (.data d qs) χ u a) := by
  have hPP1 := PP1 hW hD hp hP hArgK hRL
  have tyB : ∀ {k4 : ℕ} {X Z : Tm}, RT2 S k4 X Z → TyEq S k4 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  have hLt : HasTy S (k1 + 1) .one [] ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)) (.univ D.level) :=
    HasTy.isubS hW hP _
  have hXL : ∀ {k4 : ℕ} (θ : ISub k4 (k1 + 1)), TyCode k4
      (semK S k4 (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).isub θ)) := fun θ =>
    tyCode_of_univ hW (HasTy.isubS hW hLt θ)
  have eLr : ∀ {k4 : ℕ} (σ : ISub k4 k1) (r : I) (hr : r.Scoped k4), r.subst σ.τ = r →
      ((((Tm.data d P).isub (ISub.cons y hy ρ.up.tail))).dinst r).isub σ =
        ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).isub (ISub.cons r hr σ) := by
    intro k4 σ r hr hrr
    rw [isub_dinst, hrr]; exact isub_up_dinst _ σ r hr
  have conv01 : ∀ {k4 : ℕ} (σ : ISub k4 k1), RT2 S k4
      ((((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .zero).isub σ)
      ((((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one).isub σ) := by
    intro k4 σ
    rw [eLr σ .zero trivial rfl, eLr σ .one trivial rfl]
    have hh : (ival (idEnv k4) (ψ.subst σ.τ)).holds :=
      (holds_iff_entails (I.scoped_subst hψs σ.sc)).2 (ent_one_subst hψ σ.τ)
    exact RT2.symm hW (hXL _) (LC k4 σ .one trivial hh)
  have conv01' : RT2 S k1 (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .zero)
      (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one) := by
    have := conv01 (ISub.id k1)
    rwa [isub_id_of_closed (closed_of_ty hW (HasTy.isubS hW hLt (ISub.cons .zero trivial (ISub.id k1)) |>
      fun h => by rwa [isub_cons_id_of_closed (closed_ty (spec_to_minimal hW hLt))] at h)),
      isub_id_of_closed (closed_of_ty hW (HasTy.isubS hW hLt (ISub.cons .one trivial (ISub.id k1)) |>
      fun h => by rwa [isub_cons_id_of_closed (closed_ty (spec_to_minimal hW hLt))] at h))] at this
  obtain ⟨_, ⟨-, -, -, hb⟩, -⟩ := gen_transpF (spec_to_minimal hW hT) rfl
  have hc1 : ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).closedB 0 (k1 + 1) = true := closed_ty (spec_to_minimal hW hLt)
  have hd0 : HasTy S k1 .one [] (.data d ((P.isub (ISub.cons y hy ρ.up.tail)).dinst .zero)) (.univ D.level) := by
    have := HasTy.isubS hW hLt (ISub.cons .zero trivial (ISub.id k1))
    rwa [isub_cons_id_of_closed hc1] at this
  have hb0 := (hcomp_data_retype hW (minimal_to_spec hb : HasTy S k1 .one [] _
    (.data d ((P.isub (ISub.cons y hy ρ.up.tail)).dinst .zero))) hd0).1
  have eHc := transpHcomp_eq (D := D) hD hp hH hb0 hT
  have eF := EqTm.transpFace hψ hT
  have htH := HasTy.eqR eHc
  have hWty1 := HasTy.eqR eF
  have heqHW := eHc.symm.trans eF
  have htube : TubeD S k1 (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one) χ
      (.transp ((Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))).dsubst skipI) ψ.shift u) u := by
    intro k' σ r hr0 hh
    rw [tHc_tube_pt _ _ _ σ r hr0]
    have hσ := HasTy.isubS hW htH σ
    have htp := hcomp_tube_typed' hW (T := (Tm.data d ((P.isub (ISub.cons y hy ρ.up.tail)).dinst .one)).isub σ)
      (u := (Tm.transp ((Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))).dsubst skipI) ψ.shift u).isub σ.up)
      (a := (Tm.transp (Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))) ψ a).isub σ) (φ := χ.subst σ.τ) hσ r hr0 hh
    rw [tHc_tube_pt _ _ _ σ r hr0] at htp
    have hU1 := RE2.conv hW (conv01 σ) (hU k' σ r hr0 hh)
    have hst := stable_transpFace hW (ent_one_subst hψ σ.τ) htp
    exact RE2.expandL hW (RT2.refl' hW (RE2.tyCode hW (hU k' σ r hr0 hh)) (conv01 σ)) htp (RE2.typed hU1).1 hst hU1
  have tS : TubeD S k1 (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one) χ
      (.transp ((Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))).dsubst skipI) ψ.shift u)
      (.transp ((Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))).dsubst skipI) ψ.shift u) := by
    intro k' σ r hr0 hh
    have h := htube k' σ r hr0 hh
    have hT1 := RT2.refl' hW (RE2.tyCode hW (hU k' σ r hr0 hh)) (conv01 σ)
    exact RE2.trans hW hT1 h (RE2.symm hW hT1 h)
  have tS' : TubeD S k1 (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one) χ u u :=
    fun k' σ r hr0 hh => RE2.conv hW (conv01 σ) (hU k' σ r hr0 hh)
  obtain ⟨_, ⟨-, -, -, hta, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW htH) rfl
  have hst := stable_transpFace hW hψ (minimal_to_spec hta)
  have hA1 := RE2.conv hW conv01' hA
  have haa := RE2.expandL hW (RT2.refl' hW (RE2.tyCode hW hA) conv01') (minimal_to_spec hta) (RE2.typed hA1).1 hst hA1
  have eE := lineP_dinst hW hD hp hP hArgK hRL ρ y hy .one trivial
  rw [eE] at htH htube tS tS' haa hWty1 heqHW ⊢
  exact hcomp_relD hW hD hH hP hPP1 _ htH hWty1 heqHW (ent_refl _) (ent_refl _) htube tS tS' haa

/-- The data of the transport of a constructor normal form along a line, with itself. -/
theorem tc_node (hyp : HITHyp2 S) {k1 : ℕ} (ρ : ISub k1 K) (y : I) (hy : y.Scoped (k1 + 1))
    (h0 : I.Eq (y.subst (ISub.cons .zero trivial (ISub.id k1)).τ) .zero) {ψ : I} (hψs : ψ.Scoped k1)
    (LC : LineConst S k1 ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)) ψ)
    {c : ℕ} {C : Ctor} {q : Tm} {Z : List Tm} {rs : List I} (hC : D.ctors[c]? = some C)
    (hZl : Z.length = C.args.length)
    (hty : HasTy S k1 .one [] (.transp ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)) ψ (.con d c q (Tm.ofList Z) rs))
      (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one))
    (hZ : ∀ i (hi : i < C.args.length), RE2 S k1 ((C.argTy d D.params.length i).substList
      ((Z.take i).reverse ++ ((P.isub (ISub.cons y hy ρ.up.tail)).dinst .zero).toList.reverse))
      (Z.getD i .abort) (Z.getD i .abort))
    (hrec : ∀ j (hj : j < Z.length), C.isRec j = true → TM1s S d K P k1 ρ.hom (.data d ((P.dinst .zero).isub ρ)) Z[j]) :
    TC S k1 d D (P.isub (ISub.cons y hy ρ.up.tail)) (P.isub (ISub.cons y hy ρ.up.tail)) ψ ψ c C q q Z Z rs rs := by
  have hRL' := Rob.line hRL ρ y y hy hy (I_eq_refl _)
  refine ⟨hW, hD, hp, hC, HasTy.isubS hW hP _, hRL', hRL', argK_restr hArgK _, hψs, ent_refl _, ent_refl _, LC, hty,
    hty, EqTm.refl hty, hZ, fun i hi hri k3 τ z z' hz hz' hEz hz0 => ?_,
    conR_hit hW hD hH hyp hC (HasTy.isubS hW hP _) hRL' (forall2_ieq_refl _)⟩
  · have h := hrec i (by omega) hri ρ rfl rfl k3 τ _ _
      (I.scoped_subst hy (ISub.cons z hz τ.up.tail).sc) (I.scoped_subst hy (ISub.cons z' hz' τ.up.tail).sc)
      (ieq_subst_cons (I_eq_refl y) hEz hz hz' τ.up.tail) (ieq_zero_comp hy h0 hz hz0 τ)
    rw [getD_eq_get' (show i < Z.length by omega)]
    show KanT2At S k3 (Tm.data d ((P.isub _).isub _)) (Tm.data d ((P.isub _).isub _)) _ _
    rw [Tm.isub_isub, Tm.isub_isub, line_comp, line_comp, ISub.comp_up_tail]
    exact h

end face

end

end Model.Whnf
