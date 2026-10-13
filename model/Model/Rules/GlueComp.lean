import Model.Rules.GlueLemmas

/-!
# The computation rule `hcompGlue`
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

/-- The Glue data of a Glue type at a point, from the typing of its components. -/
theorem glueOK_at {A T e : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V}
    (hT : FaceNat S T φ m ρ γ) (heN : FaceNat S e φ m ρ γ) (hAty : TyOK S A m ρ γ) (hAnat : Natural S A m ρ γ)
    (he : ∀ k (f : Hom k m), (Cof.restr (ival ρ φ).face f).holds →
      sem S e k (ρ.restr f) (TEnv.restr γ f) ∈ El (sem S (Tm.equiv T A) k (ρ.restr f) (TEnv.restr γ f)) (Hom.id k) ∧
      TyOK S (Tm.equiv T A) k (ρ.restr f) (TEnv.restr γ f)) :
    GlueOK (sem S A m ρ γ) (ival ρ φ).face (partialKV m (ival ρ φ).face (faceVals S T ρ γ))
      (partialKV m (ival ρ φ).face (faceVals S e ρ γ)) := by
  have hnat : ∀ k (f : Hom k m), (Cof.restr (ival ρ φ).face f).holds →
      sem S (Tm.equiv T A) k (ρ.restr f) (TEnv.restr γ f) =
        equivCode k (faceVals S T ρ γ k f) (res f (sem S A m ρ γ)) := by
    intro k f hf
    have hhf : (ival (ρ.restr f) φ).holds := (holds_face_restr_iff f).1 hf
    rw [sem_equiv ((hT.restr f).natural_of_holds (γ := TEnv.restr γ f) (fun x => isKV_res _ _) hhf)
      (hAnat.restr f), hAnat k f]; rfl
  refine ⟨hAty.fib, isCof_ival_face ρ φ, partialKV_self _ _, partialKV_self _ _, fun k f hf => ?_, hT.coh,
    fun k f hf => ?_, heN.coh⟩
  · have := (he k f hf).2
    unfold TyOK at this; rw [hnat k f hf] at this
    rw [dat_partialKV, if_pos hf]
    have hkv := hT.kv k f hf
    rw [dat_partialKV, if_pos hf] at hkv
    exact (this.equiv_dom hkv).fib
  · have := (he k f hf).1
    rw [hnat k f hf] at this
    rw [dat_partialKV, if_pos hf, dat_partialKV, if_pos hf]; exact this

section hcompGlue

variable {A T e u u0 : Tm} {φ ψ : I} {ρ : IEnv m} {γ : ℕ → V}

/-- The `hcomp` in `T` of the contractum, at a point of the face `φ`. -/
theorem hcT_cond (hc : HcompCond S (.glue A φ T e) ψ u u0 m ρ γ) (hT : FaceNat S T φ m ρ γ)
    (heN : FaceNat S e φ m ρ γ) {f : Hom k m} (hf : (Cof.restr (ival ρ φ).face f).holds) :
    HcompCond S T ψ u u0 k (ρ.restr f) (TEnv.restr γ f) := by
  have hc' := hc.restr f
  have hhf : (ival (ρ.restr f) φ).holds := (holds_face_restr_iff f).1 hf
  have eG := sem_glue_holds (A := A) (γ := TEnv.restr γ f) (fun x => isKV_res _ _) hhf (hT.restr f) (heN.restr f)
    ((hT.restr f).kv_of_holds (γ := TEnv.restr γ f) (fun x => isKV_res _ _) hhf)
  obtain ⟨h1, h2, h3, -, h5⟩ := hc'
  rw [eG] at h1 h2 h3
  exact ⟨h1, h2, h3, (hT.restr f).natural_of_holds (γ := TEnv.restr γ f) (fun x => isKV_res _ _) hhf, h5⟩

/-- The system of the `A`-composition in `hcompGlue` agrees with the model's tube on its face. -/
theorem hcompGlue_tube (hc : HcompCond S (.glue A φ T e) ψ u u0 m ρ γ) (hT : FaceNat S T φ m ρ γ)
    (heN : FaceNat S e φ m ρ γ) (n : ℕ) (h : Hom n m) (r : DM n)
    (hh : ((Cof.or (ival ρ ψ).face (ival ρ φ).face).restr h).holds) :
    tubeV S (.split ψ.shift (.unglue φ.shift e.dshift u) φ.shift (.app (.fst e.dshift) (Tm.hfill T ψ u u0))) ρ γ
        n h r =
      glueTube m (ival ρ φ).face (partialKV m (ival ρ φ).face (faceVals S T ρ γ))
        (partialKV m (ival ρ φ).face (faceVals S e ρ γ)) (ival ρ ψ).face (tubeV S u ρ γ) (sem S u0 m ρ γ) n h r := by
  set env := (ρ.restr h).cons r
  have hψ' : (ival env ψ.shift).holds ↔ (Cof.restr (ival ρ ψ).face h).holds := by
    rw [ival_shift, IEnv.tail_cons, holds_face_restr_iff]
  have hφ' : (ival env φ.shift).holds ↔ (Cof.restr (ival ρ φ).face h).holds := by
    rw [ival_shift, IEnv.tail_cons, holds_face_restr_iff]
  have hfφ : (ival env φ.shift).face = Cof.restr (ival ρ φ).face h := by
    rw [ival_shift, IEnv.tail_cons, face_ival_restr]
  have eX : sem S (.unglue φ.shift e.dshift u) n env (TEnv.restr γ h) =
      ungAt n (Cof.restr (ival ρ φ).face h) (sem S e n (ρ.restr h) (TEnv.restr γ h)) (tubeV S u ρ γ n h r) := by
    rw [sem_unglue, hfφ, sem_dshift_cons]; rfl
  have eXG : ungAt n (Cof.restr (ival ρ φ).face h) (sem S e n (ρ.restr h) (TEnv.restr γ h)) (tubeV S u ρ γ n h r) =
      ungAt n (Cof.restr (ival ρ φ).face h) (dat (partialKV m (ival ρ φ).face (faceVals S e ρ γ)) n h)
        (tubeV S u ρ γ n h r) := by
    by_cases hf : (Cof.restr (ival ρ φ).face h).holds
    · rw [dat_partialKV, if_pos hf]; rfl
    · exact ungAt_not hf _ _ _
  have eY : (Cof.restr (ival ρ φ).face h).holds →
      sem S (.app (.fst e.dshift) (Tm.hfill T ψ u u0)) n env (TEnv.restr γ h) =
        eqFun n (sem S e n (ρ.restr h) (TEnv.restr γ h)) (res (Hom.endpt n r)
          (hfillF (sem S T n (ρ.restr h) (TEnv.restr γ h)) (Hom.id n) (Cof.restr (ival ρ ψ).face h)
            ((tubeV S u ρ γ).restr h) (res h (sem S u0 m ρ γ)))) := by
    intro hf
    have hcTh := hcT_cond hc hT heN hf
    obtain ⟨cf, hfv⟩ := hfill_cond hcTh
    have hnat : Natural S (Tm.hfill T ψ u u0) (n + 1) (ρ.restr h).ext (TEnv.restr (TEnv.restr γ h) (Hom.wk n)) :=
      cf.natural
    have henv : env = (ρ.restr h).ext.restr (Hom.endpt n r) := (IEnv.ext_restr_endpt _ _).symm
    have hγe : TEnv.restr γ h = TEnv.restr (TEnv.restr (TEnv.restr γ h) (Hom.wk n)) (Hom.endpt n r) := by
      rw [TEnv.restr_restr, Hom.wk_comp_endpt, TEnv.restr_id_of_kv (γ := TEnv.restr γ h) (fun x => isKV_res _ _)]
    have hval : sem S (Tm.hfill T ψ u u0) n env (TEnv.restr γ h) =
        res (Hom.endpt n r) (sem S (Tm.hfill T ψ u u0) (n + 1) (ρ.restr h).ext (TEnv.restr (TEnv.restr γ h) (Hom.wk n))) := by
      conv_lhs => rw [henv, hγe]
      exact hnat n _
    have hnat' : Natural S (Tm.hfill T ψ u u0) n env (TEnv.restr γ h) := by
      rw [henv, hγe]; exact hnat.restr _
    rw [sem_app_of_nat hnat', sem_fst, sem_dshift_cons, hval, hfv, face_ival_restr, tubeV_restr, hc.2.2.2.2 n h]
    rfl
  simp only [tubeV]
  unfold glueTube
  rw [Cof.or_restr, Cof.holds_or] at hh
  by_cases h1 : (Cof.restr (ival ρ ψ).face h).holds
  · have hover : (ival env φ.shift).holds →
        sem S (.unglue φ.shift e.dshift u) n env (TEnv.restr γ h) =
          sem S (.app (.fst e.dshift) (Tm.hfill T ψ u u0)) n env (TEnv.restr γ h) := by
      intro hf
      have hf' := hφ'.1 hf
      have hcTh := hcT_cond hc hT heN hf'
      rw [eX, eY hf']
      obtain ⟨hty, hTT, hb, -, -⟩ := hcTh
      have hb' : res h (sem S u0 m ρ γ) ∈ El (sem S T n (ρ.restr h) (TEnv.restr γ h)) (Hom.id n) := by
        rw [← hc.2.2.2.2 n h]; exact hb
      have hTT' : TubeOK (sem S T n (ρ.restr h) (TEnv.restr γ h)) (Hom.id n) (Cof.restr (ival ρ ψ).face h)
          ((tubeV S u ρ γ).restr h) (res h (sem S u0 m ρ γ)) := by
        rw [← face_ival_restr, ← tubeV_restr, ← hc.2.2.2.2 n h]; exact hTT
      have hψid : ((Cof.restr (ival ρ ψ).face h).restr (Hom.id n)).holds := by
        rw [((isCof_ival_face ρ ψ).restr h).restr_id]; exact h1
      have hface := hfillF_face hty.fib ((isCof_ival_face ρ ψ).restr h) hb' hTT' (Hom.id n) hψid r
      have hm := hc.2.1.mem n h r h1
      have hkv := hc.1.fib.elKV _ _ _ hm
      rw [show Hom.endpt n r = Hom.snoc (Hom.id n) r from rfl, hface, ungAt, if_pos hf', if_pos hkv]
      simp only [Tube.restr, Hom.comp_id]
    rw [sem_split (Or.inl (hψ'.2 h1)) (fun _ => hover), if_pos (hψ'.2 h1), if_pos h1, eX, eXG]
  · have hf := hh.resolve_left h1
    rw [sem_split (Or.inr (hφ'.2 hf)) (fun h => absurd (hψ'.1 h) h1), if_neg (fun h => h1 (hψ'.1 h)),
      if_neg h1, if_pos hf, eY hf, dat_partialKV, if_pos hf, dat_partialKV, if_pos hf]
    rfl

theorem sem_hcompGlue (hγ : ∀ x, IsKV m (γ x)) (hc : HcompCond S (.glue A φ T e) ψ u u0 m ρ γ)
    (hAty : TyOK S A m ρ γ) (hAnat : Natural S A m ρ γ)
    (he : ∀ k (f : Hom k m), (Cof.restr (ival ρ φ).face f).holds →
      sem S e k (ρ.restr f) (TEnv.restr γ f) ∈ El (sem S (Tm.equiv T A) k (ρ.restr f) (TEnv.restr γ f)) (Hom.id k) ∧
      TyOK S (Tm.equiv T A) k (ρ.restr f) (TEnv.restr γ f)) :
    sem S (Tm.hcompGlue A φ T e ψ u u0) m ρ γ = sem S (.hcomp (.glue A φ T e) ψ u u0) m ρ γ := by
  have hne : sem S (.glue A φ T e) m ρ γ ≠ ∅ := fun h => by
    have := hc.1.fib.kv; rw [h] at this; exact not_isKV_empty this
  obtain ⟨hT, heN⟩ := cond_of_sem_glue hne
  have hG := glueOK_at hT heN hAty hAnat he
  have hsemG := sem_glue (A := A) hT heN
  set Tp := partialKV m (ival ρ φ).face (faceVals S T ρ γ)
  set ep := partialKV m (ival ρ φ).face (faceVals S e ρ γ)
  have hu0G := hc.2.2.1
  have huG := hc.2.1
  rw [hsemG] at hu0G huG
  have hψ := isCof_ival_face ρ ψ
  set sysA := Tm.split ψ.shift (.unglue φ.shift e.dshift u) φ.shift (.app (.fst e.dshift) (Tm.hfill T ψ u u0))
  -- the base of the `A`-composition
  have hbase : sem S (.unglue φ e u0) m ρ γ =
      ungAt m (Cof.restr (ival ρ φ).face (Hom.id m)) (dat ep m (Hom.id m)) (sem S u0 m ρ γ) := by
    rw [sem_unglue, (isCof_ival_face ρ φ).restr_id]
    by_cases hf : Cof.holds (ival ρ φ).face
    · have hid : (Cof.restr (ival ρ φ).face (Hom.id m)).holds := by
        rw [(isCof_ival_face ρ φ).restr_id]; exact hf
      rw [dat_partialKV, if_pos hid, faceVals, IEnv.restr_id, TEnv.restr_id_of_kv hγ]
    · exact ungAt_not hf _ _ _
  have hcA : HcompCond S A (.or ψ φ) sysA (.unglue φ e u0) m ρ γ := by
    refine ⟨hAty, ?_, ?_, hAnat, fun k g => ?_⟩
    · rw [face_ival_or, hbase]
      exact (glueTube_ok' hG hψ hu0G huG).congr (hψ.or (isCof_ival_face ρ φ))
        fun n h r hh => (hcompGlue_tube hc hT heN n h r hh).symm
    · rw [hbase]; exact hG.ung_mem hu0G
    · rw [hbase, hG.ung_res hu0G g, Hom.id_comp, sem_unglue, hc.2.2.2.2 k g, face_ival_restr]
      by_cases hg : (Cof.restr (ival ρ φ).face g).holds
      · rw [dat_partialKV, if_pos hg]; rfl
      · exact ungAt_not hg _ _ _
  have eA : sem S (.hcomp A (.or ψ φ) sysA (.unglue φ e u0)) m ρ γ =
      hcompAt (sem S A m ρ γ) (Hom.id m) (Cof.or (ival ρ ψ).face (ival ρ φ).face)
        (glueTube m (ival ρ φ).face Tp ep (ival ρ ψ).face (tubeV S u ρ γ) (sem S u0 m ρ γ))
        (ungAt m (Cof.restr (ival ρ φ).face (Hom.id m)) (dat ep m (Hom.id m)) (sem S u0 m ρ γ)) := by
    rw [sem_hcomp hcA, face_ival_or, hbase]
    exact hcompAt_congr fun n h r hh => hcompGlue_tube hc hT heN n h r hh
  show sem S (.glueEl φ e (.hcomp T ψ u u0) (.hcomp A (.or ψ φ) sysA (.unglue φ e u0))) m ρ γ = _
  rw [sem_hcomp hc, hsemG]
  by_cases hh : (ival ρ φ).holds
  · have hhf := (holds_iff_face ρ φ).1 hh
    have hid : (Cof.restr (ival ρ φ).face (Hom.id m)).holds := by
      rw [(isCof_ival_face ρ φ).restr_id]; exact hhf
    have hcT := hcT_cond hc hT heN hid
    rw [IEnv.restr_id, TEnv.restr_id_of_kv hγ] at hcT
    have hTm : dat Tp m (Hom.id m) = sem S T m ρ γ := by
      rw [dat_partialKV, if_pos hid, faceVals, IEnv.restr_id, TEnv.restr_id_of_kv hγ]
    have hem : dat ep m (Hom.id m) = sem S e m ρ γ := by
      rw [dat_partialKV, if_pos hid, faceVals, IEnv.restr_id, TEnv.restr_id_of_kv hγ]
    have hres_kv := hG.fibA.elKV _ _ _ (hG.fibA.hcMem _ _ _ _ _
        (hψ.or (isCof_ival_face ρ φ)) (hG.ung_mem hu0G) (glueTube_ok' hG hψ hu0G huG))
    have heq := glueHc_eqFun' hG hψ hu0G huG hid
    have hur : (tubeV S u ρ γ).restr (Hom.id m) = tubeV S u ρ γ := by
      funext n h r; simp only [Tube.restr, Hom.id_comp]
    rw [hur, hψ.restr_id, res_id (hG.elKV hu0G), res_id hres_kv, hTm] at heq
    have hcheck : eqFun m (sem S e m ρ γ) (sem S (.hcomp T ψ u u0) m ρ γ) =
        sem S (.hcomp A (.or ψ φ) sysA (.unglue φ e u0)) m ρ γ := by
      rw [sem_hcomp hcT, eA, ← hem]; exact heq
    rw [hcompAt_glueC_holds hid, sem_glueEl_holds hh hcheck, sem_hcomp hcT, hTm]
  · have hhf : ¬ Cof.holds (ival ρ φ).face := fun h => hh ((holds_iff_face ρ φ).2 h)
    have hres_kv := hG.fibA.elKV _ _ _ (hG.fibA.hcMem _ _ _ _ _
        (hψ.or (isCof_ival_face ρ φ)) (hG.ung_mem hu0G) (glueTube_ok' hG hψ hu0G huG))
    rw [hcompAt_glueC_id hG hhf hu0G huG, glueHcF_eq, sem_glueEl_not hh (by rw [eA]; exact hres_kv), eA]
    congr 1
    · unfold glueTp partialKV; congr 1; funext k f; split
      · rename_i hf
        dsimp only
        rw [show dat Tp k f = sem S T k (ρ.restr f) (TEnv.restr γ f) by
          simp only [Tp, dat_partialKV, if_pos hf]; rfl]
        rw [faceVals, sem_hcomp (hcT_cond hc hT heN hf), face_ival_restr, tubeV_restr, hc.2.2.2.2 k f]
        apply hcompAt_congr
        intro n g r hg
        simp only [Tube.restr]
        rw [Cof.restr_restr] at hg
        rw [tube_canon_eq hg]
      · rfl
    · rw [ungAt, if_neg (by rw [(isCof_ival_face ρ φ).restr_id]; exact hhf)]
      apply hcompAt_congr
      intro n h r hh'
      simp only [glueTube]
      split
      · rw [tube_canon_eq ‹_›]
      · split
        · rw [hfillF_congr (u' := (Tube.canon (ival ρ ψ).face (tubeV S u ρ γ)).restr h)]
          intro n' g r' hg
          simp only [Tube.restr]
          rw [Cof.restr_restr] at hg
          rw [tube_canon_eq hg]
        · rfl

end hcompGlue


end

end Model
