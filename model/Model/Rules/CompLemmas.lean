import Model.Rules.KanLemmas

/-!
# The Kan computation rules

For each computation rule `op (F …) … ≡ contractum`, the code's operation is the semantic reading
of the contractum; here we compute the denotation of the contractum at a point where the redex
is defined and show that it agrees.
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

theorem TubeOK.congr {c : V} {f : Hom k m} {φ : Cof k} {u u' : Tube k} {u0 : V} (hφ : φ.IsCof)
    (h : ∀ n (g : Hom n k) r, (φ.restr g).holds → u n g r = u' n g r) (hu : TubeOK c f φ u u0) :
    TubeOK c f φ u' u0 where
  mem n g r hg := h n g r hg ▸ hu.mem n g r hg
  coh n g r hg n' g' := by
    have hg' : (φ.restr (g.comp g')).holds := by
      rw [← Cof.restr_restr]; exact Cof.IsCof.holds_restr (hφ.restr g) hg g'
    rw [← h n g r hg, ← h n' _ _ hg']; exact hu.coh n g r hg n' g'
  base n g hg := by rw [← h n g _ hg]; exact hu.base n g hg

theorem sem_app_shift_var0 (t : Tm) (ρ : IEnv m) (γ : ℕ → V) (a : V) :
    sem S (.app t.shift (.var 0)) m ρ (TEnv.cons γ a) = appV m (sem S t m ρ γ) a := by
  rw [sem_app_of_nat (natural_var S 0 _ _), sem_shift, sem_var, TEnv.cons_zero]

theorem below_piC_famAt (A B : V) (hB : IsKV m B) (g : Hom n m) (a : V)
    (ha : ∃ y, ZFSet.pair a y ∈ dat B n g) : Below (apZ (dat B n g) a) (piC m A B) := by
  have h1 : Below (apZ (dat B n g) a) B := (below_apZ ha).trans (below_dat hB _)
  have h2 : Below (res (Hom.id m) B) (piC m A B) := by
    unfold piC
    refine Below.trans ?_ (below_dat_mkKV _ (Hom.id m))
    simp only [piDatum, quad, tagZ]
    exact ((below_pair_right _ _).trans (below_pair_right _ _)).trans (below_pair_left _ _)
  rw [res_id hB] at h2
  exact h1.trans h2

/-- The Π data of a good Π-code at a point. -/
theorem TyOK.pi_data {A B : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : TyOK S (.pi A B) m ρ γ) :
    let Av := sem S A m ρ γ
    let Bf := famV m Av fun k f a => sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)
    IsKV m Av ∧ sem S (.pi A B) m ρ γ = piC m Av Bf ∧ Fib Av m ∧ FamOK Av Bf m ∧
      ∃ l ≤ maxLevel, ∀ n (g : Hom n m), ∀ a ∈ El Av g,
        apZ (dat Bf n g) a ∈ Vt l ∧ WF l n (apZ (dat Bf n g) a) := by
  intro Av Bf
  obtain ⟨hAkv, l, hl, hV, hWF⟩ := h.pi_at
  rw [sem_pi hAkv] at hV hWF
  obtain ⟨hAWF, hfam, hcoh⟩ := WF.pi_inv hAkv (isKV_famV _ _) hWF
  refine ⟨hAkv, sem_pi hAkv, hAWF.fib, ⟨isKV_famV _ _, fun k f => ?_, fun k f a ha => (hfam k f a ha).fib,
    hcoh⟩, l, hl, fun n g a ha => ⟨?_, hfam n g a ha⟩⟩
  · rw [dat_famV]
    exact fnZ_congr fun a ha => (apZ_fnZ (fun a => sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)) ha).symm
  · exact Vt_below (below_piC_famAt _ _ (isKV_famV _ _) _ _ ⟨_, by rw [dat_famV]; exact mem_fnZ.2 ⟨_, ha, rfl⟩⟩) hV

/-! ### hcompPi -/

theorem sem_hcompPi {A B u u0 : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V}
    (hc : HcompCond S (.pi A B) φ u u0 m ρ γ) :
    sem S (Tm.hcompPi A B φ u u0) m ρ γ = sem S (.hcomp (.pi A B) φ u u0) m ρ γ := by
  obtain ⟨hAkv, hsem, hAfib, hfam, l, hl, hfamW⟩ := (show TyOK S (.pi A B) m ρ γ from hc.1).pi_data
  have hu0 := hc.2.2.1
  have hu := hc.2.1
  have hu0nat := hc.2.2.2.2
  rw [hsem] at hu0 hu
  rw [sem_hcomp hc, hsem, hcompAt_piC hAfib hfam hu0 hu]
  simp only [Tm.hcompPi]
  rw [sem_lam]
  unfold hcompPiF lamV
  congr 1; funext n g
  dsimp only
  rw [El_res, Hom.id_comp]
  apply fnZ_congr; intro v hv
  simp only [dat_res, Hom.id_comp]
  have hv' : v ∈ El (res (Hom.id m) (sem S A m ρ γ)) g := by rw [El_res, Hom.id_comp]; exact hv
  obtain ⟨hC, hb, hut⟩ := hcompPi_inner hAfib hfam (isCof_ival_face ρ φ) hu0 hu g hv'
  simp only [dat_res, Hom.id_comp] at hC hb hut
  set Bf := famV m (sem S A m ρ γ) fun k f a => sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)
  have eB : sem S B n (ρ.restr g) (TEnv.cons (TEnv.restr γ g) v) = apZ (dat Bf n g) v :=
    (apZ_dat_famV (sem S A m ρ γ) (fun k f a => sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)) g hv).symm
  have eb : sem S (.app u0.shift (.var 0)) n (ρ.restr g) (TEnv.cons (TEnv.restr γ g) v) =
      appV n (res g (sem S u0 m ρ γ)) v := by
    rw [sem_app_shift_var0, hu0nat n g]
  have et : ∀ n' (g' : Hom n' n) r, (Cof.restr (Cof.restr (ival ρ φ).face g) g').holds →
      tubeV S (.app u.shift (.var 0)) (ρ.restr g) (TEnv.cons (TEnv.restr γ g) v) n' g' r =
      appV n' (Tube.canon (ival ρ φ).face (tubeV S u ρ γ) n' (g.comp g') r) (res g' v) := by
    intro n' g' r hh
    rw [Cof.restr_restr] at hh
    simp only [tubeV]
    rw [TEnv.restr_cons, sem_app_shift_var0, tube_canon_eq hh, IEnv.restr_restr, TEnv.restr_restr]
    rfl
  have hface : (ival (ρ.restr g) φ).face = Cof.restr (ival ρ φ).face g := by rw [ival.restr, DM.face_restr]
  have hu0' : res g (sem S u0 m ρ γ) ∈ piElSet n (res g (sem S A m ρ γ)) (res g Bf) := by
    rw [El_piC] at hu0; have := res_mem_piElSet hu0 g
    rwa [res_id hAkv, res_id (isKV_famV _ _)] at this
  have hvid : v ∈ El (res g (sem S A m ρ γ)) (Hom.id n) := by rw [El_res, Hom.comp_id]; exact hv
  have hcond : HcompCond S B φ (.app u.shift (.var 0)) (.app u0.shift (.var 0)) n (ρ.restr g)
      (TEnv.cons (TEnv.restr γ g) v) := by
    refine ⟨?_, ?_, ?_, fun k h => ?_, fun k h => ?_⟩
    · rw [eB]; exact ⟨l, hl, Or.inl ⟨(hfamW n g v hv).2, (hfamW n g v hv).1⟩⟩
    · rw [eB, eb, hface]
      exact (hut.congr ((isCof_ival_face ρ φ).restr g) fun n' g' r hh => (et n' g' r hh).symm)
    · rw [eB, eb]; exact hb
    · have hv2 : res h v ∈ El (sem S A m ρ γ) (g.comp h) := hAfib.elRes _ _ v hv _ h
      rw [IEnv.restr_restr, TEnv.restr_cons, TEnv.restr_restr, eB, hfam.coh n g v hv k h]
      exact (apZ_dat_famV (sem S A m ρ γ) (fun k f a => sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a))
        (g.comp h) hv2).symm
    · rw [IEnv.restr_restr, TEnv.restr_cons, TEnv.restr_restr, sem_app_shift_var0, eb, hu0nat k (g.comp h),
        res_appV hu0' hvid h, res_res]
  rw [sem_hcomp hcond, eB, eb, hface]
  exact hcompAt_congr et

theorem sem_dsubst (t : Tm) (τ : ℕ → I) (ρ : IEnv m) (γ : ℕ → V) :
    sem S (t.dsubst τ) m ρ γ = sem S t m (fun i => ival ρ (τ i)) γ := by
  rw [Tm.dsubst, sem_subst S t m ρ γ _ _ (fun x => natural_var S x ρ γ)]; rfl

/-- A point of the form `⟦A⟧(ρ.ext, γ.wk)` of a natural line is the same as the line. -/
theorem papp_dshift_var0_generic {p : Tm} {ρ : IEnv m} {γ : ℕ → V} {P : V} (hnat : Natural S p m ρ γ)
    (hP : sem S p m ρ γ = pathOfLine m P) (hPkv : IsKV (m + 1) P) :
    sem S (.papp p.dshift (.var 0)) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) = P ∧
      Natural S (.papp p.dshift (.var 0)) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) := by
  have hb := sem_eta_body hnat hP
  have h2 := hb (m + 1) (Hom.id (m + 1))
  rw [IEnv.restr_id, TEnv.restr_id_of_kv (γ := TEnv.restr γ (Hom.wk m)) (fun x => isKV_res _ _),
    res_id hPkv] at h2
  exact ⟨h2, fun k g => by rw [hb k g, h2]⟩

/-! ### hcompIPi -/

theorem sem_hcompIPi {A u u0 : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V}
    (hc : HcompCond S (.ipi A) φ u u0 m ρ γ) :
    sem S (Tm.hcompIPi A φ u u0) m ρ γ = sem S (.hcomp (.ipi A) φ u u0) m ρ γ := by
  obtain ⟨hN, hL, hsem, l, hl, hV, hW⟩ := (show TyOK S (.ipi A) m ρ γ from hc.1).ipi_at
  have hLfib := hW.fib
  have hp0 := hc.2.2.1
  have hu := hc.2.1
  have hu0nat := hc.2.2.2.2
  rw [hsem] at hp0 hu
  have hφ := isCof_ival_face ρ φ
  obtain ⟨hp0eq, hline⟩ := ipi_line hLfib hp0
  rw [Hom.lift_id] at hline
  have hP := papp_dshift_var0_generic hu0nat hp0eq (hLfib.elKV _ _ _ hline)
  have hface : (ival ρ.ext φ.shift).face = Cof.restr (ival ρ φ).face (Hom.wk m) := by
    rw [ival_shift]; exact face_ival_restr ρ φ (Hom.wk m)
  have et : ∀ n (h : Hom n (m + 1)) r, (Cof.restr (Cof.restr (ival ρ φ).face (Hom.wk m)) h).holds →
      tubeV S (.papp (u.dsubst fun | 0 => .var 0 | n + 1 => .var (n + 2)) (.var 1)) ρ.ext
        (TEnv.restr γ (Hom.wk m)) n h r = ipiHTube (Tube.canon (ival ρ φ).face (tubeV S u ρ γ)) n h r := by
    intro n h r hh
    rw [Cof.restr_restr] at hh
    simp only [tubeV, ipiHTube, sem_papp, sem_dsubst, tube_canon_eq hh, TEnv.restr_restr]
    congr 2
    funext i; cases i with
    | zero => rfl
    | succ i => simp [IEnv.cons, IEnv.restr, IEnv.ext, DM.restr_restr]
  have hcb : HcompCond S A φ.shift (.papp (u.dsubst fun | 0 => .var 0 | n + 1 => .var (n + 2)) (.var 1))
      (.papp u0.dshift (.var 0)) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) := by
    refine ⟨⟨l, hl, Or.inl ⟨hW, hV⟩⟩, ?_, ?_, hN, hP.2⟩
    · rw [hP.1, hface]
      have := ipiHTube_ok hLfib hφ hp0 hu
      rw [Hom.lift_id] at this
      exact this.congr (hφ.restr _) fun n h r hh => (et n h r hh).symm
    · rw [hP.1]; exact hline
  rw [sem_hcomp hc, hsem, hcompAt_ipiC hp0 hu, hcompIPiF_eq, Hom.lift_id]
  have e1 : sem S (Tm.hcompIPi A φ u u0) m ρ γ = pathOfLine m (lineV S (.hcomp A φ.shift
      (.papp (u.dsubst fun | 0 => .var 0 | n + 1 => .var (n + 2)) (.var 1)) (.papp u0.dshift (.var 0))) m ρ γ) :=
    sem_plam hcb.natural
  rw [e1]
  unfold lineV
  rw [sem_hcomp hcb, hP.1, hface]
  congr 1
  exact hcompAt_congr et

end

end Model
