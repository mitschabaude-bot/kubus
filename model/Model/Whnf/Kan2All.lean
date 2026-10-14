import Model.Whnf.Kan2UnivH
import Model.Whnf.Kan2GlueTM
import Model.Whnf.Kan2DataCode

/-!
# The binary Kan operations at all codes

`kanP2_tyCode`: composition and transport relate related data at every pair of types related at a
restriction of a type code, by induction on codes (`tyCode_ind`), one case per type former. The
components of a normal form are related at restrictions of the components of the code
(`Comp2_piC`, …), so the induction hypotheses at the component codes give the Kan properties the
per-former lemmas need (`kanH2_of_code`, `khRel_of_code`). Composition in a universe of level `l`
uses transport along lines of level `l` only, which the induction hypothesis covers.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

theorem kanH2_of_code {Y Y' : Tm} {X : V} {m : ℕ} {g : Hom k m} (hK : KanP2 S m X) (hne : X ≠ ∅)
    (hsem : semK S k Y = res g X) (h : RT2 S k Y Y') : KanH2 S k Y Y' :=
  hK.1 k g Y Y' ((Comp2_ty_iff hne hsem).2 h)

theorem kanT2_of_code {Y Y' : Tm} {X : V} {m : ℕ} {g : Hom (k + 1) m} (hK : KanP2 S m X) (hne : X ≠ ∅)
    (hsem : semK S (k + 1) Y = res g X) (h : RT2 S (k + 1) Y Y') : KanT2 S k Y Y' :=
  hK.2 k g Y Y' ((Comp2_ty_iff hne hsem).2 h)

variable (hW : WfSig S)
include hW

/-- The Kan properties of all types related to restrictions of a type whose code is a restriction of a
Kan code. -/
theorem khRel_of_code {Y : Tm} {X : V} {m : ℕ} {g : Hom k m} (hK : KanP2 S m X) (hne : X ≠ ∅) (hY : IsTyK S k Y)
    (hsem : semK S k Y = res g X) : KHRel S k Y ∧ KTRel S k Y := by
  have e : ∀ {k'} (σ : ISub k' k) {Z : Tm}, RT2 S k' (Y.isub σ) Z → semK S k' Z = res (g.comp σ.hom) X :=
    fun σ Z h => by rw [RT2.semK_eq hW h, semK_isubTy hW hY σ, hsem, res_res]
  exact ⟨fun k' σ Z Z' h1 h2 => kanH2_of_code hK hne (e σ h1) h2,
    fun k' Θ Z Z' h1 h2 => kanT2_of_code hK hne (e Θ h1) h2⟩

/-! ### The empty type -/

theorem kanP2_emptyC {m : ℕ} : KanP2 S m (emptyC m) := by
  refine ⟨fun k f A A' hT => ?_, fun k f A A' hT => ?_⟩
  · intro φ φ' u u' a0 a0' hty hty' heq hteq h12 h21 htube ha0 hbd hbd'
    have hb := Comp2_ty_base hT
    unfold RE2 at ha0
    rw [hb.2.2.2.1, ← Comp2_eq_res hb.1, Comp2_emptyC] at ha0
    exact ha0.elim
  · intro hLR φ φ' a0 a0' hC hty hty' heq h12 h21 ha0
    have hb := Comp2_ty_base hT
    obtain ⟨l0, ⟨hTl, -, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
    have hT0 := HasTy.isubS hW (minimal_to_spec hTl) (ISub.cons .zero trivial (ISub.id k))
    rw [isub_cons_id_of_closed (closed_ty hTl)] at hT0
    have hs := semK_isubTy hW hb.2.1 (ISub.cons .zero trivial (ISub.id k))
    rw [isub_cons_id_of_closed (closed_ty hTl), hb.2.2.2.1, res_res] at hs
    unfold RE2 at ha0
    rw [hs, ← Comp2_eq_res hb.1, Comp2_emptyC] at ha0
    exact ha0.elim

/-! ### Universes -/

theorem kanP2_univC {m l : ℕ} (ih : ∀ m' X, WF l m' X → KanP2 S m' X) : KanP2 S m (univC m l) := by
  have hKT : KTAt S l := fun k X X' hXX hX => by
    have hm := mem_of_ty hW hX
    rw [show semK S (k + 1) (.univ l) = univC (k + 1) l from rfl, El_univC] at hm
    have hne := semK_ne hW hX
    exact kanT2_of_code (g := Hom.id (k + 1)) (ih (k + 1) _ (ZFSet.mem_sep.1 hm).2) hne
      (res_id (kv_semK_of_univ hW hX)).symm hXX
  refine ⟨fun k f A A' hT => ?_, fun k f A A' hT => ?_⟩
  · have hTT := Comp2_ty_RT2 hT
    have hb := Comp2_ty_base hT
    rw [Comp2_univC] at hT
    have hR := hT.2 k (ISub.id k)
    rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at hR
    exact kanH2_univ hW hKT hTT hR.1
  · have hTT := Comp2_ty_RT2 hT
    have hb := Comp2_ty_base hT
    rw [Comp2_univC] at hT
    have hR := hT.2 (k + 1) (ISub.id (k + 1))
    rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at hR
    exact kanT2_univ hW hTT hR.1


/-! ### Types whose code is a restriction of a Kan code -/

/-- `Y` is a type whose code is a restriction of a code with the binary Kan properties. -/
def KCode (S : Sig) (k : ℕ) (Y : Tm) : Prop :=
  ∃ (m : ℕ) (X : V) (g : Hom k m), KanP2 S m X ∧ X ≠ ∅ ∧ IsTyK S k Y ∧ semK S k Y = res g X

theorem KCode.isub {Y : Tm} (h : KCode S k Y) (σ : ISub k' k) : KCode S k' (Y.isub σ) := by
  obtain ⟨m, X, g, hK, hne, hY, hsem⟩ := h
  exact ⟨m, X, g.comp σ.hom, hK, hne, hY.isub hW σ, by rw [semK_isubTy hW hY σ, hsem, res_res]⟩

omit hW in
theorem KCode.kanH {Y Y' : Tm} (h : KCode S k Y) (hY : RT2 S k Y Y') : KanH2 S k Y Y' := by
  obtain ⟨m, X, g, hK, hne, -, hsem⟩ := h
  exact kanH2_of_code hK hne hsem hY

omit hW in
theorem KCode.kanT {Y Y' : Tm} (h : KCode S (k + 1) Y) (hY : RT2 S (k + 1) Y Y') : KanT2 S k Y Y' := by
  obtain ⟨m, X, g, hK, hne, -, hsem⟩ := h
  exact kanT2_of_code hK hne hsem hY

theorem KCode.relH {Y X X' : Tm} (h : KCode S k Y) (h1 : RT2 S k Y X) (h2 : RT2 S k X X') : KanH2 S k X X' := by
  obtain ⟨m, Xc, g, hK, hne, -, hsem⟩ := h
  exact kanH2_of_code hK hne (by rw [RT2.semK_eq hW h1, hsem]) h2

theorem KCode.relT {Y X X' : Tm} (h : KCode S (k + 1) Y) (h1 : RT2 S (k + 1) Y X) (h2 : RT2 S (k + 1) X X') :
    KanT2 S k X X' := by
  obtain ⟨m, Xc, g, hK, hne, -, hsem⟩ := h
  exact kanT2_of_code hK hne (by rw [RT2.semK_eq hW h1, hsem]) h2

theorem KCode.hrel {Y : Tm} (h : KCode S k Y) : KHRel S k Y ∧ KTRel S k Y := by
  obtain ⟨m, X, g, hK, hne, hY, hsem⟩ := h
  exact khRel_of_code hW hK hne hY hsem

omit hW in
theorem KCode.of_comp {m : ℕ} {X : V} {g : Hom k m} {Y Y' : Tm} (hK : KanP2 S m X) (h : (Comp2 S X m k g).ty Y Y') :
    KCode S k Y :=
  let hb := Comp2_ty_base h
  ⟨m, X, g, hK, hb.1, hb.2.1, hb.2.2.2.1⟩

/-! ### Π- and Σ-types -/

/-- The components of the normal forms of a type related at a restriction of a `Π`/`Σ` code. -/
theorem famComp {m : ℕ} {A B : V} (hne : A ≠ ∅)
    (ihA : KanP2 S m A) (ihB : ∀ k (f : Hom k m), ∀ a ∈ El A f, KanP2 S k (apZ (dat B k f) a))
    {f : Hom k m} {T T' : Tm} {F : Tm → Tm → Tm} (hF : ∀ a b a' b', F a b = F a' b' → a = a' ∧ b = b')
    (h : ∀ k' (σ : ISub k' k), ∃ A1 B1 A1' B1', RedT S k' (T.isub σ) (F A1 B1) ∧ RedT S k' (T'.isub σ) (F A1' B1') ∧
      (Comp2 S A m k' (f.comp σ.hom)).ty A1 A1' ∧ ∀ a a', (Comp2 S A m k' (f.comp σ.hom)).el A1 a a' →
        (Comp2 S (apZ (dat B k' (f.comp σ.hom)) (semK S k' a)) k' k' (Hom.id k')).ty (B1.inst a) (B1'.inst a'))
    {k' : ℕ} (σ : ISub k' k) {A2 B2 : Tm} (hR : RedT S k' (T.isub σ) (F A2 B2)) :
    KCode S k' A2 ∧ ∀ b, RE2 S k' A2 b b → KCode S k' (B2.inst b) := by
  obtain ⟨A3, B3, A3', B3', hR3, -, hA3, hB3⟩ := h k' σ
  obtain ⟨rfl, rfl⟩ := hF _ _ _ _ (RedW.unique hR3.1 hR.1)
  have hb := Comp2_ty_base hA3
  refine ⟨KCode.of_comp ihA hA3, fun b hbb => ?_⟩
  have hb' : (Comp2 S A m k' (f.comp σ.hom)).el A3 b b := (Comp2_el_iff hne hb.2.2.2.1).2 hbb
  have hmem : semK S k' b ∈ El A (f.comp σ.hom) := by
    have := (Comp2_el hb').2; rwa [El_res, Hom.comp_id] at this
  exact KCode.of_comp (ihB k' _ _ hmem) (hB3 b b hb')

theorem kanP2_piC {l m : ℕ} {A B : V} (hA : WF l m A)
    (ihA : KanP2 S m A) (ihB : ∀ k (f : Hom k m), ∀ a ∈ El A f, KanP2 S k (apZ (dat B k f) a)) :
    KanP2 S m (piC m A B) := by
  have hne : A ≠ ∅ := IsKV.ne_empty hA.fib.kv
  have hF : ∀ a b a' b', Tm.pi a b = Tm.pi a' b' → a = a' ∧ b = b' := fun _ _ _ _ h => by
    injection h with h1 h2; exact ⟨h1, h2⟩
  refine ⟨fun k f T T' hT => ?_, fun k f T T' hT => ?_⟩
  · have hTT := Comp2_ty_RT2 hT
    have hb := Comp2_ty_base hT
    rw [Comp2_piC A B hne] at hT
    obtain ⟨A1, B1, -, -, hR, -⟩ := hT.2.1 k (ISub.id k)
    rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at hR
    obtain ⟨l1, hpi⟩ := piW_typed hW hb.2.1 hR
    have hXT : TyCode k (semK S k T) := by rw [semK_tyEq hW hR.2]; exact tyCode_of_univ hW hpi
    refine kanH2_pi hW (PiStr_of hW hTT hR hpi) (fun k' ρ A2 B2 hR2 b hbb k'' ρ' X' hX' => ?_)
      (fun t t' hE happ => RE2_piW_intro hW (RT2.refl hW hXT hTT) hR hpi hE happ)
    exact (((famComp hW hne ihA ihB hF hT.2.1 ρ hR2).2 b hbb).isub hW ρ').kanH hX'
  · have hTT := Comp2_ty_RT2 hT
    have hb := Comp2_ty_base hT
    rw [Comp2_piC A B hne] at hT
    obtain ⟨A1, B1, -, -, hR, -⟩ := hT.2.1 (k + 1) (ISub.id (k + 1))
    rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at hR
    obtain ⟨l1, hpi⟩ := piW_typed hW hb.2.1 hR
    refine kanT2_pi hW hTT hR hpi (fun k1 ρ A2 B2 hR2 k2 ρ' X' hX' => ?_)
      (fun k1 ρ A2 B2 hR2 b hbb k2 ρ' X' hX' => ?_)
    · exact (((famComp hW hne ihA ihB hF hT.2.1 ρ hR2).1).isub hW ρ').kanT hX'
    · exact (((famComp hW hne ihA ihB hF hT.2.1 ρ hR2).2 b hbb).isub hW ρ').kanT hX'


theorem kanP2_sigmaC {l m : ℕ} {A B : V} (hA : WF l m A)
    (ihA : KanP2 S m A) (ihB : ∀ k (f : Hom k m), ∀ a ∈ El A f, KanP2 S k (apZ (dat B k f) a)) :
    KanP2 S m (sigmaC m A B) := by
  have hne : A ≠ ∅ := IsKV.ne_empty hA.fib.kv
  have hF : ∀ a b a' b', Tm.sigma a b = Tm.sigma a' b' → a = a' ∧ b = b' := fun _ _ _ _ h => by
    injection h with h1 h2; exact ⟨h1, h2⟩
  refine ⟨fun k f T T' hT => ?_, fun k f T T' hT => ?_⟩
  · have hTT := Comp2_ty_RT2 hT
    have hb := Comp2_ty_base hT
    rw [Comp2_sigmaC A B hne] at hT
    obtain ⟨A1, B1, -, -, hR, -⟩ := hT.2.1 k (ISub.id k)
    rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at hR
    obtain ⟨l1, hsig⟩ := sigmaW_typed hW hb.2.1 hR
    refine kanH2_sigma hW hTT hR hsig (fun k1 ρ1 A2 B2 hR2 k2 ρ2 X X' h1 h2 => ?_)
      (fun k1 ρ1 A2 B2 hR2 b hbb k2 ρ2 X X' h1 h2 => ?_) (fun k1 ρ1 A2 B2 hR2 b hbb k2 ρ2 X X' h1 h2 => ?_)
    · exact ((famComp hW hne ihA ihB hF hT.2.1 ρ1 hR2).1.hrel hW).1 k2 ρ2 X X' h1 h2
    · exact (((famComp hW hne ihA ihB hF hT.2.1 ρ1 hR2).2 b hbb).hrel hW).1 k2 ρ2 X X' h1 h2
    · exact (((famComp hW hne ihA ihB hF hT.2.1 ρ1 hR2).2 b hbb).hrel hW).2 k2 ρ2 X X' h1 h2
  · have hTT := Comp2_ty_RT2 hT
    have hb := Comp2_ty_base hT
    rw [Comp2_sigmaC A B hne] at hT
    obtain ⟨A1, B1, -, -, hR, -⟩ := hT.2.1 (k + 1) (ISub.id (k + 1))
    rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at hR
    obtain ⟨l1, hsig⟩ := sigmaW_typed hW hb.2.1 hR
    refine kanT2_sigma hW hTT hR hsig (fun k1 ρ A2 B2 hR2 k2 ρ' X' hX' => ?_)
      (fun k1 ρ A2 B2 hR2 b hbb k2 ρ' X' hX' => ?_)
    · exact (((famComp hW hne ihA ihB hF hT.2.1 ρ hR2).1).isub hW ρ').kanT hX'
    · exact (((famComp hW hne ihA ihB hF hT.2.1 ρ hR2).2 b hbb).isub hW ρ').kanT hX'

/-! ### Path types and `(i : I) → A` -/

theorem kanP2_pathC {m : ℕ} {L a0 a1 : V} (hLne : L ≠ ∅) (ihL : KanP2 S (m + 1) L) :
    KanP2 S m (pathC m L a0 a1) := by
  have pt : ∀ {k : ℕ} {f : Hom k m} {T T' : Tm}, (Comp2 S (pathC m L a0 a1) m k f).ty T T' →
      ∀ k' (σ : ISub k' k) L2 c0 c1, RedT S k' (T.isub σ) (.path L2 c0 c1) → ∀ (s : I), s.Scoped k' →
        KCode S k' (L2.dinst s) := by
    intro k f T T' hT k' σ L2 c0 c1 hR2 s hs
    rw [Comp2_pathC L a0 a1 hLne] at hT
    obtain ⟨L3, b0, b1, L3', b0', b1', hR3, -, -, hpt, -⟩ := hT.2.1 k' σ
    have e := RedW.unique hR3.1 hR2.1
    injection e with e1 e2 e3
    subst e1
    exact KCode.of_comp ihL (hpt s s hs hs (I_eq_refl _))
  refine ⟨fun k f T T' hT => ?_, fun k f T T' hT => ?_⟩
  · have hTT := Comp2_ty_RT2 hT
    have hb := Comp2_ty_base hT
    have hT' := hT
    rw [Comp2_pathC L a0 a1 hLne] at hT'
    obtain ⟨L1, b0, b1, -, -, -, hR, -⟩ := hT'.2.1 k (ISub.id k)
    rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at hR
    obtain ⟨l1, hpath⟩ := pathW_typed hW hb.2.1 hR
    exact kanH2_path hW hTT hR hpath fun k' ρ L2 c0 c1 hR2 s hs k'' ρ' X' hX' =>
      ((pt hT k' ρ L2 c0 c1 hR2 s hs).isub hW ρ').kanH hX'
  · have hTT := Comp2_ty_RT2 hT
    have hb := Comp2_ty_base hT
    have hT' := hT
    rw [Comp2_pathC L a0 a1 hLne] at hT'
    obtain ⟨L1, b0, b1, -, -, -, hR, -⟩ := hT'.2.1 (k + 1) (ISub.id (k + 1))
    rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at hR
    obtain ⟨l1, hpath⟩ := pathW_typed hW hb.2.1 hR
    exact kanT2_path hW hTT hR hpath (fun k1 ρ L2 c0 c1 hR2 s hs k2 ρ' X' hX' =>
      ((pt hT (k1 + 1) ρ L2 c0 c1 hR2 s hs).isub hW ρ').kanT hX')
      (fun k1 ρ L2 c0 c1 hR2 s hs k2 ρ' X' hX' => ((pt hT k1 ρ L2 c0 c1 hR2 s hs).isub hW ρ').kanH hX')

theorem kanP2_ipiC {m : ℕ} {L : V} (hLne : L ≠ ∅) (ihL : KanP2 S (m + 1) L) : KanP2 S m (ipiC m L) := by
  have pt : ∀ {k : ℕ} {f : Hom k m} {T T' : Tm}, (Comp2 S (ipiC m L) m k f).ty T T' →
      ∀ k' (σ : ISub k' k) L2, RedT S k' (T.isub σ) (.ipi L2) → ∀ (s : I), s.Scoped k' →
        KCode S k' (L2.dinst s) := by
    intro k f T T' hT k' σ L2 hR2 s hs
    rw [Comp2_ipiC L hLne] at hT
    obtain ⟨L3, L3', hR3, -, -, hpt⟩ := hT.2.1 k' σ
    have e := RedW.unique hR3.1 hR2.1
    injection e with e1
    subst e1
    exact KCode.of_comp ihL (hpt s s hs hs (I_eq_refl _))
  refine ⟨fun k f T T' hT => ?_, fun k f T T' hT => ?_⟩
  · have hTT := Comp2_ty_RT2 hT
    have hb := Comp2_ty_base hT
    have hT' := hT
    rw [Comp2_ipiC L hLne] at hT'
    obtain ⟨L1, -, hR, -⟩ := hT'.2.1 k (ISub.id k)
    rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at hR
    obtain ⟨l1, hipi⟩ := ipiW_typed hW hb.2.1 hR
    exact kanH2_ipi hW hTT hR hipi fun k' ρ L2 hR2 s hs k'' ρ' X' hX' =>
      ((pt hT k' ρ L2 hR2 s hs).isub hW ρ').kanH hX'
  · have hTT := Comp2_ty_RT2 hT
    have hb := Comp2_ty_base hT
    have hT' := hT
    rw [Comp2_ipiC L hLne] at hT'
    obtain ⟨L1, -, hR, -⟩ := hT'.2.1 (k + 1) (ISub.id (k + 1))
    rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at hR
    obtain ⟨l1, hipi⟩ := ipiW_typed hW hb.2.1 hR
    exact kanT2_ipi hW hTT hR hipi fun k1 ρ L2 hR2 s hs k2 ρ' X' hX' =>
      ((pt hT (k1 + 1) ρ L2 hR2 s hs).isub hW ρ').kanT hX'


/-! ### Glue types -/

omit hW in
theorem face_tr {k1 : ℕ} {φ2 : I} {C : Cof k1} (hf : (ival (idEnv k1) φ2).face = C) {k2 : ℕ} (σ : ISub k2 k1) :
    (ival (idEnv k2) (φ2.subst σ.τ)).holds ↔ (C.restr σ.hom).holds := by
  rw [DM.holds_iff_face_holds, face_isub hf σ]

/-- The components of the normal forms of a type related at a restriction of a Glue code, at the
restrictions where the face does not hold. -/
theorem glueComp {m : ℕ} {A Tp : V} {φ : Cof m} (hAne : A ≠ ∅)
    (ihA : KanP2 S m A) (ihT : ∀ k (f : Hom k m), (φ.restr f).holds → KanP2 S k (dat Tp k f))
    {f : Hom k m} {T T' : Tm}
    (hloc : ∀ k' (σ : ISub k' k), glueLocT S A Tp φ f k' σ (T.isub σ) (T'.isub σ))
    {k1 : ℕ} (ρ1 : ISub k1 k) (hn1 : ¬ (φ.restr (f.comp ρ1.hom)).holds) {A2 : Tm} {φ2 : I} {T2 e2 : Tm}
    (hR2 : RedT S k1 (T.isub ρ1) (.glue A2 φ2 T2 e2)) :
    KCode S k1 A2 ∧ (ival (idEnv k1) φ2).face = φ.restr (f.comp ρ1.hom) ∧
      ∀ k2 (σ : ISub k2 k1), (ival (idEnv k2) (φ2.subst σ.τ)).holds → KCode S k2 (T2.isub σ) := by
  have h := hloc k1 ρ1
  unfold glueLocT at h
  rw [if_neg hn1] at h
  obtain ⟨A3, φ3, T3, e3, A3', φ3', T3', e3', r3, -, -, -, f3, -, hA3, hfib⟩ := h
  have e := RedW.unique r3.1 hR2.1
  simp only [Tm.glue.injEq] at e
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e
  refine ⟨KCode.of_comp ihA hA3, f3, fun k2 σ hh => ?_⟩
  have hc : (φ.restr (f.comp (ρ1.comp σ).hom)).holds := by
    rw [← ISub.comp_hom, ← Cof.restr_restr]; exact (face_tr f3 σ).1 hh
  exact KCode.of_comp (ihT k2 _ hc) (hfib k2 σ hc).1

theorem kanP2_glueC {l m : ℕ} {A Tp ep : V} {φ : Cof m} (hAw : WF l m A) (hφ : φ.IsCof)
    (hTn : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h))
    (hTkv : ∀ k (f : Hom k m), (φ.restr f).holds → IsKV k (dat Tp k f))
    (ihA : KanP2 S m A) (ihT : ∀ k (f : Hom k m), (φ.restr f).holds → KanP2 S k (dat Tp k f)) :
    KanP2 S m (glueC m A φ Tp ep) := by
  have hAne : A ≠ ∅ := IsKV.ne_empty hAw.fib.kv
  -- the normal form of a type related at a restriction where the face does not hold
  have nf : ∀ {k : ℕ} {f : Hom k m} {T T' : Tm}, (Comp2 S (glueC m A φ Tp ep) m k f).ty T T' →
      ¬ (φ.restr f).holds →
      (∀ k' (σ : ISub k' k), glueLocT S A Tp φ f k' σ (T.isub σ) (T'.isub σ)) ∧
      ∃ A1 φ1 T1 e1 l1, RedT S k T (.glue A1 φ1 T1 e1) ∧ HasTy S k .one [] (.glue A1 φ1 T1 e1) (.univ l1) ∧
        (ival (idEnv k) φ1).face = φ.restr f ∧ φ1.Scoped k := by
    intro k f T T' hT hh
    have hb := Comp2_ty_base hT
    rw [Comp2_glueC_at hφ hTn hTkv f, if_neg hh,
      Comp2_glueC (isKV_res _ _) (isKV_res _ _) (hφ.restr f) hh] at hT
    obtain ⟨-, hloc, -, -⟩ := hT
    have hloc' : ∀ k' (σ : ISub k' k), glueLocT S A Tp φ f k' σ (T.isub σ) (T'.isub σ) := fun k' σ => by
      rw [← glueLocT_res hAne]; exact hloc k' σ
    refine ⟨hloc', ?_⟩
    have h0 := hloc' k (ISub.id k)
    unfold glueLocT at h0
    rw [if_neg (by rw [ISub.hom_id, Hom.comp_id]; exact hh)] at h0
    obtain ⟨A1, φ1, T1, e1, A1', φ1', T1', e1', r1, -, s1, -, f1, -, -, -⟩ := h0
    rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at r1
    obtain ⟨l1, h1 | h1⟩ := hb.2.1.of_tyEq r1.2
    swap; · cases h1
    rw [ISub.hom_id, Hom.comp_id] at f1
    exact ⟨A1, φ1, T1, e1, l1, r1, h1, f1, s1⟩
  -- the induction hypotheses of the Glue lemmas at the normal form
  have ihs : ∀ {k : ℕ} {f : Hom k m} {T T' : Tm} {φ1 : I},
      (∀ k' (σ : ISub k' k), glueLocT S A Tp φ f k' σ (T.isub σ) (T'.isub σ)) →
      (ival (idEnv k) φ1).face = φ.restr f → φ1.Scoped k →
      ∀ k1 (ρ1 : ISub k1 k) (A2 : Tm) (φ2 : I) (T2 e2 : Tm), ¬ (ival (idEnv k1) (φ1.subst ρ1.τ)).holds →
        RedT S k1 (T.isub ρ1) (.glue A2 φ2 T2 e2) →
        KCode S k1 A2 ∧ ∀ k2 (σ : ISub k2 k1), (ival (idEnv k2) (φ2.subst σ.τ)).holds → KCode S k2 (T2.isub σ) := by
    intro k f T T' φ1 hloc f1 s1 k1 ρ1 A2 φ2 T2 e2 hn1 hR2
    have hn1' : ¬ (φ.restr (f.comp ρ1.hom)).holds := by
      rw [← Cof.restr_restr]; exact fun h => hn1 ((face_tr f1 ρ1).2 h)
    have g := glueComp hW hAne ihA ihT hloc ρ1 hn1' hR2
    exact ⟨g.1, g.2.2⟩
  refine ⟨fun k f T T' hT => ?_, fun k f T T' hT => ?_⟩
  · by_cases hh : (φ.restr f).holds
    · have hT' := hT
      rw [Comp2_glueC_at hφ hTn hTkv f, if_pos hh] at hT'
      exact (ihT k f hh).1 k (Hom.id k) T T' hT'
    have hTT := Comp2_ty_RT2 hT
    obtain ⟨hloc, A1, φ1, T1, e1, l1, hR, hG, f1, s1⟩ := nf hT hh
    exact kanH2_glue hW hTT hR hG
      (fun k1 ρ1 A2 φ2 T2 e2 hn1 hR2 => ((ihs hloc f1 s1 k1 ρ1 A2 φ2 T2 e2 hn1 hR2).1.hrel hW).1)
      (fun k1 ρ1 A2 φ2 T2 e2 hn1 hR2 k2 σ hh2 X X' h1 h2 =>
        ((ihs hloc f1 s1 k1 ρ1 A2 φ2 T2 e2 hn1 hR2).2 k2 σ hh2).relH hW h1 h2)
  · by_cases hh : (φ.restr f).holds
    · have hT' := hT
      rw [Comp2_glueC_at hφ hTn hTkv f, if_pos hh] at hT'
      exact (ihT (k + 1) f hh).2 k (Hom.id (k + 1)) T T' hT'
    have hTT := Comp2_ty_RT2 hT
    obtain ⟨hloc, A1, φ1, T1, e1, l1, hR, hG, f1, s1⟩ := nf hT hh
    exact kanT2_glue hW hTT hR hG
      (fun k1 ρ1 A2 φ2 T2 e2 hn1 hR2 => (ihs hloc f1 s1 k1 ρ1 A2 φ2 T2 e2 hn1 hR2).1.hrel hW)
      (fun k1 ρ1 A2 φ2 T2 e2 hn1 hR2 => ⟨fun k2 σ hh2 X X' h1 h2 =>
        ((ihs hloc f1 s1 k1 ρ1 A2 φ2 T2 e2 hn1 hR2).2 k2 σ hh2).relH hW h1 h2,
        fun k2 Θ hh2 X X' h1 h2 => ((ihs hloc f1 s1 k1 ρ1 A2 φ2 T2 e2 hn1 hR2).2 (k2 + 1) Θ hh2).relT hW h1 h2⟩)


/-! ### Inductive types -/

theorem data_decl {m : ℕ} {Θ : SData m} {f : Hom k m} {A A' : Tm} (hT : (Comp2 S (dataC Θ) m k f).ty A A') :
    ∃ D, S[Θ.idx]? = some (.data D) := by
  have hb := Comp2_ty_base hT
  rw [Comp2_dataC] at hT
  obtain ⟨ps, -, hR, -⟩ := hT.2.1 k (ISub.id k)
  rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at hR
  obtain ⟨l, hd⟩ := ty_of_tyEq hW hb.2.1 hR.2 (fun l h => by cases h)
  obtain ⟨D, hD, -⟩ := gen_data (spec_to_minimal hW hd) rfl
  exact ⟨D, hD⟩

theorem kanP2_dataC' (hyp : HITHyp2 S) {m : ℕ} {Θ : SData m} (hKS : KanShape S m Θ) : KanP2 S m (dataC Θ) := by
  refine ⟨fun k f A A' hT => ?_, fun k f A A' hT => ?_⟩
  · obtain ⟨D, hD⟩ := data_decl hW hT
    exact kanH2_dataC hW hD hKS hT
  · obtain ⟨D, hD⟩ := data_decl hW hT
    exact kanT2_dataC hW hD hKS hyp hT

/-! ### All codes -/

theorem kanP2_tyCode (hyp : HITHyp2 S) {m : ℕ} {X : V} (hX : TyCode m X) : KanP2 S m X := by
  refine tyCode_ind (fun m X => KanP2 S m X) (fun m => kanP2_emptyC hW) ?_ ?_ ?_ ?_ ?_ ?_ ?_ m X hX
  · intro l m A B hA hB hBf hBw hBn ihA ihB
    exact kanP2_piC hW hA ihA ihB
  · intro l m A B hA hB hBf hBw hBn ihA ihB
    exact kanP2_sigmaC hW hA ihA ihB
  · intro l m L a0 a1 hL h0 h1 ihL
    exact kanP2_pathC hW (IsKV.ne_empty hL.fib.kv) ihL
  · intro l m L hL ihL
    exact kanP2_ipiC hW (IsKV.ne_empty hL.fib.kv) ihL
  · intro m l hl ih
    exact kanP2_univC hW ih
  · intro l m A φ Tp ep hl hAw hφ hn hTpE hepE hTw hTn hem hen ihA ihT
    exact kanP2_glueC hW hAw hφ hTn (fun k f hh => (hTw k f hh).fib.kv) ihA ihT
  · intro l m Θ hc hw hpw ih ihp
    exact kanP2_dataC' hW hyp (kanShape_of ih)

/-- **The binary Kan property of all related types.** -/
theorem kanOracle2 (hyp : HITHyp2 S) : KanOracle2 S := by
  have hKT : ∀ l, KTAt S l := fun l k X X' hXX hX =>
    (kanP2_tyCode hW hyp (tyCode_of_univ hW hX)).2 k (Hom.id (k + 1)) X X' (by unfold RT2 at hXX; exact hXX)
  refine ⟨fun k A A' h => ?_, fun k A A' h => ?_⟩
  · obtain ⟨l, hA | rfl⟩ := (Comp2_ty_base h).2.1
    · exact (kanP2_tyCode hW hyp (tyCode_of_univ hW hA)).1 k (Hom.id k) A A' (by unfold RT2 at h; exact h)
    · exact kanH2_univ hW (hKT l) h ⟨redW_self rfl, TyEq.refl _⟩
  · obtain ⟨l, hA | rfl⟩ := (Comp2_ty_base h).2.1
    · exact (kanP2_tyCode hW hyp (tyCode_of_univ hW hA)).2 k (Hom.id (k + 1)) A A' (by unfold RT2 at h; exact h)
    · exact kanT2_univ hW h ⟨redW_self rfl, TyEq.refl _⟩

end

end Model.Whnf
