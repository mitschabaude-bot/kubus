import Model.Canon.CompBasic

/-!
# Canonicity: computability at the type formers' codes
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore ZFSet

noncomputable section

variable {S : Sig} {k k' m : ℕ}

theorem appV_res_res (B : V) (f : Hom k m) (g : Hom k' k) (a : V) :
    appV k' (res g (res f B)) a = apZ (dat B k' (f.comp g)) a := by
  simp [appV, here, dat_res, Hom.comp_id]

theorem Comp_piC (A B : V) (hA : A ≠ ∅) (f : Hom k m) :
    Comp S (piC m A B) m k f =
      ⟨fun T => (IsTyK S k T ∧ semK S k T = res f (piC m A B)) ∧ ∃ A1 B1, TyEq S k T (.pi A1 B1) ∧
          ∀ k' (σ : ISub k' k), (Comp S A m k' (f.comp σ.hom)).ty (A1.isub σ) ∧
            ∀ a, (Comp S A m k' (f.comp σ.hom)).el (A1.isub σ) a →
              (Comp S (apZ (dat B k' (f.comp σ.hom)) (semK S k' a)) k' k' (Hom.id k')).ty ((B1.isub σ).inst a),
        fun T t => HasTy S k .one [] t T ∧ semK S k t ∈ El (res f (piC m A B)) (Hom.id k) ∧
          piE S (fun k' σ => (Comp S A m k' (f.comp σ.hom)).el)
            (fun k' σ a k'' σ' => (Comp S (apZ (dat B k' (f.comp σ.hom)) (semK S k' a)) k' k'' σ'.hom).el)
            k (ISub.id k) T t⟩ := by
  rw [Comp_unfold (show piC m A B ≠ ∅ from mkKV_ne_empty _)]
  simp only [body, core, piC, dat_mkKV, piDatum, π1_quad, tagZ, π1_pair, π2_pair, Hom.comp_id, true_or,
    if_true, natZ_inj, Comp_res hA, appV_res_res]

theorem natOf_natZ (n : ℕ) : natOf (natZ n) = n := by
  have h : ∃ n', natZ n' = natZ n := ⟨n, rfl⟩
  rw [natOf, dif_pos h]; exact natZ_inj.1 h.choose_spec

theorem Comp_sigmaC (A B : V) (hA : A ≠ ∅) (f : Hom k m) :
    Comp S (sigmaC m A B) m k f =
      ⟨fun T => (IsTyK S k T ∧ semK S k T = res f (sigmaC m A B)) ∧ ∃ A1 B1, TyEq S k T (.sigma A1 B1) ∧
          ∀ k' (σ : ISub k' k), (Comp S A m k' (f.comp σ.hom)).ty (A1.isub σ) ∧
            ∀ a, (Comp S A m k' (f.comp σ.hom)).el (A1.isub σ) a →
              (Comp S (apZ (dat B k' (f.comp σ.hom)) (semK S k' a)) k' k' (Hom.id k')).ty ((B1.isub σ).inst a),
        fun T t => HasTy S k .one [] t T ∧ semK S k t ∈ El (res f (sigmaC m A B)) (Hom.id k) ∧
          sigmaE S (fun k' σ => (Comp S A m k' (f.comp σ.hom)).el)
            (fun k' σ a k'' σ' => (Comp S (apZ (dat B k' (f.comp σ.hom)) (semK S k' a)) k' k'' σ'.hom).el)
            k (ISub.id k) T t⟩ := by
  rw [Comp_unfold (show sigmaC m A B ≠ ∅ from mkKV_ne_empty _)]
  simp only [body, core, sigmaC, dat_mkKV, sigmaDatum, π1_quad, tagZ, π1_pair, π2_pair, Hom.comp_id, or_true,
    if_true, natZ_inj, Comp_res hA, appV_res_res, tPi, tSigma, if_false, show ¬ (3 = 2) by decide]

theorem Comp_pathC (L a0 a1 : V) (hL : L ≠ ∅) (f : Hom k m) :
    Comp S (pathC m L a0 a1) m k f =
      ⟨fun T => (IsTyK S k T ∧ semK S k T = res f (pathC m L a0 a1)) ∧ ∃ L1 b0 b1, TyEq S k T (.path L1 b0 b1) ∧
          ∀ k' (σ : ISub k' k), (Comp S L (m + 1) (k' + 1) ((Hom.lift f).comp σ.up.hom)).ty (L1.isub σ.up) ∧
            (Comp S L (m + 1) k' ((Hom.lift f).comp (ISub.cons .zero trivial σ).hom)).el
              ((L1.isub σ.up).dinst .zero) (b0.isub σ) ∧
            (Comp S L (m + 1) k' ((Hom.lift f).comp (ISub.cons .one trivial σ).hom)).el
              ((L1.isub σ.up).dinst .one) (b1.isub σ),
        fun T t => HasTy S k .one [] t T ∧ semK S k t ∈ El (res f (pathC m L a0 a1)) (Hom.id k) ∧
          pathE S (fun k' σ => (Comp S L (m + 1) k' ((Hom.lift f).comp σ.hom)).el) k (ISub.id k) T t⟩ := by
  rw [Comp_unfold (show pathC m L a0 a1 ≠ ∅ from mkKV_ne_empty _)]
  simp only [body, core, pathC, dat_mkKV, pathDatum, π1_quad, tagZ, π1_pair, π2_pair, Hom.comp_id, true_or,
    if_true, natZ_inj, Comp_res hL, tPi, tSigma, tPath, if_false, show ¬ (4 = 2) by decide,
    show ¬ (4 = 3) by decide, or_self]

theorem Comp_ipiC (L : V) (hL : L ≠ ∅) (f : Hom k m) :
    Comp S (ipiC m L) m k f =
      ⟨fun T => (IsTyK S k T ∧ semK S k T = res f (ipiC m L)) ∧ ∃ L1, TyEq S k T (.ipi L1) ∧
          ∀ k' (σ : ISub k' k), (Comp S L (m + 1) (k' + 1) ((Hom.lift f).comp σ.up.hom)).ty (L1.isub σ.up),
        fun T t => HasTy S k .one [] t T ∧ semK S k t ∈ El (res f (ipiC m L)) (Hom.id k) ∧
          ipiE S (fun k' σ => (Comp S L (m + 1) k' ((Hom.lift f).comp σ.hom)).el) k (ISub.id k) T t⟩ := by
  rw [Comp_unfold (show ipiC m L ≠ ∅ from mkKV_ne_empty _)]
  simp only [body, core, ipiC, dat_mkKV, ipiDatum, π1_quad, tagZ, π1_pair, π2_pair, Hom.comp_id, or_true,
    if_true, natZ_inj, Comp_res hL, tPi, tSigma, tPath, tIPi, if_false, show ¬ (5 = 2) by decide,
    show ¬ (5 = 3) by decide, show ¬ (5 = 4) by decide, or_self]

theorem Comp_univC (l : ℕ) (f : Hom k m) :
    Comp S (univC m l) m k f =
      ⟨fun T => (IsTyK S k T ∧ semK S k T = res f (univC m l)) ∧ TyEq S k T (.univ l),
        fun T t => HasTy S k .one [] t T ∧ semK S k t ∈ El (res f (univC m l)) (Hom.id k) ∧
          TyEq S k T (.univ l) ∧ ∃ _ : semK S k t ∈ ZFSet.sep (WF l k) (Vt l), (Comp S (semK S k t) k k (Hom.id k)).ty t⟩ := by
  rw [Comp_unfold (show univC m l ≠ ∅ from mkKV_ne_empty (fun k _ => univDatum (WF l) l k))]
  simp only [body, core, univC, univCode, dat_mkKV, univDatum, π1_quad, tagZ, π1_pair, π2_pair,
    natZ_inj, tPi, tSigma, tPath, tIPi, tUniv, if_false, show ¬ (6 = 2) by decide,
    show ¬ (6 = 3) by decide, show ¬ (6 = 4) by decide, show ¬ (6 = 5) by decide, or_self, if_true,
    natOf_natZ, π1π2_quad]

theorem Comp_emptyC (f : Hom k m) :
    Comp S (emptyC m) m k f =
      ⟨fun T => IsTyK S k T ∧ semK S k T = res f (emptyC m), fun _ _ => False⟩ := by
  rw [Comp_unfold (show emptyC m ≠ ∅ from mkKV_ne_empty (fun _ _ => emptyDatum))]
  simp only [body, core, emptyC, dat_mkKV, emptyDatum, π1_quad, tagZ, π1_pair, π2_pair,
    natZ_inj, tPi, tSigma, tPath, tIPi, tUniv, tEmpty, if_false, show ¬ (1 = 2) by decide,
    show ¬ (1 = 3) by decide, show ¬ (1 = 4) by decide, show ¬ (1 = 5) by decide, show ¬ (1 = 6) by decide,
    or_self, if_true, and_false]

theorem Comp_eq_res {X : V} (hX : X ≠ ∅) (f : Hom k m) : Comp S X m k f = Comp S (res f X) k k (Hom.id k) := by
  rw [Comp_res hX, Hom.comp_id]

theorem cofOf_enc (φ : Cof k) : cofOf k (enc φ) = φ := by
  have h : ∃ φ' : Cof k, enc φ' = enc φ := ⟨φ, rfl⟩
  rw [cofOf, dif_pos h]; exact enc_injective h.choose_spec

theorem Comp_glueC {A Tp ep : V} {φ : Cof m} (hA : IsKV m A) (hTp : IsKV m Tp) (hφ : φ.IsCof)
    (hn : ¬ φ.holds) :
    Comp S (glueC m A φ Tp ep) m m (Hom.id m) =
      ⟨fun T => (IsTyK S m T ∧ semK S m T = res (Hom.id m) (glueC m A φ Tp ep)) ∧
          ∃ A1 φ1 T1 e1, TyEq S m T (.glue A1 φ1 T1 e1) ∧ φ1.Scoped m ∧ (ival (idEnv m) φ1).face = φ ∧
          (∀ k' (σ : ISub k' m), (Comp S A m k' σ.hom).ty (A1.isub σ)) ∧
          ∀ k' (σ : ISub k' m), (φ.restr σ.hom).holds →
            (Comp S (dat Tp k' σ.hom) k' k' (Hom.id k')).ty (T1.isub σ) ∧
            equivE S (fun k'' σ' => (Comp S (dat Tp k' σ.hom) k' k'' σ'.hom).el)
              (fun k'' σ' => (Comp S A m k'' (σ.comp σ').hom).el) k' (ISub.id k')
              (Tm.equiv (T1.isub σ) (A1.isub σ)) (e1.isub σ),
        fun T g => HasTy S m .one [] g T ∧ semK S m g ∈ El (res (Hom.id m) (glueC m A φ Tp ep)) (Hom.id m) ∧
          HasTy S m .one [] g T ∧ ∃ A1 φ1 T1 e1, TyEq S m T (.glue A1 φ1 T1 e1) ∧ φ1.Scoped m ∧
          (ival (idEnv m) φ1).face = φ ∧
          (∀ k' (σ : ISub k' m), (Comp S A m k' σ.hom).el (A1.isub σ) (.unglue (φ1.subst σ.τ) (e1.isub σ) (g.isub σ))) ∧
          ∀ k' (σ : ISub k' m), (φ.restr σ.hom).holds →
            (Comp S (dat Tp k' σ.hom) k' k' (Hom.id k')).el (T1.isub σ) (g.isub σ)⟩ := by
  rw [Comp_unfold (show glueC m A φ Tp ep ≠ ∅ from mkKV_ne_empty _)]
  have hn' : ¬ (φ.restr ((Hom.id m).comp (Hom.id m))).holds := by rwa [Hom.comp_id, hφ.restr_id]
  have hdat : dat (glueC m A φ Tp ep) m (Hom.id m) = glueDatum m A φ Tp (res (Hom.id m) ep) := by
    unfold glueC; rw [dat_mkKV, if_neg (by rwa [hφ.restr_id]), hφ.restr_id, res_id hA, res_id hTp]
  simp only [body, core, Hom.comp_id, hdat, glueDatum, π1_quad, tagZ, π1_pair, π2_pair, Hom.comp_id,
    natZ_inj, tPi, tSigma, tPath, tIPi, tUniv, tEmpty, tGlue, if_false, show ¬ (7 = 2) by decide,
    show ¬ (7 = 3) by decide, show ¬ (7 = 4) by decide, show ¬ (7 = 5) by decide, show ¬ (7 = 6) by decide,
    show ¬ (7 = 1) by decide, or_self, if_true, cofOf_enc, hφ.restr_id, res_id hA, res_id hTp, Hom.id_comp]

/-- The point argument relation of an inductive type's code. -/
def dataP (S : Sig) (Θ : SData m) (f : Hom k m) : (k' : ℕ) → Hom k' k → ℕ → ℕ → List V → Tm → Tm → Prop :=
  fun k' g c j pre A t => (Comp S (tyLook (shapeV (Θ.restr (f.comp g))) c j pre) k' k' (Hom.id k')).el A t

theorem Comp_dataC (Θ : SData m) (f : Hom k m) :
    Comp S (dataC Θ) m k f =
      ⟨fun T => (IsTyK S k T ∧ semK S k T = res f (dataC Θ)) ∧ ∃ ps, TyEq S k T (.data Θ.idx ps) ∧
          ps = Tm.ofList ps.toList ∧
          ∀ k' (σ : ISub k' k) (c : ℕ) (C : Ctor) (args : List Tm), (dataD S Θ.idx).ctors[c]? = some C →
            args.length < C.args.length → C.isRec args.length = false →
            (∀ j (hj : j < args.length), C.isRec j = true →
              DR S Θ.idx (dataD S Θ.idx) (dataP S Θ f) k' σ.hom (T.isub σ) args[j]) →
            (∀ j (hj : j < args.length), C.isRec j = false →
              dataP S Θ f k' σ.hom c j ((args.take j).map (semK S k'))
                ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList
                  ((args.take j).reverse ++ (ps.isub σ).toList.reverse)) args[j]) →
            (Comp S (tyLook (shapeV (Θ.restr (f.comp σ.hom))) c args.length (args.map (semK S k')))
              k' k' (Hom.id k')).ty
              ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList
                (args.reverse ++ (ps.isub σ).toList.reverse)),
        fun T t => HasTy S k .one [] t T ∧ semK S k t ∈ El (res f (dataC Θ)) (Hom.id k) ∧
          HasTy S k .one [] t T ∧ DR S Θ.idx (dataD S Θ.idx) (dataP S Θ f) k (Hom.id k) T t⟩ := by
  rw [Comp_unfold (show dataC Θ ≠ ∅ from mkKV_ne_empty _)]
  simp only [body, core, dataC, dat_mkKV, dataDatum, π1_quad, tagZ, π1_pair, π2_pair, Hom.comp_id,
    natZ_inj, tPi, tSigma, tPath, tIPi, tUniv, tEmpty, tGlue, tData, if_false, show ¬ (11 = 2) by decide,
    show ¬ (11 = 3) by decide, show ¬ (11 = 4) by decide, show ¬ (11 = 5) by decide, show ¬ (11 = 6) by decide,
    show ¬ (11 = 1) by decide, show ¬ (11 = 7) by decide, or_self, if_true, natOf_natZ]
  rfl

end

end Model.Canon
