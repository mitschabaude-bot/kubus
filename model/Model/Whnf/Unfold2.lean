import Model.Whnf.Rel
import Model.Canon.Unfold
import Model.Canon.GlueBasic

/-!
# The binary relation at the type formers' codes
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore ZFSet Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' m m' : ℕ}

theorem Comp2_unfold {X : V} (hX : X ≠ ∅) (f : Hom k m) :
    Comp2 S X m k f = body2 S k (fun k' g => dat X k' (f.comp g)) (res f X) (rank X)
      (fun k' g => rank_dat_lt hX _) (fun Y _ => Comp2 S Y) := by
  rw [Comp2_eq]; unfold compF2; rw [dif_pos hX]

theorem body2_congr {Dt Dt' : (k' : ℕ) → Hom k' k → V} (hDt : Dt = Dt') (self : V) {ρ ρ' : Ordinal}
    (hD : ∀ k' (h : Hom k' k), rank (Dt k' h) < ρ) (hD' : ∀ k' (h : Hom k' k), rank (Dt' k' h) < ρ') :
    body2 S k Dt self ρ hD (fun Y _ => Comp2 S Y) = body2 S k Dt' self ρ' hD' (fun Y _ => Comp2 S Y) := by
  subst hDt; rfl

theorem Comp2_congr {X Y : V} (hX : X ≠ ∅) (hY : Y ≠ ∅) (f : Hom k m) (g : Hom k m')
    (hd : ∀ k' (h : Hom k' k), dat X k' (f.comp h) = dat Y k' (g.comp h)) (hr : res f X = res g Y) :
    Comp2 S X m k f = Comp2 S Y m' k g := by
  rw [Comp2_unfold hX, Comp2_unfold hY, hr]
  exact body2_congr (funext fun k' => funext fun h => hd k' h) _ _ _

theorem Comp2_res {X : V} (hX : X ≠ ∅) (g : Hom k m) (h : Hom k' k) :
    Comp2 S (res g X) k k' h = Comp2 S X m k' (g.comp h) := by
  refine Comp2_congr (mkKV_ne_empty _) hX h (g.comp h) (fun n h' => ?_) ?_
  · show dat (res g X) n (h.comp h') = _
    rw [dat_res, Hom.comp_assoc]
  · show res h (res g X) = _
    rw [res_res]

theorem Comp2_eq_res {X : V} (hX : X ≠ ∅) (f : Hom k m) : Comp2 S X m k f = Comp2 S (res f X) k k (Hom.id k) := by
  rw [Comp2_res hX, Hom.comp_id]

/-- Related elements are typed, equal, and in the code's element set. -/
theorem Comp2_el {X : V} {f : Hom k m} {A t t' : Tm} (h : (Comp2 S X m k f).el A t t') :
    EB S k A t t' ∧ semK S k t ∈ El (res f X) (Hom.id k) := by
  by_cases hX : X = ∅
  · subst hX; rw [Comp2_eq] at h; unfold compF2 at h; rw [dif_neg (by simp)] at h; exact h.elim
  · rw [Comp2_unfold hX] at h; exact ⟨h.1, h.2.1⟩

theorem Comp2_piC (A B : V) (hA : A ≠ ∅) (f : Hom k m) :
    Comp2 S (piC m A B) m k f =
      ⟨fun T T' => (IsTyK S k T ∧ IsTyK S k T' ∧ semK S k T = res f (piC m A B) ∧
          semK S k T' = res f (piC m A B) ∧ TyEq S k T T') ∧ ∀ k' (σ : ISub k' k), ∃ A1 B1 A1' B1',
          RedT S k' (T.isub σ) (.pi A1 B1) ∧ RedT S k' (T'.isub σ) (.pi A1' B1') ∧
          (Comp2 S A m k' (f.comp σ.hom)).ty A1 A1' ∧
            ∀ a a', (Comp2 S A m k' (f.comp σ.hom)).el A1 a a' →
              (Comp2 S (apZ (dat B k' (f.comp σ.hom)) (semK S k' a)) k' k' (Hom.id k')).ty (B1.inst a) (B1'.inst a'),
        fun T t t' => EB S k T t t' ∧ semK S k t ∈ El (res f (piC m A B)) (Hom.id k) ∧
          piE2 S (fun k' σ => (Comp2 S A m k' (f.comp σ.hom)).el)
            (fun k' σ a k'' σ' => (Comp2 S (apZ (dat B k' (f.comp σ.hom)) (semK S k' a)) k' k'' σ'.hom).el)
            k (ISub.id k) T t t'⟩ := by
  rw [Comp2_unfold (show piC m A B ≠ ∅ from mkKV_ne_empty _)]
  simp only [body2, core2, piC, dat_mkKV, piDatum, π1_quad, tagZ, π1_pair, π2_pair, Hom.comp_id, true_or,
    if_true, natZ_inj, Comp2_res hA, appV_res_res]

theorem Comp2_sigmaC (A B : V) (hA : A ≠ ∅) (f : Hom k m) :
    Comp2 S (sigmaC m A B) m k f =
      ⟨fun T T' => (IsTyK S k T ∧ IsTyK S k T' ∧ semK S k T = res f (sigmaC m A B) ∧
          semK S k T' = res f (sigmaC m A B) ∧ TyEq S k T T') ∧ ∀ k' (σ : ISub k' k), ∃ A1 B1 A1' B1',
          RedT S k' (T.isub σ) (.sigma A1 B1) ∧ RedT S k' (T'.isub σ) (.sigma A1' B1') ∧
          (Comp2 S A m k' (f.comp σ.hom)).ty A1 A1' ∧
            ∀ a a', (Comp2 S A m k' (f.comp σ.hom)).el A1 a a' →
              (Comp2 S (apZ (dat B k' (f.comp σ.hom)) (semK S k' a)) k' k' (Hom.id k')).ty (B1.inst a) (B1'.inst a'),
        fun T t t' => EB S k T t t' ∧ semK S k t ∈ El (res f (sigmaC m A B)) (Hom.id k) ∧
          sigmaE2 S (fun k' σ => (Comp2 S A m k' (f.comp σ.hom)).el)
            (fun k' σ a k'' σ' => (Comp2 S (apZ (dat B k' (f.comp σ.hom)) (semK S k' a)) k' k'' σ'.hom).el)
            k (ISub.id k) T t t'⟩ := by
  rw [Comp2_unfold (show sigmaC m A B ≠ ∅ from mkKV_ne_empty _)]
  simp only [body2, core2, sigmaC, dat_mkKV, sigmaDatum, π1_quad, tagZ, π1_pair, π2_pair, Hom.comp_id, or_true,
    if_true, natZ_inj, Comp2_res hA, appV_res_res, tPi, tSigma, if_false, show ¬ (3 = 2) by decide]

theorem Comp2_pathC (L a0 a1 : V) (hL : L ≠ ∅) (f : Hom k m) :
    Comp2 S (pathC m L a0 a1) m k f =
      ⟨fun T T' => (IsTyK S k T ∧ IsTyK S k T' ∧ semK S k T = res f (pathC m L a0 a1) ∧
          semK S k T' = res f (pathC m L a0 a1) ∧ TyEq S k T T') ∧ ∀ k' (σ : ISub k' k), ∃ L1 b0 b1 L1' b0' b1',
          RedT S k' (T.isub σ) (.path L1 b0 b1) ∧ RedT S k' (T'.isub σ) (.path L1' b0' b1') ∧
          (Comp2 S L (m + 1) (k' + 1) ((Hom.lift f).comp σ.up.hom)).ty L1 L1' ∧
          (Comp2 S L (m + 1) k' ((Hom.lift f).comp (ISub.cons .zero trivial σ).hom)).el (L1.dinst .zero) b0 b0' ∧
          (Comp2 S L (m + 1) k' ((Hom.lift f).comp (ISub.cons .one trivial σ).hom)).el (L1.dinst .one) b1 b1',
        fun T t t' => EB S k T t t' ∧ semK S k t ∈ El (res f (pathC m L a0 a1)) (Hom.id k) ∧
          pathE2 S (fun k' σ => (Comp2 S L (m + 1) k' ((Hom.lift f).comp σ.hom)).el) k (ISub.id k) T t t'⟩ := by
  rw [Comp2_unfold (show pathC m L a0 a1 ≠ ∅ from mkKV_ne_empty _)]
  simp only [body2, core2, pathC, dat_mkKV, pathDatum, π1_quad, tagZ, π1_pair, π2_pair, Hom.comp_id, true_or,
    if_true, natZ_inj, Comp2_res hL, tPi, tSigma, tPath, if_false, show ¬ (4 = 2) by decide,
    show ¬ (4 = 3) by decide, or_self]

theorem Comp2_ipiC (L : V) (hL : L ≠ ∅) (f : Hom k m) :
    Comp2 S (ipiC m L) m k f =
      ⟨fun T T' => (IsTyK S k T ∧ IsTyK S k T' ∧ semK S k T = res f (ipiC m L) ∧
          semK S k T' = res f (ipiC m L) ∧ TyEq S k T T') ∧ ∀ k' (σ : ISub k' k), ∃ L1 L1',
          RedT S k' (T.isub σ) (.ipi L1) ∧ RedT S k' (T'.isub σ) (.ipi L1') ∧
          (Comp2 S L (m + 1) (k' + 1) ((Hom.lift f).comp σ.up.hom)).ty L1 L1',
        fun T t t' => EB S k T t t' ∧ semK S k t ∈ El (res f (ipiC m L)) (Hom.id k) ∧
          ipiE2 S (fun k' σ => (Comp2 S L (m + 1) k' ((Hom.lift f).comp σ.hom)).el) k (ISub.id k) T t t'⟩ := by
  rw [Comp2_unfold (show ipiC m L ≠ ∅ from mkKV_ne_empty _)]
  simp only [body2, core2, ipiC, dat_mkKV, ipiDatum, π1_quad, tagZ, π1_pair, π2_pair, Hom.comp_id, or_true,
    if_true, natZ_inj, Comp2_res hL, tPi, tSigma, tPath, tIPi, if_false, show ¬ (5 = 2) by decide,
    show ¬ (5 = 3) by decide, show ¬ (5 = 4) by decide, or_self]

theorem Comp2_univC (l : ℕ) (f : Hom k m) :
    Comp2 S (univC m l) m k f =
      ⟨fun T T' => (IsTyK S k T ∧ IsTyK S k T' ∧ semK S k T = res f (univC m l) ∧
          semK S k T' = res f (univC m l) ∧ TyEq S k T T') ∧ ∀ k' (σ : ISub k' k),
          RedT S k' (T.isub σ) (.univ l) ∧ RedT S k' (T'.isub σ) (.univ l),
        fun T t t' => EB S k T t t' ∧ semK S k t ∈ El (res f (univC m l)) (Hom.id k) ∧
          ∃ _ : semK S k t ∈ ZFSet.sep (WF l k) (Vt l), (Comp2 S (semK S k t) k k (Hom.id k)).ty t t'⟩ := by
  rw [Comp2_unfold (show univC m l ≠ ∅ from mkKV_ne_empty (fun k _ => univDatum (WF l) l k))]
  simp only [body2, core2, univC, univCode, dat_mkKV, univDatum, π1_quad, tagZ, π1_pair, π2_pair,
    natZ_inj, tPi, tSigma, tPath, tIPi, tUniv, if_false, show ¬ (6 = 2) by decide,
    show ¬ (6 = 3) by decide, show ¬ (6 = 4) by decide, show ¬ (6 = 5) by decide, or_self, if_true,
    natOf_natZ, π1π2_quad]

theorem Comp2_emptyC (f : Hom k m) :
    Comp2 S (emptyC m) m k f =
      ⟨fun T T' => IsTyK S k T ∧ IsTyK S k T' ∧ semK S k T = res f (emptyC m) ∧
          semK S k T' = res f (emptyC m) ∧ TyEq S k T T', fun _ _ _ => False⟩ := by
  rw [Comp2_unfold (show emptyC m ≠ ∅ from mkKV_ne_empty (fun _ _ => emptyDatum))]
  simp only [body2, core2, emptyC, dat_mkKV, emptyDatum, π1_quad, tagZ, π1_pair, π2_pair,
    natZ_inj, tPi, tSigma, tPath, tIPi, tUniv, tEmpty, if_false, show ¬ (1 = 2) by decide,
    show ¬ (1 = 3) by decide, show ¬ (1 = 4) by decide, show ¬ (1 = 5) by decide, show ¬ (1 = 6) by decide,
    or_self, if_true, and_false, and_true]

theorem Comp2_glueC {A Tp ep : V} {φ : Cof m} (hA : IsKV m A) (hTp : IsKV m Tp) (hφ : φ.IsCof)
    (hn : ¬ φ.holds) :
    Comp2 S (glueC m A φ Tp ep) m m (Hom.id m) =
      ⟨fun T T' => (IsTyK S m T ∧ IsTyK S m T' ∧ semK S m T = res (Hom.id m) (glueC m A φ Tp ep) ∧
          semK S m T' = res (Hom.id m) (glueC m A φ Tp ep) ∧ TyEq S m T T') ∧ ∀ k' (σ : ISub k' m),
          if (φ.restr σ.hom).holds then (Comp2 S (dat Tp k' σ.hom) k' k' (Hom.id k')).ty (T.isub σ) (T'.isub σ)
          else ∃ A1 φ1 T1 e1 A1' φ1' T1' e1',
            RedT S k' (T.isub σ) (.glue A1 φ1 T1 e1) ∧ RedT S k' (T'.isub σ) (.glue A1' φ1' T1' e1') ∧
            φ1.Scoped k' ∧ φ1'.Scoped k' ∧
            (ival (idEnv k') φ1).face = φ.restr σ.hom ∧ (ival (idEnv k') φ1').face = φ.restr σ.hom ∧
            (Comp2 S A m k' σ.hom).ty A1 A1' ∧
            ∀ k'' (σ' : ISub k'' k'), (φ.restr (σ.comp σ').hom).holds →
              (Comp2 S (dat Tp k'' (σ.comp σ').hom) k'' k'' (Hom.id k'')).ty (T1.isub σ') (T1'.isub σ') ∧
              (equivF S (fun k3 σ3 => Comp2 S (dat Tp k'' (σ.comp σ').hom) k'' k3 σ3.hom)
                (fun k3 σ3 => Comp2 S A m k3 ((σ.comp σ').comp σ3).hom) k'' (ISub.id k'')).el
                (Tm.equiv (T1.isub σ') (A1.isub σ')) (e1.isub σ') (e1'.isub σ'),
        fun T g g' => EB S m T g g' ∧ semK S m g ∈ El (res (Hom.id m) (glueC m A φ Tp ep)) (Hom.id m) ∧
          EB S m T g g' ∧ ∀ k' (σ : ISub k' m),
          if (φ.restr σ.hom).holds then (Comp2 S (dat Tp k' σ.hom) k' k' (Hom.id k')).el (T.isub σ) (g.isub σ) (g'.isub σ)
          else ∃ A1 φ1 T1 e1 ψ e0 t0 a0 ψ' e0' t0' a0', RedT S k' (T.isub σ) (.glue A1 φ1 T1 e1) ∧
            RedE S k' (T.isub σ) (g.isub σ) (.glueEl ψ e0 t0 a0) ∧ RedE S k' (T.isub σ) (g'.isub σ) (.glueEl ψ' e0' t0' a0') ∧
            I.Entails ψ φ1 ∧ I.Entails φ1 ψ ∧ I.Entails ψ' φ1 ∧ I.Entails φ1 ψ' ∧
            EqTm S k' (cof .one φ1) [] e0 e1 (Tm.equiv T1 A1) ∧ EqTm S k' (cof .one φ1) [] e0' e1 (Tm.equiv T1 A1) ∧
            (Comp2 S A m k' σ.hom).el A1 a0 a0'⟩ := by
  rw [Comp2_unfold (show glueC m A φ Tp ep ≠ ∅ from mkKV_ne_empty _)]
  have hdat : dat (glueC m A φ Tp ep) m (Hom.id m) = glueDatum m A φ Tp (res (Hom.id m) ep) := by
    unfold glueC; rw [dat_mkKV, if_neg (by rwa [hφ.restr_id]), hφ.restr_id, res_id hA, res_id hTp]
  simp only [body2, core2, Hom.comp_id, hdat, glueDatum, π1_quad, tagZ, π1_pair, π2_pair, Hom.comp_id,
    natZ_inj, tPi, tSigma, tPath, tIPi, tUniv, tEmpty, tGlue, if_false, show ¬ (7 = 2) by decide,
    show ¬ (7 = 3) by decide, show ¬ (7 = 4) by decide, show ¬ (7 = 5) by decide, show ¬ (7 = 6) by decide,
    show ¬ (7 = 1) by decide, or_self, if_true, cofOf_enc, Hom.id_comp]

/-- The point argument relation of an inductive type's code. -/
def dataP2 (S : Sig) (Θ : SData m) (f : Hom k m) : (k' : ℕ) → Hom k' k → ℕ → ℕ → List V → Tm → Tm → Tm → Prop :=
  fun k' g c j pre A t t' => (Comp2 S (tyLook (shapeV (Θ.restr (f.comp g))) c j pre) k' k' (Hom.id k')).el A t t'

/-- The argument types of an inductive type's code at related arguments, from the parameters `ps`
to the parameters `ps'`, at the restrictions of `σ`. -/
def argRel2 (S : Sig) (Θ : SData m) (f : Hom k m) (k' : ℕ) (σ : ISub k' k) (ps ps' : Tm) : Prop :=
  ∀ k'' (σ' : ISub k'' k') (c : ℕ) (C : Ctor) (args args' : List Tm), (dataD S Θ.idx).ctors[c]? = some C →
    args.length < C.args.length → args'.length = args.length → C.isRec args.length = false →
    (∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
      DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k'' (σ.comp σ').hom
        (.data Θ.idx (ps.isub σ')) args[j] args'[j]) →
    (∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = false →
      dataP2 S Θ f k'' (σ.comp σ').hom c j ((args.take j).map (semK S k''))
        ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList
          ((args.take j).reverse ++ (ps.isub σ').toList.reverse))
        args[j] args'[j]) →
    (Comp2 S (tyLook (shapeV (Θ.restr (f.comp (σ.comp σ').hom))) c args.length (args.map (semK S k'')))
      k'' k'' (Hom.id k'')).ty
      ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList
        (args.reverse ++ (ps.isub σ').toList.reverse))
      ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList
        (args'.reverse ++ (ps'.isub σ').toList.reverse))

theorem Comp2_dataC (Θ : SData m) (f : Hom k m) :
    Comp2 S (dataC Θ) m k f =
      ⟨fun T T' => (IsTyK S k T ∧ IsTyK S k T' ∧ semK S k T = res f (dataC Θ) ∧
          semK S k T' = res f (dataC Θ) ∧ TyEq S k T T') ∧ ∀ k' (σ : ISub k' k), ∃ ps ps',
          RedT S k' (T.isub σ) (.data Θ.idx ps) ∧ RedT S k' (T'.isub σ) (.data Θ.idx ps') ∧
          ps = Tm.ofList ps.toList ∧ ps' = Tm.ofList ps'.toList ∧
          argRel2 S Θ f k' σ ps ps' ∧ argRel2 S Θ f k' σ ps' ps ∧ argRel2 S Θ f k' σ ps ps ∧
          argRel2 S Θ f k' σ ps' ps',
        fun T t t' => EB S k T t t' ∧ semK S k t ∈ El (res f (dataC Θ)) (Hom.id k) ∧
          EB S k T t t' ∧ DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k (Hom.id k) T t t'⟩ := by
  rw [Comp2_unfold (show dataC Θ ≠ ∅ from mkKV_ne_empty _)]
  simp only [body2, core2, dataC, dat_mkKV, dataDatum, π1_quad, tagZ, π1_pair, π2_pair, Hom.comp_id,
    natZ_inj, tPi, tSigma, tPath, tIPi, tUniv, tEmpty, tGlue, tData, if_false, show ¬ (11 = 2) by decide,
    show ¬ (11 = 3) by decide, show ¬ (11 = 4) by decide, show ¬ (11 = 5) by decide, show ¬ (11 = 6) by decide,
    show ¬ (11 = 1) by decide, show ¬ (11 = 7) by decide, or_self, if_true, natOf_natZ, π1π2_quad, dataP2, argRel2]
  rfl

/-- The relations of a Glue code at a restriction: those of `T` where the face holds. -/
theorem Comp2_glueC_at {A Tp ep : V} {φ : Cof m} (hφ : φ.IsCof)
    (hTp : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h))
    (hTkv : ∀ k (f : Hom k m), (φ.restr f).holds → IsKV k (dat Tp k f)) (f : Hom k m) :
    Comp2 S (glueC m A φ Tp ep) m k f =
      if (φ.restr f).holds then Comp2 S (dat Tp k f) k k (Hom.id k)
      else Comp2 S (glueC k (res f A) (φ.restr f) (res f Tp) (res f ep)) k k (Hom.id k) := by
  rw [Comp2_eq_res (IsKV.ne_empty (isKV_glueC _ _ _ _)), res_glueC hTp hTkv hφ f]
  split <;> rfl

/-- Every pair of related types has the base clause. -/
theorem Comp2_ty_base {X : V} {f : Hom k m} {T T' : Tm} (h : (Comp2 S X m k f).ty T T') :
    X ≠ ∅ ∧ IsTyK S k T ∧ IsTyK S k T' ∧ semK S k T = res f X ∧ semK S k T' = res f X ∧ TyEq S k T T' := by
  rw [Comp2_eq] at h; unfold compF2 at h
  split at h
  · rename_i hX
    exact ⟨hX, h.1⟩
  · exact h.elim

theorem Comp2_eq_semK {X : V} {f : Hom k m} {T T' : Tm} (h : (Comp2 S X m k f).ty T T') :
    Comp2 S X m k f = Comp2 S (semK S k T) k k (Hom.id k) := by
  obtain ⟨hX, -, -, hs, -⟩ := Comp2_ty_base h
  rw [hs, Comp2_eq_res hX]

end

end Model.Whnf
