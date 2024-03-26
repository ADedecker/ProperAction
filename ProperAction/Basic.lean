import ProperAction.ProperMaps
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.PUnitInstances

/-!
# Proper group actions
-/

set_option autoImplicit false

@[mk_iff]
class ProperVAdd (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [AddGroup G]
    [AddAction G X] : Prop where
  isProperMap_vadd_pair' : IsProperMap (fun gx ↦ ⟨gx.1 +ᵥ gx.2, gx.2⟩ : G × X → X × X)
-- isProperMap_vadd_pair' : IsProperMap (fun (g, x) ↦ ⟨g +ᵥ x, x⟩ : G × X → X × X)

@[to_additive, mk_iff]
class ProperSMul (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [Group G]
    [MulAction G X] : Prop where
  isProperMap_smul_pair' : IsProperMap (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X)
-- isProperMap_smul_pair' : IsProperMap (fun (g, x) ↦ ⟨g • x, x⟩ : G × X → X × X)

@[to_additive]
lemma isProperMap_smul_pair (G X : Type*) [Group G] [MulAction G X]
    [TopologicalSpace G] [TopologicalSpace X] [ProperSMul G X] :
    IsProperMap (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) :=
  ProperSMul.isProperMap_smul_pair'

#check properSMul_iff
#check properVAdd_iff

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
variable [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace Y]

@[to_additive]
instance [ProperSMul G X] : ContinuousSMul G X where
  continuous_smul := (isProperMap_smul_pair G X).continuous.fst

/-!
### Some typical cases of proper actions
-/

instance [ProperSMul G X] [ContinuousSMul G Y] : ProperSMul G (X × Y) where
  isProperMap_smul_pair' := by
    constructor
    · rw [continuous_prod_mk]
      constructor
      apply Continuous.smul
      apply continuous_fst
      apply continuous_snd
      apply continuous_snd
    · intro F y h
      have : MapClusterPt (y.1.1, y.2.1) F (fun gxy => (gxy.1 • gxy.2.1, gxy.2.1)) := by sorry
      sorry

open Filter Topology


theorem foo_ultrafilter : ProperSMul G X ↔ ContinuousSMul G X ∧ (∀ 𝒰 : Ultrafilter (G × X), ∀ x₁ x₂ : X,
    Tendsto (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) 𝒰 (𝓝 (x₁, x₂)) →
    ∃ g : G, g • x₂ = x₁ ∧ Tendsto Prod.fst (𝒰 : Filter (G × X)) (𝓝 g)) := by
  constructor
  · intro h
    constructor
    infer_instance
    intro 𝒰 x₁ x₂ h'
    rw [properSMul_iff, isProperMap_iff_ultrafilter] at h
    have ⟨(g, x), hgx1, hgx2⟩ := h.2 h'
    use g
    constructor
    · have : x = x₂ :=
        calc
          x = (g • x, x).2 := rfl
          _ = (x₁, x₂).2 := by rw [hgx1]
          _ = x₂ := rfl
      calc
        g • x₂ = g • x := by rw[← this]
        _ = (g • x, x).1 := rfl
        _ = (x₁, x₂).1 := by rw [hgx1]
        _ = x₁ := rfl
    · have := continuous_fst.tendsto (g, x)
      rw [Tendsto] at *
      calc
        map Prod.fst ↑𝒰 ≤ map Prod.fst (𝓝 (g, x)) := map_le_map hgx2
        _ ≤ 𝓝 (g, x).1 := this
  · rintro ⟨cont, h⟩
    constructor
    rw [isProperMap_iff_ultrafilter]
    constructor
    · rw [continuous_prod_mk]
      constructor
      continuity
      apply continuous_snd
    · intro 𝒰 (x₁, x₂) hxx
      rcases h 𝒰 x₁ x₂ hxx with ⟨g, hg1, hg2⟩
      use (g, x₂)
      constructor
      · rw [hg1]
      · rw [nhds_prod_eq, 𝒰.le_prod]
        constructor
        · assumption
        · change Tendsto (Prod.snd ∘ (fun gx : G × X ↦ (gx.1 • gx.2, gx.2))) ↑𝒰 (𝓝 (Prod.snd (x₁, x₂)))
          apply Filter.Tendsto.comp
          apply Continuous.tendsto
          exact continuous_snd
          assumption


theorem foo_ultrafilter_t2 [T2Space X] : ProperSMul G X ↔ ContinuousSMul G X ∧ (∀ 𝒰 : Ultrafilter (G × X), ∀ x₁ x₂ : X,
    Tendsto (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) 𝒰 (𝓝 (x₁, x₂)) →
    ∃ g : G, Tendsto Prod.fst (𝒰 : Filter (G × X)) (𝓝 g)) := by
  constructor
  · intro h
    constructor
    infer_instance
    intro 𝒰 x₁ x₂ h'
    rw [properSMul_iff, isProperMap_iff_ultrafilter_of_t2] at h
    have ⟨(g, x), hgx⟩ := h.2 h'
    use g
    have := continuous_fst.tendsto (g, x)
    rw [Tendsto] at *
    calc
      map Prod.fst ↑𝒰 ≤ map Prod.fst (𝓝 (g, x)) := map_le_map hgx
      _ ≤ 𝓝 (g, x).1 := this
  · rintro ⟨cont, h⟩
    constructor
    rw [isProperMap_iff_ultrafilter_of_t2]
    constructor
    · rw [continuous_prod_mk]
      constructor
      apply Continuous.smul
      apply continuous_fst
      apply continuous_snd
      apply continuous_snd
    · intro 𝒰 (x₁, x₂) hxx
      rcases h 𝒰 x₁ x₂ hxx with ⟨g, hg⟩
      use (g, x₂)
      rw [nhds_prod_eq, 𝒰.le_prod]
      constructor
      · assumption
      · change Tendsto (Prod.snd ∘ (fun gx : G × X ↦ (gx.1 • gx.2, gx.2))) ↑𝒰 (𝓝 (Prod.snd (x₁, x₂)))
        apply Filter.Tendsto.comp
        apply Continuous.tendsto
        exact continuous_snd
        assumption


instance [ProperSMul G X] [ContinuousSMul G X]: ProperSMul G (X × Y) where
  isProperMap_smul_pair' := sorry

instance {ι : Type*} {X : ι → Type*} [Π i, TopologicalSpace (X i)] [Π i, MulAction G (X i)]
    [∀ i, ProperSMul G (X i)] : ProperSMul G (Π i, X i) where
  isProperMap_smul_pair' := sorry

instance {H : Subgroup G} [ProperSMul G X] [IsClosed (H : Set G)] : ProperSMul H X where
  isProperMap_smul_pair' := sorry

-- for the one above, we may want to use this, or some variation of it:
example {H : Type*} [Group H] [MulAction H X] [TopologicalSpace H] [ProperSMul G X]
    (f : H →* G) (f_clemb : ClosedEmbedding f) (f_compat : ∀ (h : H) (x : X), f h • x = h • x) :
    ProperSMul H X where
  isProperMap_smul_pair' := sorry

-- Some things to generalize
#check t2Space_of_properlyDiscontinuousSMul_of_t2Space
#check Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite
