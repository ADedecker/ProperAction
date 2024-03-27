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

variable {G X Y Z W : Type*} [g : Group G] [MulAction G X] [MulAction G Y]
variable [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]

@[to_additive]
instance [ProperSMul G X] : ContinuousSMul G X where
  continuous_smul := (isProperMap_smul_pair G X).continuous.fst

/-!
### Some typical cases of proper actions
-/

open Filter Topology

/-
Proof:
We use the criterion:
X/G is T2 if the diagonal
Δ is closed in X/G × X/G.
To use the criterion,
we use that
1. the graph R of the relation induced by G
is closed X × X, by the properness assumption.
2. The product
π × π : X × X → X/G × X/G
is a QuotientMap
3. R = π × π ^-1 (Δ),
so R is closed iff Δ is closed.

To show that π × π is a QuotientMap,
we use the
lemma IsOpenMap.to_quotientMap: Continuous, surjctive and open (CSO)
implies QuotientMap
and the fact a QuotientMap whiches comes
from the relation induced by a group action
is moreover open,
and the fact that CSO is table by product.

-/
theorem t2Space_of_ProperSMul (hproper:ProperSMul G X) :
  T2Space (Quotient (MulAction.orbitRel G X)) := by
  rw [t2_iff_isClosed_diagonal] -- T2 if the diagonal is closed
  set R := MulAction.orbitRel G X -- the orbit relation
  set XmodG := Quotient R -- the quotient
  set π : X → XmodG := Quotient.mk' -- the projection
  have hpiopen: IsOpenMap π := by -- the projection is open
    apply isOpenMap_quotient_mk'_mul
  have picont : Continuous π := continuous_quotient_mk' -- π is continuous
  have pisurj : Function.Surjective π := by apply surjective_quotient_mk' -- π is surjective
  have piquotient: QuotientMap π := by -- π is a QuotientMap ! shoud be already done somewhere
    rw [QuotientMap]
    constructor
    apply surjective_quotient_mk'
    rfl
  set pipi := Prod.map π π
  have pipiopen : IsOpenMap pipi := IsOpenMap.prod hpiopen hpiopen -- π × π open
  have pipisurj : (Function.Surjective (pipi) ) :=  -- π × π surj
    Function.Surjective.Prod_map pisurj pisurj
  have pipipquotient := -- π × π is q QuotientMap because open, continuous and surj
    IsOpenMap.to_quotientMap pipiopen (Continuous.prod_map picont picont) pipisurj
  rw [<-QuotientMap.isClosed_preimage pipipquotient] -- closed iff preimage closed
  set gr' := pipi ⁻¹' Set.diagonal (Quotient R) -- preimage of the diag
  set m : G × X → X × X := fun (g,x) => (g • x, x)
  set gr := Set.range m -- graph of the orbit relation
  have r_eq_r' : gr' = gr := by -- the preimage of the diag is the graph of the relation
    ext ⟨x,y ⟩
    constructor
    · intro h
      rw [Set.mem_preimage] at h
      rw [Set.mem_diagonal_iff] at h
      change (π x = π y) at h
      replace h := Quotient.exact h
      change Setoid.Rel (MulAction.orbitRel G X) x y at h
      rw [MulAction.orbitRel_apply] at h
      rw [MulAction.orbit] at h
      choose g hg using h
      simp at hg
      rw [Set.mem_range]
      use (g,y)
      change (g • y, y) = (x, y)
      simp
      assumption
    · intro h
      rw [Set.mem_range] at h
      choose gy hgy using h
      set g := gy.1
      have gy2_y : gy.2 = y := by
        apply (congr_arg Prod.snd hgy)
      have gy_x : g • y = x := by
        change (gy.1 • gy.2, gy.2) = (x,y) at hgy
        rw [gy2_y] at hgy
        simp at hgy
        exact hgy
    sorry -- gx = y => π (x) = π (y) !
  rw [r_eq_r']
  exact hproper.isProperMap_smul_pair'.isClosedMap.closed_range


 /-
 apply a continuous map g to a Tendsto
 -/
 lemma tendsto_map_cont {lx: Filter X} {f : X → Y} {g : Y → Z}  {y : Y}
  (H : Tendsto f lx (𝓝 y)) (hg: Continuous g) :
  Tendsto (g ∘ f) lx (𝓝 (g y)) := by
  --exact (hg.tendsto _).comp H
    apply Filter.Tendsto.comp _ H
    exact hg.tendsto y
    -- apply ContinuousAt.tendsto
    -- rw [continuous_iff_continuousAt] at hg
    -- specialize hg y
    -- assumption


theorem foo : ProperSMul G X ↔ (∀ ℱ : Filter (G × X), ∀ x₁ x₂ : X,
    ClusterPt (x₁, x₂) (map (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) ℱ) →
    ∃ g : G, x₁ = g • x₂ ∧ ClusterPt g (map Prod.fst ℱ)) :=
  sorry

theorem foo_ultrafilter [T2Space X]:
ProperSMul G X ↔ ContinuousSMul G X ∧ (∀ ℱ : Ultrafilter (G × X), ∀ x₁ x₂ : X,
    Tendsto (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) ℱ (𝓝 (x₁, x₂)) →
    ∃ g : G, Tendsto Prod.fst (ℱ : Filter (G × X)) (𝓝 g)) := by
    constructor
    · sorry
    · intro ⟨hcont,hconv⟩
      apply ProperSMul.mk
      rw [isProperMap_iff_ultrafilter]
      constructor
      · continuity
      · intro 𝒰 ⟨x1,x2⟩ h
        specialize hconv 𝒰
        specialize hconv x1 x2
        specialize hconv h
        choose g htendsto using hconv
        have hproj := tendsto_map_cont h (continuous_snd)
        rw [Function.comp] at hproj
        simp at hproj
        use (g,x2)
        have uconv: 𝒰 ≤ 𝓝 (g, x2) := by
          rw [nhds_prod_eq]
          rw [Filter.le_prod]
          constructor
          assumption
          assumption
        constructor
        · simp
          change Tendsto (fun x => x) (↑𝒰) (𝓝 (g, x2)) at uconv
          have uconvmult := tendsto_map_cont uconv (hcont.continuous_smul)
          rw [Function.comp] at uconvmult
          simp at uconvmult
          have hproj1 := tendsto_map_cont h (continuous_fst)
          rw [Function.comp] at hproj1
          simp at hproj1
          apply tendsto_nhds_unique uconvmult hproj1
        · assumption

/-
Lemma: "ClusterPt x lx -> ClusterPt (f x) (f lx)"
slighlty easier to use version of ClusterPt.map
-/
lemma map_cluster {lx: Filter X} {f : X → Y}  {x : X} (H : ClusterPt x lx) (hf: Continuous f):
  ClusterPt (f x) (map f lx) := by
  apply ClusterPt.map H
  · rw [continuous_iff_continuousAt] at hf
    specialize hf x
    assumption
  · rw [Tendsto]


theorem proper_product_florestan
[ProperSMul G X] [ContinuousSMul G Y] [T2Space (X × Y)]:
ProperSMul G (X × Y) := by
    rw [foo_ultrafilter]
    intro ℱ z1 z2 h
    set proj : (X × Y) × (X × Y) -> X × X :=
      fun z => (z.1.1, z.2.1)
    have proj_cont:(Continuous proj) := by
      fun_prop
    replace h := tendsto_map_cont h proj_cont
    rw [Function.comp] at h
    set proj_gx : (G × X × Y) → (G × X) := fun (g,x,_) => (g,x)
    set act : (G × X) -> (X × X) := fun (g,x) => (g • x, x)
    have commut : (fun (x: G × X × Y) => proj (x.1 • x.2, x.2)) = act ∘ proj_gx := by rfl
    rw [commut] at h
    rw [<-Filter.tendsto_map'_iff] at h
    have actproper : IsProperMap act := isProperMap_smul_pair G X
    have ⟨⟨g,x⟩,⟨heq,hconv⟩⟩ :=
      IsProperMap.ultrafilter_le_nhds_of_tendsto (𝒰 := Ultrafilter.map proj_gx ℱ) actproper h
    have hconvproj := tendsto_map_cont (hconv) (continuous_fst)
    use g
    exact hconvproj














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
