import Mathlib.Topology.Constructions

example {X Y A B : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] (f : A → X) (g : B → Y)
    (hf : ClosedEmbedding f) (hg : ClosedEmbedding g) :
    ClosedEmbedding (Prod.map f g) := by
  refine ⟨hf.toEmbedding.prod_map hg.toEmbedding, ?_⟩
  rw [Set.range_prod_map]
  exact hf.isClosed_range.prod hg.isClosed_range
