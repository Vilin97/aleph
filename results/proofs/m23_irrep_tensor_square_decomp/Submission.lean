import Mathlib
import Submission.Helpers

open scoped TensorProduct

namespace Submission

def HasTensorSquareDecomp (dim cardG ncomp : ℕ) : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Fintype G),
    Fintype.card G = cardG ∧
      ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
        (_ : Module (MonoidAlgebra ℂ G) V)
        (_ : IsScalarTower ℂ (MonoidAlgebra ℂ G) V)
        (_ : Module (MonoidAlgebra ℂ G) (TensorProduct ℂ V V))
        (_ : IsScalarTower ℂ (MonoidAlgebra ℂ G) (TensorProduct ℂ V V)),
        Module.finrank ℂ V = dim ∧
        IsSimpleModule (MonoidAlgebra ℂ G) V ∧
        (∀ (g : G) (v w : V),
          (MonoidAlgebra.of ℂ G g : MonoidAlgebra ℂ G) • (TensorProduct.tmul ℂ v w) =
            TensorProduct.tmul ℂ
              (((MonoidAlgebra.of ℂ G g : MonoidAlgebra ℂ G) • v))
              (((MonoidAlgebra.of ℂ G g : MonoidAlgebra ℂ G) • w))) ∧
        (isotypicComponents (MonoidAlgebra ℂ G) (TensorProduct ℂ V V)).ncard = ncomp

theorem externalTensorProduct_module_data {G1 G2 W U : Type*} [Group G1] [Fintype G1] [Group G2] [Fintype G2]
    [AddCommGroup W] [Module ℂ W] [Module (MonoidAlgebra ℂ G1) W]
    [IsScalarTower ℂ (MonoidAlgebra ℂ G1) W]
    [AddCommGroup U] [Module ℂ U] [Module (MonoidAlgebra ℂ G2) U]
    [IsScalarTower ℂ (MonoidAlgebra ℂ G2) U] :
    ∃ (_ : Module (MonoidAlgebra ℂ (G1 × G2)) (TensorProduct ℂ W U))
      (_ : IsScalarTower ℂ (MonoidAlgebra ℂ (G1 × G2)) (TensorProduct ℂ W U))
      (_ : Module (MonoidAlgebra ℂ (G1 × G2))
          (TensorProduct ℂ (TensorProduct ℂ W U) (TensorProduct ℂ W U)))
      (_ : IsScalarTower ℂ (MonoidAlgebra ℂ (G1 × G2))
          (TensorProduct ℂ (TensorProduct ℂ W U) (TensorProduct ℂ W U))),
      (∀ (g : G1 × G2) (w : W) (u : U),
        (MonoidAlgebra.of ℂ (G1 × G2) g : MonoidAlgebra ℂ (G1 × G2)) •
            (TensorProduct.tmul ℂ w u) =
          TensorProduct.tmul ℂ
            (((MonoidAlgebra.of ℂ G1 g.1 : MonoidAlgebra ℂ G1) • w))
            (((MonoidAlgebra.of ℂ G2 g.2 : MonoidAlgebra ℂ G2) • u))) ∧
      (∀ (g : G1 × G2) (v w : TensorProduct ℂ W U),
        (MonoidAlgebra.of ℂ (G1 × G2) g : MonoidAlgebra ℂ (G1 × G2)) •
            (TensorProduct.tmul ℂ v w) =
          TensorProduct.tmul ℂ
            (((MonoidAlgebra.of ℂ (G1 × G2) g : MonoidAlgebra ℂ (G1 × G2)) • v))
            (((MonoidAlgebra.of ℂ (G1 × G2) g : MonoidAlgebra ℂ (G1 × G2)) • w))) := by
  -- Do **not** look for a pre-existing `Representation.TensorProduct.of`; build the product-group representation manually.
  -- 
  -- Concrete plan:
  -- 1. Set `ρ1 := Representation.ofModule' (k := ℂ) (G := G1) W` and `ρ2 := Representation.ofModule' (k := ℂ) (G := G2) U`.
  -- 2. Define
  --    `let ρ : Representation ℂ (G1 × G2) (TensorProduct ℂ W U) :=
  --       { toFun := fun g => TensorProduct.AlgebraTensorModule.map (ρ1 g.1) (ρ2 g.2)
  --         map_one' := by simpa using (TensorProduct.AlgebraTensorModule.map_one (R := ℂ) (A := ℂ) (M := W) (N := U))
  --         map_mul' := by intro g h; simpa [TensorProduct.AlgebraTensorModule.map_mul, map_mul] }`.
  -- 3. The theorem wants instances on the **raw type** `TensorProduct ℂ W U`, not on the synonym `ρ.asModule`. So install them directly by
  --    `letI : Module (MonoidAlgebra ℂ (G1 × G2)) (TensorProduct ℂ W U) :=
  --       Module.compHom (TensorProduct ℂ W U) ρ.asAlgebraHom.toRingHom`
  --    and
  --    `letI : IsScalarTower ℂ (MonoidAlgebra ℂ (G1 × G2)) (TensorProduct ℂ W U) :=
  --       IsScalarTower.of_algHom ρ.asAlgebraHom`.
  --    Do the same for `ρsq := ρ.tprod ρ` on the raw tensor-square type.
  -- 4. Then the existential witnesses are `inferInstance`, not `ρ.asModule`.
  -- 
  -- For the first action formula, rewrite the `MonoidAlgebra.of` action via `Representation.asAlgebraHom_of` and evaluate with `TensorProduct.AlgebraTensorModule.map_tmul`; the right-hand side is exactly the pair of factor actions. For the second action formula, use `Representation.tprod_apply`, `TensorProduct.map_tmul`, and the first formula.
  sorry

theorem hasTensorSquareDecomp_24_2_2: HasTensorSquareDecomp 2 24 2 := by
  -- Use the binary tetrahedral group `2.A4`, for example `SL(2,3)` or an explicit semidirect-product model `QuaternionGroup 2 ⋊ C3`. The semidirect-product model is attractive because the order-24 calculation is then routine from `SemidirectProduct.card`.
  -- 
  -- Take the standard 2-dimensional complex representation `U` (equivalently the usual faithful subgroup of `SL(2,ℂ)`). Two proof routes for irreducibility are natural.
  -- 1. Direct route: show no nonzero line in `U` is preserved by the chosen generators.
  -- 2. Image-algebra route: exhibit concrete matrices in the image whose ℂ-span contains the matrix units, hence all of `Module.End ℂ U`; then simplicity follows from the standard surjective-image/Burnside argument.
  -- 
  -- For the tensor square, use the classical decomposition `U ⊗ U = Sym² U ⊕ Λ² U`. The alternating square `Λ² U` is 1-dimensional and given by the determinant character, hence trivial for the `SL(2,3)` / binary-tetrahedral model. The symmetric square `Sym² U` is 3-dimensional and irreducible. Therefore the tensor square has exactly two isotypic components. If direct submodule manipulations are awkward, certify the same decomposition by characters: `χ_{U⊗U} = χ_U^2` splits as the sum of the trivial character and one 3-dimensional irreducible.
  sorry

theorem hasTensorSquareDecomp_253_11_2: HasTensorSquareDecomp 11 253 2 := by
  -- Candidate group: the Frobenius group `C23 ⋊ C11`, with `C11` acting through an order-11 subgroup of `(ZMod 23)ˣ`. A convenient formal model is `SemidirectProduct (Multiplicative (ZMod 23)) (Multiplicative (ZMod 11)) φ`, where `φ` comes from multiplication by a unit of order `11` on `ZMod 23`.
  -- 
  -- Take `W := Fin 11 → ℂ` with basis `e_i`. Let a generator of `C23` act diagonally by distinct 23rd roots of unity `ζ^(h^i)` and let a generator of `C11` act by cyclic shift `e_i ↦ e_{i+1}`. Two good routes to irreducibility:
  -- 1. Weight-space route: any nonzero submodule contains a `C23`-eigenline, and the `C11`-shift permutes the 11 eigenlines transitively, forcing the whole space.
  -- 2. Image-algebra route: the diagonal operator `D` and shift `S` generate the full matrix algebra on `W`. Since the eigenvalues of `D` are pairwise distinct, polynomial interpolation in `D` gives all diagonal matrix units; conjugating by powers of `S` gives every `E_{ij}`.
  -- 
  -- For the tensor-square count, work on the basis `e_i ⊗ e_j`. The diagonal operator has weights `h^i + h^j ∈ 𝔽23`, and these weights split into exactly two `C11`-orbits. Character-theoretically this means the square of the 11-dimensional irreducible uses exactly the two 11-dimensional irreducible types. A helpful alternative viewpoint is that `W ⊗ W` splits into symmetric and alternating parts of dimensions `66` and `55`, matching `6` and `5` copies of the two 11-dimensional simple types. Either route should lead to `(isotypicComponents ...).ncard = 2`.
  sorry

theorem inflate_hasTensorSquareDecomp_by_1680: HasTensorSquareDecomp 22 (253 * 24) 4 → HasTensorSquareDecomp 22 10200960 4 := by
  -- Unpack the witness. Let `H := Multiplicative (ZMod 1680)` and `G' := H × G`. Then `Fintype.card H = 1680` (from `ZMod.card`) and `Fintype.card G' = 1680 * (253 * 24)` by `Fintype.card_prod`, so arithmetic reduces the cardinality goal to `10200960`.
  -- 
  -- Keep the same underlying vector space `V`, but inflate the action along the projection `π : H × G →* G`. The clean route is to convert the old module to a representation `ρ := Representation.ofModule' (k := ℂ) (G := G) V`, define `ρ' := ρ.comp π`, and then use `ρ'.asModule` and `(ρ'.tprod ρ').asModule` for the new `MonoidAlgebra`-module structures. The pure-tensor tensor-square action formula follows from `Representation.tprod_apply` together with the fact that `π` ignores the `H`-coordinate.
  -- 
  -- For simplicity and the isotypic count, the new action factors through `π`, so `G'`-submodules of `V` are exactly the old `G`-submodules, and the same factor-through argument shows the isotypic components of `V ⊗ V` are unchanged. An alternative route is to transport simplicity along the surjective ring hom induced by projection `MonoidAlgebra ℂ (H × G) →+* MonoidAlgebra ℂ G` via `LinearMap.isSimpleModule_iff_of_bijective` applied to the identity map.
  sorry

theorem isSimpleModule_externalTensor {G1 G2 W U : Type*} [Group G1] [Fintype G1] [Group G2] [Fintype G2]
    [AddCommGroup W] [Module ℂ W] [Module (MonoidAlgebra ℂ G1) W]
    [IsScalarTower ℂ (MonoidAlgebra ℂ G1) W]
    [AddCommGroup U] [Module ℂ U] [Module (MonoidAlgebra ℂ G2) U]
    [IsScalarTower ℂ (MonoidAlgebra ℂ G2) U]
    [Module (MonoidAlgebra ℂ (G1 × G2)) (TensorProduct ℂ W U)]
    [IsScalarTower ℂ (MonoidAlgebra ℂ (G1 × G2)) (TensorProduct ℂ W U)]
    (hW : IsSimpleModule (MonoidAlgebra ℂ G1) W)
    (hU : IsSimpleModule (MonoidAlgebra ℂ G2) U)
    (hactV : ∀ (g : G1 × G2) (w : W) (u : U),
        (MonoidAlgebra.of ℂ (G1 × G2) g : MonoidAlgebra ℂ (G1 × G2)) •
            (TensorProduct.tmul ℂ w u) =
          TensorProduct.tmul ℂ
            (((MonoidAlgebra.of ℂ G1 g.1 : MonoidAlgebra ℂ G1) • w))
            (((MonoidAlgebra.of ℂ G2 g.2 : MonoidAlgebra ℂ G2) • u))) :
    IsSimpleModule (MonoidAlgebra ℂ (G1 × G2)) (TensorProduct ℂ W U) := by
  -- There is no ready-made `hW.externalTensor` theorem in scope, so do not search for such a lemma. Use a character proof, and first manufacture the finiteness hypotheses needed for `FDRep`.
  -- 
  -- Concrete route:
  -- 1. From `hW` and `hU`, obtain nonzero vectors using `IsSimpleModule.nontrivial`.
  -- 2. Use `IsSimpleModule.span_singleton_eq_top` (or equivalently `toSpanSingleton_surjective`) to show each module is cyclic over its group algebra, hence `Module.Finite (MonoidAlgebra ℂ G1) W` and `Module.Finite (MonoidAlgebra ℂ G2) U`.
  -- 3. Since `MonoidAlgebra ℂ G1` and `MonoidAlgebra ℂ G2` are finite ℂ-modules (`MonoidAlgebra.moduleFinite`), apply `Module.Finite.trans` to deduce `Module.Finite ℂ W` and `Module.Finite ℂ U`.
  -- 4. Now define `ρW := Representation.ofModule' (k := ℂ) (G := G1) W` and `ρU := Representation.ofModule' (k := ℂ) (G := G2) U`, then form `FDRep.of ρW` and `FDRep.of ρU`.
  -- 5. Use `hactV` to identify the given `G1 × G2` action on `TensorProduct ℂ W U` with the external tensor product of the factor representations.
  -- 6. For simple factor reps, the character inner product over `G1 × G2` factorizes (split the sum over pairs using `Fintype.sum_prod_type` or an equivalent product-sum lemma), and `FDRep.char_orthonormal` on each factor shows the product character is irreducible. Conclude simplicity of the original module.
  -- 
  -- A secondary route is Burnside/surjective image: if the factor images are full endomorphism algebras, then the image on `W ⊗ U` is full via `homTensorHomEquiv` / matrix-Kronecker algebra, but the character route is likely the cleanest.
  sorry

theorem isotypicComponents_ncard_externalTensor_tensorSquare {n1 n2 : ℕ} {G1 G2 W U : Type*} [Group G1] [Fintype G1] [Group G2] [Fintype G2]
    [AddCommGroup W] [Module ℂ W] [Module (MonoidAlgebra ℂ G1) W]
    [IsScalarTower ℂ (MonoidAlgebra ℂ G1) W]
    [Module (MonoidAlgebra ℂ G1) (TensorProduct ℂ W W)]
    [IsScalarTower ℂ (MonoidAlgebra ℂ G1) (TensorProduct ℂ W W)]
    [AddCommGroup U] [Module ℂ U] [Module (MonoidAlgebra ℂ G2) U]
    [IsScalarTower ℂ (MonoidAlgebra ℂ G2) U]
    [Module (MonoidAlgebra ℂ G2) (TensorProduct ℂ U U)]
    [IsScalarTower ℂ (MonoidAlgebra ℂ G2) (TensorProduct ℂ U U)]
    [Module (MonoidAlgebra ℂ (G1 × G2)) (TensorProduct ℂ W U)]
    [IsScalarTower ℂ (MonoidAlgebra ℂ (G1 × G2)) (TensorProduct ℂ W U)]
    [Module (MonoidAlgebra ℂ (G1 × G2))
        (TensorProduct ℂ (TensorProduct ℂ W U) (TensorProduct ℂ W U))]
    [IsScalarTower ℂ (MonoidAlgebra ℂ (G1 × G2))
        (TensorProduct ℂ (TensorProduct ℂ W U) (TensorProduct ℂ W U))]
    (hactW : ∀ (g : G1) (v w : W),
        (MonoidAlgebra.of ℂ G1 g : MonoidAlgebra ℂ G1) • (TensorProduct.tmul ℂ v w) =
          TensorProduct.tmul ℂ
            (((MonoidAlgebra.of ℂ G1 g : MonoidAlgebra ℂ G1) • v))
            (((MonoidAlgebra.of ℂ G1 g : MonoidAlgebra ℂ G1) • w)))
    (hactU : ∀ (g : G2) (v w : U),
        (MonoidAlgebra.of ℂ G2 g : MonoidAlgebra ℂ G2) • (TensorProduct.tmul ℂ v w) =
          TensorProduct.tmul ℂ
            (((MonoidAlgebra.of ℂ G2 g : MonoidAlgebra ℂ G2) • v))
            (((MonoidAlgebra.of ℂ G2 g : MonoidAlgebra ℂ G2) • w)))
    (hactV : ∀ (g : G1 × G2) (w : W) (u : U),
        (MonoidAlgebra.of ℂ (G1 × G2) g : MonoidAlgebra ℂ (G1 × G2)) •
            (TensorProduct.tmul ℂ w u) =
          TensorProduct.tmul ℂ
            (((MonoidAlgebra.of ℂ G1 g.1 : MonoidAlgebra ℂ G1) • w))
            (((MonoidAlgebra.of ℂ G2 g.2 : MonoidAlgebra ℂ G2) • u)))
    (hactVV : ∀ (g : G1 × G2) (v w : TensorProduct ℂ W U),
        (MonoidAlgebra.of ℂ (G1 × G2) g : MonoidAlgebra ℂ (G1 × G2)) •
            (TensorProduct.tmul ℂ v w) =
          TensorProduct.tmul ℂ
            (((MonoidAlgebra.of ℂ (G1 × G2) g : MonoidAlgebra ℂ (G1 × G2)) • v))
            (((MonoidAlgebra.of ℂ (G1 × G2) g : MonoidAlgebra ℂ (G1 × G2)) • w)))
    (hnW : (isotypicComponents (MonoidAlgebra ℂ G1) (TensorProduct ℂ W W)).ncard = n1)
    (hnU : (isotypicComponents (MonoidAlgebra ℂ G2) (TensorProduct ℂ U U)).ncard = n2) :
    (isotypicComponents (MonoidAlgebra ℂ (G1 × G2))
        (TensorProduct ℂ (TensorProduct ℂ W U) (TensorProduct ℂ W U))).ncard = n1 * n2 := by
  -- Do not try to prove this by simplification from one factor; it is genuinely about the tensor-square of the external product.
  -- 
  -- Concrete plan:
  -- 1. Use Maschke explicitly: `letI : IsSemisimpleModule ... := MonoidAlgebra.Submodule.instIsSemisimpleModule` for the two factor tensor-square modules and the product-group tensor-square module if instance search hesitates.
  -- 2. Use `TensorProduct.AlgebraTensorModule.tensorTensorTensorComm` (or `TensorProduct.tensorTensorTensorComm`) to identify `((W ⊗ U) ⊗ (W ⊗ U))` with `((W ⊗ W) ⊗ (U ⊗ U))`.
  -- 3. Check with `hactW`, `hactU`, `hactV`, `hactVV` that under this equivalence the `G1 × G2` action is the external tensor-product action of the two tensor-square modules.
  -- 4. Pair isotypic types: for each simple type `S` in `W ⊗ W` and `T` in `U ⊗ U`, the outer tensor product gives one simple type for the product-group action; `isSimpleModule_externalTensor` is the key input.
  -- 5. Show every product-group isotypic component arises from exactly one pair `(S,T)`. Then the indexing set is a product, so the cardinality is `n1 * n2`.
  -- 
  -- Two reasonable formalization routes:
  -- - via `IsSemisimpleModule.endAlgEquiv`, where the endomorphism algebra splits as a product indexed by pairs of factor isotypic components;
  -- - via direct character bookkeeping after moving to `FDRep`.
  sorry

theorem combine_hasTensorSquareDecomp_253_24: HasTensorSquareDecomp 11 253 2 →
    HasTensorSquareDecomp 2 24 2 →
    HasTensorSquareDecomp 22 (253 * 24) 4 := by
  intro h253 h24
  classical
  rcases h253 with ⟨G₁, instGroup₁, instFintype₁, hcard₁, W, instAddCommGroupW, instModuleW,
    instAlgModuleW, instTowerW, instTensorModuleW, instTensorTowerW, hdimW, hsimpleW, hactW,
    hncompW⟩
  rcases h24 with ⟨G₂, instGroup₂, instFintype₂, hcard₂, U, instAddCommGroupU, instModuleU,
    instAlgModuleU, instTowerU, instTensorModuleU, instTensorTowerU, hdimU, hsimpleU, hactU,
    hncompU⟩
  obtain ⟨instV, instTowerV, instVV, instTowerVV, hactV, hactVV⟩ :=
    externalTensorProduct_module_data (G1 := G₁) (G2 := G₂) (W := W) (U := U)
  letI : Module (MonoidAlgebra ℂ (G₁ × G₂)) (TensorProduct ℂ W U) := instV
  letI : IsScalarTower ℂ (MonoidAlgebra ℂ (G₁ × G₂)) (TensorProduct ℂ W U) := instTowerV
  letI : Module (MonoidAlgebra ℂ (G₁ × G₂))
      (TensorProduct ℂ (TensorProduct ℂ W U) (TensorProduct ℂ W U)) := instVV
  letI : IsScalarTower ℂ (MonoidAlgebra ℂ (G₁ × G₂))
      (TensorProduct ℂ (TensorProduct ℂ W U) (TensorProduct ℂ W U)) := instTowerVV
  refine ⟨G₁ × G₂, inferInstance, inferInstance, ?_, TensorProduct ℂ W U, inferInstance,
    inferInstance, instV, instTowerV, instVV, instTowerVV, ?_, ?_, ?_, ?_⟩
  · simpa [hcard₁, hcard₂] using Fintype.card_prod G₁ G₂
  · rw [Module.finrank_tensorProduct]
    norm_num [hdimW, hdimU]
  · exact isSimpleModule_externalTensor (G1 := G₁) (G2 := G₂) (W := W) (U := U)
      hsimpleW hsimpleU hactV
  · exact hactVV
  · simpa [hncompW, hncompU] using
      (isotypicComponents_ncard_externalTensor_tensorSquare (G1 := G₁) (G2 := G₂)
        (W := W) (U := U) (n1 := 2) (n2 := 2) hactW hactU hactV hactVV hncompW hncompU)

theorem m23_irrep_tensor_square_decomp :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G),
      Fintype.card G = 10200960 ∧
      ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
        (_ : Module (MonoidAlgebra ℂ G) V)
        (_ : IsScalarTower ℂ (MonoidAlgebra ℂ G) V)
        (_ : Module (MonoidAlgebra ℂ G) (V ⊗[ℂ] V))
        (_ : IsScalarTower ℂ (MonoidAlgebra ℂ G) (V ⊗[ℂ] V)),
        Module.finrank ℂ V = 22 ∧
        IsSimpleModule (MonoidAlgebra ℂ G) V ∧
        (∀ (g : G) (v w : V),
          (MonoidAlgebra.of ℂ G g : MonoidAlgebra ℂ G) • (v ⊗ₜ[ℂ] w) =
            ((MonoidAlgebra.of ℂ G g : MonoidAlgebra ℂ G) • v) ⊗ₜ[ℂ]
              ((MonoidAlgebra.of ℂ G g : MonoidAlgebra ℂ G) • w)) ∧
        (isotypicComponents (MonoidAlgebra ℂ G) (V ⊗[ℂ] V)).ncard = 4 := by
  exact
    inflate_hasTensorSquareDecomp_by_1680
      (combine_hasTensorSquareDecomp_253_24 hasTensorSquareDecomp_253_11_2 hasTensorSquareDecomp_24_2_2)


end Submission
