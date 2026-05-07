import Mathlib
import Submission.Helpers

namespace Submission

def vn_diagOperator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (n : ℕ) (A : H →L[ℂ] H) : (Fin n → H) →L[ℂ] (Fin n → H) :=
  ContinuousLinearMap.piMap fun _ : Fin n => A

def vn_diagPiLpOperator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (n : ℕ) (A : H →L[ℂ] H) :
    PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  let e : PiLp 2 (fun _ : Fin n => H) ≃L[ℂ] (Fin n → H) :=
    PiLp.continuousLinearEquiv (p := 2) ℂ (fun _ : Fin n => H)
  ∑ i : Fin n,
    (((e.symm.toContinuousLinearMap ∘L ContinuousLinearMap.single ℂ (fun _ : Fin n => H) i) ∘L A) ∘L
      PiLp.proj (p := 2) (𝕜 := ℂ) (β := fun _ : Fin n => H) i)

def vn_doubleCommutantSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))

theorem vn_diagOperator_mem_doubleCommutant {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (n : ℕ) {x : H →L[ℂ] H}
    (hx : x ∈ vn_doubleCommutantSet S) :
    vn_diagOperator n x ∈ Set.centralizer
      (Set.centralizer ((fun A : H →L[ℂ] H => vn_diagOperator n A) '' (S : Set (H →L[ℂ] H)))) := by
  unfold vn_doubleCommutantSet at hx
  rw [Set.mem_centralizer_iff] at hx ⊢
  intro B hB
  rw [Set.mem_centralizer_iff] at hB
  have hproj (A : H →L[ℂ] H) (i : Fin n) :
      (ContinuousLinearMap.proj i).comp (vn_diagOperator n A) =
        A.comp (ContinuousLinearMap.proj i) := by
    ext v
    simp [vn_diagOperator]
  have hsingle (A : H →L[ℂ] H) (j : Fin n) :
      (vn_diagOperator n A).comp (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j) =
        (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j).comp A := by
    ext y k
    by_cases hk : k = j
    · subst hk
      simp [vn_diagOperator]
    · simp [vn_diagOperator, hk]
  have hcoeff_mem (i j : Fin n) :
      ((ContinuousLinearMap.proj i).comp B).comp
          (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j) ∈
        Set.centralizer (S : Set (H →L[ℂ] H)) := by
    rw [Set.mem_centralizer_iff]
    intro A hA
    have hcomm : (vn_diagOperator n A).comp B = B.comp (vn_diagOperator n A) := by
      simpa using hB (vn_diagOperator n A) ⟨A, hA, rfl⟩
    have hcomm' := congrArg
      (fun T => ((ContinuousLinearMap.proj i).comp T).comp
        (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j)) hcomm
    simpa [ContinuousLinearMap.comp_assoc, hproj, hsingle] using hcomm'
  have hcoeff_comm (i j : Fin n) :
      (((ContinuousLinearMap.proj i).comp B).comp
          (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j)).comp x =
        x.comp (((ContinuousLinearMap.proj i).comp B).comp
          (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j)) := by
    simpa using hx _ (hcoeff_mem i j)
  change B.comp (vn_diagOperator n x) = (vn_diagOperator n x).comp B
  ext v i
  have hsum_left :=
    ContinuousLinearMap.sum_comp_single
      (L := (ContinuousLinearMap.proj i).comp (B.comp (vn_diagOperator n x))) (v := v)
  have hsum_right :=
    ContinuousLinearMap.sum_comp_single
      (L := (ContinuousLinearMap.proj i).comp ((vn_diagOperator n x).comp B)) (v := v)
  calc
    ((B.comp (vn_diagOperator n x)) v) i
        = ((ContinuousLinearMap.proj i).comp (B.comp (vn_diagOperator n x))) v := by
            rfl
    _ = ((ContinuousLinearMap.proj i).comp ((vn_diagOperator n x).comp B)) v := by
      rw [← hsum_left, ← hsum_right]
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hcomp :
          (((ContinuousLinearMap.proj i).comp (B.comp (vn_diagOperator n x))).comp
              (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j)) =
            (((ContinuousLinearMap.proj i).comp ((vn_diagOperator n x).comp B)).comp
              (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j)) := by
        calc
          (((ContinuousLinearMap.proj i).comp (B.comp (vn_diagOperator n x))).comp
              (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j))
              = ((((ContinuousLinearMap.proj i).comp B).comp
                    (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j)).comp x) := by
                  simp [ContinuousLinearMap.comp_assoc, hsingle]
          _ = x.comp (((ContinuousLinearMap.proj i).comp B).comp
                (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j)) := by
                  exact hcoeff_comm i j
          _ = (((ContinuousLinearMap.proj i).comp ((vn_diagOperator n x).comp B)).comp
                (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j)) := by
                  have hmid :
                      x.comp ((ContinuousLinearMap.proj i).comp B) =
                        (ContinuousLinearMap.proj i).comp ((vn_diagOperator n x).comp B) := by
                    calc
                      x.comp ((ContinuousLinearMap.proj i).comp B)
                          = (x.comp (ContinuousLinearMap.proj i)).comp B := by
                              rw [← ContinuousLinearMap.comp_assoc]
                      _ = ((ContinuousLinearMap.proj i).comp (vn_diagOperator n x)).comp B := by
                              rw [← hproj x i]
                      _ = (ContinuousLinearMap.proj i).comp ((vn_diagOperator n x).comp B) := by
                              rw [ContinuousLinearMap.comp_assoc]
                  exact congrArg
                    (fun T => T.comp (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j)) hmid
      exact congrArg (fun T => T (v j)) hcomp
    _ = (((vn_diagOperator n x).comp B) v) i := by
      rfl

def vn_pointwiseImage {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (PointwiseConvergenceCLM (RingHom.id ℂ) H H) :=
  ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
    (S : Set (H →L[ℂ] H))

def vn_tupleOrbit {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (n : ℕ) (v : Fin n → H) : Set (Fin n → H) :=
  (fun A : H →L[ℂ] H => fun i : Fin n => A (v i)) '' (S : Set (H →L[ℂ] H))

def vn_tupleOrbitPiLpSubmodule {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (n : ℕ) (v : Fin n → H) :
    Submodule ℂ (PiLp 2 (fun _ : Fin n => H)) where
  carrier := (fun A : H →L[ℂ] H => WithLp.toLp 2 (fun i : Fin n => A (v i))) '' (S : Set (H →L[ℂ] H))
  zero_mem' := by
    refine ⟨0, S.zero_mem, ?_⟩
    ext i
    simp
  add_mem' := by
    rintro x y ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
    refine ⟨A + B, S.add_mem hA hB, ?_⟩
    ext i
    simp
  smul_mem' := by
    rintro c x ⟨A, hA, rfl⟩
    refine ⟨c • A, S.smul_mem hA c, ?_⟩
    ext i
    simp

theorem vn_bicommutant_tuple_mem_closure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (n : ℕ) (v : Fin n → H)
    {x : H →L[ℂ] H} (hx : x ∈ vn_doubleCommutantSet S) :
    (fun i : Fin n => x (v i)) ∈ closure (vn_tupleOrbit S n v) := by
  classical
  let K := PiLp 2 (fun _ : Fin n => H)
  let e : K ≃L[ℂ] (Fin n → H) := PiLp.continuousLinearEquiv (p := 2) ℂ (fun _ : Fin n => H)
  let π (A : H →L[ℂ] H) : K →L[ℂ] K :=
    e.symm.toContinuousLinearMap ∘L vn_diagOperator n A ∘L e.toContinuousLinearMap
  let M0 : Submodule ℂ K := vn_tupleOrbitPiLpSubmodule S n v
  let M : Submodule ℂ K := M0.topologicalClosure
  have hπ_apply (A : H →L[ℂ] H) (w : K) : π A w = WithLp.toLp 2 (fun i => A (w i)) := by
    apply PiLp.ext
    intro i
    change WithLp.ofLp (e.symm (vn_diagOperator n A (e w))) i = A (w i)
    rw [PiLp.coe_symm_continuousLinearEquiv]
    rw [WithLp.ofLp_toLp]
    rw [PiLp.coe_continuousLinearEquiv]
    simp [π, vn_diagOperator]
  have hM0_mem (A : H →L[ℂ] H) (hA : A ∈ S) : WithLp.toLp 2 (fun i : Fin n => A (v i)) ∈ M0 := by
    exact ⟨A, hA, rfl⟩
  have hvM0 : WithLp.toLp 2 v ∈ M0 := by
    simpa using hM0_mem 1 S.one_mem
  have hπ_map_M0 (A : H →L[ℂ] H) (hA : A ∈ S) : Set.MapsTo (π A) (M0 : Set K) (M0 : Set K) := by
    intro w hw
    rcases hw with ⟨B, hB, rfl⟩
    refine ⟨A * B, S.mul_mem hA hB, ?_⟩
    apply PiLp.ext
    intro i
    simp [hπ_apply, ContinuousLinearMap.mul_apply]
  have hM_closed : IsClosed (M : Set K) := Submodule.isClosed_topologicalClosure M0
  have hM0_le_M : M0 ≤ M := Submodule.le_topologicalClosure M0
  have hπ_map_M (A : H →L[ℂ] H) (hA : A ∈ S) : Set.MapsTo (π A) (M : Set K) (M : Set K) := by
    have h0 : Set.MapsTo (π A) (M0 : Set K) (M : Set K) := by
      intro y hy
      exact hM0_le_M (hπ_map_M0 A hA hy)
    simpa [M, Submodule.topologicalClosure_coe] using
      (Set.MapsTo.closure_left h0 (π A).continuous hM_closed)
  have hπ_star (A : H →L[ℂ] H) : ContinuousLinearMap.adjoint (π A) = π (star A) := by
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff (A := π (star A)) (B := π A)).2
    intro w z
    rw [hπ_apply, hπ_apply, PiLp.inner_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simpa using ContinuousLinearMap.adjoint_inner_left A (z i) (w i)
  have hπ_map_orthogonal (A : H →L[ℂ] H) (hA : A ∈ S) :
      Set.MapsTo (π A) ((Mᗮ : Submodule ℂ K) : Set K) ((Mᗮ : Submodule ℂ K) : Set K) := by
    intro z hz
    have hz' : z ∈ (Mᗮ : Submodule ℂ K) := by
      simpa using hz
    have hz'' : π A z ∈ (Mᗮ : Submodule ℂ K) := by
      rw [Submodule.mem_orthogonal'] at hz' ⊢
      intro y hy
      have hy' : π (star A) y ∈ M := hπ_map_M (star A) (by simpa using (star_mem_iff.2 hA)) hy
      calc
        inner ℂ (π A z) y = inner ℂ z ((ContinuousLinearMap.adjoint (π A)) y) := by
          rw [← ContinuousLinearMap.adjoint_inner_right]
        _ = inner ℂ z (π (star A) y) := by rw [hπ_star]
        _ = 0 := hz' _ hy'
    simpa using hz''
  have hdiag_apply (A : H →L[ℂ] H) (z : K) : e (π A z) = vn_diagOperator n A (e z) := by
    ext i
    change WithLp.ofLp (π A z) i = (vn_diagOperator n A (WithLp.ofLp z)) i
    rw [hπ_apply]
    rw [WithLp.ofLp_toLp]
    simp [vn_diagOperator]
  let p : K →L[ℂ] K := M.starProjection
  have hpidem : IsIdempotentElem p := by
    change IsIdempotentElem M.starProjection
    exact Submodule.isIdempotentElem_starProjection M
  have hp_range : p.range = M := by
    change M.starProjection.range = M
    exact Submodule.range_starProjection M
  have hp_ker : p.ker = Mᗮ := by
    change M.starProjection.ker = Mᗮ
    exact Submodule.ker_starProjection M
  have hp_comm_π (A : H →L[ℂ] H) (hA : A ∈ S) : Commute p (π A) := by
    have hrange : p.range ∈ Module.End.invtSubmodule (π A) := by
      rw [hp_range]
      simpa [Module.End.mem_invtSubmodule_iff_mapsTo] using hπ_map_M A hA
    have hker : p.ker ∈ Module.End.invtSubmodule (π A) := by
      rw [hp_ker]
      simpa [Module.End.mem_invtSubmodule_iff_mapsTo] using hπ_map_orthogonal A hA
    exact (ContinuousLinearMap.IsIdempotentElem.commute_iff (f := p) (T := π A) hpidem).2 ⟨hrange, hker⟩
  let B : (Fin n → H) →L[ℂ] (Fin n → H) :=
    e.toContinuousLinearMap ∘L p ∘L e.symm.toContinuousLinearMap
  have hB_mem_centralizer :
      B ∈ Set.centralizer ((fun A : H →L[ℂ] H => vn_diagOperator n A) '' (S : Set (H →L[ℂ] H))) := by
    rw [Set.mem_centralizer_iff]
    intro C hC
    rcases hC with ⟨A, hA, rfl⟩
    ext w i
    have hcomm : p (π A (e.symm w)) = π A (p (e.symm w)) := by
      exact congrArg (fun T : K →L[ℂ] K => T (e.symm w)) (hp_comm_π A hA).eq
    have hcomm' : e (p (π A (e.symm w))) = e (π A (p (e.symm w))) := by
      exact congrArg e hcomm
    have hleft : e (p (π A (e.symm w))) = B ((vn_diagOperator n A) w) := by
      calc
        e (p (π A (e.symm w))) = B (e (π A (e.symm w))) := by
          simp [B, ContinuousLinearMap.comp_apply]
        _ = B ((vn_diagOperator n A) w) := by
          rw [hdiag_apply A (e.symm w)]
          simp
    have hright : e (π A (p (e.symm w))) = (vn_diagOperator n A) (B w) := by
      calc
        e (π A (p (e.symm w))) = (vn_diagOperator n A) (e (p (e.symm w))) := by
          rw [hdiag_apply A (p (e.symm w))]
        _ = (vn_diagOperator n A) (B w) := by
          simp [B, ContinuousLinearMap.comp_apply]
    have hfun : B ((vn_diagOperator n A) w) = (vn_diagOperator n A) (B w) := by
      rw [← hleft, ← hright]
      exact hcomm'
    simpa using congrArg (fun f : Fin n → H => f i) hfun.symm
  have hB_comm_x : vn_diagOperator n x * B = B * vn_diagOperator n x := by
    have hxdiag := vn_diagOperator_mem_doubleCommutant S n hx
    have hxdiag' := (Set.mem_centralizer_iff.mp hxdiag) B hB_mem_centralizer
    exact hxdiag'.symm
  have hvM : WithLp.toLp 2 v ∈ M := hM0_le_M hvM0
  have hpv : p (WithLp.toLp 2 v) = WithLp.toLp 2 v := by
    exact (Submodule.starProjection_eq_self_iff).2 hvM
  have hB_v : B v = v := by
    ext i
    have h := congrArg (fun z : K => WithLp.ofLp z i) hpv
    simpa [B, PiLp.coe_continuousLinearEquiv, PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_toLp] using h
  have hB_xv : B (fun i : Fin n => x (v i)) = fun i : Fin n => x (v i) := by
    have htmp := congrArg (fun T : (Fin n → H) →L[ℂ] (Fin n → H) => T v) hB_comm_x
    have htmp' : (fun i : Fin n => x (v i)) = B (fun i : Fin n => x (v i)) := by
      simpa [ContinuousLinearMap.mul_def, hB_v, vn_diagOperator] using htmp
    simpa using htmp'.symm
  have hxv_mem_M : e.symm (fun i : Fin n => x (v i)) ∈ M := by
    apply (Submodule.starProjection_eq_self_iff).1
    have htmp := congrArg e.symm hB_xv
    simpa [B, p, ContinuousLinearMap.comp_apply] using htmp
  have himage_M0 : e '' (M0 : Set K) = vn_tupleOrbit S n v := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨A, hA, rfl⟩
      refine ⟨A, hA, ?_⟩
      ext i
      rw [PiLp.coe_continuousLinearEquiv]
    · rintro ⟨A, hA, rfl⟩
      refine ⟨WithLp.toLp 2 (fun i : Fin n => A (v i)), ?_, ?_⟩
      · exact hM0_mem A hA
      · ext i
        rw [PiLp.coe_continuousLinearEquiv]
  have himage_M : e '' (M : Set K) = closure (vn_tupleOrbit S n v) := by
    calc
      e '' (M : Set K) = e '' closure (M0 : Set K) := by
        simp [M, Submodule.topologicalClosure_coe]
      _ = closure (e '' (M0 : Set K)) := by
        simpa using (ContinuousLinearEquiv.image_closure e (M0 : Set K))
      _ = closure (vn_tupleOrbit S n v) := by rw [himage_M0]
  have hxv_image : (fun i : Fin n => x (v i)) ∈ e '' (M : Set K) := by
    refine ⟨e.symm (fun i : Fin n => x (v i)), hxv_mem_M, ?_⟩
    simp
  rw [himage_M] at hxv_image
  exact hxv_image

theorem vn_pointwiseClosed_implies_doubleCommutant {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    IsClosed (vn_pointwiseImage S) → vn_doubleCommutantSet S = (S : Set (H →L[ℂ] H)) := by
  intro hclosed
  ext x
  constructor
  · intro hx
    have hxcl : ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x ∈ closure (vn_pointwiseImage S) := by
      classical
      let px : PointwiseConvergenceCLM (RingHom.id ℂ) H H :=
        ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x
      change px ∈ closure (vn_pointwiseImage S)
      rw [mem_closure_iff_nhds_basis
        ((PointwiseConvergenceCLM.hasBasis_nhds_zero (σ := RingHom.id ℂ) (E := H) (F := H)).nhds_of_zero px)]
      intro SV hSV
      rcases hSV with ⟨hsfin, hVnhds⟩
      letI : Finite SV.1 := hsfin
      letI : Fintype SV.1 := Fintype.ofFinite SV.1
      let n : ℕ := Fintype.card SV.1
      let e : SV.1 ≃ Fin n := Fintype.equivFin SV.1
      let v : Fin n → H := fun i => ((e.symm i : SV.1) : H)
      have hxTuple := vn_bicommutant_tuple_mem_closure S n v hx
      let tupleSet : Set (Fin n → H) := Set.pi Set.univ (fun i => {y : H | y - x (v i) ∈ SV.2})
      have htuple_nhds : tupleSet ∈ nhds (fun i : Fin n => x (v i)) := by
        dsimp [tupleSet]
        refine set_pi_mem_nhds ?_ ?_
        · simpa using (Set.to_finite (Set.univ : Set (Fin n)))
        · intro i hi
          rw [((nhds (0 : H)).basis_sets.nhds_of_zero (x (v i))).mem_iff]
          exact ⟨SV.2, hVnhds, subset_rfl⟩
      rcases (mem_closure_iff_nhds.mp hxTuple) tupleSet htuple_nhds with ⟨y, hy⟩
      rcases hy with ⟨hyTuple, hyMem⟩
      rcases hyMem with ⟨A, hAS, rfl⟩
      refine ⟨ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H A, ?_, ?_⟩
      · exact ⟨A, hAS, rfl⟩
      · intro z hz
        let i : Fin n := e ⟨z, hz⟩
        have hi : v i = z := by
          simp [v, i, e]
        have hAi : A (v i) - x (v i) ∈ SV.2 := by
          have : (fun i : Fin n => A (v i)) i ∈ {y : H | y - x (v i) ∈ SV.2} := by
            simpa [tupleSet] using hyTuple i (by simp : i ∈ Set.univ)
          simpa using this
        simpa [ContinuousLinearMap.toPointwiseConvergenceCLM_apply, hi] using hAi
    have hximg : ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x ∈ vn_pointwiseImage S := by
      simpa [hclosed.closure_eq] using hxcl
    rcases hximg with ⟨a, haS, hax⟩
    have hxa : x = a := by
      ext v
      simpa [ContinuousLinearMap.toPointwiseConvergenceCLM_apply] using
        (congrArg (fun f : PointwiseConvergenceCLM (RingHom.id ℂ) H H => f v) hax).symm
    simpa [hxa] using haS
  · intro hx
    exact Set.subset_centralizer_centralizer hx

def vn_wotImage {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (ContinuousLinearMapWOT (RingHom.id ℂ) H H) :=
  ContinuousLinearMap.toWOT (RingHom.id ℂ) H H '' (S : Set (H →L[ℂ] H))

theorem vn_wotClosed_implies_pointwiseClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    IsClosed (vn_wotImage S) → IsClosed (vn_pointwiseImage S) := by
  intro hclosed
  classical
  let ιptwot : PointwiseConvergenceCLM (RingHom.id ℂ) H H → ContinuousLinearMapWOT (RingHom.id ℂ) H H :=
    fun T =>
      ContinuousLinearMap.toWOT (RingHom.id ℂ) H H
        ((ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) H {s : Set H | Finite s}).symm T)
  have hcont : Continuous ιptwot := by
    refine ContinuousLinearMapWOT.continuous_of_dual_apply_continuous ?_
    intro x y
    simpa [ιptwot] using
      y.continuous.comp
        (continuous_eval_const x : Continuous fun T : PointwiseConvergenceCLM (RingHom.id ℂ) H H => T x)
  have hpre : vn_pointwiseImage S = ιptwot ⁻¹' vn_wotImage S := by
    ext T
    constructor
    · rintro ⟨A, hA, rfl⟩
      refine ⟨A, hA, ?_⟩
      apply ContinuousLinearMapWOT.ext
      intro x
      rfl
    · rintro hT
      rcases hT with ⟨A, hA, hEq⟩
      refine ⟨A, hA, ?_⟩
      ext x
      have hx := congrArg (fun U => U x) hEq
      simpa [ιptwot] using hx
  rw [hpre]
  exact hclosed.preimage hcont

theorem vn_wotImage_centralizer_isClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : Set (H →L[ℂ] H)) :
    IsClosed ((ContinuousLinearMap.toWOT (RingHom.id ℂ) H H) '' Set.centralizer T) := by
  classical
  let e : (H →L[ℂ] H) ≃ₗ[ℂ] (H →WOT[ℂ] H) := ContinuousLinearMap.toWOT (RingHom.id ℂ) H H
  let pre : (H →L[ℂ] H) → (H →WOT[ℂ] H) → (H →WOT[ℂ] H) :=
    fun z U => e ((e.symm U).comp z)
  let post : (H →L[ℂ] H) → (H →WOT[ℂ] H) → (H →WOT[ℂ] H) :=
    fun z U => e (z.comp (e.symm U))
  have hpre_cont : ∀ z : H →L[ℂ] H, Continuous (pre z) := by
    intro z
    refine ContinuousLinearMapWOT.continuous_of_dual_apply_continuous ?_
    intro x y
    simpa [pre, e, ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMapWOT.continuous_dual_apply (σ := RingHom.id ℂ) (E := H) (F := H)
        (x := z x) (y := y))
  have hpost_cont : ∀ z : H →L[ℂ] H, Continuous (post z) := by
    intro z
    refine ContinuousLinearMapWOT.continuous_of_dual_apply_continuous ?_
    intro x y
    simpa [post, e, ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMapWOT.continuous_dual_apply (σ := RingHom.id ℂ) (E := H) (F := H)
        (x := x) (y := y.comp z))
  have hclosed :
      ∀ z : H →L[ℂ] H, IsClosed {U : H →WOT[ℂ] H | pre z U = post z U} := by
    intro z
    exact isClosed_eq (hpre_cont z) (hpost_cont z)
  have himage :
      (e '' Set.centralizer T : Set (H →WOT[ℂ] H)) =
        ⋂ z ∈ T, {U : H →WOT[ℂ] H | pre z U = post z U} := by
    ext U
    constructor
    · rintro ⟨A, hA, rfl⟩
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro z hz
      simpa [pre, post, e] using
        congrArg e (((Set.mem_centralizer_iff).mp hA z hz).symm)
    · intro hU
      simp only [Set.mem_iInter, Set.mem_setOf_eq] at hU
      refine ⟨e.symm U, ?_, e.apply_symm_apply U⟩
      rw [Set.mem_centralizer_iff]
      intro z hz
      simpa [pre, post, e] using (congrArg e.symm (hU z hz)).symm
  rw [himage]
  exact isClosed_biInter (fun z hz => hclosed z)

theorem vn_doubleCommutant_implies_wotClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    vn_doubleCommutantSet S = (S : Set (H →L[ℂ] H)) → IsClosed (vn_wotImage S) := by
  intro hS
  rw [vn_wotImage]
  rw [← hS]
  simpa [vn_doubleCommutantSet] using
    (vn_wotImage_centralizer_isClosed (H := H)
      (T := Set.centralizer (S : Set (H →L[ℂ] H))))

theorem vonNeumann_doubleCommutant_tfae {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    List.TFAE
      [ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = S
      , IsClosed
          (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H '' (S : Set (H →L[ℂ] H)))
      , IsClosed
          (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
            (S : Set (H →L[ℂ] H))) ] := by
  change List.TFAE
    [ vn_doubleCommutantSet S = (S : Set (H →L[ℂ] H))
    , IsClosed (vn_wotImage S)
    , IsClosed (vn_pointwiseImage S) ]
  tfae_have 1 → 2 := by
    intro h
    exact vn_doubleCommutant_implies_wotClosed S h
  tfae_have 2 → 3 := by
    intro h
    exact vn_wotClosed_implies_pointwiseClosed S h
  tfae_have 3 → 1 := by
    intro h
    exact vn_pointwiseClosed_implies_doubleCommutant S h
  tfae_finish


end Submission
