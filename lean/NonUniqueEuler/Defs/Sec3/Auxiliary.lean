import NonUniqueEuler.Statement.WeakSolution
import NonUniqueEuler.Defs.Infra.Equimeasurable
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Section 3: auxiliary objects (cutoffs, mollifiers, truncations, time test functions)

Manuscript source: `03_compactness.tex:23-41` ("Throughout this section … we use the following
auxiliary objects"). The manuscript fixes, once and for all,

* `ς ∈ C_c^∞(B₂)` with `0 ≤ ς ≤ 1`, `ς = 1` on `B₁`, and `ς_R = ς(·/R)`;
* `ρ ∈ C_c^∞(B₁)` with `ρ ≥ 0`, `∫ρ = 1`, and `ρ_ε = ε⁻²ρ(·/ε)` (convolution in `x` only);
* `ρ^t ∈ C_c^∞((-1,1))` with `ρ^t ≥ 0`, `∫ρ^t = 1`, and `ρ^t_δ = δ⁻¹ρ^t(·/δ)`;
* `ϰ ∈ C^∞(ℝ)` nondecreasing, `ϰ = 0` on `(-∞,0]`, `ϰ = 1` on `[1,∞)`;
* the truncations `T_k(s) = max(-k, min(k, s))`, `T_k ∈ Lip₀`.

We record each list of properties as a predicate (`IsSpatialCutoff`, `IsMollifier`,
`IsTimeMollifier`) and make one concrete choice satisfying it (`sigmaCut`, `rho`, `rhoT`, built
from Mathlib's `ContDiffBump`; `kappa` is Mathlib's `Real.smoothTransition`). Lemmas that hold
for every such choice should be stated for the predicate; the concrete objects are the ones
that statements mention when the manuscript's formula involves the fixed choice (e.g.
`‖∇ς‖_{L^∞}` in eq:tail, `03_compactness.tex:588-592`).

The class `Lip₀` is `Equimeas.IsLipO` (`Defs/Infra/Equimeasurable.lean`); the renormalizations of
`def:weak` are `IsRenormalization` (statement layer).

We also define the time test class `C_c^∞((-∞,T))` of `lem:dbr` (`IsTimeTestFn`) and prove that
`α(t)ψ(x)` lies in `𝒟_T` (`isTestFunction_mul`), the test functions used in the proofs of
`lem:weak-cont` and `lem:transport`(ii).

Smoothness is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)` (`C^∞`, decision D15). All lemmas in this file
are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Weak

/-! ### The spatial cutoff `ς` -/

/-- The properties of the spatial cutoff `ς` of `03_compactness.tex:24-26`: `ς ∈ C_c^∞(B₂)`,
`0 ≤ ς ≤ 1`, and `ς = 1` on `B₁`. -/
structure IsSpatialCutoff (ς : ℂ → ℝ) : Prop where
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ς
  hasCompactSupport : HasCompactSupport ς
  tsupport_subset : tsupport ς ⊆ ball (0 : ℂ) 2
  nonneg : ∀ x, 0 ≤ ς x
  le_one : ∀ x, ς x ≤ 1
  eq_one : ∀ x ∈ ball (0 : ℂ) 1, ς x = 1

/-- The bump function used for `ς`: equal to `1` on `\bar B₁`, supported in `\bar B_{3/2}`. -/
def sigmaBump : ContDiffBump (0 : ℂ) :=
  ⟨1, 3 / 2, one_pos, by norm_num⟩

/-- The fixed spatial cutoff `ς` (`03_compactness.tex:24-26`). -/
def sigmaCut : ℂ → ℝ :=
  ⇑sigmaBump

/-- The rescaled cutoff `ς_R = ς(·/R)` (`03_compactness.tex:26`). -/
def sigmaCutR (R : ℝ) (x : ℂ) : ℝ :=
  sigmaCut ((R : ℂ)⁻¹ * x)

theorem isSpatialCutoff_sigmaCut : IsSpatialCutoff sigmaCut where
  contDiff := sigmaBump.contDiff
  hasCompactSupport := sigmaBump.hasCompactSupport
  tsupport_subset := by
    rw [sigmaCut, sigmaBump.tsupport_eq]
    exact closedBall_subset_ball (by simp [sigmaBump]; norm_num)
  nonneg := fun _ => sigmaBump.nonneg
  le_one := fun _ => sigmaBump.le_one
  eq_one := fun _ hx => sigmaBump.one_of_mem_closedBall
    (ball_subset_closedBall (by simpa [sigmaBump] using hx))

theorem sigmaCut_eq_zero {x : ℂ} (hx : 3 / 2 ≤ ‖x‖) : sigmaCut x = 0 :=
  sigmaBump.zero_of_le_dist (by simpa [sigmaBump] using hx)

theorem sigmaCutR_nonneg (R : ℝ) (x : ℂ) : 0 ≤ sigmaCutR R x :=
  isSpatialCutoff_sigmaCut.nonneg _

theorem sigmaCutR_le_one (R : ℝ) (x : ℂ) : sigmaCutR R x ≤ 1 :=
  isSpatialCutoff_sigmaCut.le_one _

theorem norm_inv_mul {R : ℝ} (hR : 0 < R) (x : ℂ) : ‖(R : ℂ)⁻¹ * x‖ = ‖x‖ / R := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le, inv_mul_eq_div]

/-- `ς_R = 1` on `B_R`. -/
theorem sigmaCutR_eq_one {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : ‖x‖ < R) : sigmaCutR R x = 1 := by
  apply isSpatialCutoff_sigmaCut.eq_one
  rw [mem_ball_zero_iff, norm_inv_mul hR, div_lt_one hR]
  exact hx

/-- `ς_R = 0` outside `B_{2R}`. -/
theorem sigmaCutR_eq_zero {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : 2 * R ≤ ‖x‖) :
    sigmaCutR R x = 0 := by
  apply sigmaCut_eq_zero
  rw [norm_inv_mul hR, le_div_iff₀ hR]
  linarith

theorem contDiff_sigmaCutR (R : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sigmaCutR R) :=
  isSpatialCutoff_sigmaCut.contDiff.comp (contDiff_const.mul contDiff_id)

theorem hasCompactSupport_sigmaCutR {R : ℝ} (hR : 0 < R) : HasCompactSupport (sigmaCutR R) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * R)) fun x hx => by
    rw [mem_closedBall_zero_iff, not_le] at hx
    exact sigmaCutR_eq_zero hR hx.le

/-! ### The spatial mollifier `ρ` -/

/-- The properties of the spatial mollifier `ρ` of `03_compactness.tex:27-30`:
`ρ ∈ C_c^∞(B₁)`, `ρ ≥ 0`, `∫ρ = 1`. -/
structure IsMollifier (ρ : ℂ → ℝ) : Prop where
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ
  hasCompactSupport : HasCompactSupport ρ
  tsupport_subset : tsupport ρ ⊆ ball (0 : ℂ) 1
  nonneg : ∀ x, 0 ≤ ρ x
  integral_eq_one : ∫ x, ρ x = 1

/-- The bump function used for `ρ` (supported in `\bar B_{1/2} ⊂ B₁`). -/
def rhoBump : ContDiffBump (0 : ℂ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The fixed spatial mollifier `ρ` (`03_compactness.tex:27-28`), the normalized bump. -/
def rho : ℂ → ℝ :=
  rhoBump.normed volume

theorem isMollifier_rho : IsMollifier rho where
  contDiff := rhoBump.contDiff_normed
  hasCompactSupport := rhoBump.hasCompactSupport_normed
  tsupport_subset := by
    rw [rho, rhoBump.tsupport_normed_eq]
    exact closedBall_subset_ball (by simp [rhoBump]; norm_num)
  nonneg := rhoBump.nonneg_normed
  integral_eq_one := rhoBump.integral_normed

/-- The rescaled kernel `ρ_ε = ε⁻² ρ(·/ε)` (`03_compactness.tex:28-29`; the plane has
dimension 2). It is used for any kernel `ρ`, in particular for the mollifier `rho` and for the
kernels `ψ^{ij}(z) = z_j ∂_i ρ(z)` of the proof of `lem:commutator`. -/
def scaled (ρ : ℂ → ℝ) (ε : ℝ) (x : ℂ) : ℝ :=
  (ε ^ 2)⁻¹ * ρ ((ε : ℂ)⁻¹ * x)

/-- The spatial convolution `g ⋆ ρ_ε (x) = ∫ g(y) ρ_ε(x - y) dy` (`03_compactness.tex:29-30`). -/
def mollify (ρ : ℂ → ℝ) (ε : ℝ) (g : ℂ → ℝ) (x : ℂ) : ℝ :=
  ∫ y, g y * scaled ρ ε (x - y)

/-! ### The time mollifier `ρ^t` -/

/-- The properties of the time mollifier `ρ^t` of `03_compactness.tex:30-32`:
`ρ^t ∈ C_c^∞((-1,1))`, `ρ^t ≥ 0`, `∫ρ^t = 1`. -/
structure IsTimeMollifier (ρ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ
  hasCompactSupport : HasCompactSupport ρ
  tsupport_subset : tsupport ρ ⊆ Ioo (-1 : ℝ) 1
  nonneg : ∀ t, 0 ≤ ρ t
  integral_eq_one : ∫ t, ρ t = 1

/-- The bump function used for `ρ^t` (supported in `[-1/2, 1/2]`). -/
def rhoTBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The fixed time mollifier `ρ^t` (`03_compactness.tex:30-31`). -/
def rhoT : ℝ → ℝ :=
  rhoTBump.normed volume

theorem isTimeMollifier_rhoT : IsTimeMollifier rhoT where
  contDiff := rhoTBump.contDiff_normed
  hasCompactSupport := rhoTBump.hasCompactSupport_normed
  tsupport_subset := by
    rw [rhoT, rhoTBump.tsupport_normed_eq]
    refine (closedBall_subset_ball (by simp [rhoTBump]; norm_num : rhoTBump.rOut < 1)).trans ?_
    rw [Real.ball_eq_Ioo]
    norm_num
  nonneg := rhoTBump.nonneg_normed
  integral_eq_one := rhoTBump.integral_normed

/-- The rescaled time kernel `ρ^t_δ = δ⁻¹ ρ^t(·/δ)` (`03_compactness.tex:32-33`). -/
def scaledT (ρ : ℝ → ℝ) (δ : ℝ) (t : ℝ) : ℝ :=
  δ⁻¹ * ρ (δ⁻¹ * t)

/-! ### The smooth step `ϰ` -/

/-- The smooth step `ϰ` (`03_compactness.tex:33-35`): `C^∞`, nondecreasing, `0` on `(-∞,0]`,
`1` on `[1,∞)`. We take Mathlib's `Real.smoothTransition`. -/
def kappa : ℝ → ℝ :=
  Real.smoothTransition

theorem contDiff_kappa : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) kappa :=
  Real.smoothTransition.contDiff

theorem monotone_kappa : Monotone kappa :=
  Real.smoothTransition.monotone

theorem kappa_of_nonpos {t : ℝ} (ht : t ≤ 0) : kappa t = 0 :=
  Real.smoothTransition.zero_of_nonpos ht

theorem kappa_of_one_le {t : ℝ} (ht : 1 ≤ t) : kappa t = 1 :=
  Real.smoothTransition.one_of_one_le ht

theorem kappa_nonneg (t : ℝ) : 0 ≤ kappa t :=
  Real.smoothTransition.nonneg t

theorem kappa_le_one (t : ℝ) : kappa t ≤ 1 :=
  Real.smoothTransition.le_one t

/-! ### Truncations -/

/-- The truncation `T_k(s) = max(-k, min(k, s))` (`03_compactness.tex:35-36`). -/
def trunc (k s : ℝ) : ℝ :=
  max (-k) (min k s)

theorem lipschitzWith_trunc (k : ℝ) : LipschitzWith 1 (trunc k) :=
  (LipschitzWith.id.const_min k).const_max (-k)

/-- `T_k ∈ Lip₀` for `k ≥ 0` (`03_compactness.tex:36`). -/
theorem isLipO_trunc {k : ℝ} (hk : 0 ≤ k) : Equimeas.IsLipO (trunc k) :=
  ⟨⟨1, lipschitzWith_trunc k⟩, by simp [trunc, hk]⟩

theorem trunc_of_abs_le {k s : ℝ} (h : |s| ≤ k) : trunc k s = s := by
  rw [abs_le] at h
  simp [trunc, h.1, h.2]

theorem abs_trunc_le {k : ℝ} (hk : 0 ≤ k) (s : ℝ) : |trunc k s| ≤ k := by
  rw [abs_le, trunc]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem abs_trunc_le_abs {k : ℝ} (hk : 0 ≤ k) (s : ℝ) : |trunc k s| ≤ |s| := by
  have h := (lipschitzWith_trunc k).dist_le_mul s 0
  have h0 : trunc k 0 = 0 := by simp [trunc, hk]
  simpa [Real.dist_eq, h0] using h

/-! ### Time test functions -/

/-- The time test class `C_c^∞((-∞, T))` of `lem:dbr` (`03_compactness.tex:68-76`). -/
structure IsTimeTestFn (T : ℝ) (α : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α
  hasCompactSupport : HasCompactSupport α
  support_lt : ∀ t ∈ tsupport α, t < T

/-- For `α ∈ C_c^∞((-∞,T))` and `ψ ∈ C_c^∞(ℝ²)`, the function `α(t)ψ(x)` lies in `𝒟_T`
(`03_compactness.tex:162-163`). -/
theorem isTestFunction_mul {T : ℝ} {α : ℝ → ℝ} {ψ : ℂ → ℝ} (hα : IsTimeTestFn T α)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    IsTestFunction T (fun p : ℝ × ℂ => α p.1 * ψ p.2) := by
  set K : Set (ℝ × ℂ) := tsupport α ×ˢ tsupport ψ with hK
  have hKc : IsCompact K := hα.hasCompactSupport.isCompact.prod hψc.isCompact
  have hsupp : Function.support (fun p : ℝ × ℂ => α p.1 * ψ p.2) ⊆ K := by
    intro p hp
    rw [Function.mem_support] at hp
    refine ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩
    · exact fun h => hp (by simp [h])
    · exact fun h => hp (by simp [h])
  refine ⟨(hα.contDiff.comp contDiff_fst).mul (hψ.comp contDiff_snd), ?_, ?_⟩
  · exact HasCompactSupport.intro hKc fun p hp => Function.notMem_support.mp fun h => hp (hsupp h)
  · intro p hp
    have hpK : p ∈ K := closure_minimal hsupp hKc.isClosed hp
    exact hα.support_lt p.1 hpK.1

end NonUniqueEuler.Weak
