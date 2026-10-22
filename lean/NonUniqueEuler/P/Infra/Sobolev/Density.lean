import NonUniqueEuler.Defs.Infra.SobolevSpace
import NonUniqueEuler.H.Infra.Sobolev.Density.Trunc
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.Smooth

/-!
# Proof: density of `C_c^∞` in `H^k`, with control of supports (library I-HK)

Proof of `I/Infra/Sobolev/Density.lean` (standard; library I-HK).

1. Truncation (`DensityAux.exists_trunc_approx`, `H/Infra/Sobolev/Density/Trunc.lean`):
   `cut(·/R) f → f` in `H^k` as `R → ∞`, by the weak Leibniz rule, the scaling rule for the
   derivatives of the cutoff, and dominated convergence in `L²`.
2. Mollification (`DensityAux.exists_conv_approx`, `H/Infra/Sobolev/Density/Moll.lean`): if
   `f = 0` a.e. outside the compact `K`, then `ρ_ε ⋆ f` is a test function supported in
   `cthickening ε K`, `∂^γ(ρ_ε ⋆ f) = ρ_ε ⋆ ∂^γ f` weakly (Fubini,
   `H/Infra/Sobolev/Density/Conv.lean`), and `ρ_ε ⋆ g → g` in `L²`
   (`H/Infra/Sobolev/Density/L2.lean`).
3. Supports: `cthickening ε K ⊆ V` for small `ε` (`IsCompact.exists_cthickening_subset_open`).

The type-level density in `Hk k` follows from the function-level one through the bridge
`I/Infra/Sobolev/Space.lean` (`toHk`, `Hk.memH_fn`, `norm_toHk`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace NonUniqueEuler.Sob

/-- Density of test functions in `H^k`. -/
theorem MemH.exists_testFn_approx {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ℂ → ℂ, IsTestFn univ φ ∧ MemH k (f - φ) ∧ normH k (f - φ) < ε := by
  obtain ⟨R, hR, hT, hfT, hn⟩ := DensityAux.exists_trunc_approx hf (half_pos hε)
  have hTK : ∀ᵐ x, x ∉ Metric.closedBall (0 : ℂ) (2 * R) →
      (fun x => DensityAux.cutR R x * f x) x = 0 :=
    Eventually.of_forall (DensityAux.cutR_mul_eq_zero hR f)
  obtain ⟨φ, hφ, hTφ, hn2⟩ := DensityAux.exists_conv_approx hT
    (isCompact_closedBall 0 (2 * R)) hTK one_pos (half_pos hε)
  have hsum := MemH.add hfT hTφ
  have heq : ((f - fun x => DensityAux.cutR R x * f x) +
      ((fun x => DensityAux.cutR R x * f x) - φ)) = f - φ := by
    abel
  rw [heq] at hsum
  exact ⟨φ, hφ.mono (subset_univ _), hsum.1, by linarith [hsum.2]⟩

/-- Density with supports: if `f = 0` a.e. outside the compact set `K ⊆ V`, `V` open, the
approximants can be supported in `V`. -/
theorem MemH.exists_testFn_approx_support {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) {K V : Set ℂ}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) (hfK : ∀ᵐ x, x ∉ K → f x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ℂ → ℂ, IsTestFn V φ ∧ MemH k (f - φ) ∧ normH k (f - φ) < ε := by
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  obtain ⟨φ, hφ, h1, h2⟩ := DensityAux.exists_conv_approx hf hK hfK hr hε
  exact ⟨φ, hφ.mono hrV, h1, h2⟩

/-- Sequential form, with supports in `V`. -/
theorem MemH.exists_seq_testFn_tendsto {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) {K V : Set ℂ}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) (hfK : ∀ᵐ x, x ∉ K → f x = 0) :
    ∃ φ : ℕ → ℂ → ℂ, (∀ n, IsTestFn V (φ n)) ∧ (∀ n, MemH k (f - φ n)) ∧
      Tendsto (fun n => normH k (f - φ n)) atTop (𝓝 0) := by
  choose φ hφ hm hn using fun n : ℕ =>
    hf.exists_testFn_approx_support hK hV hKV hfK (Nat.one_div_pos_of_nat (n := n))
  refine ⟨φ, hφ, hm, ?_⟩
  exact squeeze_zero (fun n => normH_nonneg k _) (fun n => (hn n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- Test functions are dense in the Hilbert space `Hk k`. -/
theorem dense_range_toHk_testFn (k : ℕ) :
    Dense {F : Hk k | ∃ φ : ℂ → ℂ, IsTestFn univ φ ∧ F = toHk k φ} := by
  rw [Metric.dense_iff]
  intro F r hr
  obtain ⟨hF, -⟩ := Hk.memH_fn F
  obtain ⟨φ, hφ, hm, hn⟩ := MemH.exists_testFn_approx hF hr
  refine ⟨toHk k φ, ?_, φ, hφ, rfl⟩
  have hφH : MemH k φ := IsTestFn.memH hφ k
  have h2 : toHk k (F.fn - φ) = toHk k F.fn - toHk k φ := by
    have hadd := toHk_add hF (MemH.const_smul hφH (-1)).1
    have e : F.fn + (-1 : ℂ) • φ = F.fn - φ := by
      funext x
      simp [sub_eq_add_neg]
    rw [e] at hadd
    rw [hadd, toHk_smul hφH, neg_one_smul, sub_eq_add_neg]
  have h3 : F - toHk k φ = toHk k (F.fn - φ) := by
    rw [h2, toHk_fn_self F]
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev, h3, norm_toHk hm]
  exact hn

end NonUniqueEuler.Sob
