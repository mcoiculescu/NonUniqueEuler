import NonUniqueEuler.H.Sec2.HkCalculus.Commutator
import NonUniqueEuler.H.Sec2.HkCalculus.Energy
import NonUniqueEuler.I.Sec2.HkCalculus.CutoffBS
import NonUniqueEuler.I.Infra.Sobolev.Local
import NonUniqueEuler.I.Infra.Sobolev.ReIm

/-!
# Proof of `I/Sec2/HkCalculus.lean`: `lem:Hk-calculus`

Manuscript: `lem:Hk-calculus`, `02_prelim.tex:645-766`.

* (2): `HkCalcAux.exists_isHkProdConst` (`H/Sec2/HkCalculus/Product.lean`), constant `(k+1) 2^k`.
* (1): the cut-off field `Ũ = χ_N U` (`exists_normW1inf_mul_testFn_le`,
  `exists_normH_mul_testFn_le`, `I/Infra/Sobolev/Local.lean`) equals `U` on the neighborhood `V`
  of `N` where `χ_N = 1`; the commutator bound is `HkCalcAux.comm_main`
  (`H/Sec2/HkCalculus/Commutator.lean`), the energy claims are `HkCalcAux.energy_main`,
  `HkCalcAux.energy_real` (`H/Sec2/HkCalculus/Energy.lean`), with `div Ũ = 0` on `N`
  (`HkCalcAux.weakDivOn_univ_ae_eq_zero`). The constant is
  `C = max (2·2^k max(C₁, C₂)) ((k+1) 2^k) + 1`, chosen after `k, N, N₁, χ_N`.
* (3): `exists_cutoffBS_real` (`I/Sec2/HkCalculus/CutoffBS.lean`) applied to `Re w` and `Im w`,
  with `‖Re w‖²_{H^j} + ‖Im w‖²_{H^j} = ‖w‖²_{H^j}` (`MemH.re_im`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob

/-- `lem:Hk-calculus`(1) and (2): for `k ≥ 3` and the setting `(N, N₁, χ_N)` there is a constant
`C > 0` with the commutator, energy and product bounds. -/
theorem exists_isHkCalcConst {k : ℕ} (hk : 3 ≤ k) {N N₁ : Set ℂ} {χN : ℂ → ℝ}
    (hset : HkCalcSetting N N₁ χN) : ∃ C : ℝ, 0 < C ∧ IsHkCalcConst k N N₁ C := by
  -- the complex cutoff `χ_N`
  have hχ : IsTestFn N₁ (fun x => (χN x : ℂ)) := by
    refine ⟨Complex.ofRealCLM.contDiff.comp hset.contDiff,
      hset.hasCompactSupport.comp_left Complex.ofReal_zero, ?_⟩
    exact (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero χN).trans
      hset.tsupport_subset
  obtain ⟨C₁, hC₁, hW⟩ := exists_normW1inf_mul_testFn_le hset.isOpen hχ
  obtain ⟨C₂, hC₂, hH⟩ := exists_normH_mul_testFn_le (k := k) hset.isOpen hχ
  obtain ⟨V, hVo, hNV, hV1⟩ := hset.eq_one_near
  have hVN₁ : V ⊆ N₁ := by
    intro x hx
    refine hset.tsupport_subset (subset_tsupport _ ?_)
    rw [Function.mem_support, hV1 x hx]
    exact one_ne_zero
  set C₀ : ℝ := 2 * 2 ^ k * max C₁ C₂ with hC₀
  set C : ℝ := max C₀ ((k + 1) * 2 ^ k) + 1 with hCdef
  have hC₀C : C₀ ≤ C := by rw [hCdef]; linarith [le_max_left C₀ ((k + 1) * 2 ^ k)]
  have hCpos : 0 < C := by
    rw [hCdef]
    have : (0 : ℝ) ≤ (k + 1) * 2 ^ k := by positivity
    linarith [le_max_right C₀ ((k + 1) * 2 ^ k)]
  refine ⟨C, hCpos, ?_, (HkCalcAux.isHkProdConst_explicit k).mono ?_⟩
  swap
  · rw [hCdef]; linarith [le_max_right C₀ ((k + 1) * 2 ^ k)]
  intro w U hw hwN hUW hUH α hα
  have hUV : ∀ x ∈ V, (fun x => (χN x : ℂ) * U x) x = U x := by
    intro x hx
    simp [hV1 x hx]
  obtain ⟨hŨw, hŨwb⟩ := hW U hUW
  obtain ⟨hŨ, hŨb⟩ := hH U hUH
  obtain ⟨hex, hCm, hCb⟩ :=
    HkCalcAux.comm_main hk hset.isCompact.isClosed hset.isOpen hNV hUV hŨ hŨw hw hwN hα
  have ha : 0 ≤ normW1infOn N₁ U := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hb : 0 ≤ normHOn k N₁ U := normHOn_nonneg k N₁ U
  have key : 2 * 2 ^ k * (normW1infOn univ (fun x => (χN x : ℂ) * U x) +
      normH k (fun x => (χN x : ℂ) * U x)) ≤ C * (normW1infOn N₁ U + normHOn k N₁ U) := by
    have h1 : normW1infOn univ (fun x => (χN x : ℂ) * U x) +
        normH k (fun x => (χN x : ℂ) * U x) ≤
        max C₁ C₂ * (normW1infOn N₁ U + normHOn k N₁ U) := by
      have e1 : C₁ * normW1infOn N₁ U ≤ max C₁ C₂ * normW1infOn N₁ U :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) ha
      have e2 : C₂ * normHOn k N₁ U ≤ max C₁ C₂ * normHOn k N₁ U :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hb
      linarith
    have h2 : (0 : ℝ) ≤ 2 * 2 ^ k := by positivity
    calc 2 * 2 ^ k * (normW1infOn univ (fun x => (χN x : ℂ) * U x) +
          normH k (fun x => (χN x : ℂ) * U x)) ≤
          2 * 2 ^ k * (max C₁ C₂ * (normW1infOn N₁ U + normHOn k N₁ U)) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = C₀ * (normW1infOn N₁ U + normHOn k N₁ U) := by rw [hC₀]; ring
      _ ≤ C * (normW1infOn N₁ U + normHOn k N₁ U) :=
          mul_le_mul_of_nonneg_right hC₀C (add_nonneg ha hb)
  have hbound : l2 (hkComm N₁ α U w) ≤
      C * (normW1infOn N₁ U + normHOn k N₁ U) * normH k w :=
    hCb.trans (mul_le_mul_of_nonneg_right key (normH_nonneg k w))
  refine ⟨hex, hCm, hbound, fun hdiv => ⟨?_, fun hreal =>
    HkCalcAux.energy_real hset.isOpen hw hα hex hreal⟩⟩
  have hdiv' := HkCalcAux.weakDivOn_univ_ae_eq_zero hset.isOpen hVo hNV hVN₁ hUV hUW hŨw hdiv
  have hE := HkCalcAux.energy_main hk hset.isCompact hNV hVN₁ hUV hŨ hŨw hw hwN hα hCm hdiv'
  calc _ ≤ l2 (hkComm N₁ α U w) * normH k w := hE
    _ ≤ (C * (normW1infOn N₁ U + normHOn k N₁ U) * normH k w) * normH k w :=
        mul_le_mul_of_nonneg_right hbound (normH_nonneg k w)
    _ = C * (normW1infOn N₁ U + normHOn k N₁ U) * normH k w ^ 2 := by ring

/-- `lem:Hk-calculus`(3): for every `j ≥ 0`, `ρ > 0` and real `χ ∈ C_c^∞(B_ρ)` there is `C' > 0`
with `‖χ K ∗ w‖_{H^{j+1}} ≤ C' ‖w‖_{H^j}` for every `w ∈ H^j` vanishing outside `B_ρ`. -/
theorem exists_isHkBSConst (j : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ ball (0 : ℂ) ρ) :
    ∃ C : ℝ, 0 < C ∧ IsHkBSConst j χ ρ C := by
  obtain ⟨C, hC, h⟩ := exists_cutoffBS_real j hρ hχ hχc hχs
  refine ⟨C, hC, ?_⟩
  intro w hw hs
  obtain ⟨hre, him, hnorm⟩ := hw.re_im
  have hsre : ∀ᵐ x, x ∉ ball (0 : ℂ) ρ → (w x).re = 0 :=
    hs.mono fun x hx hxb => by rw [hx hxb, Complex.zero_re]
  have hsim : ∀ᵐ x, x ∉ ball (0 : ℂ) ρ → (w x).im = 0 :=
    hs.mono fun x hx hxb => by rw [hx hxb, Complex.zero_im]
  obtain ⟨h1, h1b⟩ := h (fun x => (w x).re) hre hsre
  obtain ⟨h2, h2b⟩ := h (fun x => (w x).im) him hsim
  refine ⟨h1, h2, ?_⟩
  have hn1 := normH_nonneg (j + 1) (fun x => (χ x : ℂ) * BS.velocityRe w x)
  have hn2 := normH_nonneg (j + 1) (fun x => (χ x : ℂ) * BS.velocityIm w x)
  have hb1 : normH (j + 1) (fun x => (χ x : ℂ) * BS.velocityRe w x) ≤
      C * normH j (fun x => ((w x).re : ℂ)) := h1b
  have hb2 : normH (j + 1) (fun x => (χ x : ℂ) * BS.velocityIm w x) ≤
      C * normH j (fun x => ((w x).im : ℂ)) := h2b
  unfold BS.normHC2
  have hCw : 0 ≤ C * normH j w := mul_nonneg hC.le (normH_nonneg j w)
  rw [Real.sqrt_le_left hCw]
  calc normH (j + 1) (fun x => (χ x : ℂ) * BS.velocityRe w x) ^ 2 +
        normH (j + 1) (fun x => (χ x : ℂ) * BS.velocityIm w x) ^ 2 ≤
        (C * normH j (fun x => ((w x).re : ℂ))) ^ 2 +
          (C * normH j (fun x => ((w x).im : ℂ))) ^ 2 :=
        add_le_add (pow_le_pow_left₀ hn1 hb1 2) (pow_le_pow_left₀ hn2 hb2 2)
    _ = C ^ 2 * (normH j (fun x => ((w x).re : ℂ)) ^ 2 +
          normH j (fun x => ((w x).im : ℂ)) ^ 2) := by ring
    _ = (C * normH j w) ^ 2 := by rw [hnorm]; ring

/-- The chosen constant `C_P(k) = hkCalcConst k N N₁` of `05_single_ring.tex:226` works in
`lem:Hk-calculus`(1), (2). -/
theorem isHkCalcConst_hkCalcConst {k : ℕ} (hk : 3 ≤ k) {N N₁ : Set ℂ} {χN : ℂ → ℝ}
    (hset : HkCalcSetting N N₁ χN) : IsHkCalcConst k N N₁ (hkCalcConst k N N₁) :=
  hkCalcConst_spec (exists_isHkCalcConst hk hset)

/-- The chosen constant `C^el_j = elConst j χ ρ` of `05_single_ring.tex:224` works in
`lem:Hk-calculus`(3). -/
theorem isHkBSConst_elConst (j : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ ball (0 : ℂ) ρ) :
    IsHkBSConst j χ ρ (elConst j χ ρ) :=
  elConst_spec (exists_isHkBSConst j hρ hχ hχc hχs)

end NonUniqueEuler.Sob
