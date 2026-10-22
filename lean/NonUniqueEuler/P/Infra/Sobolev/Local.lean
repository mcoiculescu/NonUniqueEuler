import NonUniqueEuler.H.Infra.Sobolev.Local.Ck
import NonUniqueEuler.H.Infra.Sobolev.Local.W1inf

/-!
# Proof: local norms `H^k(V)`, `W^{1,∞}(V)` and their relation to `H^k` and `C^k`
(library I-HK)

Proves `I/Infra/Sobolev/Local.lean` (same declarations, statements copied verbatim).

* restriction and monotonicity in `V`: `LocalAux.memHOn_mono_set` (uniqueness of weak
  derivatives on the smaller open set);
* the support lemma: `LocalAux.memH_of_memHOn_of_support`, `LocalAux.normHOn_eq_normH_of_support`
  (a cutoff `ζ ∈ C_c^∞(V)`, `ζ = 1` near `K`; `ζ g` is the weak derivative on the plane);
* `C^k` bounds: `LocalAux.memCk_memHOn`, `LocalAux.memCk_memW1infOn`;
* extension by a cutoff: the local Leibniz rule `LocalAux.memHOn_mul_testFn` (induction on
  `k`, first-order product rule) and the support lemma; `LocalAux.memW1infOn_mul_testFn`.

Helpers: `H/Infra/Sobolev/Local/{Cutoff,Basic,Leibniz,Ck,W1inf}.lean`. Black boxes:
`I/Infra/Sobolev/WeakDeriv.lean`, `I/Infra/Sobolev/Smooth.lean`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob

theorem MemH.memHOn {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) {V : Set ℂ} (hV : IsOpen V) :
    MemHOn k V f ∧ normHOn k V f ≤ normH k f :=
  LocalAux.memHOn_mono_set isOpen_univ hV (subset_univ V) hf

theorem MemHOn.mono_set {k : ℕ} {f : ℂ → ℂ} {V V' : Set ℂ} (hV : IsOpen V) (hV' : IsOpen V')
    (hVV' : V' ⊆ V) (hf : MemHOn k V f) : MemHOn k V' f ∧ normHOn k V' f ≤ normHOn k V f :=
  LocalAux.memHOn_mono_set hV hV' hVV' hf

/-- For `f = 0` a.e. outside a compact `K ⊆ V`, local and global `H^k` agree. -/
theorem memHOn_iff_memH_of_support {k : ℕ} {f : ℂ → ℂ} {K V : Set ℂ} (hK : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V) (hfK : ∀ᵐ x, x ∉ K → f x = 0) :
    (MemHOn k V f ↔ MemH k f) ∧ (MemH k f → normHOn k V f = normH k f) :=
  ⟨⟨LocalAux.memH_of_memHOn_of_support hK hV hKV hfK, fun hf => (hf.memHOn hV).1⟩,
    LocalAux.normHOn_eq_normH_of_support hK hV hKV hfK⟩

/-- `C^s(U)` controls `H^s(V)` for `V ⊆ U` open of finite measure. -/
theorem MemCk.memHOn {s : ℕ} {U V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U) (hVfin : volume V < ⊤)
    {h : ℂ → ℂ} (hh : MemCk s U h) :
    MemHOn s V h ∧ normHOn s V h ≤ (s + 1) * Real.sqrt (volume V).toReal * normCk s U h :=
  LocalAux.memCk_memHOn hV hVU hVfin hh

/-- `C^1(U)` controls `W^{1,∞}(V)` for `V ⊆ U` open. -/
theorem MemCk.memW1infOn {U V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U) {h : ℂ → ℂ}
    (hh : MemCk 1 U h) : MemW1infOn V h ∧ normW1infOn V h ≤ 3 * normCk 1 U h :=
  LocalAux.memCk_memW1infOn hV hVU hh

/-- Extension by a cutoff supported in `V`: `‖χ U‖_{H^k} ≤ C ‖U‖_{H^k(V)}`. -/
theorem exists_normH_mul_testFn_le {k : ℕ} {V : Set ℂ} (hV : IsOpen V) {χ : ℂ → ℂ}
    (hχ : IsTestFn V χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : ℂ → ℂ, MemHOn k V U →
      MemH k (fun x => χ x * U x) ∧ normH k (fun x => χ x * U x) ≤ C * normHOn k V U := by
  obtain ⟨C, hC, hmul⟩ := LocalAux.memHOn_mul_testFn hV k χ (hχ.mono (subset_univ V))
  refine ⟨C, hC, fun U hU => ?_⟩
  obtain ⟨hm, hn⟩ := hmul U hU
  have hfK : ∀ᵐ x, x ∉ tsupport χ → χ x * U x = 0 :=
    Filter.Eventually.of_forall fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hsupp := memHOn_iff_memH_of_support (k := k) hχ.compact hV hχ.subset hfK
  have hH : MemH k (fun x => χ x * U x) := hsupp.1.1 hm
  refine ⟨hH, ?_⟩
  rw [← hsupp.2 hH]
  exact hn

/-- Extension by a cutoff supported in `V`: `‖χ U‖_{W^{1,∞}} ≤ C ‖U‖_{W^{1,∞}(V)}`. -/
theorem exists_normW1inf_mul_testFn_le {V : Set ℂ} (hV : IsOpen V) {χ : ℂ → ℂ}
    (hχ : IsTestFn V χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : ℂ → ℂ, MemW1infOn V U →
      MemW1infOn univ (fun x => χ x * U x) ∧
        normW1infOn univ (fun x => χ x * U x) ≤ C * normW1infOn V U :=
  LocalAux.memW1infOn_mul_testFn hV hχ

end NonUniqueEuler.Sob
