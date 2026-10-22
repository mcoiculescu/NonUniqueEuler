import NonUniqueEuler.Defs.Sec4.Operators
import NonUniqueEuler.H.Sec4.SemigroupConstruct.TransportY

/-!
# Proof: `lem:semigroup-construct` (1), the bounded operators of (2), and the remark after it

Proof of `I/Sec4/SemigroupConstruct.lean` (`04_ring.tex:924-1012`, remark `:942-947`), with
restructuring R1 (no `C₀`-semigroup machinery: `e^{tL^tr}` is `S.transportY s G t`). The work is
in the helper files `H/Sec4/SemigroupConstruct/*.lean`:

* `Basic`: elements of `Y^s`, `Y^s_ℓ` (functions, uniqueness), angular sectors (a.e. congruence by
  polar Fubini, additivity, radial factors, inversion of `ofProfile`), `secNormSq` congruence;
* `SectorOps`: `transSec` is multiplication by `-iℓΩ`; the bounded operator `k_ℓ𝒢_ℓ` on `Y^s_ℓ`
  (`cor:K-bound`, uniform in `ℓ`); `L_ℓ(G)` on profiles;
* `ExpTrans`: `exp(t(-iℓΩ)) = e^{-iℓΩt}` (exponential series, `L²` and a.e. limits) and the sector
  bound (weighted Faà di Bruno, `FaaDiBruno.exists_secNormSq_exp_mul_I_le`);
* `Coupling`: `𝒦w ∈ L²` (Young on a ball) and `𝒦 = ⊕_ℓ k_ℓ𝒢_ℓ` on `Y^s` (identification through the
  sector projections, `lem:sector`(2));
* `LinY`: `L^tr : Y^{s+1} → Y^s` (sector-wise, `|ℓ|‖g‖_{Y^s} ≤ C‖g‖_{Y^{s+1}}`) and
  `L(G) = L^tr + 𝒦`;
* `TransportY`: the transport group on `Y^s` (bound, formula — `x ↦ O_{φ(|x|)}x` preserves
  Lebesgue measure —, group law, strong continuity).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace SectorSetting

open Sect

/-- Remark after `lem:semigroup-construct` (`04_ring.tex:944-947`): `transSec` is multiplication
by `-iℓΩ(|x|;G)` on `Y^s_ℓ`. -/
theorem semigroupConstruct_transSec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ) (G : ℝ)
    (g : Ysec s S.Nstar ℓ) :
    (S.transSec s ℓ G g).fn =ᵐ[volume]
      fun x => -(Complex.I * (ℓ : ℂ) * ((S.Omega G ‖x‖ : ℝ) : ℂ)) * g.fn x :=
  SGC.transSec_spec S hS s ℓ G g

/-- Remark after `lem:semigroup-construct` (`04_ring.tex:944-947`): `k_ℓ𝒢_ℓ` is a bounded operator
on `Y^s_ℓ` (`cor:K-bound` and `lem:norm-equiv`), so the chosen `S.Ksec s ℓ` is it. -/
theorem semigroupConstruct_Ksec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ) :
    ∃ T : Ysec s S.Nstar ℓ →L[ℂ] Ysec s S.Nstar ℓ, ∀ g : Ysec s S.Nstar ℓ,
      (T g).fn =ᵐ[volume] Ang.ofProfile ℓ (S.KsecFn ℓ (Polar.angularSector g.fn ℓ)) :=
  SGC.exists_Ksec S hS s ℓ

/-- Remark after `lem:semigroup-construct` (`04_ring.tex:944-947`): `L_ℓ(G) = -iℓΩ + k_ℓ𝒢_ℓ` is
a bounded operator on `Y^s_ℓ` acting on profiles by `LsecFn` (`04_ring.tex:165-166`). -/
theorem semigroupConstruct_Lsec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ) (G : ℝ)
    (g : Ysec s S.Nstar ℓ) :
    (S.Lsec s ℓ G g).fn =ᵐ[volume]
      Ang.ofProfile ℓ (S.LsecFn ℓ G (Polar.angularSector g.fn ℓ)) :=
  SGC.Lsec_spec S hS s ℓ G g

/-- `lem:semigroup-construct`(1), the formula on a sector: `exp(t(-iℓΩ))` is multiplication by
`e^{-iℓΩ(r;G)t}`, i.e. `(e^{tL^tr}g)(r,θ) = g(r, θ - Ω(r;G)t)` on `Y^s_ℓ`. -/
theorem semigroupConstruct_exp_transSec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ)
    (G t : ℝ) (g : Ysec s S.Nstar ℓ) :
    (NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G) g).fn =ᵐ[volume]
      fun x => Complex.exp (-(Complex.I * (ℓ : ℂ) * ((S.Omega G ‖x‖ : ℝ) : ℂ) * (t : ℂ))) *
        g.fn x :=
  SGC.exp_transSec_spec S hS s ℓ G t g

/-- **`lem:semigroup-construct`(1), sector bound** (`04_ring.tex:931-933`): there is `C_s`,
depending only on `s`, `ω̄`, `ρ±` and `G₊`, with
`‖e^{-iℓΩt}g‖_{s,ℓ} ≤ C_s(1+|t|)^s ‖g‖_{s,ℓ}` for all `ℓ ∈ ℤ`, `|G| ≤ G₊`, `t ∈ ℝ`. -/
theorem semigroupConstruct_transport_sector (S : SectorSetting) (hS : S.Valid) (s : ℕ) {Gp : ℝ}
    (hGp : 0 ≤ Gp) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℤ) (G : ℝ), |G| ≤ Gp → ∀ (t : ℝ) (g : Ysec s S.Nstar ℓ),
      S.secNormY s (NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G) g) ≤
        C * (1 + |t|) ^ s * S.secNormY s g :=
  SGC.transport_sector S hS s hGp

/-- **`lem:semigroup-construct`(1), the group on `Y^s`** (`04_ring.tex:929-932`; R1 form of
"`C₀`-group"; low priority, not used downstream): `e^{tL^tr} = S.transportY s G t` is
`w ↦ w(r, θ - Ω(r;G)t)`, `‖e^{tL^tr}‖_{Y^s → Y^s} ≤ C_s(1+|t|)^s` for `|G| ≤ G₊`, `t ∈ ℝ`, it
satisfies the group law and it is strongly continuous. -/
theorem semigroupConstruct_transportY (S : SectorSetting) (hS : S.Valid) (s : ℕ) {Gp : ℝ}
    (hGp : 0 ≤ Gp) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ, |G| ≤ Gp →
      (∀ t : ℝ, ‖S.transportY s G t‖ ≤ C * (1 + |t|) ^ s) ∧
      (∀ (t : ℝ) (w : Y s S.Nstar),
        (S.transportY s G t w).fn =ᵐ[volume] S.transportFn G t w.fn) ∧
      (∀ t t' : ℝ, S.transportY s G (t + t') = (S.transportY s G t).comp (S.transportY s G t')) ∧
      (∀ w : Y s S.Nstar, Continuous fun t => S.transportY s G t w) :=
  SGC.transportY_spec S hS s hGp

/-- **`lem:semigroup-construct`(1)**: `𝒦w = -(K_BS * w)·∇ω̄` is a bounded operator on `Y^s`
(`04_ring.tex:933`), so the chosen `S.KY s` is it. -/
theorem semigroupConstruct_KY (S : SectorSetting) (hS : S.Valid) (s : ℕ) :
    ∃ T : Y s S.Nstar →L[ℂ] Y s S.Nstar, ∀ w : Y s S.Nstar,
      (T w).fn =ᵐ[volume] S.couplingFn w.fn :=
  SGC.exists_KY S hS s

/-- **`lem:semigroup-construct`(2), the operator bound** (`04_ring.tex:938-939`): `L(G)` maps
`Y^{s+1}` to `Y^s` with `‖L(G)w‖_{Y^s} ≤ C‖w‖_{Y^{s+1}}`, so the chosen `S.LinY s G` is it. -/
theorem semigroupConstruct_LinY (S : SectorSetting) (hS : S.Valid) (s : ℕ) (G : ℝ) :
    ∃ T : Y (s + 1) S.Nstar →L[ℂ] Y s S.Nstar, ∀ w : Y (s + 1) S.Nstar,
      (T w).fn =ᵐ[volume] S.linFn G w.fn :=
  SGC.exists_LinY S hS s G

end SectorSetting

end NonUniqueEuler
