import OpenAIGrouped.Unit025
import OpenAIGrouped.Unit032
import OpenAIGrouped.Unit019
import OpenAIGrouped.Unit018
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import OpenAIGrouped.Unit007
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import OpenAIGrouped.Unit029
import OpenAIGrouped.Unit012
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import OpenAIGrouped.Unit008
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorPhysicalBins.lean; sha256: 848222fd8257e5d78436e51d7a86f3020dec98b24e0e6f1789787f8e3628dfb4 -/
section Source1320
namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace SevenEighths.HeckeDetectorPhysicalBins
open HeckeFamily HeckeDetectorPrimeFamily HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem physical_bins (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ η mesh σmin σmax : ℝ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hη : 0≤η) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (data : RowData M) (cert : Ramification M data) (a : ℝ) (i : ℕ),
      51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum
        (HeckePrimeRay.twistedFamily M H hH (data.character M))
        (cert.nonprincipal M H hH) (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ (r : ℝ) (z : ℂ), rmin≤r → r≤R → σmin≤1-z.re → 1-z.re≤σmax →
      M.absNorm^2*(Ideal.span {data.m}).absNorm*(Ideal.span {(72 : O)}).absNorm*
        (Ideal.span {data.u}).absNorm≤Z^d →
      |z.im|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ → (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
    let Q := HeckePrimeRow.canonicalPrimeAmplitude M H data.u W B ((Z^d)^r) z
    let g := amplitude ((Z^d)^r) (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤((Z^d)^r)^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) := by
  have hh := HeckePrimeAmplitudeActual.ray_amplitude_bins M H hH W A B hA hWs hW
    R dmin dmax rmin τ ε e κ η mesh σmin σmax hR hdmin hdmax hrmin
    hτ hε he he' hκ hη hmesh hbudget hgap
  filter_upwards [hh] with Z hZ
  intro d hd hd' hU hT data cert a i ha ha' hnext r z hr hr' hs hs' hQ hf ht
  have hQ' (θ : RayQuotient.Characters M H) :
      ((HeckePrimeRay.twistedFamily M H hH (data.character M) θ).modulus.absNorm : ℝ)≤Z^d := by
    have hb := data.twisted_conductor M H hH θ
    have hb' : ((HeckePrimeRay.twistedFamily M H hH (data.character M) θ).modulus.absNorm : ℝ)≤
        ((M.absNorm^2*(Ideal.span {data.m}).absNorm*(Ideal.span {(72 : O)}).absNorm*
          (Ideal.span {data.u}).absNorm : ℕ) : ℝ) := by exact_mod_cast hb
    exact hb'.trans (by exact_mod_cast hQ)
  have hb := hZ d hd hd' hU hT (data.character M) (cert.nonprincipal M H hH)
    a i ha ha' hnext r (1-z.re) z.im hr hr' hs hs' hQ' hf ht
  simpa only [data.amplitude_eq M H hH] using hb

end SevenEighths.HeckeDetectorPhysicalBins

end

end OAI

end Source1320

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorPhysicalSelection.lean; sha256: a2ec5a5a0eebc9396bea8b8c73f413d82acb5eed72e70db90ec46d5a7cb3f301 -/
section Source1321
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorPhysicalSelection
open HeckeFamily HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)

def physical {Row Slot : Type*} (row : Row→O) (W : Slot→ℝ→ℂ)
    (b w : Slot→ℝ) (z : Slot→ℂ) (U : ℝ) (u : Row) (s : Slot) : ℂ :=
  HeckePrimeRow.canonicalPrimeAmplitude M H (row u) (W s) (b s) (U^(w s)) (z s)

def weightedMean {Slot : Type*} (slots : Finset Slot) (w g : Slot→ℝ) : ℝ :=
  (∑ s∈slots,w s*g s)/(∑ s∈slots,w s)

theorem weightedMean_bounds {Slot : Type*} (slots : Finset Slot) (w g : Slot→ℝ)
    (δ : ℝ) (hw : ∀ s∈slots,0≤w s) (hL : 0<∑ s∈slots,w s)
    (hg : ∀ s∈slots,0≤g s ∧ g s≤δ/2) :
    0≤weightedMean slots w g ∧ weightedMean slots w g≤δ/2 := by
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun s hs => mul_nonneg (hw s hs) (hg s hs).1)) hL.le
  · apply (div_le_iff₀ hL).mpr
    calc
      _ ≤ ∑ s∈slots,w s*(δ/2) := Finset.sum_le_sum (fun s hs =>
        mul_le_mul_of_nonneg_left (hg s hs).2 (hw s hs))
      _ = _ := by rw [←Finset.sum_mul]; ring

omit [NeZero M] in
theorem select_physical_product {Row Slot : Type*} (rows : Finset Row) (hne : rows.Nonempty)
    (slots : Finset Slot) (row : Row→O) (W : Slot→ℝ→ℂ) (b w g : Slot→ℝ)
    (zs : Slot→ℂ) (U δ mesh binWidth z : ℝ)
    (hU : 1<U) (hδ : 0≤δ) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<w s) (hwm : ∀ s∈slots,w s≤mesh)
    (hL : 0<∑ s∈slots,w s) (hz : 0≤z) (hzL : z≤∑ s∈slots,w s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      amplitude (U^(w s)) (δ/2) binWidth (physical M H row W b w zs U u s)=g s) :
    ∃ selected : Finset Slot, selected⊆slots ∧ (∀ s∈selected,0<g s) ∧
      (∑ s∈selected,w s)≤z ∧
      ∀ u∈rows, U^(2*weightedMean slots w g*z-δ*mesh)≤
        ‖∏ s∈selected,physical M H row W b w zs U u s‖^2 := by
  obtain ⟨u0,hu0⟩ := hne
  have hg (s : Slot) (hs : s∈slots) : 0≤g s ∧ g s≤δ/2 := by
    rw [←hbins u0 hu0 s hs]
    exact amplitude_bounds _ _ _ _ (by positivity)
  obtain ⟨hq,hqδ⟩ := weightedMean_bounds slots w g δ (fun s hs => (hw s hs).le) hL hg
  have hm : weightedMean slots w g*(∑ s∈slots,w s)≤∑ s∈slots,w s*g s := by
    unfold weightedMean
    rw [div_mul_cancel₀ _ hL.ne']
  obtain ⟨selected,hsub,hpositive,hlen,hspike⟩ := common_bin_selection slots w g U δ mesh binWidth
    (weightedMean slots w g) z hU hδ hmesh hbin hw hwm hg hq hqδ hz hzL hm
  exact ⟨selected,hsub,hpositive,hlen,fun u hu => hspike _ (hbins u hu)⟩

end SevenEighths.HeckeDetectorPhysicalSelection

end

end OAI

end Source1321

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorFiberSpikes.lean; sha256: 212baef4b50c9b070ba6156b1aa038f6f5c8ae8c3e9fa50f4f10bb3d70282da6 -/
section Source1322
namespace OAI

noncomputable section
open scoped Classical
open Set
namespace SevenEighths.HeckeDetectorFiberSpikes
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles

theorem fiber_spikes {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 0≤a)
    (w : ∀ u, Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(w u).label=label)
    (hJ : ∀ u∈rows,(w u).left=J) (hK : ∀ u∈rows,(w u).right=K) :
    let r := Real.logb U ((2 : ℝ)^J.val)
    let m := Real.logb U ((2 : ℝ)^K.val)
    ∀ u∈rows,
      (w u).zero.re∈Icc (0 : ℝ) 1 ∧
      |(w u).frequency|≤2*Real.pi*allowance+(3*i : ℕ)*T ∧
      U^((2*a-1)*r-2*ε)≤
        ‖polynomial (χ u label) true
          (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular (U^tstar) (U^r))
          (U^r) (w u).zero.re (w u).frequency‖^2 ∧
      U^((2*a-1)*m-2*ε)≤
        ‖polynomial (χ u label) false positiveAnnular (U^m) (w u).zero.re (w u).frequency‖^2 := by
  dsimp only
  intro u hu
  have hr : (w u).r=Real.logb U ((2 : ℝ)^J.val) := by rw [(w u).left_exponent hU,hJ u hu]
  have hm : (w u).m=Real.logb U ((2 : ℝ)^K.val) := by rw [(w u).right_exponent hU,hK u hu]
  refine ⟨⟨ha.trans (w u).zero_lower,(w u).real_part_upper⟩,(w u).frequency_bound,?_,?_⟩
  · simpa only [hr,hlabel u hu,Witness.frequency] using (w u).inverse_spike
  · simpa only [hm,hlabel u hu,Witness.frequency] using (w u).plain_spike

end SevenEighths.HeckeDetectorFiberSpikes

end

end OAI

end Source1322

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorFiberEnergy.lean; sha256: 3a2ebd4bb7ec55e8dd6f2b64682ab834d084c706e8e2e71dacc9c630544d643c -/
section Source1323
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorFiberEnergy
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorRowwisePolynomial

theorem inverse_energy {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (ha : 0≤a)
    (w : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (W : ℝ→ℂ) (D wa wb E : ℝ) (P : Row→ℂ)
    (hD : 0<D) (hwb : 0≤wb) (hs : Function.support W⊆Icc wa wb) (hE : 0≤E)
    (height : ℝ) (hh : 0≤height) (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hraw : ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (χ u label) true ((logProfile^[n]) W) D s t*P u‖^2≤E) :
    ∑ u∈rows,‖polynomial (χ u label) true W D (w u).zero.re (w u).frequency*P u‖^2≤
      12*(1+height)*E := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log D) wb
  have hcover : ∀ J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S := by
    simpa only [Real.exp_log hD] using HeckeInverseAmplification.scaleSupport_cover
      W wa wb (Real.log D) (Real.log D) hwb hs (le_refl _)
  have hσ (u : Row) (hu : u∈rows) : (w u).zero.re∈Icc (0 : ℝ) 1 :=
    ⟨ha.trans (w u).zero_lower,(w u).real_part_upper⟩
  have hf (u : Row) (hu : u∈rows) : (w u).frequency∈Icc (-height) height :=
    abs_le.mp ((w u).frequency_bound.trans hfreq)
  have hb := HeckeDetectorRowwiseMarked.marked_rowwise rows (fun u => χ u label) true W D hD S hcover
    P 0 1 (-height) height E (by norm_num) (by linarith) (fun u => (w u).zero.re)
    (fun u => (w u).frequency) hσ hf
    (by simpa using hraw 0 (by omega)) (by simpa using hraw 1 (by omega))
    (by simpa using hraw 2 (by omega))
  refine hb.trans ?_
  nlinarith

theorem plain_energy {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (ha : 0≤a)
    (w : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (W : ℝ→ℂ) (D wa wb E : ℝ) (P : Row→ℂ)
    (hD : 0<D) (hwb : 0≤wb) (hs : Function.support W⊆Icc wa wb) (hE : 0≤E)
    (height : ℝ) (hh : 0≤height) (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hraw : ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) W) D s t*
        polynomial (χ u label) false ((logProfile^[k]) W) D s t*P u‖^2≤E) :
    ∑ u∈rows,‖polynomial (χ u label) false W D (w u).zero.re (w u).frequency*
      polynomial (χ u label) false W D (w u).zero.re (w u).frequency*P u‖^2≤
      192*(1+height)*E := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log D) wb
  have hcover : ∀ J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S := by
    simpa only [Real.exp_log hD] using HeckeInverseAmplification.scaleSupport_cover
      W wa wb (Real.log D) (Real.log D) hwb hs (le_refl _)
  have hσ (u : Row) (hu : u∈rows) : (w u).zero.re∈Icc (0 : ℝ) 1 :=
    ⟨ha.trans (w u).zero_lower,(w u).real_part_upper⟩
  have hf (u : Row) (hu : u∈rows) : (w u).frequency∈Icc (-height) height :=
    abs_le.mp ((w u).frequency_bound.trans hfreq)
  have hb := HeckeDetectorRowwisePlain.plain_squared_rowwise rows (fun u => χ u label) W D hD S hcover
    P 0 1 (-height) height E (by norm_num) (by linarith) hE (fun u => (w u).zero.re)
    (fun u => (w u).frequency) hσ hf hraw
  refine hb.trans ?_
  nlinarith

end SevenEighths.HeckeDetectorFiberEnergy

end

end OAI

end Source1323

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorInverseFiberCount.lean; sha256: 1c83fbceb4bb669db72e508f7363c8352861e6110b5336989ebf2bd06b195d47 -/
section Source1324
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorInverseFiberCount
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial

def inverseTest (U tstar r : ℝ) : ℝ→ℂ :=
  HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular (U^tstar) (U^r)

variable (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)

theorem inverse_fiber_count {Row Label Slot : Type*}
    (rows : Finset Row) (hne : rows.Nonempty) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 1/2≤a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (slots : Finset Slot) (row : Row→O) (W : Slot→ℝ→ℂ) (b widths g : Slot→ℝ) (zs : Slot→ℂ)
    (mesh binWidth z εm C height : ℝ) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤mesh)
    (hL : 0<∑ s∈slots,widths s) (hz : 0≤z) (hzL : z≤∑ s∈slots,widths s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
        (physical M H row W b widths zs U u s)=g s)
    (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hcap1 : Real.logb U ((2 : ℝ)^J.val)+2*z<1)
    (hcap2 : 2*Real.logb U ((2 : ℝ)^J.val)+8*z<3)
    (hraw : ∀ selected : Finset Slot, selected⊆slots →
      Real.logb U ((2 : ℝ)^J.val)+2*(∑ s∈selected,widths s)<1 →
      2*Real.logb U ((2 : ℝ)^J.val)+8*(∑ s∈selected,widths s)<3 →
      ∀ n : ℕ,n≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
        ∑ u∈rows,‖polynomial (χ u label) true
          ((logProfile^[n]) (inverseTest U tstar (Real.logb U ((2 : ℝ)^J.val))))
          (U^(Real.logb U ((2 : ℝ)^J.val))) σ freq*
            (∏ s∈selected,physical M H row W b widths zs U u s)‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ)≤(12*(1+height)*C)*
      U^(1-(2*a-1)*Real.logb U ((2 : ℝ)^J.val)-2*weightedMean slots widths g*z+
        2*ε+(2*a-1)*mesh+εm) := by
  let r := Real.logb U ((2 : ℝ)^J.val)
  have hδ : 0≤2*a-1 := by linarith
  obtain ⟨selected,hsub,hpositive,hlen,hspike⟩ := select_physical_product M H rows hne slots
    row W b widths g zs U (2*a-1) mesh binWidth z hU hδ hmesh hbin hw hwm hL hz hzL hbins
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hcap1' : r+2*(∑ s∈selected,widths s)<1 := by dsimp [r]; linarith
  have hcap2' : 2*r+8*(∑ s∈selected,widths s)<3 := by dsimp [r]; linarith
  have hUp : 0<U := zero_lt_one.trans hU
  have hDp : 0<U^r := Real.rpow_pos_of_pos hUp _
  have hE : 0≤C*U^(1+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have he := HeckeDetectorFiberEnergy.inverse_energy rows χ U a ε tstar T allowance i
    (by linarith) witness label (inverseTest U tstar r) (U^r) (1/4) (9/4) (C*U^(1+εm))
    (fun u => ∏ s∈selected,physical M H row W b widths zs U u s) hDp (by norm_num)
    (HeckeDetectorDyadicActual.inverse_profile_support _ _) hE height hheight hfreq
    (hraw selected hsub hcap1' hcap2')
  have he' : ∑ u∈rows,
      ‖polynomial (χ u label) true (inverseTest U tstar r) (U^r) (witness u).zero.re
        (witness u).frequency*(∏ s∈selected,physical M H row W b widths zs U u s)‖^2≤
      (12*(1+height)*C)*U^(1+εm) := by
    convert he using 1; ring
  exact HeckeDetectorRowCount.inverse_count rows (fun u => χ u label)
    (inverseTest U tstar r) (U^r) (fun u => (witness u).zero.re) (fun u => (witness u).frequency)
    (fun u => ∏ s∈selected,physical M H row W b widths zs U u s)
    U (2*a-1) r (weightedMean slots widths g) z (2*ε) ((2*a-1)*mesh) εm
    (12*(1+height)*C) hUp (fun u hu => (hsp u hu).2.2.1) hspike he'

end SevenEighths.HeckeDetectorInverseFiberCount

end

end OAI

end Source1324

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorPlainFiberCount.lean; sha256: 59d4e231e772f7e2b696add18b8a1480db7d36d6f54cd3e207ac6db2e94659cc -/
section Source1325
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorPlainFiberCount
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial
variable (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)

theorem plain_fiber_count {Row Label Slot : Type*}
    (rows : Finset Row) (hne : rows.Nonempty) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 1/2≤a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (slots : Finset Slot) (row : Row→O) (W : Slot→ℝ→ℂ) (b widths g : Slot→ℝ) (zs : Slot→ℂ)
    (mesh binWidth z κplain εm C height : ℝ) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤mesh)
    (hL : 0<∑ s∈slots,widths s) (hz : 0≤z) (hzL : z≤∑ s∈slots,widths s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
        (physical M H row W b widths zs U u s)=g s)
    (hκ : 0≤κplain) (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hcap : 2*Real.logb U ((2 : ℝ)^K.val)+6*κplain*z≤1)
    (hraw : ∀ selected : Finset Slot, selected⊆slots →
      2*Real.logb U ((2 : ℝ)^K.val)+6*κplain*(∑ s∈selected,widths s)≤1 →
      ∀ j k : ℕ,j+k≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
        ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
          polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
            (∏ s∈selected,physical M H row W b widths zs U u s)‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ)≤(192*(1+height)*C)*
      U^(1-2*(2*a-1)*Real.logb U ((2 : ℝ)^K.val)-2*weightedMean slots widths g*z+
        4*ε+(2*a-1)*mesh+εm) := by
  let m := Real.logb U ((2 : ℝ)^K.val)
  have hδ : 0≤2*a-1 := by linarith
  obtain ⟨selected,hsub,hpositive,hlen,hspike⟩ := select_physical_product M H rows hne slots
    row W b widths g zs U (2*a-1) mesh binWidth z hU hδ hmesh hbin hw hwm hL hz hzL hbins
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hcap' : 2*m+6*κplain*(∑ s∈selected,widths s)≤1 := by
    have hh := mul_le_mul_of_nonneg_left hlen (show 0≤6*κplain by positivity)
    dsimp [m]
    linarith
  have hUp : 0<U := zero_lt_one.trans hU
  have hDp : 0<U^m := Real.rpow_pos_of_pos hUp _
  have hE : 0≤C*U^(1+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have he := HeckeDetectorFiberEnergy.plain_energy rows χ U a ε tstar T allowance i
    (by linarith) witness label positiveAnnular (U^m) (1/4) (9/4) (C*U^(1+εm))
    (fun u => ∏ s∈selected,physical M H row W b widths zs U u s) hDp (by norm_num)
    positiveAnnular_support hE height hheight hfreq (hraw selected hsub hcap')
  have he' : ∑ u∈rows,
      ‖polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        (∏ s∈selected,physical M H row W b widths zs U u s)‖^2≤
      (192*(1+height)*C)*U^(1+εm) := by
    convert he using 1; ring
  have hc := HeckeDetectorRowCount.plain_count rows (fun u => χ u label)
    positiveAnnular (U^m) (fun u => (witness u).zero.re) (fun u => (witness u).frequency)
    (fun u => ∏ s∈selected,physical M H row W b widths zs U u s)
    U (2*a-1) m (weightedMean slots widths g) z (2*ε) ((2*a-1)*mesh) εm
    (192*(1+height)*C) hUp (fun u hu => (hsp u hu).2.2.2) hspike he'
  convert hc using 1; congr 2; ring

end SevenEighths.HeckeDetectorPlainFiberCount

end

end OAI

end Source1325

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorNoSlotInverseCount.lean; sha256: 379a8ec696d698d261265c4a06704ebf3bcd8f715bf664edd3d095b44480b6a7 -/
section Source1326
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter
namespace SevenEighths.HeckeDetectorNoSlotInverseCount
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer HeckeDetectorInverseFiberCount

theorem no_slot_inverse_count
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (R εm : ℝ) (hR : 0≤R) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ {Label : Type*} (rows : Finset FreeRow) (χ : FreeRow→Label→Character)
        (a ε tstar T allowance : ℝ) (i : ℕ), 1<U → 1/2≤a →
      ∀ (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
        (label : Label) (J K : Fin (dyadicLength U)),
      (∀ u∈rows,(witness u).label=label) →
      (∀ u∈rows,(witness u).left=J) → (∀ u∈rows,(witness u).right=K) →
      0≤Real.logb U ((2 : ℝ)^J.val) → Real.logb U ((2 : ℝ)^J.val)≤R →
      ∀ (data : RowData) (reverse : Bool) (C height : ℝ),0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      (∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      (∀ u∈rows,∀ I : Ideal O,idealCoeff (χ u label) I=
        if reverse then starRingEnd ℂ (idealCoeff (data.character ⟨u.val,u.property.1⟩) I)
        else idealCoeff (data.character ⟨u.val,u.property.1⟩) I) →
      (∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
        let W := twistProfile (logTest
          (orientedProfile reverse (inverseTest U tstar (Real.logb U ((2 : ℝ)^J.val)))) n) s t
        RawMoment data W c κ C ∧ RawMoment data (scaleProfile W) c κ C) →
      (rows.card : ℝ)≤(12*(1+height)*(C*K₀))*
        U^(sourceExponent (Real.logb U ((2 : ℝ)^J.val))-
          (2*a-1)*Real.logb U ((2 : ℝ)^J.val)+2*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,he⟩ := no_slot_rowwise_endpoint M H hH S φ hφ hφc hφp hφ0 hφne
    a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB R εm hR hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [he] with U he
  intro Label rows χ a ε tstar T allowance i hU ha witness label J K hlabel hJ hK hr hrR
    data reverse C height hC hheight hfreq hrows hcoeff hraw
  let r := Real.logb U ((2 : ℝ)^J.val)
  let V := orientedProfile reverse (inverseTest U tstar r)
  have hUp : 0<U := zero_lt_one.trans hU
  have hD : 0<U^r := Real.rpow_pos_of_pos hUp _
  have hbase := HeckeDetectorDyadicActual.inverse_profile_support (U^tstar) (U^r)
  have hs : Function.support V⊆Icc (1/4 : ℝ) (9/4) := by
    cases reverse
    · exact hbase
    · simpa only [V,orientedProfile,Bool.true_eq,ite_true,conjugate_profile_support,inverseTest] using hbase
  have hb := HeckeDetectorDyadicActual.inverse_profile_smooth (U^tstar) (U^r)
  have hV : ContDiff ℝ ∞ V := by
    cases reverse
    · exact hb
    · exact conjugate_profile_smooth _ hb
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hσ (u : FreeRow) (hu : u∈rows) : (witness u).zero.re∈Icc (0 : ℝ) 1 := (hsp u hu).1
  have hf (u : FreeRow) (hu : u∈rows) :
      orientedFrequency reverse (witness u).frequency∈Icc (-height) height := by
    apply abs_le.mp
    rw [orientedFrequency_abs]
    exact (hsp u hu).2.1.trans hfreq
  have hen := he r data rows V (1/4) (9/4) C height (fun u => (witness u).zero.re)
    (fun u => orientedFrequency reverse (witness u).frequency)
    hr hrR hC hheight (by norm_num) (by norm_num) hs hV hrows hσ hf hraw
  have hspike (u : FreeRow) (hu : u∈rows) : U^((2*a-1)*r-2*ε)≤
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true V (U^r) (witness u).zero.re
        (orientedFrequency reverse (witness u).frequency)‖^2 := by
    have hh := (hsp u hu).2.2.1
    rw [norm_of_oriented_coefficients (χ u label) (data.character ⟨u.val,u.property.1⟩)
      reverse (hcoeff u hu) true _ _ _ _ hD] at hh
    exact hh
  have hen' : ∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true V (U^r) (witness u).zero.re
        (orientedFrequency reverse (witness u).frequency)‖^2≤
      (12*(1+height)*(C*K₀))*U^(sourceExponent r+εm) := by
    convert hen using 1; ring
  have hc' := HeckeDetectorRowCount.card_of_energy rows _ U ((2*a-1)*r-2*ε)
    (sourceExponent r+εm) (12*(1+height)*(C*K₀)) hUp hspike hen'
  convert hc' using 1; congr 2; ring

end SevenEighths.HeckeDetectorNoSlotInverseCount

end

end OAI

end Source1326

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorNoSlotPlainCount.lean; sha256: 59978157af54d9518bfcf2ddec8059ce393bc123606636180e3a868732923d23 -/
section Source1327
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorNoSlotPlainCount
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorRowwisePolynomial

theorem no_slot_plain_count {Row Label : Type*}
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 0≤a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (εm C height : ℝ) (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hraw : ∀ j k : ℕ,j+k≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
        (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
        polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
        (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq‖^2≤
          C*U^(max 1 (2*Real.logb U ((2 : ℝ)^K.val))+εm)) :
    (rows.card : ℝ)≤(192*(1+height)*C)*
      U^(max 1 (2*Real.logb U ((2 : ℝ)^K.val))-
        2*(2*a-1)*Real.logb U ((2 : ℝ)^K.val)+4*ε+εm) := by
  let m := Real.logb U ((2 : ℝ)^K.val)
  have hUp : 0<U := zero_lt_one.trans hU
  have hDp : 0<U^m := Real.rpow_pos_of_pos hUp _
  have hE : 0≤C*U^(max 1 (2*m)+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU ha
    witness label J K hlabel hJ hK
  have he := HeckeDetectorFiberEnergy.plain_energy rows χ U a ε tstar T allowance i ha
    witness label positiveAnnular (U^m) (1/4) (9/4) (C*U^(max 1 (2*m)+εm))
    (fun _ => 1) hDp (by norm_num) positiveAnnular_support hE height hheight hfreq
    (by simpa only [mul_one] using hraw)
  simp only [mul_one] at he
  have hs (u : Row) (hu : u∈rows) : U^(2*((2*a-1)*m-2*ε))≤
      ‖polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency‖^2 := by
    rw [show 2*((2*a-1)*m-2*ε)=((2*a-1)*m-2*ε)+((2*a-1)*m-2*ε) by ring,
      Real.rpow_add hUp,norm_mul,mul_pow]
    exact mul_le_mul (hsp u hu).2.2.2 (hsp u hu).2.2.2
      (Real.rpow_nonneg hUp.le _) (sq_nonneg _)
  have he' : ∑ u∈rows,
      ‖polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency‖^2≤
      (192*(1+height)*C)*U^(max 1 (2*m)+εm) := by convert he using 1; ring
  have hh := HeckeDetectorRowCount.card_of_energy rows _ U (2*((2*a-1)*m-2*ε))
    (max 1 (2*m)+εm) (192*(1+height)*C) hUp hs he'
  convert hh using 1; congr 2; ring

end SevenEighths.HeckeDetectorNoSlotPlainCount

end

end OAI

end Source1327

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorSimultaneousSupport.lean; sha256: fe274df3b8e03b30832ac3e87c995e7284144ee23c80e6c9dee940f696f8f0b3 -/
section Source1328
namespace OAI

noncomputable section

open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorSimultaneousSupport
open HeckeFamily HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorDyadicGeometry HeckeDetectorSaturation HeckeDetectorNormalized

theorem from_actual_zero (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
        (a : ℝ) (i : ℕ), i≤I → 51/100≤a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        ∀ j : ι, (χ j).modulus.absNorm≤Z^d → ∀ ρ : ℂ,
        LFunction (χ j) ρ=0 → a≤ρ.re → |ρ.im|≤(3*i : ℕ)*Z^τ →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
        ∃ J∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
          ∃ K∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
            ∃ ν r m : ℝ,
              ‖ν‖≤(Z^d)^(τ/(2*dmax)) ∧ (Z^d)^r=(2 : ℝ)^J ∧ (Z^d)^m=(2 : ℝ)^K ∧
              tstar-1/2-76*ε≤r ∧ r≤tstar+ε ∧ 0≤m ∧ m≤1/2+75*ε ∧ tstar-r-ε≤m ∧
              (Z^d)^((2*a-1)*r-2*ε)≤
                ‖polynomial (χ j) true
                  (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular ((Z^d)^tstar) ((Z^d)^r))
                  ((Z^d)^r) ρ.re (2*Real.pi*ν-ρ.im)‖^2 ∧
              (Z^d)^((2*a-1)*m-2*ε)≤
                ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) ρ.re (2*Real.pi*ν-ρ.im)‖^2 := by
  have hdmaxp : 0<dmax := hdmin.trans_le hdmax
  have hτF : 0<τ/(2*dmax) := by positivity
  obtain ⟨C,UN,hC,hN⟩ := exists_normalized_product 1 (1/2) (τ/(2*dmax))
    (by norm_num) (by norm_num) (by norm_num) hτF
  obtain ⟨US,hS⟩ := actual_saturation 22 dmax τ ε e κ η C
    (by norm_num) hdmaxp.le hτ hε he he' hκ hκ' hη hbudget hC.le
  have hscale := uniform_scale_threshold dmin (max 8 (max UN US)) hdmin
  have hzeroH := uniform_zero_height dmin τ I hτzero
  have hbudgetH := uniform_height_budget dmin τ η I hτ.le hη hτheight
  have hFourier := uniform_fourier_allowance dmax τ hdmaxp hτ
  have hcost := uniform_power_allowance 8 0 dmin ε hε.le (mul_pos hdmin hε)
  have hT := (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2 : ℝ))
  have hall := hscale.and (hzeroH.and (hbudgetH.and (hFourier.and (hcost.and
    (hT.and (eventually_ge_atTop (1 : ℝ)))))))
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.mp hall
  refine ⟨Z₀,?_⟩
  intro Z hZlarge d hd hd' ι _ χ hχ a i hi ha ha' hmax j hQ ρ hzero hρ him tstar ht ht'
  obtain ⟨hscale,hzeroH,hbudgetH,hFourier,hcost,hT,hZ⟩ := hZ₀ Z hZlarge
  let U := Z^d
  have hd0 : 0≤d := (hdmin.trans_le hd).le
  have hlarge := hscale d hd
  have hU8 : 8≤U := (le_max_left _ _).trans hlarge
  have hUN : UN≤U := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hUS : US≤U := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hU2 : 2≤U := by linarith
  have hU1 : 1<U := by linarith
  have hUp : 0<U := by linarith
  have hρlo : 51/100≤ρ.re := ha.trans hρ
  have hρhi : ρ.re≤1 := le_of_lt (lt_of_not_ge (fun hh =>
    LFunction_ne_zero_of_one_le_re (χ j) hh (Or.inr (hχ j)) hzero))
  have hh := him.trans (hzeroH d hd i hi)
  obtain ⟨hDs,hDs'⟩ := truncation_scale U tstar hU2 ht ht'
  obtain ⟨J,hJ,K,hK,ν,hν,hprod,hD,hDN,hterminal⟩ :=
    hN U hUN (χ j) (hχ j) (U^tstar) hDs hDs' (by simpa using hQ) ρ hρlo hzero hh
  obtain ⟨hr,hr',hm,hm',heJ,heK⟩ := dyadic_scale_bounds U hU8 J K hterminal
  let r := Real.logb U ((2 : ℝ)^J)
  let m := Real.logb U ((2 : ℝ)^K)
  change U^r=(2 : ℝ)^J at heJ
  change U^m=(2 : ℝ)^K at heK
  have hJpow : (Z^d)^r=(2 : ℝ)^J := heJ
  have hKpow : (Z^d)^m=(2 : ℝ)^K := heK
  have hcostU : 8≤U^ε := by simpa using hcost d hd
  have hsupport := support_exponents U tstar r m ε hU1 hcostU
    (by simpa only [heJ] using hD) (by simpa only [heJ,heK] using hDN)
  have hfreq : |2*Real.pi*ν-ρ.im|+(Z^τ)/2≤(3*i+2 : ℕ)*Z^τ := by
    have habs : |ν|≤U^(τ/(2*dmax)) := by simpa only [Real.norm_eq_abs] using hν
    have hnu := (mul_le_mul_of_nonneg_left habs (show 0≤2*Real.pi by positivity)).trans
      (hFourier d hd0 hd')
    have hbase : |2*Real.pi*ν-ρ.im|≤2*Real.pi*|ν|+|ρ.im| := by
      simpa only [sub_zero,zero_sub,abs_neg,abs_mul,
        abs_of_pos (show 0<2*Real.pi by positivity)] using
        (abs_sub_le (2*Real.pi*ν) 0 ρ.im)
    push_cast at him ⊢
    nlinarith
  have hs := hS Z d hZ hd0 hd' hT hUS hU1 χ hχ a i ha ha' hmax j (U^tstar)
    r m ρ.re (2*Real.pi*ν-ρ.im) hQ (by positivity) hr hr' hm hm'
    (by simpa only [hJpow] using hD.le) hρ hρhi hfreq (hbudgetH d hd i hi)
    (by simpa only [hJpow,hKpow] using hprod)
  refine ⟨J,hJ,K,hK,ν,r,m,hν,heJ,heK,?_,hsupport.1,hm,hs.1,
    (by linarith [hsupport.2]),hs.2.1,hs.2.2⟩
  linarith [hsupport.2,hs.1]

theorem from_actual_maximum (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
        (a : ℝ) (i : ℕ), i≤I → 51/100<a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        a≤HeckeDetectorZeros.zeroMaximum χ hχ ((3*i : ℕ)*Z^τ) →
        (∀ j : ι, (χ j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
        ∃ j : ι, ∃ ρ : ℂ, LFunction (χ j) ρ=0 ∧ a≤ρ.re ∧ |ρ.im|≤(3*i : ℕ)*Z^τ ∧
        ∃ J∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
          ∃ K∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
            ∃ ν r m : ℝ,
              ‖ν‖≤(Z^d)^(τ/(2*dmax)) ∧ (Z^d)^r=(2 : ℝ)^J ∧ (Z^d)^m=(2 : ℝ)^K ∧
              tstar-1/2-76*ε≤r ∧ r≤tstar+ε ∧ 0≤m ∧ m≤1/2+75*ε ∧ tstar-r-ε≤m ∧
              (Z^d)^((2*a-1)*r-2*ε)≤
                ‖polynomial (χ j) true
                  (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular ((Z^d)^tstar) ((Z^d)^r))
                  ((Z^d)^r) ρ.re (2*Real.pi*ν-ρ.im)‖^2 ∧
              (Z^d)^((2*a-1)*m-2*ε)≤
                ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) ρ.re (2*Real.pi*ν-ρ.im)‖^2 := by
  obtain ⟨Z₀,hZ₀⟩ := from_actual_zero dmin dmax τ ε e κ η I hdmin hdmax hτ
    hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' ι _ χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  obtain ⟨j,ρ,hzero,him,heq⟩ := HeckeDetectorZeros.maximum_attained χ hχ
    ((3*i : ℕ)*Z^τ) (ha.trans_le hcurrent)
  have hρ : a≤ρ.re := by rw [heq]; exact hcurrent
  exact ⟨j,ρ,hzero,hρ,him,hZ₀ Z hZ d hd hd' χ hχ a i hi ha.le ha' hnext j
    (hQ j) ρ hzero hρ him tstar ht ht'⟩

end SevenEighths.HeckeDetectorSimultaneousSupport

end

end OAI

end Source1328

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorSupportedWitness.lean; sha256: b1bd8fc046e2adf721bd06c8c9c206a0f19f02637668e8206d235739f03917e5 -/
section Source1329
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorSupportedWitness
open HeckeFamily HeckeDetectorWitnessRows

structure SupportedWitness {Label : Type*} (χ : Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    extends Witness χ U a ε tstar T allowance i where
  product_length_lower : tstar-r-ε≤m

theorem actual_supported_witness_family (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ,∀ Z : ℝ,Z₀≤Z → ∀ d : ℝ,dmin≤d → d≤dmax →
      ∀ {Row Label : Type*} [Fintype Label] (χ : Row→Label→Character)
        (hχ : ∀ u j,(χ u j).residue≠1) (a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
        (∀ u,HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ)<a+2*e) →
        (∀ u,a≤HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ)) →
        (∀ u j,(χ u j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ,1≤tstar → tstar≤3/2 →
          Nonempty (∀ u,SupportedWitness (χ u) (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := HeckeDetectorSimultaneousSupport.from_actual_maximum dmin dmax τ ε e κ η I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row Label _ χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  have hw (u : Row) : Nonempty (SupportedWitness (χ u) (Z^d) a ε tstar (Z^τ)
      ((Z^d)^(τ/(2*dmax))) i) := by
    obtain ⟨j,ρ,hzero,hρ,hheight,J,hJ,K,hK,nu,r,m,hnu,hleft,hright,hr,hr',hm,hm',hprod,hM,hS⟩ :=
      hZ₀ Z hZ d hd hd' (χ u) (hχ u) a i hi ha ha' (hnext u) (hcurrent u) (hQ u) tstar ht ht'
    exact ⟨⟨⟨j,ρ,hzero,hρ,hheight,⟨J,Finset.mem_range.mp hJ⟩,⟨K,Finset.mem_range.mp hK⟩,
      nu,r,m,hnu,hleft,hright,hr,hr',hm,hm',hM,hS⟩,hprod⟩⟩
  exact ⟨fun u => Classical.choice (hw u)⟩

theorem fiber_lengths {Row Label : Type*} (rows : Finset Row) (hne : rows.Nonempty)
    (χ : Row→Label→Character) (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (J K : Fin (dyadicLength U))
    (hJ : ∀ u∈rows,(w u).left=J) (hK : ∀ u∈rows,(w u).right=K) :
    let r := Real.logb U ((2 : ℝ)^J.val)
    let m := Real.logb U ((2 : ℝ)^K.val)
    tstar-r-ε≤m ∧ r≤tstar+ε ∧ m≤1/2+75*ε ∧ tstar-1/2-76*ε≤r ∧ 0≤m := by
  obtain ⟨u,hu⟩ := hne
  have hr : (w u).r=Real.logb U ((2 : ℝ)^J.val) := by
    rw [(w u).toWitness.left_exponent hU,hJ u hu]
  have hm : (w u).m=Real.logb U ((2 : ℝ)^K.val) := by
    rw [(w u).toWitness.right_exponent hU,hK u hu]
  exact hr ▸ hm ▸ ⟨(w u).product_length_lower,(w u).inverse_length_upper,
    (w u).plain_length_upper,(w u).inverse_length_lower,(w u).plain_length_lower⟩

end SevenEighths.HeckeDetectorSupportedWitness

end

end OAI

end Source1329

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorRowCountOptimization.lean; sha256: db2977184a11c1ee832e6805fffa897c34d8910cd798a31123c9b5dacf5f0c20 -/
section Source1330
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorRowCount

theorem count_bound_of_source_branches (B C U δ x Δ t r m ε ν γ : ℝ)
    (hC : 0≤C) (hU : 1≤U) (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) (hΔ : 0≤Δ) (hΔ' : Δ≤1/8)
    (ht : 1≤t) (ht' : t≤3/2) (hν : 0≤ν) (hγ : 0≤γ)
    (hleft : t-r-γ≤m) (hright : r≤t+γ)
    (hI0 : B≤C*U^(max 1 ((1+5*r)/6)-δ*r+ε))
    (hP0 : B≤C*U^(1-2*δ*m+ε))
    (hI : 23/37≤r → r<1 → ν<(1-r)/2 → B≤C*U^(inverseExponent δ x r+ε))
    (hP : r≤crossing x t → m<1/2 → ν<(1-2*m)/(9/2+12*Δ) →
      B≤C*U^(1-2*δ*m-2*(δ*x)*(1-2*m)/(9/2+12*Δ)+ε)) :
    B≤C*U^(max (shortExponent δ x t) (longExponent δ t)+Δ/4+ε+6*ν+5*γ) := by
  let target := max (shortExponent δ x t) (longExponent δ t)+Δ/4+ε+6*ν+5*γ
  have hshort : shortExponent δ x t≤max (shortExponent δ x t) (longExponent δ t) := le_max_left _ _
  have hlong : longExponent δ t≤max (shortExponent δ x t) (longExponent δ t) := le_max_right _ _
  have hbase := short_ge_base hδ hx hx' ht'
  have hcross := crossing_bounds hx hx' ht ht'
  have hchoose := selected_short_bound (t:=t) (r:=r) hδ hx hx'
  have promote (p : ℝ) (hp : B≤C*U^p) (hpt : p≤target) : B≤C*U^target :=
    hp.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hpt) hC)
  by_cases hr1 : 1≤r
  · have hmax : max 1 ((1+5*r)/6)=(1+5*r)/6 := max_eq_right (by linarith)
    rw [hmax] at hI0
    apply promote _ hI0
    have hl := long_count_bound hδ' hγ hright
    dsimp [target]
    have hcγ : (5/6-δ)*γ≤γ := by nlinarith [mul_nonneg hδ hγ]
    nlinarith
  have hr1' : r<1 := lt_of_not_ge hr1
  have hmax : max 1 ((1+5*r)/6)=1 := max_eq_left (by linarith)
  rw [hmax] at hI0
  by_cases hrc : crossing x t≤r
  · by_cases hcap : (1-r)/2≤ν
    · apply promote _ hI0
      have hz := inverse_zero_capacity hδ hcap
      have hv : 2*δ*ν≤6*ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδ') hν]
      dsimp [target]
      linarith
    · apply promote _ (hI (hcross.1.trans hrc) hr1' (lt_of_not_ge hcap))
      have hs := hchoose.2 hrc
      dsimp [target]
      linarith
  have hrc' : r≤crossing x t := (lt_of_not_ge hrc).le
  by_cases hm : 1/2≤m
  · apply promote _ hP0
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    dsimp [target]
    linarith
  have hm' : m<1/2 := lt_of_not_ge hm
  by_cases hcap : (1-2*m)/(9/2+12*Δ)≤ν
  · apply promote _ hP0
    have hk0 : 0<3/4+2*Δ := by linarith
    have hk1 : 3/4+2*Δ≤1 := by linarith
    have hz := plain_zero_capacity hδ hk0 hk1 hν
      (show (1-2*m)/(6*(3/4+2*Δ))≤ν by convert hcap using 1; ring)
    have hv : 6*δ*ν≤6*ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδ') hν]
    dsimp [target]
    linarith
  · apply promote _ (hP hrc' hm' (lt_of_not_ge hcap))
    have hmm : 1/3-γ≤m := by linarith [hcross.2.2.1]
    have hp := plain_capacity_comparison hδ (show δ≤1 by linarith) hx hx' hΔ hΔ'
      hmm hm'.le hγ hleft
    have hs := hchoose.1 hrc'
    dsimp [target]
    linarith

end SevenEighths.HeckeDetectorRowCount

end

end OAI

end Source1330

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorBranchBudget.lean; sha256: 10491ef291665f80ff61771bce01c4aa5fed4fe168b92de67427d683c6fc77a7 -/
section Source1331
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorBranchBudget
open HeckeDetectorRowCount

def commonLoss (ε εm mesh ν : ℝ) : ℝ := 154*ε+εm+mesh+ν

theorem no_slot_inverse_loss (r δ ε εm mesh ν : ℝ)
    (hε : 0≤ε) (hm : 0≤mesh) (hν : 0≤ν) :
    max 1 ((1+5*r)/6)-δ*r+2*ε+εm≤
      max 1 ((1+5*r)/6)-δ*r+commonLoss ε εm mesh ν := by
  unfold commonLoss
  linarith

theorem no_slot_plain_loss (m δ ε εm mesh ν : ℝ)
    (hε : 0≤ε) (hm : m≤1/2+75*ε) (hmesh : 0≤mesh) (hν : 0≤ν) :
    max 1 (2*m)-2*δ*m+4*ε+εm≤1-2*δ*m+commonLoss ε εm mesh ν := by
  have hx : max 1 (2*m)≤1+150*ε := max_le (by linarith) (by linarith)
  unfold commonLoss
  linarith

theorem inverse_marked_loss (r δ x ε εm mesh ν : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (_hx : 0≤x) (hx1 : x≤1/2)
    (hε : 0≤ε) (hmesh : 0≤mesh) (hν : 0≤ν) :
    1-δ*r-2*(δ*x)*((1-r)/2-ν)+2*ε+δ*mesh+εm≤
      inverseExponent δ x r+commonLoss ε εm mesh ν := by
  have hq : 2*(δ*x)≤1 := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx1), hδ1]
  have hm := mul_le_mul_of_nonneg_right hδ1 hmesh
  have hn := mul_le_mul_of_nonneg_right hq hν
  unfold inverseExponent commonLoss
  nlinarith

theorem plain_marked_loss (m δ x Δ ε εm mesh ν : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (_hx : 0≤x) (hx1 : x≤1/2)
    (hε : 0≤ε) (hmesh : 0≤mesh) (hν : 0≤ν) :
    1-2*δ*m-2*(δ*x)*((1-2*m)/(9/2+12*Δ)-ν)+4*ε+δ*mesh+εm≤
      1-2*δ*m-2*(δ*x)*(1-2*m)/(9/2+12*Δ)+commonLoss ε εm mesh ν := by
  have hq : 2*(δ*x)≤1 := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx1), hδ1]
  have hm := mul_le_mul_of_nonneg_right hδ1 hmesh
  have hn := mul_le_mul_of_nonneg_right hq hν
  unfold commonLoss
  have heq : 2*(δ*x)*((1-2*m)/(9/2+12*Δ)-ν)=
      2*(δ*x)*(1-2*m)/(9/2+12*Δ)-2*(δ*x)*ν := by ring
  rw [heq]
  linarith

theorem inverse_requested_capacity (r ν : ℝ) (hr : 23/37≤r) (_hr1 : r<1)
    (hν : 0<ν) (hνcap : ν<(1-r)/2) :
    0≤(1-r)/2-ν ∧ (1-r)/2-ν≤7/37 ∧
      r+2*((1-r)/2-ν)<1 ∧ 2*r+8*((1-r)/2-ν)<3 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem plain_requested_capacity (Δ x t r m ε ν : ℝ)
    (hΔ : 0≤Δ) (hx : 0≤x) (hx1 : x≤1/2) (ht : 1≤t) (ht1 : t≤3/2)
    (hr : r≤crossing x t) (hleft : t-r-ε≤m) (hε : ε≤1/12)
    (hν : 0≤ν) (hνcap : ν<(1-2*m)/(9/2+12*Δ)) :
    0≤(1-2*m)/(9/2+12*Δ)-ν ∧ (1-2*m)/(9/2+12*Δ)-ν≤7/37 ∧
      2*m+6*(3/4+2*Δ)*((1-2*m)/(9/2+12*Δ)-ν)≤1 := by
  have hcross := crossing_bounds hx hx1 ht ht1
  have hm : 1/4≤m := by linarith [hcross.2.2.1]
  have hd : 0<9/2+12*Δ := by linarith
  have hc : (1-2*m)/(9/2+12*Δ)≤7/37 := (div_le_iff₀ hd).mpr (by nlinarith)
  refine ⟨by linarith,by linarith,?_⟩
  have heq : 6*(3/4+2*Δ)=9/2+12*Δ := by ring
  rw [heq,mul_sub,mul_div_cancel₀ _ hd.ne']
  nlinarith [mul_nonneg hd.le hν]

end SevenEighths.HeckeDetectorBranchBudget

end

end OAI

end Source1331

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorRawFiber.lean; sha256: 491911b0b17d19943fdb1b43f479e741279e0c0c2b9f1e9e9c5d11de24335c5d -/
section Source1332
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set
namespace SevenEighths.HeckeDetectorRawFiber
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorWitnessRows
open HeckeDetectorSupportedWitness HeckeDetectorCoefficientTransfer HeckeDetectorInverseFiberCount
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles

structure Fiber (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ) (Label Slot : Type*)
    (U a ε tstar T allowance : ℝ) (i : ℕ) where
  rows : Finset FreeRow
  nonempty : rows.Nonempty
  family : FreeRow→Label→Character
  witness : ∀ u,SupportedWitness (family u) U a ε tstar T allowance i
  label : Label
  left : Fin (dyadicLength U)
  right : Fin (dyadicLength U)
  fixed_label : ∀ u∈rows,(witness u).label=label
  fixed_left : ∀ u∈rows,(witness u).left=left
  fixed_right : ∀ u∈rows,(witness u).right=right
  row_norm : ∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤U
  rowData : RowData
  reverse : Bool
  row_coeff : ∀ u∈rows,∀ J : Ideal O,idealCoeff (family u label) J=
    if reverse then starRingEnd ℂ (idealCoeff (rowData.character ⟨u.val,u.property.1⟩) J)
    else idealCoeff (rowData.character ⟨u.val,u.property.1⟩) J
  slots : Finset Slot
  profile : Slot→ℝ→ℂ
  upper : Slot→ℝ
  widths : Slot→ℝ
  external : Slot→ℂ
  bin : Slot→ℝ
  mesh : ℝ
  binWidth : ℝ
  mesh_nonneg : 0≤mesh
  binWidth_pos : 0<binWidth
  widths_pos : ∀ s∈slots,0<widths s
  widths_mesh : ∀ s∈slots,widths s≤mesh
  supply : 7/37≤∑ s∈slots,widths s
  fixed_bin : ∀ u∈rows,∀ s∈slots,
    HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
      (physical M H (fun u : FreeRow => u.val) profile upper widths external U u s)=bin s

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

def Fiber.r (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ := Real.logb U ((2 : ℝ)^F.left.val)
def Fiber.m (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ := Real.logb U ((2 : ℝ)^F.right.val)
def Fiber.q (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ := weightedMean F.slots F.widths F.bin
def Fiber.inverseProfile (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ→ℂ := inverseTest U tstar F.r
def Fiber.physicalProduct (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (u : FreeRow) : ℂ :=
  ∏ s∈selected,physical M H (fun u : FreeRow => u.val) F.profile F.upper F.widths F.external U u s

structure Moments (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (Δ c κ C height εm : ℝ) : Prop where
  inverse_raw : ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
    let W := twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t
    RawMoment F.rowData W c κ C ∧ RawMoment F.rowData (scaleProfile W) c κ C
  inverse_marked : ∀ selected : Finset Slot,selected⊆F.slots →
    F.r+2*(∑ s∈selected,F.widths s)<1 → 2*F.r+8*(∑ s∈selected,F.widths s)<3 →
    ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) true ((logProfile^[n]) F.inverseProfile)
        (U^F.r) s t*F.physicalProduct selected u‖^2≤C*U^(1+εm)
  plain_marked : ∀ selected : Finset Slot,selected⊆F.slots →
    2*F.m+6*(3/4+2*Δ)*(∑ s∈selected,F.widths s)≤1 →
    ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t*
          F.physicalProduct selected u‖^2≤C*U^(1+εm)
  plain_unmarked : ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t‖^2≤
          C*U^(max 1 (2*F.m)+εm)

theorem Fiber.mean_bounds (F : Fiber M H Label Slot U a ε tstar T allowance i) (ha : 1/2≤a) :
    0≤F.q ∧ F.q≤(2*a-1)/2 := by
  obtain ⟨u,hu⟩ := F.nonempty
  apply weightedMean_bounds F.slots F.widths F.bin (2*a-1)
    (fun s hs => (F.widths_pos s hs).le) (by linarith [F.supply])
  intro s hs
  rw [←F.fixed_bin u hu s hs]
  exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)

end SevenEighths.HeckeDetectorRawFiber

end

end OAI

end Source1332

/- Original source: OAI/NumberTheory/DirichletL/Moments/DetectorDictionaryFiber.lean; sha256: 329b8f98e7c80578bf2e1d9a5d6a7887af508f69c0b9e55e89493b57b668d5bf -/
section Source1333
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer HeckeDetectorRawFiber HeckeDetectorRowwisePolynomial
open HeckeDetectorDyadicProfiles CenteredMomentRetainedEnergy
open CenteredMomentPrimeSlot ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

def detectorPositiveRow (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (selected : Finset Slot) (j k : ℕ) (σ t : ℝ) (u : FreeRow) : ℂ :=
  positiveSlotRow η rowMaskElement 1 u.val
    (twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (twistProfile (orientedProfile F.reverse ((logProfile^[k]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (fun s : selected=>primePool M H (F.upper s.val) (U^(F.widths s.val)))
    (fun s : selected=>physicalSlotCoefficient η (F.profile s.val) (U^(F.widths s.val)) (F.external s.val))
    (fun s : selected=>U^(F.widths s.val)) 0 (U^F.m) (U^F.m)

theorem fiber_plain_energy_eq (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η)
    (hMm : M≤Ideal.span {rowMaskElement}) (hU : 0<U)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ)
    (hη : ∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→IsCoprime J η.modulus) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) σ t*
      polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) σ t*
        F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖detectorPositiveRow F η selected j k σ t u‖^2 := by
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  have hc := F.row_coeff u hu
  rw [hdata] at hc
  have he := momentData_plain_pair_norm M H η (F.family u F.label) u F.reverse hc hMm
    ((logProfile^[j]) positiveAnnular) ((logProfile^[k]) positiveAnnular)
    (fun s : selected=>F.profile s.val) (fun s : selected=>F.upper s.val)
    (fun s : selected=>U^(F.widths s.val)) (fun s : selected=>F.external s.val)
    (U^F.m) (U^F.m) σ t (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _)
    (fun s=>Real.rpow_pos_of_pos hU _) (fun s=>hη s.val s.property)
  have hprod := Finset.prod_coe_sort selected (fun s=>HeckePrimeRow.canonicalPrimeAmplitude M H u.val
    (F.profile s) (F.upper s) (U^(F.widths s)) (F.external s))
  rw [hprod] at he
  simpa only [detectorPositiveRow,Fiber.physicalProduct,HeckeDetectorPhysicalSelection.physical,
    Finset.prod_coe_sort] using he

theorem fiber_plain_unmarked_energy_eq (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η)
    (hMm : M≤Ideal.span {rowMaskElement}) (hU : 0<U)
    (j k : ℕ) (σ t : ℝ) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) σ t*
      polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) σ t‖^2)=
      ∑u∈F.rows,‖detectorPositiveRow F η ∅ j k σ t u‖^2 := by
  simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one] using
    fiber_plain_energy_eq F η hdata hMm hU ∅ j k σ t (by simp)

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI

end Source1333

/- Original source: OAI/NumberTheory/DirichletL/Detector/RayPoolGood.lean; sha256: d53b6c0311ae4703aa6291371e227e2252f879719e10362f25b1a2ae292710b1 -/
section Source1334
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical CanonicalQuadraticSieve PrincipalSignalComparison
local notation "Id" => Ideal HeckeFamily.O

theorem prime_coprime_of_norm_gt (η : Character) (P : PrimeIdeal)
    (hN : (η.modulus.absNorm:ℝ)<(P.val.absNorm:ℝ)) : IsCoprime P.val η.modulus := by
  apply Ideal.coprime_of_no_prime_ge
  intro J hPJ hηJ hJ
  have hmax := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have heq := hmax.eq_of_le hJ.ne_top hPJ
  rw [←heq] at hηJ
  have hd : P.val∣η.modulus := Ideal.dvd_iff_le.mpr hηJ
  have hn := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot))
    (map_dvd Ideal.absNorm hd)
  exact (not_le_of_gt hN) (by exact_mod_cast hn)

theorem pool_eventually_target_coprime (C : Set Id) (S : Finset Id) (η : Character)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∀ᶠx : ℝ in atTop,∀P∈pool C S a b x,IsCoprime P.val η.modulus := by
  filter_upwards [eventually_gt_atTop ((η.modulus.absNorm:ℝ)/a),eventually_gt_atTop (0:ℝ)] with x hx hx0
  intro P hP
  apply prime_coprime_of_norm_gt η P
  exact ((div_lt_iff₀ ha).mp hx).trans (pool_norm_bounds C S ha.le hab hx0 P hP).1

theorem pool_eventually_target_unit_value (C : Set Id) (S : Finset Id) (η : Character)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∀ᶠx : ℝ in atTop,∀P∈pool C S a b x,‖idealCoeff η P.val‖=1 := by
  filter_upwards [pool_eventually_target_coprime C S η a b ha hab] with x hx
  intro P hP
  exact idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero (hx P hP)

theorem pool_supported (C : Set Id) (S : Finset Id) (hS : SourceExclusions S)
    (a b x : ℝ) (P : PrimeIdeal) (hP : P∈pool C S a b x) : Supported P.val :=
  outside_prime_supported S hS.bad P ((mem_pool C S a b x P).mp hP).2.2.2

theorem pool_target_coprime_at_power (C : Set Id) (S : Finset Id) (η : Character)
    (a b ell : ℝ) (ha : 0<a) (hab : a≤b) (hell : 0<ell) :
    ∀ᶠZ : ℝ in atTop,∀P∈pool C S a b (Z^ell),IsCoprime P.val η.modulus :=
  (tendsto_rpow_atTop hell).eventually (pool_eventually_target_coprime C S η a b ha hab)

end SevenEighths.ProbeRaySlots
end

end OAI

end Source1334

/- Original source: OAI/NumberTheory/DirichletL/Moments/DetectorDictionarySupport.lean; sha256: 4f4ed7590dc3d5ceb78ef2ad3aaa673ee6efc41c5b884b18b545aafcea4be38a -/
section Source1335
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma annular_prime_coprime (η : Character) (a D : ℝ) (ha : 0<a) (hD : 0<D)
    (hlarge : (η.modulus.absNorm:ℝ)/a<D)
    (W : ℝ→ℂ) (hs : Function.support W⊆Set.Ici a)
    (P : Ideal O) (hp : Prime P) (hW : W ((P.absNorm:ℝ)/D)≠0) :
    IsCoprime P η.modulus := by
  apply ProbeRaySlots.prime_coprime_of_norm_gt η ⟨P,hp⟩
  have hlo : a*D≤(P.absNorm:ℝ) := (le_div_iff₀ hD).mp (hs hW)
  have hh : (η.modulus.absNorm:ℝ)<a*D := by
    have hh := (div_lt_iff₀ ha).mp hlarge
    nlinarith
  exact hh.trans_le hlo

theorem eventually_primePool_coprime (η : Character) (a : ℝ) (ha : 0<a) :
    ∀ᶠD : ℝ in atTop,∀(M : Ideal O)(H : Subgroup (O⧸M)ˣ)(W : ℝ→ℂ)(b : ℝ),
      Function.support W⊆Set.Ici a →
      ∀P∈primePool M H b D,W ((P.absNorm:ℝ)/D)≠0→IsCoprime P η.modulus := by
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_gt_atTop ((η.modulus.absNorm:ℝ)/a)] with D hD hlarge
  intro M H W b hs P hP hW
  exact annular_prime_coprime η a D ha hD hlarge W hs P (Finset.mem_filter.mp hP).2.1 hW

theorem eventually_primePool_power_coprime (η : Character) (a ell : ℝ) (ha : 0<a) (hell : 0<ell) :
    ∀ᶠZ : ℝ in atTop,∀(M : Ideal O)(H : Subgroup (O⧸M)ˣ)(W : ℝ→ℂ)(b : ℝ),
      Function.support W⊆Set.Ici a →
      ∀P∈primePool M H b (Z^ell),W ((P.absNorm:ℝ)/(Z^ell))≠0→IsCoprime P η.modulus :=
  (tendsto_rpow_atTop hell).eventually (eventually_primePool_coprime η a ha)

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI

end Source1335

/- Original source: OAI/NumberTheory/DirichletL/Moments/DetectorDictionarySource.lean; sha256: b8f6d1f292e243d21ee2a48e3c7d0033e27055d1fad16953881064ed1b1e7391 -/
section Source1336
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbePhysical CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma source_product_le_rowMask (S : Finset (Ideal O))
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) :
    (∏P∈S,P)≤Ideal.span {rowMaskElement} := by
  apply Ideal.dvd_iff_le.mp
  have hne : (Ideal.span {ConcretePrimeRowBridge.goodLambda}:Ideal O)≠Ideal.span {(2:O)} := by
    intro he
    have hh : CanonicalQuadraticSieve.badPrime false=CanonicalQuadraticSieve.badPrime true := he
    have hh := CanonicalQuadraticSieve.badPrime_injective hh
    cases hh
  have hd := Finset.prod_dvd_prod_of_subset CanonicalQuadraticSieve.fixedBadPrimes S (fun P : Ideal O=>P) hbad
  have he : (∏P∈CanonicalQuadraticSieve.fixedBadPrimes,P)=Ideal.span {rowMaskElement} := by
    change (∏P∈({Ideal.span {ConcretePrimeRowBridge.goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O)),P)=_
    rw [Finset.prod_pair hne]
    unfold rowMaskElement
    rw [←Ideal.span_singleton_mul_span_singleton]
    exact mul_comm _ _
  rwa [he] at hd

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sourceMomentBase (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) :
    Sum Bool (RayQuotient.Characters M H)→Character :=
  Sum.elim (fun b=>if b then fixedSourcePrincipal S hS else η.inverse.excludePrimes S hS)
    (fun θ=>(HeckeRayQuotient.character M H hH θ).inverse)

lemma sourceMomentData_base (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character)
    (j : Sum Bool (RayQuotient.Characters M H)) :
    sourceMomentData M H hH S hS η j=momentData (sourceMomentBase M H hH S hS η j) := by
  rcases j with b|θ
  · cases b <;> rfl
  · rfl

theorem eventually_source_slots_coprime {N : ℕ}
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character)
    (ell : Fin N→ℝ) (hell : ∀i,0<ell i) (a : ℝ) (ha : 0<a) :
    ∀ᶠZ : ℝ in atTop,∀j : Sum Bool (RayQuotient.Characters M H),∀i : Fin N,
      ∀d : ℝ,d≠0→∀(W : ℝ→ℂ)(b : ℝ),Function.support W⊆Set.Ici a→
      ∀P∈primePool M H b ((Z^d)^(ell i/d)),
        W ((P.absNorm:ℝ)/((Z^d)^(ell i/d)))≠0→
          IsCoprime P (sourceMomentBase M H hH S hS η j).modulus := by
  have he : ∀ᶠZ : ℝ in atTop,∀j : Sum Bool (RayQuotient.Characters M H),∀i : Fin N,
      ∀(W : ℝ→ℂ)(b : ℝ),Function.support W⊆Set.Ici a→
      ∀P∈primePool M H b (Z^(ell i)),W ((P.absNorm:ℝ)/(Z^(ell i)))≠0→
        IsCoprime P (sourceMomentBase M H hH S hS η j).modulus := by
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [eventually_primePool_power_coprime (sourceMomentBase M H hH S hS η j)
      a (ell i) ha (hell i)] with Z hz
    exact hz M H
  filter_upwards [he,eventually_ge_atTop (0:ℝ)] with Z hz hZ
  intro j i d hd W b hs
  have heq : (Z^d)^(ell i/d)=Z^(ell i) := by
    rw [←Real.rpow_mul hZ,mul_div_cancel₀ _ hd]
  rw [heq]
  exact hz j i W b hs

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI

end Source1336

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceFiber.lean; sha256: 4cffd09d689f283fe1c122c150e8f65292175804a6991aa2e12fb9b01a1cd64d -/
section Source1337
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentHeckeHeight CenteredMomentPrimeSlot HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open ProbeHighRowFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma rowMaskElement_eq_fixed : rowMaskElement=fixedBadMask := by
  unfold rowMaskElement fixedBadMask
  exact mul_comm _ _

lemma excluded_one_ideal (χ : Character) (I : Ideal O) :
    idealCoeff (excluded χ 1) I=idealCoeff χ I := by
  simp only [excluded_ideal χ 1 one_ne_zero,isCoprime_one_right,ite_true]

lemma natural_unit_mask_coefficient {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O) :
    idealCoeff η I*CanonicalRowCompletion.idealRowHom ((fixedBadMask*idealGenerator 1)^6*z) I=
      idealCoeff η I*CanonicalRowCompletion.idealRowHom (fixedBadMask^6*z) I := by
  rw [←F.masked_ideal 1 one_ne_zero,excluded_one_ideal,F.ideal]

lemma natural_unit_mask_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (W₁ W₂ : ℝ→ℂ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    positiveSlotRow η (fixedBadMask*idealGenerator 1) 1 z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η fixedBadMask 1 z W₁ W₂ S β P t X₁ X₂ := by
  simp only [positiveSlotRow,rowTwistedSum,rowSlot,one_mul,natural_unit_mask_coefficient F]

variable {M : Ideal O} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} (hH : RayOrthogonality.globalUnits M≤H)
variable {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}

def fiberSector (F : Fiber M H Label Slot U a ε tstar T allowance i) (η : Character)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ)
    (θ : selected→RayQuotient.Characters M H) (u : FreeRow) : ℂ :=
  sectorValue M H hH (naturalRow η u.val u.property.1).character η 1
    (twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (twistProfile (orientedProfile F.reverse ((logProfile^[k]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (fun s : selected=>fun y=>conj (F.profile s.val y)) (fun s : selected=>F.upper s.val)
    (fun s : selected=>U^(F.widths s.val)) (fun s : selected=>1-(F.external s.val).re)
    (fun s : selected=>-(F.external s.val).im) 0 (U^F.m) (U^F.m) θ

theorem detectorPositiveRow_sector {Slot : Type*}
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (η : Character)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ) (u : FreeRow) (hU : 0<U) :
    detectorPositiveRow F η selected j k σ t u=
      averageWeight (ι:=selected) M H*∑θ : selected→RayQuotient.Characters M H,
        fiberSector hH F η selected j k σ t θ u := by
  have he:=natural_physical_product M H hH (naturalRow η u.val u.property.1) η 1 one_ne_zero
    (twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (twistProfile (orientedProfile F.reverse ((logProfile^[k]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (fun s : selected=>F.profile s.val) (fun s : selected=>F.upper s.val)
    (fun s : selected=>U^(F.widths s.val)) (fun s : selected=>F.external s.val)
    0 (U^F.m) (U^F.m) (by positivity) (fun _=>Real.rpow_pos_of_pos hU _)
  rw [natural_unit_mask_positive (naturalRow η u.val u.property.1)] at he
  simpa only [detectorPositiveRow,rowMaskElement_eq_fixed,fiberSector] using he

theorem fiber_plain_sector_energy (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η)
    (hMm : M≤Ideal.span {rowMaskElement}) (hU : 0<U)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ)
    (hη : ∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→IsCoprime J η.modulus) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) σ t*
      polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) σ t*
        F.physicalProduct selected u‖^2)≤
      ∑θ : selected→RayQuotient.Characters M H,‖averageWeight (ι:=selected) M H‖*
        ∑u∈F.rows,‖fiberSector hH F η selected j k σ t θ u‖^2 := by
  rw [fiber_plain_energy_eq F η hdata hMm hU selected j k σ t hη]
  calc
    _≤∑u∈F.rows,∑θ : selected→RayQuotient.Characters M H,
        ‖averageWeight (ι:=selected) M H‖*‖fiberSector hH F η selected j k σ t θ u‖^2 := by
      apply Finset.sum_le_sum
      intro u hu
      rw [detectorPositiveRow_sector hH F η selected j k σ t u hU]
      exact sector_average_energy M H _
    _= _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source1337

/- Original source: OAI/NumberTheory/DirichletL/Parameters.lean; sha256: 32b77db1ea32e62c931063764ae60738e84737edb39a5f7d2cb40b15ee8ed424 -/
section Source1338
namespace OAI

namespace SevenEighths.Parameters

theorem compensated_geometry {d : ℝ} (_hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 6) :
    (1 / 2 : ℝ) ≤ 5 / 6 - 2 * d ∧
    3 / 16 ≤ 17 / 48 - d ∧
    5 / 16 ≤ 23 / 48 - d ∧
    1 / 12 ≤ 23 / 48 - d - 11 * (1 / 8) / 6 ∧
    (17 / 48 : ℝ) / 2 + (1 / 8) / 12 = 3 / 16 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · norm_num

theorem exists_height_cutoff {dmin allowance A : ℝ}
    (hd : 0 < dmin) (ha : 0 < allowance) (hA : 0 ≤ A) :
    ∃ τ : ℝ, 0 < τ ∧ τ < dmin / 100 ∧
      A * τ < dmin * allowance / 100 := by
  have hden : 0 < 200 * (1 + A) := by positivity
  let τ := min (dmin / 200) (dmin * allowance / (200 * (1 + A)))
  have ht : 0 < τ := lt_min (by positivity) (by positivity)
  have h1 : τ ≤ dmin / 200 := min_le_left _ _
  have h2 : τ ≤ dmin * allowance / (200 * (1 + A)) := min_le_right _ _
  have h2' : τ * (200 * (1 + A)) ≤ dmin * allowance :=
    (le_div_iff₀ hden).mp h2
  refine ⟨τ, ht, by linarith, ?_⟩
  have hp : 0 < dmin * allowance := mul_pos hd ha
  nlinarith

theorem exists_tail_order {τ B saving : ℝ} (hτ : 0 < τ) :
    ∃ N : ℕ, B - τ * N < -saving := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((B + saving) / τ)
  have h := (div_lt_iff₀ hτ).mp hN
  exact ⟨N, by nlinarith⟩

theorem cumulative_frequency_bound {ι : Type*} (s : Finset ι)
    (frequency : ι → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hfreq : ∀ i ∈ s, |frequency i| ≤ T / (4 * s.card)) :
    |∑ i ∈ s, frequency i| ≤ T / 4 := by
  by_cases hs : s.card = 0
  · have he : s = ∅ := Finset.card_eq_zero.mp hs
    simp only [he, Finset.sum_empty, abs_zero]
    positivity
  · have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs
    calc
      |∑ i ∈ s, frequency i| ≤ ∑ i ∈ s, |frequency i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, T / (4 * s.card) := Finset.sum_le_sum hfreq
      _ = T / 4 := by simp only [Finset.sum_const, nsmul_eq_mul]; field_simp

end SevenEighths.Parameters

end OAI

end Source1338

/- Original source: OAI/NumberTheory/DirichletL/ParametersSlotLengths.lean; sha256: f52f5f4282489ffce669a9ebdf91766990fa6c2d7e15178c60d4ec69cb3c0ef6 -/
section Source1339
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.Parameters

theorem exists_distinct_slot_lengths (L : ℝ) (hL : 0<L) :
    ∃N : ℕ,0<N ∧ ∃ell : Fin N→ℝ,Function.Injective ell ∧
      (∀j,0<ell j ∧ ell j<L) ∧ (∑j,ell j)=1/6 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (1/(3*L)))
  have hN1 : (1:ℝ)<N := (le_max_left _ _).trans_lt hN
  have hNp : 0<(N:ℝ) := by linarith
  have hNnat : 0<N := by exact_mod_cast hNp
  have hNL : 1/(3*L)<(N:ℝ) := (le_max_right _ _).trans_lt hN
  have hsmall : 1/(3*(N:ℝ))<L := by
    have hh := (div_lt_iff₀ (show 0<3*L by positivity)).mp hNL
    apply (div_lt_iff₀ (show 0<3*(N:ℝ) by positivity)).mpr
    nlinarith
  let w : Fin N→ℝ := fun j=>1+(j.val:ℝ)/(N:ℝ)
  let A : ℝ := ∑j,w j
  have hw (j : Fin N) : 1≤w j ∧ w j<2 := by
    have hj : (j.val:ℝ)<N := by exact_mod_cast j.isLt
    have hdiv : (j.val:ℝ)/(N:ℝ)<1 := (div_lt_one hNp).mpr hj
    dsimp only [w]
    constructor
    · linarith [div_nonneg (Nat.cast_nonneg j.val) hNp.le]
    · linarith
  have hA : (N:ℝ)≤A := by
    calc
      _ = ∑_j : Fin N,(1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _=>(hw j).1
  have hAp : 0<A := hNp.trans_le hA
  let ell : Fin N→ℝ := fun j=>w j/(6*A)
  refine ⟨N,hNnat,ell,?_,?_,?_⟩
  · intro j k he
    have hden : 6*A≠0 := by positivity
    have hwjk : w j=w k := (div_left_inj' hden).mp he
    have hjk : (j.val:ℝ)/(N:ℝ)=(k.val:ℝ)/(N:ℝ) := by dsimp [w] at hwjk;linarith
    have he' : (j.val:ℝ)=(k.val:ℝ) := (div_left_inj' hNp.ne').mp hjk
    apply Fin.ext
    exact_mod_cast he'
  · intro j
    constructor
    · exact div_pos (by linarith [(hw j).1]) (by positivity)
    · calc
        ell j < 2/(6*A) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (hw j).2
        _ ≤ 2/(6*(N:ℝ)) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
        _ = 1/(3*(N:ℝ)) := by ring
        _ < L := hsmall
  · dsimp only [ell]
    rw [←Finset.sum_div]
    change A/(6*A)=1/6
    field_simp

theorem exists_physical_slot_lengths (dmin dmax mesh R : ℝ)
    (hdmin : 0<dmin) (hd : dmin≤dmax) (hm : 0<mesh) (hR : 0<R) :
    ∃N : ℕ,0<N ∧ ∃ell : Fin N→ℝ,∃rmin : ℝ,0<rmin ∧
      Function.Injective ell ∧ (∑j,ell j)=1/6 ∧
      (∀j,0<ell j ∧ dmax*rmin≤ell j ∧ ell j≤dmin*mesh ∧ ell j≤dmin*R) ∧
      (∀d : ℝ,dmin≤d → d≤dmax → ∀j,rmin≤ell j/d ∧ ell j/d≤mesh ∧ ell j/d≤R) := by
  obtain ⟨N,hN,ell,hi,he,hS⟩ := exists_distinct_slot_lengths (dmin*min mesh R)
    (mul_pos hdmin (lt_min hm hR))
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨j,hj,hjmin⟩ := Finset.exists_min_image Finset.univ ell hne
  have hmax : 0<dmax := hdmin.trans_le hd
  let rmin := ell j/(2*dmax)
  have hr : 0<rmin := div_pos (he j).1 (by positivity)
  have hlo (k : Fin N) : dmax*rmin≤ell k := by
    have hk := hjmin k (Finset.mem_univ k)
    have hiden : dmax*rmin=ell j/2 := by dsimp [rmin]; field_simp
    rw [hiden]
    linarith [(he j).1]
  have hup (k : Fin N) : ell k≤dmin*mesh ∧ ell k≤dmin*R := by
    constructor
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le)
  refine ⟨N,hN,ell,rmin,hr,hi,hS,fun k=>⟨(he k).1,hlo k,(hup k).1,(hup k).2⟩,?_⟩
  intro d hd' hd'' k
  have hd0 : 0<d := hdmin.trans_le hd'
  refine ⟨(le_div_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_⟩
  · exact (by nlinarith : rmin*d≤dmax*rmin).trans (hlo k)
  · exact (hup k).1.trans (by nlinarith)
  · exact (hup k).2.trans (by nlinarith)

end SevenEighths.Parameters

end

end OAI

end Source1339

/- Original source: OAI/NumberTheory/DirichletL/ParametersDetectorScales.lean; sha256: 374bbbb6e7c0cd5d08ddacdb16a2233c730a6d488eb875739369fac982de437a -/
section Source1340
namespace OAI

noncomputable section
namespace SevenEighths.Parameters

theorem exists_detector_scales (R rmin mesh dmin loss ellMin allowance J : ℝ)
    (hR : 0≤R) (hr : 0<rmin) (hm : 0<mesh) (hd : 0<dmin)
    (hl : 0<loss) (hell : 0<ellMin) (ha : 0<allowance) (hJ : 0≤J) :
    ∃ε e κ cost τ : ℝ,
      0<ε ∧ ε≤1/1000 ∧ ε<rmin*mesh ∧ ε≤allowance ∧
      0<e ∧ e<1/1000 ∧ e≤ellMin/4 ∧ e≤allowance ∧
      0<κ ∧ κ≤1 ∧ 0<cost ∧
      12*e*(22+2)+8*κ+2*cost≤ε/2 ∧
      8*e*R+κ≤ε ∧
      0<τ ∧ τ<dmin/2 ∧ 4*τ<dmin*cost ∧
      2*τ*(1+J)≤loss ∧ ∀eps : ℝ,0≤eps → eps≤1 → τ*(2+4*eps)<loss := by
  let ε := min (allowance/2) (min (rmin*mesh/2) (1/2000))
  have hε : 0<ε := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hεa : ε≤allowance/2 := min_le_left _ _
  have hεr : ε≤rmin*mesh/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε≤1/2000 := (min_le_right _ _).trans (min_le_right _ _)
  let e := min (ε/(10000*(1+R))) (min (ellMin/4) (allowance/2))
  have he : 0<e := lt_min (div_pos hε (by positivity)) (lt_min (by positivity) (by positivity))
  have heb : e≤ε/(10000*(1+R)) := min_le_left _ _
  have hep : e*(10000*(1+R))≤ε := (le_div_iff₀ (by positivity)).mp heb
  have heR : 0≤e*R := mul_nonneg he.le hR
  have hel : e≤ellMin/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hea : e≤allowance/2 := (min_le_right _ _).trans (min_le_right _ _)
  let κ := ε/1000
  let cost := ε/1000
  have hk : 0<κ := by dsimp [κ]; positivity
  have hc : 0<cost := by dsimp [cost]; positivity
  let τ := min (dmin*cost/16) (min (dmin/4) (loss/(4*(1+J+6))))
  have ht : 0<τ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have htc : τ≤dmin*cost/16 := min_le_left _ _
  have htd : τ≤dmin/4 := (min_le_right _ _).trans (min_le_left _ _)
  have htl : τ≤loss/(4*(1+J+6)) := (min_le_right _ _).trans (min_le_right _ _)
  have htJ : τ*(4*(1+J+6))≤loss := (le_div_iff₀ (by positivity)).mp htl
  have hprod : 0≤τ*J := mul_nonneg ht.le hJ
  refine ⟨ε,e,κ,cost,τ,hε,by linarith,by nlinarith [mul_pos hr hm],by linarith,
    he,by nlinarith,hel,by linarith,hk,?_,hc,?_,?_,ht,by linarith,?_,?_,?_⟩
  · dsimp [κ];linarith
  · dsimp [κ,cost];nlinarith
  · dsimp [κ];nlinarith
  · have hp := mul_pos hd hc;linarith
  · nlinarith
  · intro eps heps heps1
    have hp := mul_le_mul_of_nonneg_left heps1 ht.le
    nlinarith
end SevenEighths.Parameters

end

end OAI

end Source1340

/- Original source: OAI/NumberTheory/DirichletL/ParametersCentralBudget.lean; sha256: 9ea5e11ef3b449210791351dbdeb9766bdf5f0c8701576b9ab890101b4feaa49 -/
section Source1341
namespace OAI

noncomputable section
namespace SevenEighths.Parameters

theorem exists_central_budget (Δ : ℝ) (hΔ : 0<Δ) :
    ∃ t : ℝ,0<t ∧ t<Δ/4 ∧ t≤1/100000000 ∧
      (0:ℝ)<1/200 ∧ (1/200:ℝ)<1/100 ∧
      (13/16:ℝ)+t+2*t≤7/8 ∧ (7/8:ℝ)≤37/42 ∧ t≤3/16 ∧
      0<Δ-t/4 ∧ Δ-t/4<Δ ∧
      (3/16+Δ-t+t/8+t/8 : ℝ)≤3/16+(Δ-t/4) ∧
      ∀N : ℕ,∃allowance : ℝ,0<allowance ∧
      ∀ε e eps : ℝ,0≤ε → ε≤allowance → 0≤e → e≤allowance →
        0≤eps → eps≤allowance →
        159*ε+t+t+7*t≤1/32 ∧
        (13/16)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
          (26*e+(N+8)*eps+t+t/6)+(t+t+t)+t≤49/440640 := by
  let t := min (Δ/8) (1/100000000)
  have ht : 0<t := lt_min (by positivity) (by norm_num)
  have htΔ : t≤Δ/8 := min_le_left _ _
  have ht1 : t≤1/100000000 := min_le_right _ _
  refine ⟨t,ht,by linarith,ht1,by norm_num,by norm_num,by linarith,
    by norm_num,by linarith,by linarith,by linarith,by linarith,?_⟩
  intro N
  let allowance := t/((N:ℝ)+2000)
  have hden : 0<(N:ℝ)+2000 := by positivity
  have ha : 0<allowance := div_pos ht hden
  have ha0 : allowance≤t/2000 := div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N])
  have hap : allowance*((N:ℝ)+2000)=t := by dsimp [allowance];field_simp
  refine ⟨allowance,ha,?_⟩
  intro ε e eps hε hεa he hea heps hepsa
  have hεt : 2000*ε≤t := by linarith
  have het : 2000*e≤t := by linarith
  have hepsN : ((N:ℝ)+2000)*eps≤t := by
    have h := mul_le_mul_of_nonneg_left hepsa hden.le
    nlinarith
  have heps8 : ((N:ℝ)+8)*eps≤t := by nlinarith
  constructor <;> nlinarith
end SevenEighths.Parameters

end

end OAI

end Source1341

/- Original source: OAI/NumberTheory/DirichletL/ParametersHighData.lean; sha256: e1e6e123d840366a92bc252e25510da2c103540880c7ba87e1077cac68451f0d -/
section Source1342
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.Parameters

structure HighData (Δ : ℝ) where
  t : ℝ
  N : ℕ
  ell : Fin N→ℝ
  rmin : ℝ
  ε : ℝ
  e : ℝ
  κ : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  t_pos : 0<t
  t_delta : t<Δ/4
  t_small : t≤1/100000000
  slots_pos : 0<N
  slots_injective : Function.Injective ell
  slots_sum : (∑j,ell j)=1/6
  slots_bounds : ∀j,0<ell j ∧ (7/8)*rmin≤ell j ∧ ell j≤(1/200)*t
  rmin_pos : 0<rmin
  epsilon_pos : 0<ε
  epsilon_small : ε≤1/1000
  epsilon_gap : ε<rmin*t
  e_pos : 0<e
  e_small : e<1/1000
  kappa_pos : 0<κ
  kappa_small : κ≤1
  cost_pos : 0<cost
  eps_pos : 0<eps
  eps_small : eps≤1
  sigma_pos : 0<sigma
  detector_budget : 288*e+8*κ+2*cost≤ε/2
  phase_budget : 8*e*t+κ≤ε
  count_budget : 159*ε+t+t+7*t≤1/32
  central_budget : (13/16)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
    (26*e+(N+8)*eps+t+t/6)+(t+t+t)+t≤49/440640
  geometric_budget : sigma+8*e+t/8≤63/800
  principal_budget : sigma+t/8≤17/48000
  window_budget : sigma+e≤(7/8)*((7/8)*rmin)
  floor_budget : 2*t+26*e+(N+8)*eps+t+t/6+t/8+sigma≤7/1200
  high_saving : sigma+t/8+t/8≤t
  height_choice : ∀J : ℝ,0≤J → ∃τ : ℝ,0<τ ∧ τ<(1/200)/2 ∧
    4*τ<(1/200)*cost ∧ τ<t ∧ 2*τ*(1+J)≤t ∧ τ*(2+4*eps)<t

theorem exists_high_data (Δ : ℝ) (hΔ : 0<Δ) : Nonempty (HighData Δ) := by
  obtain ⟨t,ht,htΔ,ht1,_,_,hgeo,hdtop,ht3,hω,hωΔ,hhigh,hallow⟩ := exists_central_budget Δ hΔ
  obtain ⟨N,hN,ell,rmin,hr,hell,hsum,hbounds,_⟩ :=
    exists_physical_slot_lengths (1/200) (7/8) t t (by norm_num) (by norm_num) ht ht
  obtain ⟨allowance,ha,hbud⟩ := hallow N
  let small := min allowance (t/((N:ℝ)+2000))
  have hsmall : 0<small := lt_min ha (div_pos ht (by positivity))
  have hsa : small≤allowance := min_le_left _ _
  have hst : small≤t/((N:ℝ)+2000) := min_le_right _ _
  have hst0 : small≤t/2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0<ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0<eps := by dsimp [eps];positivity
  have hepss : eps≤small := by dsimp [eps];linarith only [hsmall]
  have heps1 : eps≤1 := by linarith only [hepss, hst0, ht1]
  have hbud' := hbud ε e eps hε.le (hεa.trans hsa) he.le (hea.trans hsa)
    heps.le (hepss.trans hsa)
  have heN : ((N:ℝ)+2000)*eps≤t := by
    have h := (le_div_iff₀ (show 0<(N:ℝ)+2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps≤t := by nlinarith only [heN, heps.le]
  have het : 2000*e≤t := by linarith only [hea, hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0<sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma≤t/2 := min_le_left _ _
  have hsell : sigma≤ellMin/4 := min_le_right _ _
  refine ⟨{
    t:=t,N:=N,ell:=ell,rmin:=rmin,ε:=ε,e:=e,κ:=κ,cost:=cost,eps:=eps,sigma:=sigma
    t_pos:=ht,t_delta:=htΔ,t_small:=ht1,slots_pos:=hN,slots_injective:=hell,slots_sum:=hsum
    slots_bounds:=fun j=>⟨(hbounds j).1,(hbounds j).2.1,(hbounds j).2.2.1⟩
    rmin_pos:=hr,epsilon_pos:=hε,epsilon_small:=hε1,epsilon_gap:=hεgap
    e_pos:=he,e_small:=he1,kappa_pos:=hκ,kappa_small:=hκ1,cost_pos:=hcost
    eps_pos:=heps,eps_small:=heps1,sigma_pos:=hs,detector_budget:=by linarith only [hdet]
    phase_budget:=hphase,count_budget:=hbud'.1,central_budget:=hbud'.2
    geometric_budget:=by linarith only [hst2, het, ht1]
    principal_budget:=by linarith only [hst2, ht1]
    window_budget:=by change sigma+e≤(7/8)*ellMin;linarith only [hsell, heell, hmin]
    floor_budget:=by linarith only [hst2, het, he8, ht1]
    high_saving:=by linarith only [hst2, ht]
    height_choice:=?_ }⟩
  intro J hJ
  let τ := min ((1/200:ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
  have htau : 0<τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hτc : τ≤(1/200:ℝ)*cost/16 := min_le_left _ _
  have hτd : τ≤1/800 := (min_le_right _ _).trans (min_le_left _ _)
  have hτt : τ≤t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
  have hτJ : τ*(4*(J+7))≤t := (le_div_iff₀ (by positivity)).mp hτt
  have hprod : 0≤τ*J := mul_nonneg htau.le hJ
  have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
  refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc, hcost],
      by nlinarith only [hτJ, hprod, htau],by nlinarith only [hτJ, hprod, htau],
      by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
end SevenEighths.Parameters

end

end OAI

end Source1342

/- Original source: OAI/NumberTheory/DirichletL/ParametersProbeWindows.lean; sha256: 322ae5b168555830ccdacd6b82ec8133cde894f2c0e1fd7a725531364822ab78 -/
section Source1343
namespace OAI

noncomputable section
open scoped ContDiff
namespace SevenEighths.Parameters

theorem exists_probe_window : ∃ (w : ℝ→ℝ) (W : SchwartzMap ℝ ℂ),
    ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
    Function.support w ⊆ Set.Ioo 1 2 ∧ (∀ x,0≤w x ∧ w x≤1) ∧
    w (3/2)=1 ∧ w≠0 ∧ (∀ x,W x=(w x:ℂ)) ∧ W≠0 ∧
    Function.support W ⊆ Set.Icc 1 2 ∧
    (∀x,(W x).im=0) ∧ (∀x,0≤(W x).re) := by
  obtain ⟨w,hs,hc,hw,hr,hval⟩ := exists_contDiff_tsupport_subset
    (n:=⊤) (E:=ℝ) (s:=Set.Ioo 1 2) (x:=3/2)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
  let f : ℝ→ℂ := fun x=>(w x:ℂ)
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hw
  have hfc : HasCompactSupport f := hc.comp_left (show (fun x:ℝ=>(x:ℂ)) 0=0 by simp)
  let W : SchwartzMap ℝ ℂ := hfc.toSchwartzMap hf
  have hne : w≠0 := by intro hz;have := congrFun hz (3/2);simp [hval] at this
  refine ⟨w,W,hw,hc,(subset_tsupport w).trans hs,fun x=>hr ⟨x,rfl⟩,hval,hne,
    fun _=>rfl,?_,?_,fun _=>rfl,?_⟩
  · intro hz
    apply hne
    funext x
    have h := congrArg (fun F : SchwartzMap ℝ ℂ => (F x).re) hz
    change w x=0 at h
    exact h
  · intro x hx
    have hwx : w x≠0 := by intro h;apply hx;change (w x:ℂ)=0;rw [h];rfl
    exact Set.Ioo_subset_Icc_self (hs (subset_tsupport w hwx))
  · intro x
    exact (hr ⟨x,rfl⟩).1
end SevenEighths.Parameters

end

end OAI

end Source1343

/- Original source: OAI/NumberTheory/DirichletL/ParametersFixedSource.lean; sha256: 01fb197c3353d800ef80bc77d56ee3e27a09baab98f22c59ec23db235e901637 -/
section Source1344
namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.Parameters
open ProbePhysical ProbeHighRowFamily CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

lemma fixed_bad_primes_prime : ∀ P∈fixedBadPrimes,Prime P := by
  intro P hP
  rcases Finset.mem_insert.mp hP with hP|hP
  · subst P
    exact Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero)
      lambdaIdeal_maximal.isPrime
  · have he := Finset.mem_singleton.mp hP
    subst P
    exact Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (2:O)≠0))
      twoIdeal_maximal.isPrime

theorem exists_fixed_source (e : ℝ) (he : 0<e)
    (S₀ : Finset (Ideal O)) (hS₀ : ∀P∈S₀,Prime P) :
    ∃ S : Finset (Ideal O), S₀⊆S ∧ SourceExclusions S ∧
      FirstTail (4*e) S ∧ (∀P∈S,P.IsMaximal) := by
  obtain ⟨S,hsub,hS,hfirst⟩ := exists_both_source_exclusions (4*e) (by positivity)
    (S₀∪fixedBadPrimes)
    (fun P hP => (Finset.mem_union.mp hP).elim (hS₀ P) (fixed_bad_primes_prime P))
    Finset.subset_union_right
  refine ⟨S,Finset.subset_union_left.trans hsub,hS,hfirst,?_⟩
  intro P hP
  exact (Ideal.isPrime_of_prime (hS.prime P hP)).isMaximal (hS.prime P hP).ne_zero

theorem exists_fixed_probe_window : ∃ (w : ℝ→ℝ) (W : SchwartzMap ℝ ℂ),
    ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
    Function.support w⊆Set.Ioo 1 2 ∧ tsupport w⊆Set.Ioi 0 ∧
    (∀x,0≤w x ∧ w x≤1) ∧ w≠0 ∧ (∀x,W x=(w x:ℂ)) ∧ W≠0 ∧
    Function.support W⊆Set.Icc 1 2 ∧
    (∀x,(W x).im=0) ∧ (∀x,0≤(W x).re) := by
  obtain ⟨w,W,hw,hc,hs,hb,hv,hn,he,hWn,hWs,hr,hp⟩ := exists_probe_window
  refine ⟨w,W,hw,hc,hs,?_,hb,hn,he,hWn,hWs,hr,hp⟩
  have hcl : tsupport w⊆Set.Icc 1 2 :=
    closure_minimal (hs.trans Set.Ioo_subset_Icc_self) isClosed_Icc
  intro x hx
  exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (hcl hx).1
end SevenEighths.Parameters

end

end OAI

end Source1344

/- Original source: OAI/NumberTheory/DirichletL/Detector/RowInterchange.lean; sha256: a2cce044bfc064c73bcca39bc04ee79052b64909904c30773b36648c2eca7fff -/
section Source1345
namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem spectralSummand_norm_eq_of_re (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (s t : ℂ) (h : s.re = t.re) (I J : Ideal O) :
    ‖spectralSummand S D Ψ s I J‖ = ‖spectralSummand S D Ψ t I J‖ := by
  have h3 : (3 * s).re = (3 * t).re := by simp [Complex.mul_re, h]
  simp only [spectralSummand, norm_mul, fullIdealWeight_norm_eq_of_re _ _ h,
    fullIdealWeight_norm_eq_of_re _ _ h3]

def mellinSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (σ Z : ℝ) (p : Ideal O × Ideal O) (y : ℝ) : ℂ :=
  (Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) * Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2) *
    spectralSummand S D Ψ ((σ : ℂ) + y * Complex.I) p.1 p.2

theorem mellinSummand_norm (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (σ Z : ℝ) (hZ : 0 < Z) (p : Ideal O × Ideal O) (y : ℝ) :
    ‖mellinSummand S D Ψ σ Z p y‖ =
      (Z ^ σ * Real.exp (σ ^ 2) * ‖spectralSummand S D Ψ (σ : ℂ) p.1 p.2‖) *
        Real.exp (-1 * y ^ 2) := by
  unfold mellinSummand
  rw [norm_mul, verticalKernel_norm Z hZ σ y,
    spectralSummand_norm_eq_of_re S D Ψ _ (σ : ℂ) (by simp)]
  ring

theorem mellinSummand_integrable (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (σ Z : ℝ) (hZ : 0 < Z) (p : Ideal O × Ideal O) :
    Integrable (mellinSummand S D Ψ σ Z p) := by
  have hc : Continuous (fun y : ℝ => (σ : ℂ) + y * Complex.I) := by fun_prop
  have ht : Continuous (fun y : ℝ => spectralSummand S D Ψ
      ((σ : ℂ) + y * Complex.I) p.1 p.2) :=
    continuous_const.mul ((fullIdealWeight_continuous p.1).comp hc |>.mul
      ((fullIdealWeight_continuous p.2).comp (continuous_const.mul hc)))
  have hk := (hc.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))).mul ((hc.pow 2).cexp)
  apply ((integrable_exp_neg_mul_sq (b := 1) (by norm_num)).const_mul
    (Z ^ σ * Real.exp (σ ^ 2) * ‖spectralSummand S D Ψ (σ : ℂ) p.1 p.2‖)).mono'
    (hk.mul ht).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => (mellinSummand_norm S D Ψ σ Z hZ p y).le)

theorem mellinSummand_integral_norm (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (σ Z : ℝ) (hZ : 0 < Z) (p : Ideal O × Ideal O) :
    (∫ y : ℝ, ‖mellinSummand S D Ψ σ Z p y‖) =
      ‖spectralSummand S D Ψ (σ : ℂ) p.1 p.2‖ *
        (Z ^ σ * Real.exp (σ ^ 2) * ∫ y : ℝ, Real.exp (-1 * y ^ 2)) := by
  simp only [mellinSummand_norm S D Ψ σ Z hZ, integral_const_mul]
  ring

theorem spectralRow_integral_eq_tsum (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ)
    (Z : ℝ) (hZ : 0 < Z) :
    (∫ y : ℝ, (Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) *
      Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2) *
      spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)) =
      ∑' p, ∫ y : ℝ, mellinSummand S D Ψ σ Z p y := by
  let : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
  have hs : Summable (fun p => ∫ y : ℝ, ‖mellinSummand S D Ψ σ Z p y‖) := by
    simp only [mellinSummand_integral_norm S D Ψ σ Z hZ]
    exact (spectralRow_summable S D Ψ hΨ (σ : ℂ) hσ).norm.mul_right _
  rw [integral_tsum_of_summable_integral_norm
    (fun p => mellinSummand_integrable S D Ψ σ Z hZ p) hs]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [mellinSummand, tsum_mul_left, spectralRow]

end SevenEighths.ProbeRow
end

end OAI

end Source1345

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianMellin.lean; sha256: 0526d85d63bcee8a85cb945c231af1263839ca0808c6d714132d0781b2618a04 -/
section Source1346
namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical

def gaussianMellinProfile (y : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
    Complex.exp (-(Complex.log (y:ℂ))^2/4)

lemma gaussianMellin_integral (y : ℝ) (hy : 0<y) (σ : ℝ) :
    (∫v : ℝ,(y:ℂ)^(-((σ:ℂ)+v*Complex.I))*Complex.exp (((σ:ℂ)+v*Complex.I)^2))=
      (Real.pi:ℂ)^(1/2:ℂ)*Complex.exp (-(Complex.log (y:ℂ))^2/4) := by
  have hi (v : ℝ) :
      (y:ℂ)^(-((σ:ℂ)+v*Complex.I))*Complex.exp (((σ:ℂ)+v*Complex.I)^2)=
      Complex.exp ((-1:ℂ)*(v:ℂ)^2+
        (Complex.I*(2*(σ:ℂ)-Complex.log (y:ℂ)))*(v:ℂ)+
        ((σ:ℂ)^2-Complex.log (y:ℂ)*(σ:ℂ))) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),←Complex.exp_add]
    congr 1
    ring_nf
    simp only [Complex.I_sq]
    ring
  simp_rw [hi]
  rw [integral_cexp_quadratic (by norm_num : (-1:ℂ).re<0)]
  congr 1
  · norm_num
  · congr 1
    ring_nf
    simp only [Complex.I_sq]
    ring

lemma gaussianMellin_inversion (y : ℝ) (hy : 0<y) (σ : ℝ) :
    ((1/(2*Real.pi):ℝ):ℂ)*
      (∫v : ℝ,(y:ℂ)^(-((σ:ℂ)+v*Complex.I))*Complex.exp (((σ:ℂ)+v*Complex.I)^2))=
      gaussianMellinProfile y := by
  rw [gaussianMellin_integral y hy σ]
  exact mul_assoc _ _ _ |>.symm

lemma gaussian_completed_norm_power (a b Z : ℝ) (ha : 0<a) (hb : 0<b) (hZ : 0<Z) (t : ℂ) :
    (Z:ℂ)^t*((a:ℂ)^(-t)*(b:ℂ)^(-(3*t)))=((a*b^3/Z:ℝ):ℂ)^(-t) := by
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (mul_pos ha (pow_pos hb 3)).le hZ.le]
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg ha.le (pow_pos hb 3).le]
  have hp : ((b^3:ℝ):ℂ)^(-t)=(b:ℂ)^((3:ℂ)*(-t)) := by
    simpa only [Real.rpow_ofNat,Real.rpow_natCast,Complex.ofReal_pow,Complex.cpow_ofNat,Complex.ofReal_ofNat] using
      (Complex.cpow_mul_ofReal_nonneg hb.le (3:ℝ) (-t)).symm
  rw [hp,Complex.cpow_neg (Z:ℂ),div_inv_eq_mul]
  rw [show (3:ℂ)*(-t)= -(3*t) by ring]
  ring

lemma gaussianMellinProfile_norm (y : ℝ) (hy : 0<y) :
    ‖gaussianMellinProfile y‖=
      ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*
        Real.exp (-(Real.log y)^2/4) := by
  unfold gaussianMellinProfile
  rw [norm_mul,Complex.norm_exp,←Complex.ofReal_log hy.le]
  congr 2
  simp [←Complex.ofReal_pow]

lemma gaussianMellinProfile_power_bound (y : ℝ) (hy : 0<y) (a : ℝ) :
    ‖gaussianMellinProfile y‖≤
      ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*Real.exp (a^2)*y^(-a) := by
  rw [gaussianMellinProfile_norm y hy,Real.rpow_def_of_pos hy]
  rw [mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (Real.log y/2-a)]

end SevenEighths.ProbePhysical
end

end OAI

end Source1346

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianCompletion.lean; sha256: 5ee7ec8c1869fcce035ad7aa2b0dffefa706cc1d5d42e4385f3330d1149ceeb1 -/
section Source1347
namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CompletedGauss CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianCompletedProfile (y : ℝ) : ℂ := gaussianMellinProfile y/(Real.sqrt y:ℂ)

lemma gaussianCompleted_Vstar (y : ℝ) (hy : 0<y) :
    Vstar gaussianCompletedProfile y=gaussianMellinProfile y := by
  have h : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  simp only [Vstar,gaussianCompletedProfile]
  field_simp

lemma gaussian_mellinSummand (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (σ Z : ℝ) (hZ : 0<Z) (I J : Id) :
    ((1/(2*Real.pi):ℝ):ℂ)*(∫v : ℝ,mellinSummand S D Ψ σ Z (I,J) v)=
      correctedSummand S D Ψ gaussianCompletedProfile Z I J := by
  by_cases hI : I=0
  · subst I
    simp [mellinSummand,spectralSummand,fullIdealWeight,correctedSummand,markedSummand,CompletedGauss.summand]
  by_cases hJ : J=0
  · subst J
    simp [mellinSummand,spectralSummand,fullIdealWeight,correctedSummand,markedSummand,CompletedGauss.summand]
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hq : 0<(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/Z :=
    div_pos (mul_pos hi (pow_pos hj 3)) hZ
  have hp (v : ℝ) : mellinSummand S D Ψ σ Z (I,J) v=
      (((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/Z:ℝ):ℂ)^(-((σ:ℂ)+v*Complex.I))*
      Complex.exp (((σ:ℂ)+v*Complex.I)^2)*
      (completedMask S D I J*completedCorrection I J*
        (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I):ℂ))*cubeWeight Ψ J) := by
    unfold mellinSummand spectralSummand fullIdealWeight
    simp only [ite_eq_right hI,ite_eq_right hJ]
    rw [←gaussian_completed_norm_power _ _ Z hi hj hZ]
    push_cast
    ring
  simp_rw [hp]
  rw [integral_mul_const,←mul_assoc,gaussianMellin_inversion _ hq σ]
  unfold correctedSummand markedSummand CompletedGauss.summand
  rw [gaussianCompleted_Vstar _ hq]
  ring

lemma gaussian_correctedSummand_summable (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (Z : ℝ) (hZ : 0<Z) :
    Summable (fun p : Id×Id=>correctedSummand S D Ψ gaussianCompletedProfile Z p.1 p.2) := by
  have hs : Summable (fun p : Id×Id=>∫v : ℝ,‖mellinSummand S D Ψ 2 Z p v‖) := by
    simp only [mellinSummand_integral_norm S D Ψ 2 Z hZ]
    exact (spectralRow_summable S D Ψ hΨ (2:ℂ) (by norm_num)).norm.mul_right _
  have hi : Summable (fun p : Id×Id=>∫v : ℝ,mellinSummand S D Ψ 2 Z p v) := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun p=>norm_integral_le_integral_norm _) hs
  have hh := hi.mul_left (((1/(2*Real.pi):ℝ):ℂ))
  simpa only [gaussian_mellinSummand S D Ψ 2 Z hZ] using hh

theorem spectralRow_eq_gaussianCompleted (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (σ : ℝ) (hσ : 1<σ) (Z : ℝ) (hZ : 0<Z) :
    verticalIntegral σ (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow S D Ψ t)=
      correctedCompletedT S D Ψ gaussianCompletedProfile Z := by
  rw [verticalIntegral,spectralRow_integral_eq_tsum S D Ψ hΨ σ hσ Z hZ,←tsum_mul_left]
  unfold correctedCompletedT
  apply tsum_congr
  intro p
  exact gaussian_mellinSummand S D Ψ σ Z hZ p.1 p.2

theorem markedPhysicalProbe_eq_gaussian (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (X Y Z : ℝ) (hZ : 0<Z) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      (Y:ℂ)⁻¹*∑'s : {I : Id // CanonicalQuadraticSieve.Supported I},
        if ∀P∈C.excluded,¬P∣s.val then
          let a := primaryGenerator s.val
          let ha := CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero s.val s.property
          let has := (CanonicalQuadraticSieve.supported_span_primaryGenerator_iff s.val).mpr s.property
          let q : ℝ := Ideal.absNorm s.val
          W1 (q/Y)*CanonicalRowCompletion.idealRowHom C.generator s.val/
            (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*q*X):ℂ))*
          ∑'m : O,C.residueMonoid m*(Real.sqrt q:ℂ)⁻¹*sexticGauss a ha (-m)*
            W0 (elementNorm m/(elementNorm C.generator*q*X))*
            correctedCompletedT C.excluded D (rowCoefficient η C.Xi a has m)
              gaussianCompletedProfile Z
        else 0 := by
  unfold markedPhysicalProbe
  congr 1
  apply tsum_congr
  intro s
  split_ifs with h
  · dsimp only
    congr 1
    apply tsum_congr
    intro m
    rw [spectralRow_eq_gaussianCompleted _ _ _
      (rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ m) 4 (by norm_num) Z hZ]
  · rfl

end SevenEighths.ProbePhysical
end

end OAI

end Source1347

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianPartition.lean; sha256: e8c07b6a103deb0f0e65277c1a06b5035a36482560d9ac5c6389eaf4c783277b -/
section Source1348
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
namespace SevenEighths.ProbePhysical
open DyadicTransfer

def gaussianCutoff (y : ℝ) : ℂ := (Real.smoothTransition (2-y):ℂ)
def gaussianAnnulus (y : ℝ) : ℂ := annularCutoff gaussianCutoff y

lemma gaussianCutoff_small (y : ℝ) (hy : y≤1) : gaussianCutoff y=1 := by
  simp only [gaussianCutoff,Real.smoothTransition.one_of_one_le (by linarith : 1≤2-y),Complex.ofReal_one]
lemma gaussianCutoff_large (y : ℝ) (hy : 2≤y) : gaussianCutoff y=0 := by
  simp only [gaussianCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : 2-y≤0),Complex.ofReal_zero]
lemma gaussianAnnulus_small (y : ℝ) (hy : y≤1/2) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_le_half gaussianCutoff gaussianCutoff_small hy
lemma gaussianAnnulus_large (y : ℝ) (hy : 2≤y) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_two_le gaussianCutoff gaussianCutoff_large hy
lemma gaussianAnnulus_contDiff : ContDiff ℝ ∞ gaussianAnnulus := by
  unfold gaussianAnnulus annularCutoff gaussianCutoff
  exact (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop))).sub
    (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop)))
lemma gaussianAnnulus_compact : HasCompactSupport gaussianAnnulus := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(1/2:ℝ)) (b:=2))
  intro y hy
  change gaussianAnnulus y≠0 at hy
  constructor
  · by_contra h
    exact hy (gaussianAnnulus_small y (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact hy (gaussianAnnulus_large y (le_of_lt (lt_of_not_ge h)))

lemma gaussianAnnulus_nonneg (y : ℝ) : 0≤(gaussianAnnulus y).re := by
  by_cases hy : y≤1/2
  · rw [gaussianAnnulus_small y hy]; simp
  · change 0≤Real.smoothTransition (2-y)-Real.smoothTransition (2-2*y)
    exact sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))
lemma gaussianAnnulus_norm (y : ℝ) : ‖gaussianAnnulus y‖=(gaussianAnnulus y).re := by
  have h : gaussianAnnulus y=((gaussianAnnulus y).re:ℂ) := by
    simp [gaussianAnnulus,annularCutoff,gaussianCutoff]
  rw [h,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (gaussianAnnulus_nonneg y)]
  rfl

lemma gaussianAnnulus_support_scales (x : ℝ) (K : ℕ)
    (hlo : (2:ℝ)^K≤x) (hhi : x<(2:ℝ)^(K+1)) (j : ℕ) (hj : j∉({K,K+1}:Finset ℕ)) :
    gaussianAnnulus (x/(2:ℝ)^j)=0 := by
  have hp : (0:ℝ)<2^j := by positivity
  have hj' : j≠K ∧ j≠K+1 := by simpa using hj
  by_cases hlt : j<K
  · apply gaussianAnnulus_large
    apply (le_div_iff₀ hp).mpr
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show j+1≤K by omega)
    rw [pow_succ] at h
    linarith
  · apply gaussianAnnulus_small
    apply (div_le_iff₀ hp).mpr
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show K+2≤j by omega)
    have he : (2:ℝ)^(K+2)=2*((2:ℝ)^(K+1)) := by rw [pow_succ]; ring
    rw [he] at h
    linarith

lemma gaussianAnnulus_partition (x : ℝ) (hx : 1≤x) :
    HasSum (fun j : ℕ=>gaussianAnnulus (x/(2:ℝ)^j)) 1 := by
  obtain ⟨K,hlo,hhi⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ)<2)
  have h : HasSum (fun j : ℕ=>gaussianAnnulus (x/(2:ℝ)^j))
      (∑j∈({K,K+1}:Finset ℕ),gaussianAnnulus (x/(2:ℝ)^j)) :=
    hasSum_sum_of_ne_finset_zero (gaussianAnnulus_support_scales x K hlo hhi)
  convert h using 1
  rw [Finset.sum_pair (by omega : K≠K+1)]
  unfold gaussianAnnulus annularCutoff
  have he : 2*(x/(2:ℝ)^(K+1))=x/(2:ℝ)^K := by rw [pow_succ]; field_simp
  have hh : 2≤2*(x/(2:ℝ)^K) := by
    have hq : 1≤x/(2:ℝ)^K := (one_le_div (by positivity)).mpr hlo
    linarith
  rw [he,gaussianCutoff_small _ ((div_le_one (by positivity)).mpr hhi.le),
    gaussianCutoff_large _ hh]
  ring

lemma gaussianAnnulus_partition_norm (x : ℝ) (hx : 1≤x) :
    HasSum (fun j : ℕ=>‖gaussianAnnulus (x/(2:ℝ)^j)‖) 1 := by
  simpa only [gaussianAnnulus_norm,Complex.one_re] using
    Complex.hasSum_re (gaussianAnnulus_partition x hx)

end SevenEighths.ProbePhysical
end

end OAI

end Source1348

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianWindows.lean; sha256: 045f00d06e64c005c0d37031c3842152d959fea2609ce4cb2f4916f7485f8f50 -/
section Source1349
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Filter
namespace SevenEighths.ProbePhysical
open CompletedGauss

lemma gaussianMellinProfile_real (y : ℝ) (hy : 0<y) :
    gaussianMellinProfile y=
      ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
        (Real.exp (-(Real.log y)^2/4):ℂ) := by
  unfold gaussianMellinProfile
  rw [←Complex.ofReal_log hy.le]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

def gaussianDyadicProfile (Z : ℝ) (j : ℕ) (y : ℝ) : ℂ :=
  gaussianAnnulus y*gaussianMellinProfile ((2:ℝ)^j*y/Z)/(Real.sqrt y:ℂ)

lemma gaussianDyadicProfile_small (Z : ℝ) (j : ℕ) (y : ℝ) (hy : y≤1/2) :
    gaussianDyadicProfile Z j y=0 := by
  simp only [gaussianDyadicProfile,gaussianAnnulus_small y hy,zero_mul,zero_div]
lemma gaussianDyadicProfile_large (Z : ℝ) (j : ℕ) (y : ℝ) (hy : 2≤y) :
    gaussianDyadicProfile Z j y=0 := by
  simp only [gaussianDyadicProfile,gaussianAnnulus_large y hy,zero_mul,zero_div]

lemma gaussianDyadicProfile_compact (Z : ℝ) (j : ℕ) : HasCompactSupport (gaussianDyadicProfile Z j) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(1/2:ℝ)) (b:=2))
  intro y hy
  change gaussianDyadicProfile Z j y≠0 at hy
  constructor
  · by_contra h
    exact hy (gaussianDyadicProfile_small Z j y (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact hy (gaussianDyadicProfile_large Z j y (le_of_lt (lt_of_not_ge h)))

lemma gaussianDyadicProfile_contDiff (Z : ℝ) (hZ : 0<Z) (j : ℕ) :
    ContDiff ℝ ∞ (gaussianDyadicProfile Z j) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0<y
  · have he : gaussianDyadicProfile Z j =ᶠ[𝓝 y]
        (fun x : ℝ=>gaussianAnnulus x*
          (((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
            (Real.exp (-(Real.log ((2:ℝ)^j*x/Z))^2/4):ℂ))/(Real.sqrt x:ℂ)) := by
      filter_upwards [eventually_gt_nhds hy] with x hx
      rw [gaussianDyadicProfile,gaussianMellinProfile_real _ (div_pos (mul_pos (by positivity) hx) hZ)]
    apply ContDiffAt.congr_of_eventuallyEq _ he
    have hq : (2:ℝ)^j*y/Z≠0 := ne_of_gt (div_pos (mul_pos (by positivity) hy) hZ)
    have hs : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
    have ha := gaussianAnnulus_contDiff.contDiffAt (x:=y)
    have hl : ContDiffAt ℝ ∞ (fun x : ℝ=>Real.log ((2:ℝ)^j*x/Z)) y :=
      (show ContDiffAt ℝ ∞ (fun x : ℝ=>(2:ℝ)^j*x/Z) y by fun_prop).log hq
    have hg : ContDiffAt ℝ ∞ (fun x : ℝ=>Real.exp (-(Real.log ((2:ℝ)^j*x/Z))^2/4)) y :=
      ((hl.pow 2).neg.div_const 4).exp
    have hgC := Complex.ofRealCLM.contDiff.contDiffAt.comp y hg
    have hsR : ContDiffAt ℝ ∞ Real.sqrt y := Real.contDiffAt_sqrt hy.ne'
    have ht : ContDiffAt ℝ ∞ (fun x : ℝ=>gaussianAnnulus x*
        (((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
          (Real.exp (-(Real.log ((2:ℝ)^j*x/Z))^2/4):ℂ))) y :=
      ha.mul (contDiffAt_const.mul hgC)
    have hsc : ContDiffAt ℝ ∞ (fun x : ℝ=>(Real.sqrt x:ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y hsR
    simpa only [div_eq_mul_inv] using ht.mul (hsc.fun_inv hs)
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (show y<(1/2:ℝ) by linarith)] with x hx
    exact gaussianDyadicProfile_small Z j x hx.le

lemma gaussianDyadicProfile_Vstar (Z : ℝ) (j : ℕ) (y : ℝ) (hy : 0<y) :
    Vstar (gaussianDyadicProfile Z j) y=
      gaussianAnnulus y*gaussianMellinProfile ((2:ℝ)^j*y/Z) := by
  have h : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  simp only [Vstar,gaussianDyadicProfile]
  field_simp

end SevenEighths.ProbePhysical
end

end OAI

end Source1349

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianDecomposition.lean; sha256: 494752f7dcd2e0916be5e4d3c7a64c24e5551a9bc5a5f278200e46f068ebf389 -/
section Source1350
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma annular_reassembly_summable {α : Type*} (a : α→ℂ) (N : α→ℝ)
    (ha : Summable a) (hN : ∀p,a p≠0→1≤N p) :
    Summable (fun q : α×ℕ=>gaussianAnnulus (N q.1/(2:ℝ)^q.2)*a q.1) := by
  have hs (p : α) : HasSum (fun j : ℕ=>‖gaussianAnnulus (N p/(2:ℝ)^j)*a p‖) ‖a p‖ := by
    by_cases hp : a p=0
    · simp only [hp,mul_zero,norm_zero]
      exact hasSum_zero
    · simpa only [norm_mul,one_mul] using (gaussianAnnulus_partition_norm (N p) (hN p hp)).mul_right ‖a p‖
  apply Summable.of_norm
  apply (summable_prod_of_nonneg (fun _=>norm_nonneg _)).mpr
  exact ⟨fun p=>(hs p).summable,by simpa only [fun p=>(hs p).tsum_eq] using ha.norm⟩

lemma annular_reassembly {α : Type*} (a : α→ℂ) (N : α→ℝ)
    (ha : Summable a) (hN : ∀p,a p≠0→1≤N p) :
    (∑'j : ℕ,∑'p : α,gaussianAnnulus (N p/(2:ℝ)^j)*a p)=∑'p,a p := by
  rw [Summable.tsum_comm (f:=fun p : α=>fun j : ℕ=>gaussianAnnulus (N p/(2:ℝ)^j)*a p)
    (annular_reassembly_summable a N ha hN)]
  apply tsum_congr
  intro p
  by_cases hp : a p=0
  · simp [hp]
  · simpa only [one_mul] using ((gaussianAnnulus_partition (N p) (hN p hp)).mul_right (a p)).tsum_eq

lemma gaussian_dyadic_correctedSummand (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (Z : ℝ) (hZ : 0<Z) (j : ℕ) (I J : Id) :
    correctedSummand S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j) I J=
      gaussianAnnulus ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)*
        correctedSummand S D Ψ gaussianCompletedProfile Z I J := by
  by_cases hI : I=0
  · subst I
    simp [correctedSummand,markedSummand,summand]
  by_cases hJ : J=0
  · subst J
    simp [correctedSummand,markedSummand,summand]
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hN := mul_pos hi (pow_pos hj 3)
  unfold correctedSummand markedSummand summand
  rw [gaussianDyadicProfile_Vstar _ _ _ (div_pos hN (by positivity)),
    gaussianCompleted_Vstar _ (div_pos hN hZ)]
  have he : (2:ℝ)^j*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/Z=
      (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/Z := by
    field_simp
  rw [he]
  ring

lemma gaussian_correctedSummand_norm_ge_one (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (Z : ℝ) (I J : Id)
    (h : correctedSummand S D Ψ gaussianCompletedProfile Z I J≠0) :
    1≤(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := by
  have hI : I≠0 := by intro he; subst I; simp [correctedSummand,markedSummand,summand] at h
  have hJ : J≠0 := by intro he; subst J; simp [correctedSummand,markedSummand,summand] at h
  have hi : 1≤Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : 1≤Ideal.absNorm J := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  exact_mod_cast one_le_mul_of_one_le_of_one_le hi (one_le_pow₀ hj)

theorem correctedGaussian_eq_tsum_dyadic (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (Z : ℝ) (hZ : 0<Z) :
    correctedCompletedT S D Ψ gaussianCompletedProfile Z=
      ∑'j : ℕ,correctedCompletedT S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j) := by
  unfold correctedCompletedT
  simp_rw [gaussian_dyadic_correctedSummand S D Ψ Z hZ]
  exact (annular_reassembly _ _ (gaussian_correctedSummand_summable S D Ψ hΨ Z hZ)
    (fun p=>gaussian_correctedSummand_norm_ge_one S D Ψ Z p.1 p.2)).symm

end SevenEighths.ProbePhysical
end

end OAI

end Source1350

/- Original source: OAI/NumberTheory/DirichletL/Descent/Completion.lean; sha256: eb4b9a3c72fcc4ff54e0097db06bc0a8cecb0ef63cd8cf5115689bcf2acf1048 -/
section Source1351
namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss

local notation "Eis" => ActualEisensteinCubic.O

def markedCompletedT (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) : ℂ :=
  ∑' I : Ideal Eis, ∑' J : Ideal Eis, summand Ψ W X I J * d (I * J ^ 3)

theorem markedCompletedT_one (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ) :
    markedCompletedT Ψ W X (fun _ => 1) = completedT Ψ W X := by
  simp only [markedCompletedT, mul_one, completedT]

theorem markedCompletedT_congr_nonzero (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d e : Ideal Eis → ℂ) (h : ∀ A ≠ 0, d A = e A) :
    markedCompletedT Ψ W X d = markedCompletedT Ψ W X e := by
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  by_cases hI : I = 0
  · simp only [hI, summand_zero_left, zero_mul]
  by_cases hJ : J = 0
  · simp only [hJ, summand_zero_right, zero_mul]
  rw [h (I * J ^ 3) (mul_ne_zero hI (pow_ne_zero 3 hJ))]

theorem markedCompletedT_summable (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    Summable (fun p : Ideal Eis × Ideal Eis =>
      summand Ψ W X p.1 p.2 * d (p.1 * p.2 ^ 3)) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support Ψ W hW X hX).subset
  intro p hp hz
  exact hp (by simp only [hz, zero_mul])

theorem markedCompletedT_eq_tsum (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    markedCompletedT Ψ W X d = ∑' p : Ideal Eis × Ideal Eis,
      summand Ψ W X p.1 p.2 * d (p.1 * p.2 ^ 3) :=
  (markedCompletedT_summable Ψ W hW X hX d).tsum_prod.symm

theorem markedCompletedT_const_mul (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (c : ℂ) (d : Ideal Eis → ℂ) :
    markedCompletedT Ψ W X (fun A => c * d A) = c * markedCompletedT Ψ W X d := by
  simp only [markedCompletedT, mul_left_comm _ c, tsum_mul_left]

theorem markedCompletedT_finset_sum {ι : Type*} (s : Finset ι)
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (X : ℝ) (hX : 0 < X) (d : ι → Ideal Eis → ℂ) :
    markedCompletedT Ψ W X (fun A => ∑ i ∈ s, d i A) =
      ∑ i ∈ s, markedCompletedT Ψ W X (d i) := by
  simp only [markedCompletedT_eq_tsum Ψ W hW X hX, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun i _ => markedCompletedT_summable Ψ W hW X hX (d i))

theorem markedCompletedT_prime_priority {σ : Type*} [DecidableEq σ]
    (slots : Finset σ) (L : σ → Finset (Ideal Eis))
    (a : σ → Ideal Eis → ℂ) (H : Ideal Eis) (hH : H ≠ 0)
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X
      (fun A => primeMark slots L a (IdealMobiusDivisorSum.primeSupport (H ^ 3 * A))) =
    ∑ J ∈ slots.powerset,
      primeMark J L a (IdealMobiusDivisorSum.primeSupport H) *
        markedCompletedT Ψ W X (fun A =>
          primeMark (slots \ J)
            (fun i => L i \ IdealMobiusDivisorSum.primeSupport H) a
            (IdealMobiusDivisorSum.primeSupport A)) := by
  have hmark (A : Ideal Eis) (hA : A ≠ 0) :
      primeMark slots L a (IdealMobiusDivisorSum.primeSupport (H ^ 3 * A)) =
      ∑ J ∈ slots.powerset,
        primeMark J L a (IdealMobiusDivisorSum.primeSupport H) *
          primeMark (slots \ J)
            (fun i => L i \ IdealMobiusDivisorSum.primeSupport H) a
            (IdealMobiusDivisorSum.primeSupport A) := by
    rw [mul_comm (H ^ 3) A, ideal_primeSupport_mul_cube A H hA hH,
      Finset.union_comm, primeMark_priority]
    simp only [primeMark_residual_lists]
  rw [markedCompletedT_congr_nonzero Ψ W X _ _ hmark,
    markedCompletedT_finset_sum slots.powerset Ψ W hW X hX]
  simp only [markedCompletedT_const_mul]

def markedExpandedTerm (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) (I H J : Ideal Eis) : ℂ :=
  expandedTerm Ψ W X I H J * d (I * (H * J) ^ 3)

theorem markedExpandedTerm_finite_support (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (Function.support (fun p : Ideal Eis × Ideal Eis × Ideal Eis =>
      markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite := by
  apply (finite_support_expandedTerm Ψ W hW X hX).subset
  intro p hp hz
  apply hp
  simp only [markedExpandedTerm, hz, zero_mul]

theorem markedExpandedTerm_scale (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) (I H J : Ideal Eis) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      (summand Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) I J * d (H ^ 3 * (I * J ^ 3))) =
      markedExpandedTerm Ψ W X d I H J := by
  rw [← mul_assoc, expandedTerm_scale]
  unfold markedExpandedTerm
  congr 2
  ring

theorem weighted_markedCompletedT_reopen (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) (H : Ideal Eis) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A)) =
      ∑' I : Ideal Eis, ∑' J : Ideal Eis, markedExpandedTerm Ψ W X d I H J := by
  simp only [markedCompletedT, ← tsum_mul_left, markedExpandedTerm_scale]

theorem marked_cube_inner_inverse (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X)
    (d : Ideal Eis → ℂ) (I : Ideal Eis) :
    (∑' H : Ideal Eis, ∑' J : Ideal Eis, markedExpandedTerm Ψ W X d I H J) =
      (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
        Vstar W ((Ideal.absNorm I : ℝ) / X)) * d I := by
  let f : Ideal Eis → ℂ := fun B =>
    columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm B : ℝ) ^ 3 / X) * d (I * B ^ 3)
  have heq (H J : Ideal Eis) :
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ (H * J) * f (H * J) =
        markedExpandedTerm Ψ W X d I H J := by
    simp only [f, markedExpandedTerm, expandedTerm, map_mul, Nat.cast_mul, mul_pow,
      mul_assoc]
  have hf := markedExpandedTerm_finite_support Ψ W hW X hX d
  have hp : (Function.support (fun p : Ideal Eis × Ideal Eis =>
      markedExpandedTerm Ψ W X d I p.1 p.2)).Finite := by
    change ((fun p : Ideal Eis × Ideal Eis => (I, p)) ⁻¹'
      Function.support (fun p : Ideal Eis × Ideal Eis × Ideal Eis =>
        markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => (Prod.mk.inj hab).2) hf
  have hgeneric := ideal_cube_convolution (cubeWeight Ψ) (cubeWeight_zero Ψ) f
    (by simpa only [heq] using hp)
  simpa only [heq, f, map_one, Nat.cast_one, one_pow, mul_one] using hgeneric

theorem marked_cube_inverse_vstar (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (∑' H : Ideal Eis, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A))) =
    ∑' I : Ideal Eis, (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) / X)) * d I := by
  let F : Ideal Eis × Ideal Eis × Ideal Eis → ℂ :=
    fun p => markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2
  have hF : Summable F :=
    summable_of_hasFiniteSupport (markedExpandedTerm_finite_support Ψ W hW X hX d)
  let e : (Ideal Eis × Ideal Eis × Ideal Eis) ≃ (Ideal Eis × Ideal Eis × Ideal Eis) := {
    toFun := fun p => (p.2.1, p.1, p.2.2)
    invFun := fun p => (p.2.1, p.1, p.2.2)
    left_inv := by rintro ⟨I, H, J⟩; rfl
    right_inv := by rintro ⟨I, H, J⟩; rfl }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal Eis, ∑' I : Ideal Eis, ∑' J : Ideal Eis,
        markedExpandedTerm Ψ W X d I H J := by
      simp only [weighted_markedCompletedT_reopen]
    _ = ∑' p : Ideal Eis × Ideal Eis × Ideal Eis, F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal Eis × Ideal Eis × Ideal Eis, F p := e.tsum_eq F
    _ = ∑' I : Ideal Eis, ∑' H : Ideal Eis, ∑' J : Ideal Eis,
        markedExpandedTerm Ψ W X d I H J := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (marked_cube_inner_inverse Ψ W hW X hX d)

theorem marked_cube_inverse (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (Real.sqrt X : ℂ)⁻¹ *
      (∑' I : Ideal Eis, columnWeight Ψ I * d I * W ((Ideal.absNorm I : ℝ) / X)) =
    ∑' H : Ideal Eis, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A)) := by
  rw [marked_cube_inverse_vstar Ψ W hW X hX d, ← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [vstar_source_normalization Ψ W X hX I]
  ring

end

end SevenEighths.InverseMoment

end OAI

end Source1351

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowRow.lean; sha256: 1fb24adb6a1570727206a17be60f3f0390006e4b386e07ac8c4e8e116fee63e8 -/
section Source1352
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def physicalRowBase (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) : O→*ℂ :=
  targetMonoid η*conjugateMonoid Xi*reciprocityPhaseMonoid s hs

lemma physicalRowBase_norm (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (hXi : ∀a,‖Xi a‖≤1) (s : O) (hs : Supported (Ideal.span {s})) (a : O) :
    ‖physicalRowBase η Xi s hs a‖≤1 := by
  change ‖(targetMonoid η a*star (Xi a))*sexticReciprocityPhase s a‖≤1
  rw [norm_mul,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) (targetMonoid_norm_le_one η a)).trans (hXi a))).trans (sexticReciprocityPhase_norm s a)

lemma ray_rowCoefficient_eq_rowTwist (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m f z n : O) (hn : n=m^6*f^4*z)
    (χ : RayCharacter) :
    rayMonoid χ*rowCoefficient η Xi s hs n=
      rowTwist (rayMonoid χ*physicalRowBase η Xi s hs) m f z := by
  subst n
  ext a
  change rayMonoid χ a*((targetMonoid η a*star (Xi a))*sexticReciprocityPhase s a*
      idealRowHom (m^6*f^4*z) (Ideal.span {a}))=
    (rayMonoid χ a*((targetMonoid η a*star (Xi a))*sexticReciprocityPhase s a))*
      idealRowHom (m^6*f^4*z) (Ideal.span {a})
  ring

def wholeIdealMask (S : Finset Id) (D A : Id) : ℂ :=
  if D∣A ∧ ∀P∈S,¬P∣A then 1 else 0

lemma markedCompletedT_eq_inverse (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X) :
    ProbeCompleted.markedCompletedT S D Ψ W X=
      InverseMoment.markedCompletedT Ψ W X (wholeIdealMask S D) := by
  rw [InverseMoment.markedCompletedT_eq_tsum Ψ W hW X hX]
  unfold ProbeCompleted.markedCompletedT
  apply tsum_congr
  intro p
  change completedMask S D p.1 p.2*summand Ψ W X p.1 p.2=
    summand Ψ W X p.1 p.2*wholeIdealMask S D (p.1*p.2^3)
  exact mul_comm _ _

theorem correctedPhysicalRow_eq_inverse_rows (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m f z n : O) (hn : n=m^6*f^4*z)
    (S : Finset Id) (D : Id) (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X) :
    correctedCompletedT S D (rowCoefficient η Xi s hs n) W X=
      ∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT (rowTwist (rayMonoid χ*physicalRowBase η Xi s hs) m f z)
          W X (wholeIdealMask S D) := by
  rw [correctedCompletedT_ray_expansion S D _ W hW X hX]
  apply Finset.sum_congr rfl
  intro χ _
  rw [markedCompletedT_eq_inverse S D _ W hW X hX,ray_rowCoefficient_eq_rowTwist η Xi s hs m f z n hn χ]

end SevenEighths.ProbePhysical
end

end OAI

end Source1352

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowPeriod.lean; sha256: 9e62cdb96eff842e0f59876b6f968677ff352ac07c27d875fcb0cc9f069c9ace -/
section Source1353
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def calibrationRowModulus (C : CalibrationData) (B : O) (D : GoodMaskRowData B 1 C.generator) : Id :=
  1*Ideal.span {B}*Ideal.span {(72:O)}*Ideal.span {D.numeratorGood}

def periodicCalibrationXi (C : CalibrationData) (B : O) (D : GoodMaskRowData B 1 C.generator) : O→*ℂ :=
  C.residueMonoid*actualPeriodicRow 1 B D.numeratorUnit D.numeratorLambda D.numeratorTwo
    D.numeratorGood D.numeratorSupported

lemma calibrationRowModulus_ne_zero (C : CalibrationData) (B : O) (hB : B≠0)
    (D : GoodMaskRowData B 1 C.generator) : calibrationRowModulus C B D≠0 := by
  unfold calibrationRowModulus
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero one_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hB)
    · apply Ideal.span_singleton_eq_bot.not.mpr
      norm_num
  · exact D.numeratorSupported.1

lemma periodicCalibrationXi_norm (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (a : O) : ‖periodicCalibrationXi C B D a‖≤1 := by
  rw [periodicCalibrationXi,MonoidHom.mul_apply,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (C.residueMonoid_norm_le_one a)).trans (actualPeriodicRow_norm 1 (fun _=>by simp) B D.numeratorUnit D.numeratorLambda D.numeratorTwo
      D.numeratorGood D.numeratorSupported a)

lemma periodicCalibrationXi_periodic (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) :
    FactorsModulo (Ideal.span {C.generator}*calibrationRowModulus C B D) (periodicCalibrationXi C B D) := by
  have hp := actualPeriodicRow_periodic (1:O→*ℂ) 1 (fun _ _ _=>rfl)
    B D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
  intro x y hxy
  change C.residueMonoid x*_ = C.residueMonoid y*_
  congr 1
  · apply congrArg C.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_left hxy)
  · exact hp x y (Ideal.mul_le_right hxy)

lemma periodicCalibrationXi_eq_primary (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) (hc : IsCoprime B n) :
    periodicCalibrationXi C B D n=C.Xi n := by
  have he := rowTwist_eq_actualPeriodicRow_primary (1:O→*ℂ) B 1 C.generator hBL hB2
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorPrimary D.numeratorFactor n hpn
  rw [rowTwist_extract_sixth_mask _ _ _ _ _ hn] at he
  have hmask : coprimalityMask B n=(1:ℂ) := by
    change (if IsCoprime B n then (1:ℂ) else 0)=1
    rw [ite_eq_left hc]
  simp only [MonoidHom.one_apply,hmask,one_mul,one_pow] at he
  change C.residueMonoid n*_ = C.residueMonoid n*idealRowHom C.generator (Ideal.span {n})
  rw [←he]

def lowPeriodicBase (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) : O→*ℂ :=
  rayMonoid χ*targetMonoid η*conjugateMonoid (periodicCalibrationXi C B D)*reciprocityPhaseMonoid s hs

def lowBaseModulus (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) : Id :=
  η.modulus*(Ideal.span {C.generator}*calibrationRowModulus C B D)*Ideal.span {(4:O)}

lemma lowBaseModulus_ne_zero (η : HeckeFamily.Character) (C : CalibrationData) (B : O) (hB : B≠0)
    (D : GoodMaskRowData B 1 C.generator) : lowBaseModulus η C B D≠0 := by
  unfold lowBaseModulus
  apply mul_ne_zero
  · exact mul_ne_zero η.modulus_ne_bot (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero)
      (calibrationRowModulus_ne_zero C B hB D))
  · apply Ideal.span_singleton_eq_bot.not.mpr
    norm_num

lemma lowPeriodicBase_periodic (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter) :
    FactorsModulo (lowBaseModulus η C B D) (lowPeriodicBase η C B D s hs χ) := by
  intro x y hxy
  have h4 : (4:O)∣x-y := Ideal.mem_span_singleton.mp (Ideal.mul_le_right hxy)
  have hη : targetMonoid η x=targetMonoid η y := by
    apply congrArg η.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hc := periodicCalibrationXi_periodic C B D x y (Ideal.mul_le_right (Ideal.mul_le_left hxy))
  change ((rayMonoid χ x*targetMonoid η x)*star (periodicCalibrationXi C B D x))*
      sexticReciprocityPhase s x=
    ((rayMonoid χ y*targetMonoid η y)*star (periodicCalibrationXi C B D y))*sexticReciprocityPhase s y
  rw [hη,hc,sexticReciprocityPhase_congr_right s x y h4]
  have hr : rayMonoid χ x=rayMonoid χ y := rayCharacter_eq_of_mod_four χ x y h4
  rw [hr]

lemma lowPeriodicBase_norm (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) (a : O) : ‖lowPeriodicBase η C B D s hs χ a‖≤1 := by
  have hr : ‖rayMonoid χ a‖≤1 := FiniteRayExpansion.norm_char_le_one χ _
  change ‖((rayMonoid χ a*targetMonoid η a)*star (periodicCalibrationXi C B D a))*sexticReciprocityPhase s a‖≤1
  simp only [norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) hr).trans (targetMonoid_norm_le_one η a))).trans (periodicCalibrationXi_norm C B D a))).trans (sexticReciprocityPhase_norm s a)

lemma lowPeriodicBase_eq_primary (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) (hc : IsCoprime B n) :
    lowPeriodicBase η C B D s hs χ n=(rayMonoid χ*physicalRowBase η C.Xi s hs) n := by
  change ((rayMonoid χ n*targetMonoid η n)*star (periodicCalibrationXi C B D n))*sexticReciprocityPhase s n=
    rayMonoid χ n*((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n)
  rw [periodicCalibrationXi_eq_primary C B D hBL hB2 n hn hpn hc]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1353

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowPuncture.lean; sha256: de069c3f87d4ae0f8d6813ea1d47707b9ab9d0b8380ea8625a3cc0caa04b294d -/
section Source1354
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma calibration_generator_dvd (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (a : O) (ha : Ideal.span {a}∈S) : a∣(calibrationForSet S hS).generator := by
  apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mp
  rw [calibrationForSet_span]
  exact Finset.dvd_prod_of_mem (fun P : Id=>P) ha

lemma calibration_generator_bad (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) :
    λ₀∣(calibrationForSet S hS).generator ∧ (2:O)∣(calibrationForSet S hS).generator := by
  constructor
  · apply calibration_generator_dvd S hS
    apply hbad
    simp only [fixedBadPrimes,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inl rfl
  · apply calibration_generator_dvd S hS
    apply hbad
    simp only [fixedBadPrimes,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inr trivial

lemma supported_of_coprime_bad (B n : O) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (hc : IsCoprime B n) : Supported (Ideal.span {n}) := by
  apply supported_span_iff n |>.mpr
  constructor
  · exact PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mp
      (hc.of_isCoprime_of_dvd_left hBL)
  · have h2 : IsCoprime (-2:O) n := (hc.of_isCoprime_of_dvd_left hB2).neg_left
    have hn := negative_two_prime.irreducible.coprime_iff_not_dvd.mp h2
    simpa only [neg_dvd] using hn

lemma lowPeriodicBase_zero_of_not_coprime (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) (n : O) (hc : ¬IsCoprime B n) : lowPeriodicBase η C B D s hs χ n=0 := by
  have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [ite_eq_right hc]
  change ((rayMonoid χ n*targetMonoid η n)*star (C.residueMonoid n*
      ((((1:O→*ℂ) n*coprimalityMask B n)*
        numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported n)*
        movingNumeratorRow D.numeratorGood D.numeratorSupported n)))*sexticReciprocityPhase s n=0
  rw [hm]
  simp only [mul_zero,zero_mul,star_zero]

lemma lowPeriodicRow_eq_primary (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter) (z n : O) (hpn : λ₀^2∣n-1) :
    rowTwist (lowPeriodicBase η C B D s hs χ) B 1 z n=
      (coprimalityMask B*(rayMonoid χ*rowCoefficient η C.Xi s hs z)) n := by
  by_cases hc : IsCoprime B n
  · have hn := supported_of_coprime_bad B n hBL hB2 hc
    have hm : coprimalityMask B n=(1:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=1;rw [ite_eq_left hc]
    rw [rowTwist_extract_sixth_mask _ _ _ _ _ hn,lowPeriodicBase_eq_primary η C B D hBL hB2 s hs χ n hn hpn hc]
    simp only [MonoidHom.mul_apply,hm,mul_one,one_pow,one_mul]
    change (rayMonoid χ n*((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n))*
      idealRowHom z (Ideal.span {n})=rayMonoid χ n*
        (((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n)*idealRowHom z (Ideal.span {n}))
    ring
  · have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [ite_eq_right hc]
    change lowPeriodicBase η C B D s hs χ n*idealRowHom (B^6*1^4*z) (Ideal.span {n})=
      coprimalityMask B n*(rayMonoid χ n*rowCoefficient η C.Xi s hs z n)
    rw [lowPeriodicBase_zero_of_not_coprime η C B D s hs χ n hc,hm,zero_mul,zero_mul]

lemma calibration_coprime_iff_excluded_span (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (a : O) :
    IsCoprime (calibrationForSet S hS).generator a ↔ ∀P∈S,¬P∣Ideal.span {a} := by
  rw [calibrationForSet_coprime_iff]
  constructor
  · intro h P hP hd
    exact h P hP (Ideal.dvd_iff_le.mp hd (Ideal.subset_span (by simp)))
  · intro h P hP ha
    apply h P hP
    exact Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha))

end SevenEighths.ProbePhysical
end

end OAI

end Source1354

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowCompletion.lean; sha256: 15bd6e1af491221e8db627e922ea01f2bc69a8e3cce3d24b72ea1366483ee71d -/
section Source1355
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma summand_zero_completedIndex (Ψ : O→*ℂ) (W : ℝ→ℂ) (X : ℝ) (I J : Id)
    (h : completedIndex I J=0) : summand Ψ W X I J=0 := by
  have hprod : primaryGenerator I*primaryGenerator J^3=0 := h
  rcases mul_eq_zero.mp hprod with hI|hJ
  · simp only [summand,columnWeight,squarefreeGaussCoefficient,hI,ne_eq,not_true_eq_false,
      and_false,dite_false,zero_mul,zero_div]
  · have hj : primaryGenerator J=0 := (pow_eq_zero_iff (by decide : 3≠0)).mp hJ
    have hc : cubeWeight Ψ J=0 := by
      change star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3*
        Ψ (primaryGenerator J)^3/(Ideal.absNorm J:ℂ)=0
      simp only [hj,FiniteGaussPhase.angularFactor,map_zero,norm_zero,Complex.ofReal_zero,
        div_zero,star_zero,zero_pow (by decide : (3:ℕ)≠0),zero_mul,zero_div]
    simp only [summand,hc,mul_zero,zero_mul]

lemma markedSummand_eq_punctured (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : Id) (Ψ : O→*ℂ) (W : ℝ→ℂ) (X : ℝ) (I J : Id) :
    markedSummand S D Ψ W X I J=
      summand (coprimalityMask (calibrationForSet S hS).generator*Ψ) W X I J*
        (if D∣I*J^3 then (1:ℂ) else 0) := by
  rw [summand_mul_fixed_twist]
  change completedMask S D I J*summand Ψ W X I J=
    coprimalityMask (calibrationForSet S hS).generator (completedIndex I J)*summand Ψ W X I J*
      (if D∣I*J^3 then (1:ℂ) else 0)
  by_cases hA : completedIndex I J=0
  · rw [summand_zero_completedIndex Ψ W X I J hA]
    simp only [mul_zero,zero_mul]
  · have he := calibration_coprime_iff_excluded_span S hS (completedIndex I J)
    rw [completedIndex_eq_primaryGenerator] at he hA
    rw [(primaryGenerator_spec (I*J^3) hA).1] at he
    change _=(if IsCoprime (calibrationForSet S hS).generator (completedIndex I J) then (1:ℂ) else 0)*_ * _
    rw [completedIndex_eq_primaryGenerator,he]
    unfold completedMask
    by_cases hd : D∣I*J^3 <;> by_cases hx : ∀P∈S,¬P∣I*J^3 <;>
      simp only [hd,hx,and_self,and_false,true_and,false_and,ite_true,ite_false,mul_one,mul_zero,zero_mul] ; simp_all

lemma markedCompletedT_eq_punctured (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : Id) (Ψ : O→*ℂ) (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X) :
    ProbeCompleted.markedCompletedT S D Ψ W X=
      InverseMoment.markedCompletedT (coprimalityMask (calibrationForSet S hS).generator*Ψ) W X
        (fun A=>if D∣A then (1:ℂ) else 0) := by
  rw [InverseMoment.markedCompletedT_eq_tsum _ W hW X hX]
  unfold ProbeCompleted.markedCompletedT
  apply tsum_congr
  intro p
  exact markedSummand_eq_punctured S hS D Ψ W X p.1 p.2

lemma inverseMarkedCompletedT_congr_primary (Ψ Φ : O→*ℂ)
    (h : ∀n : O,ConcretePrimeRowBridge.goodLambda^2∣n-1→Ψ n=Φ n)
    (W : ℝ→ℂ) (X : ℝ) (d : Id→ℂ) :
    InverseMoment.markedCompletedT Ψ W X d=InverseMoment.markedCompletedT Φ W X d := by
  unfold InverseMoment.markedCompletedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [summand,summand,columnWeight_congr_primary Ψ Φ h,cubeWeight_congr_primary Ψ Φ h]

def calibrationLowData (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) :
    GoodMaskRowData (calibrationForSet S hS).generator 1 (calibrationForSet S hS).generator :=
  goodMaskRowData _ 1 _ (calibrationForSet S hS).generator_ne_zero one_ne_zero
    (calibrationForSet S hS).generator_ne_zero

theorem correctedPhysicalRow_eq_periodic_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (s : O) (hs : Supported (Ideal.span {s})) (z : O) (D : Id)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X)
    (E : GoodMaskRowData (calibrationForSet S hS).generator 1 (calibrationForSet S hS).generator) :
    correctedCompletedT S D (rowCoefficient η (calibrationForSet S hS).Xi s hs z) W X=
      ∑χ : RayCharacter,correctionCoeff χ*InverseMoment.markedCompletedT
        (rowTwist (lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator E s hs χ)
          (calibrationForSet S hS).generator 1 z) W X (fun A=>if D∣A then (1:ℂ) else 0) := by
  rw [correctedCompletedT_ray_expansion S D _ W hW X hX]
  apply Finset.sum_congr rfl
  intro χ _
  rw [markedCompletedT_eq_punctured S hS D _ W hW X hX]
  congr 1
  apply inverseMarkedCompletedT_congr_primary
  intro n hn
  exact (lowPeriodicRow_eq_primary η (calibrationForSet S hS) (calibrationForSet S hS).generator E
    (calibration_generator_bad S hS hbad).1 (calibration_generator_bad S hS hbad).2 s hs χ z n hn).symm

end SevenEighths.ProbePhysical
end

end OAI

end Source1355

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianLow.lean; sha256: 3a37f28e065cc4c54fbd92e44a08cf0dd03ac6ae1cebc0bba46203be74721bd6 -/
section Source1356
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianDyadicSchwartz (Z : ℝ) (hZ : 0<Z) (j : ℕ) : SchwartzMap ℝ ℂ :=
  (gaussianDyadicProfile_compact Z j).toSchwartzMap (gaussianDyadicProfile_contDiff Z hZ j)

theorem physicalSpectralRow_eq_dyadic_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (s : O) (hs : Supported (Ideal.span {s})) (z : O) (D : Id)
    (Z : ℝ) (hZ : 0<Z) :
    verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*
      spectralRow S D (rowCoefficient η (calibrationForSet S hS).Xi s hs z) t)=
      ∑'j : ℕ,∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist
            (lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
              (calibrationLowData S hS) s hs χ)
            (calibrationForSet S hS).generator 1 z)
          (gaussianDyadicSchwartz Z hZ j) ((2:ℝ)^j)
          (fun A=>if D∣A then (1:ℂ) else 0) := by
  have hΨ := rowCoefficient_norm_le_one η (calibrationForSet S hS).Xi
    (calibrationForSet S hS).Xi_norm_le_one s hs z
  rw [spectralRow_eq_gaussianCompleted _ _ _ hΨ 4 (by norm_num) Z hZ,
    correctedGaussian_eq_tsum_dyadic _ _ _ hΨ Z hZ]
  apply tsum_congr
  intro j
  exact correctedPhysicalRow_eq_periodic_inverse η S hS hbad s hs z D
    (gaussianDyadicProfile Z j) (gaussianDyadicProfile_compact Z j) ((2:ℝ)^j)
    (by positivity) (calibrationLowData S hS)

end SevenEighths.ProbePhysical
end

end OAI

end Source1356

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianDerivative.lean; sha256: e822dd45a58f81ae149643bd4749a53a2e52cee9d70dd83397415ac8e522cf6d -/
section Source1357
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Filter Set Metric
namespace SevenEighths.ProbePhysical

def gaussianLog (z : ℂ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*Complex.exp (-(Complex.log z)^2/4)

lemma gaussianLog_ofReal (y : ℝ) : gaussianLog (y:ℂ)=gaussianMellinProfile y := rfl

lemma gaussianLog_power_bound (z : ℂ) (hz : z≠0) (a : ℝ) :
    ‖gaussianLog z‖≤
      ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*
        Real.exp (Real.pi^2/4+a^2)*‖z‖^(-a) := by
  have hre : (-(Complex.log z)^2/4).re=
      ((Complex.log z).im^2-(Real.log ‖z‖)^2)/4 := by
    simp [pow_two,Complex.mul_re,Complex.log_re]
  have hp : (Complex.log z).im^2≤Real.pi^2 := by
    have h1 := Complex.log_im_le_pi z
    have h2 := Complex.neg_pi_lt_log_im z
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show 0≤Real.pi+(Complex.log z).im by linarith)]
  unfold gaussianLog
  rw [norm_mul,Complex.norm_exp,hre,Real.rpow_def_of_pos (norm_pos_iff.mpr hz),
    mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (Real.log ‖z‖/2-a)]

lemma iteratedDeriv_restrict_positive (f : ℂ→ℂ)
    (hf : ∀x : ℝ,0<x→AnalyticAt ℂ f (x:ℂ)) (n : ℕ) (x : ℝ) (hx : 0<x) :
    iteratedDeriv n (fun y : ℝ=>f (y:ℂ)) x=iteratedDeriv n f (x:ℂ) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ',iteratedDeriv_succ']
    have he : Set.EqOn (deriv (fun y : ℝ=>f (y:ℂ))) (fun y : ℝ=>deriv f (y:ℂ)) (Set.Ioi 0) := by
      intro y hy
      exact (hf y hy).differentiableAt.hasDerivAt.comp_ofReal.deriv
    rw [he.iteratedDeriv_of_isOpen isOpen_Ioi n hx]
    exact ih (deriv f) (fun y hy=>(hf y hy).deriv)

lemma gaussianLog_analytic (z : ℂ) (hz : 0<z.re) : AnalyticAt ℂ gaussianLog z := by
  have hl := analyticAt_clog (Complex.mem_slitPlane_iff.mpr (Or.inl hz))
  unfold gaussianLog
  exact analyticAt_const.mul (((hl.pow 2).neg.div_const (c:=4)).cexp)

lemma gaussianLog_scaled_analytic (r : ℝ) (hr : 0<r) (z : ℂ) (hz : 0<z.re) :
    AnalyticAt ℂ (fun w : ℂ=>gaussianLog ((r:ℂ)*w)) z := by
  have h : 0<((r:ℂ)*z).re := by simpa using mul_pos hr hz
  exact (gaussianLog_analytic _ h).comp (analyticAt_const.mul analyticAt_id)

lemma gaussianLog_scaled_disk_bound (a : ℝ) :
    ∃C : ℝ,0<C ∧ ∀r : ℝ,0<r→∀y∈Set.Icc (1/2:ℝ) 2,
      ∀z∈Metric.closedBall (y:ℂ) (1/4),‖gaussianLog ((r:ℂ)*z)‖≤C*r^(-a) := by
  have hc : ContinuousOn (fun t : ℝ=>t^(-a)) (Set.Icc (1/4:ℝ) (9/4)) := by
    intro t ht
    exact (continuousAt_id.rpow_const (Or.inl (show t≠0 by linarith [ht.1]))).continuousWithinAt
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hBpos : 0<B := by
    have hh := hB 1 (by norm_num : (1:ℝ)∈Set.Icc (1/4:ℝ) (9/4))
    norm_num at hh
    linarith
  let c := ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*Real.exp (Real.pi^2/4+a^2)
  have hcn : 0≤c := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine ⟨(c+1)*B,by positivity,?_⟩
  intro r hr y hy z hz
  have hd : ‖z-(y:ℂ)‖≤1/4 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have hyr : ‖(y:ℂ)‖=y := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith [hy.1])]
  have hu := norm_sub_norm_le z (y:ℂ)
  have hl := norm_sub_norm_le (y:ℂ) z
  rw [hyr] at hu hl
  rw [norm_sub_rev] at hl
  have hzn : ‖z‖∈Set.Icc (1/4:ℝ) (9/4) := ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hz0 : z≠0 := norm_pos_iff.mp (by linarith [hzn.1])
  have hrz : (r:ℂ)*z≠0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hz0
  have hb : ‖z‖^(-a)≤B := (le_abs_self _).trans (hB ‖z‖ hzn)
  have hh := gaussianLog_power_bound ((r:ℂ)*z) hrz a
  have hnorm : ‖(r:ℂ)*z‖=r*‖z‖ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  rw [hnorm,Real.mul_rpow hr.le (norm_nonneg _)] at hh
  calc
    _ ≤ c*(r^(-a)*‖z‖^(-a)) := hh
    _ ≤ c*(r^(-a)*B) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (by positivity)) hcn
    _ ≤ (c+1)*B*r^(-a) := by nlinarith [mul_nonneg hBpos.le (Real.rpow_pos_of_pos hr (-a)).le]

lemma gaussianLog_scaled_derivative_bound (a : ℝ) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀r : ℝ,0<r→∀y∈Set.Icc (1/2:ℝ) 2,
      ‖iteratedDeriv n (fun x : ℝ=>gaussianMellinProfile (r*x)) y‖≤C*r^(-a) := by
  obtain ⟨B,hB,hbound⟩ := gaussianLog_scaled_disk_bound a
  refine ⟨(n.factorial:ℝ)*B/(1/4:ℝ)^n,by positivity,?_⟩
  intro r hr y hy
  have hf : ∀x : ℝ,0<x→AnalyticAt ℂ (fun z : ℂ=>gaussianLog ((r:ℂ)*z)) (x:ℂ) :=
    fun x hx=>gaussianLog_scaled_analytic r hr (x:ℂ) hx
  have he : (fun x : ℝ=>gaussianMellinProfile (r*x))=
      (fun x : ℝ=>gaussianLog ((r:ℂ)*(x:ℂ))) := by
    funext x
    rw [←Complex.ofReal_mul,gaussianLog_ofReal]
  rw [he,iteratedDeriv_restrict_positive _ hf n y (by linarith [hy.1])]
  have hd : DiffContOnCl ℂ (fun z : ℂ=>gaussianLog ((r:ℂ)*z)) (Metric.ball (y:ℂ) (1/4)) := by
    apply DifferentiableOn.diffContOnCl_ball (U:={z : ℂ|0<z.re})
      (fun z hz=>(gaussianLog_scaled_analytic r hr z hz).differentiableAt.differentiableWithinAt)
    intro z hz
    have hn : ‖z-(y:ℂ)‖≤1/4 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    have ha := (Complex.abs_re_le_norm (z-(y:ℂ))).trans hn
    simp only [Complex.sub_re,Complex.ofReal_re,abs_le] at ha
    change 0<z.re
    linarith [hy.1]
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0:ℝ)<1/4) hd
    (fun z hz=>hbound r hr y hy z (Metric.sphere_subset_closedBall hz))
  exact hh.trans_eq (by ring)

end SevenEighths.ProbePhysical
end

end OAI

end Source1357

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianSeminorm.lean; sha256: f355f3fe007d6f1f3bb535ca92e0e37e996ffc214669ae3f33cb1a8f2d11b25a -/
section Source1358
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open Filter Set
namespace SevenEighths.ProbePhysical

def gaussianFixedWindow (y : ℝ) : ℂ := gaussianAnnulus y/(Real.sqrt y:ℂ)
lemma gaussianFixedWindow_small (y : ℝ) (hy : y≤1/2) : gaussianFixedWindow y=0 := by
  simp only [gaussianFixedWindow,gaussianAnnulus_small y hy,zero_div]
lemma gaussianFixedWindow_large (y : ℝ) (hy : 2≤y) : gaussianFixedWindow y=0 := by
  simp only [gaussianFixedWindow,gaussianAnnulus_large y hy,zero_div]
lemma gaussianFixedWindow_compact : HasCompactSupport gaussianFixedWindow := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(1/2:ℝ)) (b:=2))
  intro y hy
  change gaussianFixedWindow y≠0 at hy
  constructor
  · by_contra h; exact hy (gaussianFixedWindow_small y (le_of_lt (lt_of_not_ge h)))
  · by_contra h; exact hy (gaussianFixedWindow_large y (le_of_lt (lt_of_not_ge h)))
lemma gaussianFixedWindow_contDiff : ContDiff ℝ ∞ gaussianFixedWindow := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0<y
  · have hs : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
    have hf : ContDiffAt ℝ ∞ (fun x : ℝ=>(Real.sqrt x:ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y (Real.contDiffAt_sqrt hy.ne')
    unfold gaussianFixedWindow
    simp only [div_eq_mul_inv]
    exact gaussianAnnulus_contDiff.contDiffAt.mul (hf.fun_inv hs)
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (show y<(1/2:ℝ) by linarith)] with x hx
    exact gaussianFixedWindow_small x hx.le

def gaussianFixedSchwartz : SchwartzMap ℝ ℂ := gaussianFixedWindow_compact.toSchwartzMap gaussianFixedWindow_contDiff

lemma gaussianProfile_scaled_smooth (r : ℝ) (hr : 0<r) (y : ℝ) (hy : 0<y) :
    ContDiffAt ℝ ∞ (fun x : ℝ=>gaussianMellinProfile (r*x)) y := by
  have hf : ContDiffAt ℂ ∞ (fun z : ℂ=>gaussianLog ((r:ℂ)*z)) (y:ℂ) :=
    (gaussianLog_scaled_analytic r hr (y:ℂ) hy).contDiffAt
  have hh := (hf.restrict_scalars ℝ).comp y Complex.ofRealCLM.contDiff.contDiffAt
  simpa only [Function.comp_def,Complex.ofRealCLM_apply,←Complex.ofReal_mul,gaussianLog_ofReal] using hh

lemma gaussianDyadicProfile_factor (Z : ℝ) (j : ℕ) :
    gaussianDyadicProfile Z j=(fun y : ℝ=>gaussianFixedWindow y*
      gaussianMellinProfile (((2:ℝ)^j/Z)*y)) := by
  funext y
  unfold gaussianDyadicProfile gaussianFixedWindow
  rw [show (2:ℝ)^j*y/Z=((2:ℝ)^j/Z)*y by ring]
  ring

lemma gaussianDyadicProfile_derivative_outside (Z : ℝ) (j n : ℕ) (y : ℝ)
    (hy : y∉Set.Icc (1/2:ℝ) 2) : iteratedDeriv n (gaussianDyadicProfile Z j) y=0 := by
  have he : gaussianDyadicProfile Z j=ᶠ[𝓝 y](fun _=>0) := by
    simp only [Set.mem_Icc,not_and_or,not_le] at hy
    rcases hy with hy|hy
    · filter_upwards [eventually_lt_nhds hy] with x hx
      exact gaussianDyadicProfile_small Z j x hx.le
    · filter_upwards [eventually_gt_nhds hy] with x hx
      exact gaussianDyadicProfile_large Z j x hx.le
  rw [he.iteratedDeriv_eq n]
  simp

lemma gaussianDyadicProfile_derivative_uniform (a : ℝ) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,0<Z→∀j : ℕ,∀y∈Set.Icc (1/2:ℝ) 2,
      ‖iteratedDeriv n (gaussianDyadicProfile Z j) y‖≤C*(((2:ℝ)^j/Z)^(-a)) := by
  choose B hB hbound using fun i : ℕ=>gaussianLog_scaled_derivative_bound a i
  let A (i : ℕ) := SchwartzMap.seminorm ℝ 0 i gaussianFixedSchwartz
  let C := ∑i∈Finset.range (n+1),(n.choose i:ℝ)*A i*B (n-i)
  have hA (i : ℕ) : 0≤A i := by exact apply_nonneg _ _
  have hC : 0≤C := Finset.sum_nonneg (fun i _=>mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _).le)
  refine ⟨C+1,by positivity,?_⟩
  intro Z hZ j y hy
  have hr : 0<(2:ℝ)^j/Z := div_pos (by positivity) hZ
  have hy0 : 0<y := by linarith [hy.1]
  rw [gaussianDyadicProfile_factor,iteratedDeriv_fun_mul
    (gaussianFixedWindow_contDiff.contDiffAt.of_le (by simp))
    ((gaussianProfile_scaled_smooth _ hr y hy0).of_le (by simp))]
  calc
    _ ≤ ∑i∈Finset.range (n+1),‖(n.choose i:ℂ)*iteratedDeriv i gaussianFixedWindow y*
        iteratedDeriv (n-i) (fun x : ℝ=>gaussianMellinProfile (((2:ℝ)^j/Z)*x)) y‖ := norm_sum_le _ _
    _ ≤ ∑i∈Finset.range (n+1),((n.choose i:ℝ)*A i)*(B (n-i)*(((2:ℝ)^j/Z)^(-a))) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul,norm_mul,Complex.norm_natCast]
      have hfixed : ‖iteratedDeriv i gaussianFixedWindow y‖≤A i := by
        have hh := SchwartzMap.le_seminorm' ℝ 0 i gaussianFixedSchwartz y
        simp only [pow_zero,one_mul] at hh
        exact hh
      exact mul_le_mul (mul_le_mul_of_nonneg_left hfixed (Nat.cast_nonneg _))
        (hbound _ _ hr y hy) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))
    _ = C*(((2:ℝ)^j/Z)^(-a)) := by simp only [C,Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ (C+1)*(((2:ℝ)^j/Z)^(-a)) := by nlinarith [Real.rpow_pos_of_pos hr (-a)]

theorem gaussianDyadicSchwartz_seminorm (a : ℝ) (k n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,∀j : ℕ,
      SchwartzMap.seminorm ℝ k n (gaussianDyadicSchwartz Z hZ j)≤C*(((2:ℝ)^j/Z)^(-a)) := by
  obtain ⟨B,hB,hbound⟩ := gaussianDyadicProfile_derivative_uniform a n
  refine ⟨(2:ℝ)^k*B,by positivity,?_⟩
  intro Z hZ j
  have hr : 0<(2:ℝ)^j/Z := div_pos (by positivity) hZ
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro y
  change |y|^k*‖iteratedDeriv n (gaussianDyadicProfile Z j) y‖≤_
  by_cases hy : y∈Set.Icc (1/2:ℝ) 2
  · have habs : |y|≤2 := by rw [abs_of_nonneg (by linarith [hy.1])]; exact hy.2
    calc
      _ ≤ (2:ℝ)^k*(B*(((2:ℝ)^j/Z)^(-a))) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) habs k) (hbound Z hZ j y hy)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [gaussianDyadicProfile_derivative_outside Z j n y hy,norm_zero,mul_zero]
    positivity

theorem gaussianDyadicSchwartz_finite_seminorm (a : ℝ) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,∀j : ℕ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
        C*(((2:ℝ)^j/Z)^(-a)) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1,by norm_num,?_⟩
    intro Z hZ j
    simp only [Finset.sup_empty,one_mul]
    change 0≤(((2:ℝ)^j/Z)^(-a))
    exact Real.rpow_nonneg (by positivity) _
  | @insert p S hp ih =>
    obtain ⟨B,hB,hbound⟩ := gaussianDyadicSchwartz_seminorm a p.1 p.2
    obtain ⟨C,hC,hrest⟩ := ih
    refine ⟨B+C,by positivity,?_⟩
    intro Z hZ j
    rw [Finset.sup_insert,Seminorm.sup_apply]
    apply max_le
    · exact (hbound Z hZ j).trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) (-a)])
    · exact (hrest Z hZ j).trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) (-a)])

theorem gaussianDyadicSchwartz_two_sided (A : ℝ) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,∀j : ℕ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
        C*min (((2:ℝ)^j/Z)^A) (((2:ℝ)^j/Z)^(-A)) := by
  obtain ⟨B,hB,hlo⟩ := gaussianDyadicSchwartz_finite_seminorm (-A) S
  obtain ⟨C,hC,hhi⟩ := gaussianDyadicSchwartz_finite_seminorm A S
  refine ⟨B+C,by positivity,?_⟩
  intro Z hZ j
  rw [mul_min_of_nonneg _ _ (by positivity : 0≤B+C)]
  apply le_min
  · have hh := hlo Z hZ j
    rw [neg_neg] at hh
    exact hh.trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) A])
  · exact (hhi Z hZ j).trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) (-A)])

end SevenEighths.ProbePhysical
end

end OAI

end Source1358

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussianSummation.lean; sha256: 8cbdf3603586c4d8f8da6f22fcbbcc8d4521d19b7977da4a2db8c7b5e537e196 -/
section Source1359
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbePhysical

lemma gaussianDyadicSchwartz_polynomial_decay (N : ℕ) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,∀j : ℕ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
        C/(1+(2:ℝ)^j/Z)^N := by
  obtain ⟨B,hB,hzero⟩ := gaussianDyadicSchwartz_finite_seminorm 0 S
  obtain ⟨C,hC,hdecay⟩ := gaussianDyadicSchwartz_finite_seminorm (N:ℝ) S
  refine ⟨(B+C)*(2:ℝ)^N,by positivity,?_⟩
  intro Z hZ j
  let r := (2:ℝ)^j/Z
  have hr : 0<r := div_pos (by positivity) hZ
  have hden : 0<(1+r)^N := pow_pos (by linarith) _
  change _≤(B+C)*(2:ℝ)^N/(1+r)^N
  by_cases hr1 : r≤1
  · have hh := hzero Z hZ j
    simp only [neg_zero,Real.rpow_zero,mul_one] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+r)^N≤(2:ℝ)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hb := mul_le_mul_of_nonneg_left hp hB.le
    nlinarith [mul_nonneg hC.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)]
  · have hh := hdecay Z hZ j
    change _≤C*r^(-(N:ℝ)) at hh
    rw [Real.rpow_neg hr.le,Real.rpow_natCast] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+r)^N≤(2*r)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hi : 0≤C*(r^N)⁻¹ := by positivity
    have hm := mul_le_mul_of_nonneg_left hp hi
    rw [mul_pow] at hm
    have hn : r^N≠0 := ne_of_gt (pow_pos hr _)
    have he : (C*(r^N)⁻¹)*((2:ℝ)^N*r^N)=C*(2:ℝ)^N := by field_simp
    rw [he] at hm
    exact hm.trans (by nlinarith [mul_nonneg hB.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)])

theorem gaussianDyadicSchwartz_summed (s : ℝ) (hs : 0<s) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,
      Summable (fun j : ℕ=>((2:ℝ)^j)^s*
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)) ∧
      (∑'j : ℕ,((2:ℝ)^j)^s*
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j))≤C*Z^s := by
  obtain ⟨N,hN⟩ := exists_nat_gt s
  obtain ⟨B,hB,hbound⟩ := gaussianDyadicSchwartz_polynomial_decay N S
  obtain ⟨C,hC,hkernel⟩ := CompletedDyadic.kernel_sum_bound s (N:ℝ) hs hN
  refine ⟨B*C,by positivity,?_⟩
  intro Z hZ
  obtain ⟨hks,hkt⟩ := hkernel Z⁻¹ (inv_pos.mpr hZ)
  have hb (j : ℕ) : ((2:ℝ)^j)^s*
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
      B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := by
    have hh := mul_le_mul_of_nonneg_left (hbound Z hZ j) (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s)
    simpa only [CompletedDyadic.kernelTerm,Real.rpow_natCast,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hnon (j : ℕ) : 0≤((2:ℝ)^j)^s*
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j) := by positivity
  have hsum := Summable.of_nonneg_of_le hnon hb (hks.mul_left B)
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := hsum.tsum_le_tsum hb (hks.mul_left B)
    _ = B*∑'j : ℕ,CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := tsum_mul_left
    _ ≤ B*(C*(Z⁻¹)^(-s)) := mul_le_mul_of_nonneg_left hkt hB.le
    _ = (B*C)*Z^s := by rw [Real.inv_rpow hZ.le,Real.rpow_neg hZ.le,inv_inv]; ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1359
