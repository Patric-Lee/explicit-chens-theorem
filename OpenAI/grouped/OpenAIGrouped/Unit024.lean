import OpenAIGrouped.Unit023
import OpenAIGrouped.Unit021
import OpenAIGrouped.Unit016
import OpenAIGrouped.Unit019
import OpenAIGrouped.Unit015
import OpenAIGrouped.Unit010
import OpenAIGrouped.Unit011
import OpenAIGrouped.Unit022
import OpenAIGrouped.Unit014

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Moments/UniformNaturalRetained.lean; sha256: 6c1d0c213d19a2f0efb28a31314419738261fa3221f2e0d4e5bbc44032142806 -/
section Source960
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentUniformNaturalRetained
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum CenteredMomentNaturalPrimitive
open CenteredMomentUniformRetainedEnergy CenteredMomentUniformReflectionApproximation CenteredMomentRetainedWeightedSource
open CenteredMomentReflectedChoiceEnergy CenteredMomentReflectionWeightedEnergy
open CenteredMomentOriginalReflectionApproximation CenteredMomentSectorLocalization

theorem actual_natural_retained_energy (epsilon Cscale xi : ℝ)
     (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι],∀(G : ι→𝓢(ℝ,ℂ))(χ ψ : ι→Character)(P : ι→ℂ)(omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d M along bshort D E Rcap : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      (∀i,(ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0<D → 0≤E → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) → 1≤Rcap →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Z^bshort) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedSchwartz (χ i) (ψ i) (G i) (Z^along) (Z^(xi/4))*
        polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*D^2*(1+2*(max 0 (M-along+xi)*Real.log Z))*E := by
  obtain ⟨H,C,hC,hb⟩ := actual_retained_uniform_energy epsilon hepsilon B J hB
  refine ⟨H,C,hC,?_⟩
  filter_upwards [eventually_natural_choice_geometry Cscale xi hscale hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ G χ ψ P omega Wshort c d M along bshort D E Rcap hd hshort hshortsmooth
    hnatural hmod hD hE hGD hRcap hcap henergy
  have hz : 0<Z := by linarith [hZ.1]
  have hlog : 0≤Real.log Z := (Real.log_pos hZ.1).le
  have hexp : Real.exp (bshort*Real.log Z)=Z^bshort := by
    rw [Real.rpow_def_of_pos hz,mul_comm]
  have hgeom (i : ι) (u : Index (sourcePrimes (χ i) (ψ i)))
      (hY : 0<dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2)
      (hu : u.2∈CenteredMomentReflectedTruncation.retainedAnnuli (Z^(xi/4))
        (dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2) hY) :
      Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2)∈
        Set.Icc 0 (max 0 (M-along+xi)*Real.log Z) := by
    have hh := hZ.2 (χ i) (ψ i) M along (hnatural i) (hmod i) u hY hu
    exact ⟨hh.2.1,hh.2.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog)⟩
  have hrad (i : ι) : (Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap :=
    (radical_le_original (χ i) (ψ i) (hnatural i)).trans (hcap i)
  have hh := hb G χ ψ P (fun _=>Z^along) (fun _=>Z^(xi/4)) (fun _=>bshort*Real.log Z) omega
    Wshort c d 0 (max 0 (M-along+xi)*Real.log Z) (bshort*Real.log Z) (bshort*Real.log Z)
    D E Rcap (fun _=>Real.rpow_pos_of_pos hz _) hd hshort hshortsmooth
    (mul_nonneg (le_max_left _ _) hlog) le_rfl (fun _=>⟨le_rfl,le_rfl⟩) hgeom
    hD hE hGD hRcap hrad (by
      intro v j k x hx y hy
      have hey : y=bshort*Real.log Z := le_antisymm hy.2 hy.1
      simpa only [hey,hexp] using henergy v j k x hx)
  simpa only [hexp,sub_zero,sub_self,mul_zero,add_zero,mul_one] using hh

end SevenEighths.CenteredMomentUniformNaturalRetained

end

end OAI

end Source960

/- Original source: OAI/NumberTheory/DirichletL/Moments/UniformOriginalEnergy.lean; sha256: 600d41574689ea6caf3e6e7158124fa97633b23eb4d30fbb209b3fa6403b6737 -/
section Source961
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentUniformOriginalEnergy
open HeckeFamily CenteredMomentUniformReflectionApproximation CenteredMomentNaturalPrimitive
open CenteredMomentOriginalReflectionEnergy

theorem actual_original_energy_to_retained (xi saving L Cscale ε : ℝ)
     (hxi : 0<xi) (hscale : 0<Cscale) (hε : 0<ε) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀χ : ι→Character,
        (∀i,(χ i).residue≠1) →
        ∃ψ : ι→Character,
        (∀i,FiniteFourier.IsPrimitiveOnIdeals (ψ i).residue ∧ (ψ i).residue≠1 ∧
          (ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) ∧
        ∀(W : ι→𝓢(ℝ,ℂ))(X : ι→ℝ)(P : ι→ℂ)(D Z Rcap : ℝ),0<D → 1≤Z → 1≤Rcap →
          (∀i,0<X i) → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (W i)≤D) → (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
          (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^L*X i) →
          (∑i,‖HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0*P i‖^2)≤
            2*(∑i,‖retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2))*P i‖^2)+
            C*Rcap^(2*ε)*D^2*Z^(-2*saving)*(∑i,‖P i‖^2) := by
  obtain ⟨H,C,hC,hb⟩ := actual_original_approximation xi saving L Cscale ε hxi hscale hε
  refine ⟨H,2*C^2,by positivity,?_⟩
  intro ι _ χ hχ
  choose ψ G hp hnψ hG hcap happrox using fun i=>hb (χ i) (hχ i)
  refine ⟨ψ,fun i=>⟨hp i,hnψ i,hcap i⟩,?_⟩
  intro W X P D Z Rcap hD hZ hR hX hWD hmod hsource
  let B := C*D*Rcap^ε*Z^(-saving)
  have hB : 0≤B := by dsimp [B];positivity
  have herr (i : ι) :
      ‖HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0-
        G i*retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2))‖≤B := by
    apply (happrox i (W i) (X i) Z (hX i) hZ (hsource i)).trans
    dsimp [B]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hWD i) hC.le)
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hmod i) hε.le)
      (by positivity) (by positivity)
  have hpoint (i : ι) :
      ‖HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0*P i‖^2≤
      2*‖retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2))*P i‖^2+B^2*(2*‖P i‖^2) := by
    have hh := norm_sq_comparison
      (HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0*P i)
      ((G i*retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2)))*P i)
    have he : ‖HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0*P i-
        (G i*retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2)))*P i‖≤B*‖P i‖ := by
      rw [←sub_mul,norm_mul]
      exact mul_le_mul_of_nonneg_right (herr i) (norm_nonneg _)
    have hs := pow_le_pow_left₀ (norm_nonneg _) he 2
    simp only [norm_mul,hG,one_mul] at hh
    simp only [mul_pow] at hs
    simp only [norm_mul]
    nlinarith
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset ι))=>hpoint i)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  have hBeq : B^2*2=(2*C^2)*Rcap^(2*ε)*D^2*Z^(-2*saving) := by
    have hr0 : 0≤Rcap := by linarith
    have hz0 : 0≤Z := by linarith
    have hr : (Rcap^ε)^2=Rcap^(2*ε) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hr0];congr 1;ring
    have hz : (Z^(-saving))^2=Z^(-2*saving) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hz0];congr 1;ring
    dsimp [B]
    rw [mul_pow,mul_pow,mul_pow,hr,hz]
    ring
  convert hh using 1
  rw [←mul_assoc,hBeq]

end SevenEighths.CenteredMomentUniformOriginalEnergy

end

end OAI

end Source961

/- Original source: OAI/NumberTheory/DirichletL/Moments/UniformOriginalComparison.lean; sha256: 132c6c53051fe11e4a82bd8e38157b59a3aa981e7f3d87fa4b127553917deb96 -/
section Source962
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentUniformOriginalComparison
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentUniformNaturalRetained CenteredMomentUniformOriginalEnergy
open CenteredMomentSectorLocalization

theorem actual_original_comparison (epsilon Cscale xi saving L : ℝ)
     (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C D : ℝ,0<C ∧ 0<D ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι],∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)(omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d M along bshort E S Rcap : ℝ),
      (∀i,(χ i).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      M≤L+along → (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0≤E → 0<S → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤S) → 1≤Rcap →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Z^bshort) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i) false (G i) (Z^along) 0 0*
        polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*S^2*(1+2*(max 0 (M-along+xi)*Real.log Z))*E+
        D*Rcap^(2*epsilon)*S^2*Z^(-2*saving)*
          (∑i,‖polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2) := by
  obtain ⟨H,C,hC,hr⟩ := actual_natural_retained_energy epsilon Cscale xi hepsilon hscale hxi B J hB
  obtain ⟨H',D,hD,ho⟩ := actual_original_energy_to_retained (xi/2) saving L Cscale epsilon
    (by positivity) hscale hepsilon
  refine ⟨H∪H',2*C,D,by positivity,hD,?_⟩
  filter_upwards [hr] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ G χ P omega Wshort c d M along bshort E S Rcap hχ hd hshort hshortsmooth
    hML hmod hE hS hGS hRcap hcap henergy
  have hz : 0<Z := by linarith [hZ.1]
  have hG1 (i:ι):H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤S :=
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left : H⊆H∪H')) (G i)).trans (hGS i)
  have hG2 (i:ι):H'.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤S :=
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right : H'⊆H∪H')) (G i)).trans (hGS i)
  obtain ⟨ψ,hψ,horiginal⟩ := ho χ hχ
  let Q (i : ι) := polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i
  have hsource (i : ι) : ((χ i).modulus.absNorm:ℝ)≤Cscale*Z^L*Z^along := by
    have hh := (hmod i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hML) hscale.le)
    rw [Real.rpow_add hz] at hh
    simpa only [mul_assoc] using hh
  have he := horiginal G (fun _=>Z^along) Q S Z Rcap hS hZ.1.le hRcap
    (fun _=>Real.rpow_pos_of_pos hz _) hG2 hcap hsource
  have hcut : (xi/2)/2=xi/4 := by ring
  rw [hcut] at he
  have hretained := hZ.2 G χ ψ P omega Wshort c d M along bshort S E Rcap
    hd hshort hshortsmooth (fun i=>(hψ i).2.2) hmod hS hE hG1 hRcap hcap henergy
  dsimp only [Q] at he
  simp only [←mul_assoc] at he
  have hh := he.trans (add_le_add (mul_le_mul_of_nonneg_left hretained (by norm_num : (0:ℝ)≤2)) le_rfl)
  convert hh using 1 ; ring

end SevenEighths.CenteredMomentUniformOriginalComparison

end

end OAI

end Source962

/- Original source: OAI/NumberTheory/DirichletL/Moments/UniformRadialComparison.lean; sha256: 7a90cb493ab9f60f6863a9fa8f45359092f1a39907b2f5bcf4d652c3a5373866 -/
section Source963
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentUniformRadialComparison
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentOriginalRadialComparison CenteredMomentRadialPolynomialEnergy
local notation "O" => HeckeFamily.O

theorem actual_original_radial_comparison (epsilon Cscale xi saving L : ℝ)
     (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C D : ℝ,0<C ∧ 0<D ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀(G:O→𝓢(ℝ,ℂ))(χ : O→Character)(P : O→ℂ)(omega : O→ℝ)(keep : O→Prop)
        (Φ : 𝓢(ℝ,ℂ))(K Pbound : ℝ)(Wshort : ℝ→ℂ)(c d M along bshort E Src Rcap : ℝ),
      0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) → (∀z,‖P z‖≤Pbound) →
      (∀z,keep z → (χ z).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      M≤L+along → (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0≤E → 0<Src → (∀z,keep z → H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G z)≤Src) → 1≤Rcap →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        radialEnergy (fun z=>polynomial (χ z) false (scaleTest (fun y : ℝ=>(annulus y:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ z) false (scaleTest Wshort k) (Z^bshort) 0 (omega z)*P z) keep Φ K
          ≤E*(1+‖v‖)^(2*J)) →
      radialEnergy (fun z=>polynomial (χ z) false (G z) (Z^along) 0 0*
        polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) keep Φ K≤
        C*Rcap^epsilon*Src^2*(1+2*(max 0 (M-along+xi)*Real.log Z))*E+
        D*Rcap^(2*epsilon)*Src^2*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) keep Φ K := by
  obtain ⟨H,C,D,hC,hD,h⟩:=CenteredMomentUniformOriginalComparison.actual_original_comparison
    epsilon Cscale xi saving L hepsilon hscale hxi B J hB
  refine ⟨H,C,D,hC,hD,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro G χ P omega keep Φ K Pbound Wshort c d M along bshort E Src Rcap hK hΦ hP hχ
    hd hshort hshortsmooth hML hmod hE hSrc hGS hRcap hcap henergy
  have hz : 0<Z:=by linarith [hZ.1]
  have hshortsum:=single_radial_summable χ P omega Wshort c d (Z^bshort) Pbound hd
    (Real.rpow_pos_of_pos hz _) hshort hP keep Φ K hK
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  let weightedP (z : ↥S) : ℂ:=P z*(Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)
  have hmem (z : ↥S) : keep (z:O):=(Finset.mem_filter.mp z.property).2
  have hh:=hZ.2 (fun z:↥S=>G z) (fun z:↥S=>χ z) weightedP (fun z=>omega z)
    Wshort c d M along bshort E Src Rcap (fun z=>hχ z (hmem z)) hd hshort hshortsmooth
    hML (fun z=>hmod z (hmem z)) hE hSrc (fun z=>hGS z (hmem z)) hRcap
    (fun z=>hcap z (hmem z)) ?_
  · simp only [weightedP,←mul_assoc] at hh
    rw [finite_weighted rows keep (fun z=>polynomial (χ z) false (G z) (Z^along) 0 0*polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) Φ K hΦ,
      finite_weighted rows keep (fun z=>polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) Φ K hΦ] at hh
    apply hh.trans
    apply add_le_add
    · apply le_of_eq;ring
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hshortsum.sum_le_tsum rows (fun z _=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  · intro v j k x hx
    have hschild:=pair_radial_summable χ P (fun _=>-2*Real.pi*v) omega
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (scaleTest Wshort k)
      (1/4) 1 c d (Real.exp x) (Z^bshort) Pbound (by norm_num) hd
      (Real.exp_pos _) (Real.rpow_pos_of_pos hz _)
      (scaleTest_support _ _ _ CenteredMomentOneReflectionScaleEnergy.annulus_complex_support j)
      (scaleTest_support _ _ _ hshort k) hP keep Φ K hK
    simp only [weightedP,←mul_assoc]
    rw [finite_weighted rows keep (fun z=>polynomial (χ z) false (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*polynomial (χ z) false (scaleTest Wshort k) (Z^bshort) 0 (omega z)*P z) Φ K hΦ]
    exact (hschild.sum_le_tsum rows (fun z _=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)).trans
      (henergy v j k x hx)

end SevenEighths.CenteredMomentUniformRadialComparison

end

end OAI

end Source963

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonMaskRadialEnergy.lean; sha256: 838aac67e0bc70213469f3912e19bbdae1f60b8df7259c68547b0db092de7d21 -/
section Source964
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentCommonMaskRadialEnergy
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentRadialPolynomialEnergy
open CenteredMomentUniformReflectionProfile
local notation "O" => HeckeFamily.O

lemma naturalSlot_bounded (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) :
    ∃B : ℝ,0≤B ∧ ∀χ : Character,‖naturalSlot χ pool β P‖≤B := by
  refine ⟨‖(Real.sqrt P:ℂ)⁻¹‖*∑I∈pool,‖β I‖,by positivity,?_⟩
  intro χ
  unfold naturalSlot
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)

lemma slots_bounded {α : Type*} (F : Finset α) (pool : α→Finset (Ideal O))
    (β : α→Ideal O→ℂ) (P : α→ℝ) :
    ∃B : ℝ,0≤B ∧ ∀χ : Character,‖∏j∈F,naturalSlot χ (pool j) (β j) (P j)‖≤B := by
  choose B hB hb using fun j=>naturalSlot_bounded (pool j) (β j) (P j)
  refine ⟨∏j∈F,B j,Finset.prod_nonneg (fun j _=>hB j),?_⟩
  intro χ
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun j _=>norm_nonneg _) (fun j _=>hb j χ)

theorem actual_radial_shared_energy {α : Type*} [DecidableEq α]
    (F : Finset α) (b M : α→ℝ) (hM : ∀j∈F,0≤M j) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)
      (χ : O→Character)(W₁ W₂ : 𝓢(ℝ,ℂ))(X₁ X₂ a₁ b₁ a₂ b₂ : ℝ)
      (pool : α→Finset (Ideal O))(β : α→Ideal O→ℂ)(P : α→ℝ)
      (keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K E : ℝ),
      0<X₁ → 0<X₂ → 0≤b₁ → 0≤b₂ →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      (∀j∈F,∀I∈pool j,Prime I) → (∀j∈F,0<P j) →
      (∀j∈F,∀I∈pool j,‖β j I‖≤M j) →
      (∀j∈F,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤b j*P j) →
      0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) → 0≤E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        radialEnergy (fun z=>polynomial (χ z) false W₁
          (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          polynomial (χ z) false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ z) (pool j) (β j) (P j)) keep Φ K≤E) →
      radialEnergy (fun z=>polynomial ((χ z).excludePrimes R hR) false W₁ X₁ 0 0 *
        polynomial ((χ z).excludePrimes R hR) false W₂ X₂ 0 0 *
        ∏j∈F,naturalSlot ((χ z).excludePrimes R hR) (pool j) (β j) (P j)) keep Φ K≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E := by
  obtain ⟨C,hC,he⟩:=actual_shared_energy F b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro R hR χ W₁ W₂ X₁ X₂ a₁ b₁ a₂ b₂ pool β P keep Φ K E
    hX₁ hX₂ hb₁ hb₂ hs₁ hs₂ hp hP hβ hs hK hΦ hE hchild
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  let q (z : ↥S) : ℂ:=(Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)
  have hh:=he R hR (fun z:↥S=>χ z) (fun z=>q z • W₁) (fun _=>W₂)
    (fun _=>X₁) (fun _=>X₂) (fun _=>pool) (fun _=>β) (fun _=>P)
    (fun _=>hX₁) (fun _=>hX₂) (fun _=>hp) (fun _=>hP)
    (fun _=>hβ) (fun _=>hs) E hE ?_
  · have hid (χ₀ : Character) (z : ↥S) (X : ℝ) :
        polynomial χ₀ false (q z • W₁ : 𝓢(ℝ,ℂ)) X 0 0=q z*polynomial χ₀ false W₁ X 0 0 := by
      exact polynomial_const_mul χ₀ W₁ X 0 0 (q z)
    simp_rw [hid] at hh
    have halg (z : ↥S) (u v w : ℂ) : q z*u*v*w=(u*v*w)*q z := by ring
    simp_rw [halg] at hh
    exact (finite_weighted rows keep _ Φ K hΦ).symm.trans_le hh
  · intro D₁ hD₁ D₂ hD₂ J hJ
    have hn (D : Finset (Ideal O)) (hD : D∈R.powerset) :
        0<(Ideal.absNorm (∏I∈D,I):ℝ) := by
      apply Nat.cast_pos.mpr
      exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Finset.prod_ne_zero_iff.mpr (fun I hI=>(hR I (Finset.mem_powerset.mp hD hI)).ne_zero)))
    obtain ⟨PB,hPB,hbound⟩:=slots_bounded (F\J) pool β P
    have hsum:=pair_radial_summable χ
      (fun z=>∏j∈F\J,naturalSlot (χ z) (pool j) (β j) (P j))
      (fun _=>0) (fun _=>0) W₁ W₂ a₁ b₁ a₂ b₂
      (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) PB
      hb₁ hb₂ (div_pos hX₁ (hn D₁ hD₁)) (div_pos hX₂ (hn D₂ hD₂)) hs₁ hs₂
      (fun z=>hbound (χ z)) keep Φ K hK
    have hid (χ₀ : Character) (z : ↥S) (X : ℝ) :
        polynomial χ₀ false (q z • W₁ : 𝓢(ℝ,ℂ)) X 0 0=q z*polynomial χ₀ false W₁ X 0 0 :=
      polynomial_const_mul χ₀ W₁ X 0 0 (q z)
    simp_rw [hid]
    have halg (z : ↥S) (u v w : ℂ) : q z*u*v*w=(u*v*w)*q z := by ring
    simp_rw [halg]
    dsimp only [q]
    rw [finite_weighted rows keep (fun z=>polynomial (χ z) false W₁
      (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
      polynomial (χ z) false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
      ∏j∈F\J,naturalSlot (χ z) (pool j) (β j) (P j)) Φ K hΦ]
    exact (hsum.sum_le_tsum rows (fun z _=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)).trans
      (hchild D₁ hD₁ D₂ hD₂ J hJ)
end SevenEighths.CenteredMomentCommonMaskRadialEnergy

end

end OAI

end Source964

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalCoreFloor.lean; sha256: 646f514c99a2e7f89835d34e47fecdf25fa8208ef8fa1e3007d5260c6a0d712e -/
section Source965
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentNaturalCoreFloor
open HeckeFamily HeckeRowClosure CenteredMomentCoreFloor CenteredMomentPlainGlobalEnergy
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

 theorem natural_zero_all_lengths_floor (a b:ℝ)(ha:0<a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀(W₁ W₂:SchwartzMap ℝ ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b→
    ∀(η:Character)(Q:Ideal O)(r:Radial)(bΦ:ℝ),0≤bΦ→
      (Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ)→
      (∀z,r.keep z→z≠0)→
      (∀z,r.keep z→¬FixedInducingRow η Q fixedBadMask 1 z)→
    ∀(Z m q ρ t X₁ X₂:ℝ),1≤Z→0≤m→0≤q→
      r.scale=Z^m→m+q≤ρ→1≤X₁→1≤X₂→
      (η.modulus.absNorm:ℝ)≤Z^q→
    zeroEnergy η fixedBadMask 1 t W₁ W₂ X₁ X₂ r≤
      C*bΦ^4*diagonalControl r.profile*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*(3+|t|)^8*Z^(m+q+4*ρ):=by
  obtain ⟨S,C,hC,hfloor⟩:=zero_all_lengths_floor a b ha
  let F:ℝ:=fixedConductorFactor
  have hF:0<F:=by
    unfold F fixedConductorFactor
    norm_cast
    apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)))
  refine ⟨S,C*F^4,mul_pos hC (pow_pos hF _),?_⟩
  intro W₁ W₂ hs₁ hs₂ η Q r bΦ hbΦ hΦsupp hz hex Z m q ρ t X₁ X₂ hZ hm hq hscale hwidth hX₁ hX₂ hη
  let r':Radial:={r with keep:=fun z=>r.keep z ∧ r.profile (‖eisEmbedding z‖^2/r.scale)≠0}
  let χ:O→Character:=fun z=>if hz:z≠0 then (naturalRow η z hz).character else η
  have hrow (z:O)(h:r'.keep z):∀n,elementCoeff (χ z) n=
      CanonicalRowCompletion.rowTwist (elementHom η) fixedBadMask 1 (1*z) n:=by
    have hz0:=hz z h.1
    simpa only [χ,dite_eq_left hz0,one_mul] using (naturalRow η z hz0).element
  have hnon (z:O)(h:r'.keep z):(χ z).residue≠1:=
    CenteredMomentNonprincipalGate.actual_row_nonprincipal η (χ z) Q fixedBadMask 1 z
      (hrow z h) (hex z h.1)
  have hmod (z:O)(h:r'.keep z):((χ z).modulus.absNorm:ℝ)≤(F*bΦ)*Z^(m+q):=by
    have hz0:=hz z h.1
    have hs:‖eisEmbedding z‖^2/r.scale≤bΦ:=hΦsupp h.2
    have hn:((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^m:=by
      rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
      rw [←hscale]
      exact (div_le_iff₀ r.scale_pos).mp hs
    have hh:=(naturalRow η z hz0).modulus_power_bound Z q m bΦ
      (zero_lt_one.trans_le hZ) hbΦ hη hn
    simpa only [χ,dite_eq_left hz0,add_comm q m] using hh
  have he:=hfloor W₁ W₂ hs₁ hs₂ η fixedBadMask 1 r' χ hnon hrow
    Z m q ρ (F*bΦ) t X₁ X₂ hZ hm hq (mul_nonneg hF.le hbΦ) hscale hwidth hX₁ hX₂ hmod
  have heq:zeroEnergy η fixedBadMask 1 t W₁ W₂ X₁ X₂ r=
      zeroEnergy η fixedBadMask 1 t W₁ W₂ X₁ X₂ r':=by
    unfold zeroEnergy
    apply tsum_congr
    intro z
    by_cases hk:r.keep z
    · by_cases hp:r.profile (‖eisEmbedding z‖^2/r.scale)=0
      · simp [r',hk,hp]
      · simp [r',hk,hp]
    · simp [r',hk]
  rw [heq]
  exact he.trans_eq (by dsimp [r'];ring)

end SevenEighths.CenteredMomentNaturalCoreFloor

end

end OAI

end Source965

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalControl.lean; sha256: 98803ec478799b188928cc6d8d73ef4249d0ffdbef8e9d03424efe629f2d5c20 -/
section Source966
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open FourierBridge JointLogSeparation CompletedHeight CenteredMomentLattice
open EisensteinSchwartzPoisson

theorem frequencyTwist_source_control (S : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, ∃ T : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (g : 𝓢(ℝ, ℂ)) (t : ℝ),
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (frequencyTwist g t) ≤
          C * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g * (1 + ‖t‖)^n := by
  let T := S.biUnion fun z => (Finset.range (z.2+1)).image fun i => (z.1,i)
  let c : ℕ × ℕ → ℝ := fun z => (2:ℝ)^z.2*(1+2*Real.pi)^z.2*(z.2+1)
  let C := 1 + ∑ z ∈ S, c z
  have hc (z) : 0 ≤ c z := by dsimp [c]; positivity
  have hC : 0 < C := by
    have := Finset.sum_nonneg (fun z (_ : z∈S) => hc z)
    dsimp [C]; linarith
  refine ⟨S.sup Prod.snd,T,C,hC,?_⟩
  intro g t
  have hder (z) (hz : z ∈ S) : derivativeSeminormSum g z.1 z.2 ≤
      (z.2+1:ℝ) * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g := by
    calc
      _ ≤ ∑ i ∈ Finset.range (z.2+1), T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g := by
        apply Finset.sum_le_sum
        intro i hi
        apply Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ ℝ ℂ) (i := (z.1,i))
        exact Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩
      _ = _ := by simp
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hzC : c z ≤ C := by
    have := Finset.single_le_sum (fun z (_ : z∈S) => hc z) hz
    dsimp [C]; linarith
  calc
    _ ≤ ((2:ℝ)^z.2*(1+2*Real.pi)^z.2*derivativeSeminormSum g z.1 z.2) *
        (1+‖t‖)^z.2 := frequencyTwist_seminorm_polynomial g t z.1 z.2
    _ ≤ (c z * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g) *
        (1+‖t‖)^z.2 := by
      dsimp only [c]
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hder z hz)
          (show 0 ≤ (2:ℝ)^z.2*(1+2*Real.pi)^z.2 by positivity))
        (show 0 ≤ (1+‖t‖)^z.2 by positivity)).trans_eq (by ring)
    _ ≤ (C * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g) *
        (1+‖t‖)^(S.sup Prod.snd) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hzC (apply_nonneg _ _)
      · exact pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Finset.le_sup hz)
      · positivity
      · positivity

theorem normPowerProfile_source_control (a b : ℝ) (ha : 0 < a)
    (S : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, ∃ T : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ W : 𝓢(ℝ, ℂ), ∀ hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b,
      ∀ t : ℝ,
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
        C * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (1+‖t‖)^n := by
  obtain ⟨S₁,C₁,hC₁,h₁⟩ := schwartzCLM_finite_seminorm_control (fixedLogReturnCLM a b ha) S
  obtain ⟨n,S₂,C₂,hC₂,h₂⟩ := frequencyTwist_source_control S₁
  obtain ⟨T,C₃,hC₃,h₃⟩ := schwartzCLM_finite_seminorm_control
    (CubicReflectionKernel.logPullbackCLM a b) S₂
  refine ⟨n,T,C₁*C₂*C₃,by positivity,?_⟩
  intro W hs t
  have heq : CubicReflectionKernel.logSchwartz W a b ha hs (W.smooth ⊤) =
      CubicReflectionKernel.logPullbackCLM a b W := by
    ext u
    rw [CubicReflectionKernel.logSchwartz_apply,
      CubicReflectionKernel.logPullbackCLM_eq_actual a b ha W hs]
  have ht : (1+‖t/(2*Real.pi)‖)^n ≤ (1+‖t‖)^n := by
    gcongr
    exact CenteredMomentHeight.normalized_height_le t
  unfold normPowerProfile uniformTwistedSchwartz
  rw [heq]
  calc
    _ ≤ C₁ * S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (frequencyTwist (CubicReflectionKernel.logPullbackCLM a b W) (t/(2*Real.pi))) := h₁ _
    _ ≤ C₁ * (C₂ * (C₃ * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * (1+‖t‖)^n) := by
      apply mul_le_mul_of_nonneg_left _ hC₁.le
      exact (h₂ _ _).trans (mul_le_mul
        (mul_le_mul_of_nonneg_left (h₃ W) hC₂.le) ht (by positivity) (by positivity))
    _ = _ := by ring
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI

end Source966

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalMaskedFloor.lean; sha256: 79ff18916a44ded9608ca7a29e754cbd97896b20a40ae43a9b3f9dbc699d8f64 -/
section Source967
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentNaturalMaskedFloor
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentPlainPositiveEnergy CenteredMomentPlainGlobalEnergy
open CenteredMomentCommonMaskRadialEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentCoreFloor CenteredMomentLattice CenteredMomentTwist
open CenteredMomentAllocatedNaturalSource HeckeInverseAmplification
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

theorem excluded_pair (a b ε : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) :
    ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0<C ∧
    ∀ (W₁ W₂ : 𝓢(ℝ,ℂ)), Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
    ∀ (χ : O→Character) (r : Radial) (R : Ideal O) (Q X₁ X₂ : ℝ), R≠0 →
      0≤Q → 0<X₁ → 0<X₂ →
      (∀z,r.keep z→(χ z).residue≠1) →
      (∀z,r.keep z→((χ z).modulus.absNorm:ℝ)≤Q) →
    radialEnergy (fun z=>polynomial (excluded (χ z) R) false W₁ X₁ 0 0 *
      polynomial (excluded (χ z) R) false W₂ X₂ 0 0) r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Q^4 := by
  obtain ⟨S,C,hC,hpair⟩ := actual_radial_pair_bound a b ha
  obtain ⟨Cd,hCd,hdel⟩ := actual_radial_shared_energy (∅ : Finset (Fin 0))
    (fun _=>0) (fun _=>0) (by simp) ε hε
  refine ⟨S,Cd*C*3^8,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ χ r R Q X₁ X₂ hR hQ hX₁ hX₂ hχ hmod
  let E := C*diagonalControl r.profile*max 1 r.scale*
    ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
      (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Q^4*3^8
  have hdiag := diagonalControl_nonneg r.profile
  have hE : 0≤E := by dsimp [E]; positivity
  have hh := hdel (CompletedGauss.primeSupport R) (support_prime R) χ W₁ W₂
    X₁ X₂ a b a b (fun _=>∅) (fun _ _=>0) (fun _=>1) r.keep r.profile r.scale E
    hX₁ hX₂ hb hb hs₁ hs₂ (by simp) (by simp) (by simp) (by simp)
    r.scale_pos r.nonneg hE ?_
  · simp only [Finset.prod_empty,mul_one] at hh
    rw [primeSupport_product_radical R hR] at hh
    change radialEnergy (fun z=>polynomial (excluded (χ z) R) false W₁ X₁ 0 0 *
      polynomial (excluded (χ z) R) false W₂ X₂ 0 0) r.keep r.profile r.scale ≤ _ at hh
    exact hh.trans_eq (by dsimp [E]; ring)
  · intro D₁ hD₁ D₂ hD₂ J hJ
    have hn (D : Finset (Ideal O)) (hD : D∈(CompletedGauss.primeSupport R).powerset) :
        0<(Ideal.absNorm (∏I∈D,I):ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Finset.prod_ne_zero_iff.mpr (fun I hi=>(support_prime R I (Finset.mem_powerset.mp hD hi)).ne_zero)))
    have he := hpair W₁ W₂ hs₁ hs₂ χ r Q
      (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0
      hQ (div_pos hX₁ (hn D₁ hD₁)) (div_pos hX₂ (hn D₂ hD₂)) hχ hmod
    norm_num only [abs_zero,add_zero,show (3:ℝ)^4=81 by norm_num] at he
    simpa only [Finset.empty_sdiff,Finset.prod_empty,mul_one] using he.trans_eq (by dsimp [E]; ring)

lemma twist_polynomial (χ : Character) (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support (W:ℝ→ℂ)⊆Set.Icc a b) (t X : ℝ) :
    polynomial χ false (normPowerProfile W a b ha hs (W.smooth ⊤) t) X 0 0 =
      polynomial χ false W X 0 t := by
  have hp : (normPowerProfile W a b ha hs (W.smooth ⊤) t:ℝ→ℂ)=twistProfile W 0 t := by
    funext x
    rw [normPowerProfile_apply]
    unfold twistProfile HeckeDyadic.shift
    simp only [Complex.ofReal_zero,zero_sub,neg_neg]
    rw [mul_comm Complex.I (t:ℂ)]
    ring
  rw [hp,polynomial_twistProfile]

theorem natural_masked_floor (a b ε : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) :
    ∃ n : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0<C ∧
    ∀ (W₁ W₂ : 𝓢(ℝ,ℂ)), Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
    ∀ (η : Character) (Q R : Ideal O) (r : Radial) (bΦ : ℝ), R≠0 → 0≤bΦ →
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η Q (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z) →
    ∀ (Z m q ρ t X₁ X₂ : ℝ), 1≤Z → 0≤m → 0≤q → r.scale=Z^m →
      m+q≤ρ → 0<X₁ → 0<X₂ → (η.modulus.absNorm:ℝ)≤Z^q →
    zeroEnergy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂ X₁ X₂ r ≤
      C*(R.radical.absNorm:ℝ)^ε*bΦ^4*diagonalControl r.profile*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*(1+‖t‖)^n*Z^(m+q+4*ρ) := by
  obtain ⟨S,C,hC,hpair⟩ := excluded_pair a b ε ha hb hε
  obtain ⟨n,T,Ct,hCt,ht⟩ :=
    CenteredMomentFiniteProfileExceptional.normPowerProfile_source_control a b ha S
  let F : ℝ := fixedConductorFactor
  have hF : 0<F := by
    unfold F fixedConductorFactor
    norm_cast
    apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)))
  refine ⟨4*n,T,C*Ct^4*F^4,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ η Q R r bΦ hR hbΦ hsΦ hz hex Z m q ρ t X₁ X₂ hZ hm hq hscale hρ hX₁ hX₂ hη
  let r' : Radial := {r with keep := fun z=>r.keep z ∧ r.profile (‖eisEmbedding z‖^2/r.scale)≠0}
  let χ : O→Character := fun z=>if hz:z≠0 then (naturalRow η z hz).character else η
  have hχ (z:O) (h:r'.keep z) : (χ z).residue≠1 := by
    have hn := hz z h.1
    have hc : χ z=(naturalRow η z hn).character := by simp [χ,hn]
    exact (congrArg (fun ψ : Character=>ψ.residue≠1) hc).mpr
      ((naturalRow η z hn).nonprincipal hn Q R hR (hex z h.1))
  have hmod (z:O) (h:r'.keep z) : ((χ z).modulus.absNorm:ℝ)≤F*bΦ*Z^(m+q) := by
    have hn := hz z h.1
    have hh : ((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^m := by
      rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←hscale]
      exact (div_le_iff₀ r.scale_pos).mp (hsΦ h.2)
    simpa only [χ,dite_eq_left hn,add_comm q m] using
      (naturalRow η z hn).modulus_power_bound Z q m bΦ (zero_lt_one.trans_le hZ) hbΦ hη hh
  let V₁ := normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t
  let V₂ := normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t
  have hv₁ : Function.support (V₁:ℝ→ℂ)⊆Set.Icc a b := (normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t).trans hs₁
  have hv₂ : Function.support (V₂:ℝ→ℂ)⊆Set.Icc a b := (normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t).trans hs₂
  have he := hpair V₁ V₂ hv₁ hv₂ χ r' R (F*bΦ*Z^(m+q)) X₁ X₂ hR
    (by positivity) hX₁ hX₂ hχ hmod
  have hid : zeroEnergy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂ X₁ X₂ r =
      radialEnergy (fun z=>polynomial (excluded (χ z) R) false V₁ X₁ 0 0 *
        polynomial (excluded (χ z) R) false V₂ X₂ 0 0) r'.keep r'.profile r'.scale := by
    unfold zeroEnergy radialEnergy
    apply tsum_congr
    intro z
    by_cases hk : r.keep z
    · by_cases hp : r.profile (‖eisEmbedding z‖^2/r.scale)=0
      · simp [r',hk,hp]
      · have hn := hz z hk
        simp only [r',hk,true_and,ite_true]
        rw [zero_row_norm η (excluded (χ z) R) _ 1 z
          (by simpa only [χ,dite_eq_left hn,one_mul] using (naturalRow η z hn).masked_element R hR)
          W₁ W₂ a b ha hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤) t X₁ X₂ hX₁ hX₂]
        rw [norm_mul,twist_polynomial,twist_polynomial]
        split_ifs with h
        · rfl
        · exact False.elim (h hp)
    · simp [r',hk]
  rw [←hid] at he
  have hB₁ := ht W₁ hs₁ t
  have hB₂ := ht W₂ hs₂ t
  have hprod : (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₁ * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₂)^2 ≤
      (Ct^4*(T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+‖t‖)^(4*n) := by
    have hh := pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      (mul_le_mul hB₁ hB₂ (apply_nonneg _ _) (by positivity)) 2
    exact hh.trans_eq (by dsimp [V₁,V₂]; rw [Nat.mul_comm 4 n,pow_mul]; ring)
  have hp : Z^m*(Z^(m+q))^4≤Z^(m+q+4*ρ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans hZ),←Real.rpow_add (zero_lt_one.trans_le hZ)]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  have hd := diagonalControl_nonneg r.profile
  dsimp only [r'] at he
  rw [hscale,max_eq_right (Real.one_le_rpow hZ hm)] at he
  apply he.trans
  calc
    _ ≤ C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*Z^m*
      ((Ct^4*(T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+‖t‖)^(4*n))*(F*bΦ*Z^(m+q))^4 := by
        gcongr
    _ = (C*Ct^4*F^4*(R.radical.absNorm:ℝ)^ε*bΦ^4*diagonalControl r.profile*
      (T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2*(1+‖t‖)^(4*n))*(Z^m*(Z^(m+q))^4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

end SevenEighths.CenteredMomentNaturalMaskedFloor

end

end OAI

end Source967

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalVolume.lean; sha256: bff775dabfc5195af50c00b8d4e8ea71cab1605ef7be8c795cbb6994ce1d8934 -/
section Source968
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentLattice CenteredMomentHeckeVolume
open CenteredMomentHeckeCancellation CenteredMomentHeckeHeight
open CenteredMomentMask
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

theorem volumeControl_source_control (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ n : ℕ, ∃ S : Finset (ℕ × ℕ), (0,0) ∈ S ∧
      ∀ Q : Ideal O, ∃ C : ℝ, 0 < C ∧
      ∀ W : 𝓢(ℝ,ℂ), ∀ hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b,
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character,
      (Ideal.absNorm χ.modulus : ℝ) ≤ Z^B → ∀ t : ℝ,
      volumeControl Q χ (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * Z^ε * (1+‖t‖)^n := by
  obtain ⟨n,T,C,hC,hprofile⟩ := normPowerProfile_source_control a b ha pvSeminorms
  obtain ⟨D,hD,hdiv⟩ := polynomial_mask_divisor_bound ε B hε hB
  let S := insert (0,0) T
  refine ⟨n,S,by simp [S],?_⟩
  intro Q
  let mass : ℝ := Nat.card (O ⧸ Ideal.span {fixedPeriod Q})
  let A := D*mass*pvConstant*C
  have hmass : 0 ≤ mass := Nat.cast_nonneg _
  have hpv := pvConstant_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨1+A,by positivity,?_⟩
  intro W hs Z hZ χ hnorm t
  have hTS : T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro z hz
    exact Seminorm.le_finset_sup_apply (Finset.mem_insert_of_mem hz)
  have hp := (hprofile W hs t).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTS hC.le) (by positivity))
  have herr : volumeControl Q χ (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
      (D*Z^ε)*(mass*(pvConstant*(C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(1+‖t‖)^n))) := by
    unfold volumeControl pvControl
    rw [mul_assoc]
    apply mul_le_mul (hdiv Z hZ χ.modulus χ.modulus_ne_bot hnorm)
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp pvConstant_pos.le) hmass)
    · exact mul_nonneg hmass (mul_nonneg hpv.le (apply_nonneg _ _))
    · exact mul_nonneg hD.le (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  calc
    _ ≤ _ := herr
    _ = A*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by dsimp [A]; ring
    _ ≤ (1+A)*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by
      gcongr
      linarith

theorem retained_volumeControl_source_control (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ n : ℕ, ∃ S : Finset (ℕ × ℕ), (0,0) ∈ S ∧
      ∀ Q : Ideal O, ∃ C : ℝ, 0 < C ∧
      ∀ W : 𝓢(ℝ,ℂ), ∀ hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b,
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character,
      (Ideal.absNorm χ.modulus : ℝ) ≤ Z^B →
      ∀ X : ℝ, ∀ hX : 0<X, ∀ hret : 1≤X*b, ∀ t : ℝ,
      volumeControl Q χ (CenteredMomentRetainedProfile.retainedProfile
        W a b ha hs (W.smooth ⊤) X hX hret t) ≤
        C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by
  obtain ⟨n,S,hS,hbound⟩ := volumeControl_source_control a b ε B ha hε hB
  refine ⟨n,S,hS,?_⟩
  intro Q
  obtain ⟨C,hC,hCbound⟩ := hbound Q
  refine ⟨(max 1 b)^(pvSeminorms.sup Prod.snd)*C,by positivity,?_⟩
  intro W hs Z hZ χ hχ X hX hret t
  exact (CenteredMomentRetainedProfile.retained_volumeControl_le
    Q χ W a b ha hs (W.smooth ⊤) X hX hret t).trans
    ((mul_le_mul_of_nonneg_left (hCbound W hs Z hZ χ hχ t) (by positivity)).trans_eq (by ring))
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI

end Source968

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalUnit.lean; sha256: 41425d0ccfd3908ca74318e20940dbf413fc739e8b00e0282f07c39c4a9f7b6e -/
section Source969
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeTwist
open CenteredMomentHeckeCancellation CenteredMomentLattice
local notation "O" => HeckeFamily.O

theorem rectangle_source_unit (a b ε B : ℝ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, Q≠0 → ∃ C : ℝ, 0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁≤1 →
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂≤1 →
      ∀ Z : ℝ, 1≤Z → ∀ η χ ψ : Character,
      (Ideal.absNorm χ.modulus:ℝ)≤Z^B → Q≤ψ.modulus →
      CenteredExceptionalProfile.InducedBy χ ψ →
      ∀ m A z : O, ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀ n,elementCoeff χ n=CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η) m 1 (A*z) n) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0<L →
      L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂-
        twistedIdealSum χ W₁ t Y₁*twistedIdealSum χ W₂ t Y₂)‖ ≤
        C*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,S,hS,hvol⟩ := volumeControl_source_control a b ε B ha hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨D,hD,hDvol⟩ := hvol Q
  let V := 128*(b+b)
  have hV : 0≤V := by dsimp [V]; positivity
  refine ⟨1+8*D*V,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ hS₁ hS₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hbound₁ (y:ℝ) : ‖W₁ y‖≤1 :=
    (SchwartzMap.norm_le_seminorm ℝ W₁ y).trans
      ((Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hS).trans hS₁)
  have hbound₂ (y:ℝ) : ‖W₂ y‖≤1 :=
    (SchwartzMap.norm_le_seminorm ℝ W₂ y).trans
      ((Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hS).trans hS₂)
  have herr (W:𝓢(ℝ,ℂ)) (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
      (hS':S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W≤1) :
      volumeControl Q χ (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
        D*Z^ε*(1+‖t‖)^J := by
    apply (hDvol W hs Z hZ χ hnorm t).trans
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hS' hD.le) (Real.rpow_nonneg (by linarith) _))
        (show 0≤(1+‖t‖)^J by positivity)
  have hraw := actual_twisted_rectangle_saving η χ ψ Q hQ hQψ hind m A z hml hm2 hrow
    W₁ W₂ a b a b 1 1 ha ha hb hb zero_le_one zero_le_one hs₁ hs₂
    (W₁.smooth ⊤) (W₂.smooth ⊤) hbound₁ hbound₂
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0<T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hn := CenteredMoment.normalized_centered_saving _ T L V _ hT (by
    simpa only [mul_one] using hraw)
  have hE := add_le_add (herr W₁ hs₁ hS₁) (herr W₂ hs₂ hS₂)
  have hr : 0≤Real.sqrt T/L := div_nonneg (Real.sqrt_nonneg _) hL.le
  calc
    _ ≤ _ := hn
    _ ≤ 4*(D*Z^ε*(1+‖t‖)^J+D*Z^ε*(1+‖t‖)^J)*V*(Real.sqrt T/L) := by
      gcongr
    _ = (8*D*V)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by ring
    _ ≤ (1+8*D*V)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
      gcongr
      linarith
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI

end Source969

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalNormalize.lean; sha256: 3a9731f3d3f6c45f6198f74599d3a5c09bfc751d40c1d306473b777fa68ff05a -/
section Source970
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeTwist

def sourceControl (S : Finset (ℕ×ℕ)) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W

def normalizedProfile (S : Finset (ℕ×ℕ)) (W : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  (sourceControl S W)⁻¹ • W

theorem sourceControl_nonneg (S) (W : 𝓢(ℝ,ℂ)) : 0≤sourceControl S W := apply_nonneg _ _

theorem sourceControl_zero (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    (W : 𝓢(ℝ,ℂ)) (hW : sourceControl S W=0) : W=0 := by
  ext x
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  exact (SchwartzMap.norm_le_seminorm ℝ W x).trans
    ((Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hS).trans_eq hW)

theorem normalizedProfile_control (S) (W : 𝓢(ℝ,ℂ)) :
    sourceControl S (normalizedProfile S W)≤1 := by
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((sourceControl S W)⁻¹ • W)≤1
  rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr (sourceControl_nonneg S W))]
  change (sourceControl S W)⁻¹*sourceControl S W≤1
  by_cases h : sourceControl S W=0
  · simp [h]
  · rw [inv_mul_cancel₀ h]

theorem normalizedProfile_support (S) (W : 𝓢(ℝ,ℂ)) :
    Function.support (normalizedProfile S W:ℝ→ℂ)⊆Function.support (W:ℝ→ℂ) := by
  intro x hx hw
  apply hx
  simp [normalizedProfile,smul_apply,hw]

theorem normalizedProfile_reconstruct (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    (W : 𝓢(ℝ,ℂ)) : sourceControl S W • normalizedProfile S W=W := by
  by_cases h : sourceControl S W=0
  · rw [sourceControl_zero S hS W h]
    simp [sourceControl,normalizedProfile]
  · simp [normalizedProfile,smul_smul,h]

theorem twistedIdealSum_profile_smul (χ : Character) (W : 𝓢(ℝ,ℂ))
    (c t X : ℝ) : twistedIdealSum χ (c • W : 𝓢(ℝ,ℂ)) t X = (c:ℂ)*twistedIdealSum χ W t X := by
  unfold twistedIdealSum
  rw [←tsum_mul_left]
  apply tsum_congr
  intro I
  change _ * ((c:ℂ) * W _) = (c:ℂ) * (_ * W _)
  ring

theorem twistedIdealSum_normalized (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    (χ : Character) (W : 𝓢(ℝ,ℂ)) (t X : ℝ) :
    twistedIdealSum χ W t X = (sourceControl S W:ℂ)*
      twistedIdealSum χ (normalizedProfile S W) t X := by
  rw [←twistedIdealSum_profile_smul,normalizedProfile_reconstruct S hS W]
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI

end Source970

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalRectangle.lean; sha256: da99e36a0e263e9d6d2dbbc04896ab22ecebf80afd722bb157d2a5e3bf98f45d -/
section Source971
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeTwist
open CenteredMomentHeckeCancellation CenteredMomentLattice
local notation "O" => HeckeFamily.O

theorem rectangle_source_control (a b ε B : ℝ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, Q≠0 → ∃ C : ℝ, 0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀ Z : ℝ, 1≤Z → ∀ η χ ψ : Character,
      (Ideal.absNorm χ.modulus:ℝ)≤Z^B → Q≤ψ.modulus →
      CenteredExceptionalProfile.InducedBy χ ψ →
      ∀ m A z : O, ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀ n,elementCoeff χ n=CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η) m 1 (A*z) n) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0<L →
      L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂-
        twistedIdealSum χ W₁ t Y₁*twistedIdealSum χ W₂ t Y₂)‖ ≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,S,hS,hunit⟩ := rectangle_source_unit a b ε B ha hb hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩ := hunit Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have h := hbound (normalizedProfile S W₁) (normalizedProfile S W₂)
    ((normalizedProfile_support S W₁).trans hs₁)
    ((normalizedProfile_support S W₂).trans hs₂)
    (normalizedProfile_control S W₁) (normalizedProfile_control S W₂)
    Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have heq : (Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂-
      twistedIdealSum χ W₁ t Y₁*twistedIdealSum χ W₂ t Y₂) =
      ((sourceControl S W₁*sourceControl S W₂:ℝ):ℂ)*
      ((Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ (normalizedProfile S W₁) t X₁*
        twistedIdealSum χ (normalizedProfile S W₂) t X₂-
        twistedIdealSum χ (normalizedProfile S W₁) t Y₁*
        twistedIdealSum χ (normalizedProfile S W₂) t Y₂)) := by
    rw [twistedIdealSum_normalized S hS χ W₁ t X₁,
      twistedIdealSum_normalized S hS χ W₂ t X₂,
      twistedIdealSum_normalized S hS χ W₁ t Y₁,
      twistedIdealSum_normalized S hS χ W₂ t Y₂]
    push_cast
    ring
  rw [heq,norm_mul,Complex.norm_real,Real.norm_of_nonneg
    (mul_nonneg (sourceControl_nonneg S W₁) (sourceControl_nonneg S W₂))]
  exact (mul_le_mul_of_nonneg_left h
    (mul_nonneg (sourceControl_nonneg S W₁) (sourceControl_nonneg S W₂))).trans_eq (by ring)
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI

end Source971

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalRow.lean; sha256: de1d3e122da1cc136d8bd2cd94976cc575530d2ffd8b9f7149e220535a1b979e -/
section Source972
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeVolume
open CenteredMomentHeckeTwist CenteredMomentExceptionalCappedAmplitude
local notation "O" => HeckeFamily.O
theorem row_rectangle_source_control
    (a b ε B : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, Q≠0 → ∃ C : ℝ, 0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀ Z : ℝ, 1≤Z → ∀ (η : Character) (m A₀ z : O),
      m ≠ 0 → A₀ ≠ 0 → z ≠ 0 →
      (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A₀*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A₀ z →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹ *
        (rowTwistedSum η m A₀ z W₁ t X₁*rowTwistedSum η m A₀ z W₂ t X₂-
         rowTwistedSum η m A₀ z W₁ t Y₁*rowTwistedSum η m A₀ z W₂ t Y₂)‖ ≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,S,hS,hJ⟩ := rectangle_source_control a b ε B ha hb hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩ := hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η m A₀ z hm hA hz hmLam hm2 hcond hex t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  obtain ⟨χ,ψ,hχ,hprim,hind,hQψ,hrow⟩ := fixedInducingRow_controlled η Q m A₀ z hm hA hz hmLam hm2 hex
  have hχnorm : (Ideal.absNorm χ.modulus:ℝ) ≤ Z^B :=
    (show (Ideal.absNorm χ.modulus:ℝ) ≤ HeckeRowClosure.rowConductorBound η m 1 (A₀*z) by exact_mod_cast hχ).trans hcond
  simp_rw [rowTwistedSum_eq η χ m A₀ z hrow]
  exact hbound W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hχnorm hQψ hind m A₀ z hmLam hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI

end Source972

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalCapped.lean; sha256: 5f64d16980c72f5ae9fb62e4b5c8da1cb8cf0c9fa6d236000fc2868bf4d85930 -/
section Source973
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeVolume
open CenteredMomentHeckeTwist CenteredMomentExceptionalCappedAmplitude
local notation "O" => HeckeFamily.O
theorem capped_rectangle_source_control
    (a b ε B : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, Q≠0 → ∃ C : ℝ, 0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀ Z : ℝ, 1≤Z → ∀ (η : Character) (m A₀ z : O),
      m ≠ 0 → A₀ ≠ 0 → z ≠ 0 →
      (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A₀*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A₀ z →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹ *
        (rowTwistedSum η m A₀ z W₁ t X₁*rowTwistedSum η m A₀ z W₂ t X₂-
         rowTwistedSum η m A₀ z W₁ t Y₁*rowTwistedSum η m A₀ z W₂ t Y₂)‖ ≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/max 1 L) := by
  obtain ⟨J,S,hS,hJ⟩ := row_rectangle_source_control a b ε B ha hb hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hcancel⟩ := hJ Q hQ
  let D : ℝ := 2*(128*b)*(128*b)
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨C+D,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η m A z hm hA hz hml hm2 hcond hex
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let P₁ := sourceControl S W₁
  let P₂ := sourceControl S W₂
  have hP₁ : 0≤P₁ := sourceControl_nonneg S W₁
  have hP₂ : 0≤P₂ := sourceControl_nonneg S W₂
  have hw₁ (x:ℝ) : ‖W₁ x‖≤P₁ :=
    (SchwartzMap.norm_le_seminorm ℝ W₁ x).trans
      (Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ)
        (s := S) (x := W₁) (i := (0, 0)) hS)
  have hw₂ (x:ℝ) : ‖W₂ x‖≤P₂ :=
    (SchwartzMap.norm_le_seminorm ℝ W₂ x).trans
      (Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ)
        (s := S) (x := W₂) (i := (0, 0)) hS)
  by_cases hlarge : 1≤L
  · rw [max_eq_right hlarge]
    apply (hcancel W₁ W₂ hs₁ hs₂ Z hZ η m A z hm hA hz hml hm2 hcond hex
      t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY).trans
    gcongr
    exact le_add_of_nonneg_right hD
  · rw [max_eq_left (le_of_not_ge hlarge),div_one]
    have habs := normalized_rectangle_absolute η m A z W₁ W₂ b b P₁ P₂ hb hb hP₁ hP₂
      (fun _ hx=>(hs₁ hx).2) (fun _ hx=>(hs₂ hx).2) hw₁ hw₂
      t X₁ X₂ Y₁ Y₂ T (hL.trans_le hX₁) (hL.trans_le hX₂)
      (hL.trans_le hY₁) (hL.trans_le hY₂) hpX hpY
    have hc : D ≤ (C+D)*Z^ε*(1+‖t‖)^J := by
      calc
        _ ≤ C+D := le_add_of_nonneg_left hC.le
        _ ≤ (C+D)*Z^ε := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hZ hε.le)
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith [norm_nonneg t]))
    apply habs.trans
    calc
      _ = D*(P₁*P₂)*Real.sqrt T := by dsimp [D]; ring
      _ ≤ ((C+D)*Z^ε*(1+‖t‖)^J)*(P₁*P₂)*Real.sqrt T := by
        gcongr
      _ = _ := by dsimp [P₁,P₂]; ring
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI

end Source973

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalSlots.lean; sha256: ef07318e7392d531abae46181c92e78847d5cdbb6e3d796bcc3e3ceadc17a935 -/
section Source974
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
theorem capped_slots_source_control
    (a b ε B : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ, ∃ R : Finset (ℕ×ℕ), (0,0)∈R ∧
      ∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧
      ∀W₁ W₂ : 𝓢(ℝ,ℂ), Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀(ι : Type*) [Fintype ι],∀Z : ℝ,1≤Z →
      ∀(η : Character)(m A z : O),m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀(S : ι→Finset (Ideal O))(β : ι→Ideal O→ℂ)(P b M : ι→ℝ),
      (∀i,0<P i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀I∈S i,‖β i I‖≤M i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀t X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖≤
        C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖t‖)^J*(∏i,128*b i*M i)*(Real.sqrt (T*∏i,P i)/max 1 L) := by
  obtain ⟨J,R,hR,hJ⟩ := capped_rectangle_source_control a b ε B ha hb hε hB
  refine ⟨J,R,hR,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩ := hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ ι _ Z hZ η m A z hm hA hz hml hm2 hc he S β P b M hP hb hM hβ hN
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hR₁ := sourceControl_nonneg R W₁
  have hR₂ := sourceControl_nonneg R W₂
  have hT : 0<T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) t‖≤(128*b i*M i)*P i := by
    convert rowSlot_bound η m A z (S i) (β i) t (b i*P i) (M i)
      (mul_nonneg (hb i) (hP i).le) (hM i) (hβ i) (hN i) using 1; ring
  exact whole_product_normalization _ (fun i=>rowSlot η m A z (S i) (β i) t)
    (fun i=>128*b i*M i) P (C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖t‖)^J) T (max 1 L) (by positivity) hT
    (zero_lt_one.trans_le (le_max_left _ _))
    (fun i=>mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hP hslots
    (hbound W₁ W₂ hs₁ hs₂ Z hZ η m A z hm hA hz hml hm2 hc he t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI

end Source974

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalAllocated.lean; sha256: c29d81c3503369b9f699bee1141d127c966276e455d7b01c9c8a0a3fb3845a1e -/
section Source975
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorRectangle CenteredMomentAllocatedCenteredCapped
open ConcretePrimeRowBridge CenteredMomentExceptionalCappedAmplitude
local notation "O" => HeckeFamily.O
theorem allocated_source_control (lo hi ε B:ℝ) (hlo:0<lo) (hhi:0≤hi) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∃R:Finset (ℕ×ℕ),(0,0)∈R ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀W₁ W₂:𝓢(ℝ,ℂ), Function.support (W₁:ℝ→ℂ)⊆Set.Icc lo hi →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc lo hi →
      ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀Z:ℝ,1<Z → ∀η:Character,∀m A z:O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀(S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b M:ι→ℝ),
      (∀i,1≤P i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀I∈S i,‖β i I‖≤M i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀(L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2))),
      ∀h X₁ X₂ Y₁ Y₂ T r:ℝ,Z^r≤X₁ → Z^r≤X₂ → Z^r≤Y₁ → Z^r≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖residualCenteredRow η m A z h S β P L a
        W₁ W₂ X₁ X₂ Y₁ Y₂ T‖≤
      C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖h‖)^J*(∏i:liveIndices L a,128*b i*M i)*
        (Real.sqrt ((T*∏i,P i)/formalReductionFactor L a P)/
          Z^(max (r-Real.logb Z (formalReductionFactor L a P)) 0)):=by
  obtain ⟨J,R,hR,hJ⟩:=capped_slots_source_control lo hi ε B hlo hhi hε hB
  refine ⟨J,R,hR,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ ι _ _ Z hZ η m A z hm hA hz hmLam hm2 hcond hex S β P b M hP hb hM hβ hN
    L a h X₁ X₂ Y₁ Y₂ T r hX₁ hX₂ hY₁ hY₂ hXT hYT
  have hp (i:ι):0<P i:=zero_lt_one.trans_le (hP i)
  have hred:0<formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=>hp i))
  have hh:=hbound W₁ W₂ hs₁ hs₂ (liveIndices L a) Z hZ.le η m A z hm hA hz hmLam hm2 hcond hex
    (fun i=>S i) (fun i=>β i) (fun i=>P i) (fun i=>b i) (fun i=>M i)
    (fun i=>hp i) (fun i=>hb i) (fun i=>hM i) (fun i=>hβ i) (fun i=>hN i)
    h
    (X₁/Ideal.absNorm (selectedPlain L a 0)) (X₂/Ideal.absNorm (selectedPlain L a 1))
    (Y₁/Ideal.absNorm (selectedPlain L a 0)) (Y₂/Ideal.absNorm (selectedPlain L a 1))
    (T/selectedNorm L a) (Z^r/formalReductionFactor L a P)
    (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hred)
    (allocated_lower L a P hP Z r X₁ (zero_lt_one.trans hZ) hX₁ 0)
    (allocated_lower L a P hP Z r X₂ (zero_lt_one.trans hZ) hX₂ 1)
    (allocated_lower L a P hP Z r Y₁ (zero_lt_one.trans hZ) hY₁ 0)
    (allocated_lower L a P hP Z r Y₂ (zero_lt_one.trans hZ) hY₂ 1)
    (by rw [div_mul_div_comm,hXT];rfl) (by rw [div_mul_div_comm,hYT];rfl)
  rw [remaining_volume L a P hp T,max_raw_reduction Z _ r hZ hred] at hh
  exact hh

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI

end Source975

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalAmplitude.lean; sha256: b4044325b0dc4fc04c56d358464cfd5c0ed045a355aa7ab4a548b250f710e48e -/
section Source976
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRawEnergy CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction
open CenteredMomentAllocatedDetectorAmplitude ConcretePrimeRowBridge CenteredMomentDivisorRows
local notation "O" => HeckeFamily.O
theorem allocated_amplitude_source_control (lo hi ε B:ℝ) (hlo:0<lo) (hhi:0≤hi) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∃R:Finset (ℕ×ℕ),(0,0)∈R ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀W₁ W₂:𝓢(ℝ,ℂ), Function.support (W₁:ℝ→ℂ)⊆Set.Icc lo hi →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc lo hi →
      ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀(s:Data ι)(Z:ℝ),1<Z → (∀i,1≤s.P i) →
      ∀z:O,s.m≠0 → s.A≠0 → z≠0 → goodLambda∣s.m → (2:O)∣s.m →
      (HeckeRowClosure.rowConductorBound s.η s.m 1 (s.A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow s.η Q s.m s.A z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))),
      ∀r:ℝ,s.W₁=W₁ → s.W₂=W₂ →
      Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ‖amplitude s D a z‖^2≤
        (C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖s.t‖)^J*slotControl s)^2*
          (s.X₁*s.X₂*∏i,s.P i)/
          ((formalReductionFactor D a s.P)^2*(Z^(max (r-Real.logb Z (formalReductionFactor D a s.P)) 0))^2):=by
  obtain ⟨J,R,hR,hJ⟩:=allocated_source_control lo hi ε B hlo hhi hε hB
  refine ⟨J,R,hR,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hcap⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ ι _ _ s Z hZ hP z hm hA hz hml hm2 hcond hex D a r hW₁ hW₂ hX₁ hX₂ hY₁ hY₂
  have hb:=hcap W₁ W₂ hs₁ hs₂ ι Z hZ s.η s.m s.A z hm hA hz hml hm2 hcond hex s.slots s.coefficient s.P
    (fun i=>max 0 (s.hi i)) s.M hP (fun i=>le_max_left _ _) (fun i=>zero_le_one.trans (s.M_ge_one i))
    s.coefficient_bound (fun i I _ hi=>coefficient_support s i I hi) D a
    s.t s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) r
    hX₁ hX₂ hY₁ hY₂ rfl s.same_product
  rw [←hW₁,←hW₂] at hb
  have ha:=allocated_raw_energy s.η s.m s.A z s.t s.slots s.prime s.coefficient s.M s.P
    (fun i=>zero_le_one.trans (s.M_ge_one i)) s.P_pos s.coefficient_bound D a s.W₁ s.W₂
    s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos (mul_pos s.X₁_pos s.X₂_pos)
  have hred:=s.reduction_pos D a
  have hraw:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  let V:=s.X₁*s.X₂*∏i,s.P i
  let d:=formalReductionFactor D a s.P
  let H:=C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖s.t‖)^J
  let F:=∏i∈frozenIndices D a,s.M i
  let L:=∏i:liveIndices D a,128*max 0 (s.hi i)*s.M i
  let M:=Z^(max (r-Real.logb Z d) 0)
  have hR₁:=sourceControl_nonneg R W₁
  have hR₂:=sourceControl_nonneg R W₂
  have hH:0≤H:=by dsimp [H]; positivity
  have hM:0<M:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hFL:0≤F*L:=mul_nonneg
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))
    (Finset.prod_nonneg (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (le_max_left _ _)) (zero_le_one.trans (s.M_ge_one i))))
  have hp:F*L≤slotControl s:=slot_product_bound s D a
  calc
    ‖amplitude s D a z‖^2≤F^2/d*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
        s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2:=ha
    _≤F^2/d*(H*L*(Real.sqrt (V/d)/M))^2:=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (div_nonneg (sq_nonneg _) hred.le)
    _=(H*(F*L))^2*V/(d^2*M^2):=by
      rw [mul_pow,mul_pow,div_pow,Real.sq_sqrt (div_nonneg hraw.le hred.le)]
      dsimp only [V,d]
      field_simp [hred.ne']
    _≤(H*slotControl s)^2*V/(d^2*M^2):=by
      apply div_le_div_of_nonneg_right _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      apply mul_le_mul_of_nonneg_right _ hraw.le
      exact pow_le_pow_left₀ (mul_nonneg hH hFL) (mul_le_mul_of_nonneg_left hp hH) 2
    _=_:=rfl

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI

end Source976

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalPair.lean; sha256: 956ff7daf1e9da732bfce2b6ada80f6b4edadf40b51858dd9ee3f011d11690d1 -/
section Source977
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u
structure Profiles (lo hi:ℝ) where
  profile : Fin 2→𝓢(ℝ,ℂ)
  support : ∀i,Function.support (profile i:ℝ→ℂ)⊆Set.Icc lo hi

def Profiles.control {lo hi:ℝ} (p:Profiles lo hi) (R:Finset (ℕ×ℕ)) : ℝ :=
  sourceControl R (p.profile 0)*sourceControl R (p.profile 1)

lemma Profiles.control_nonneg {lo hi:ℝ} (p:Profiles lo hi) (R:Finset (ℕ×ℕ)) : 0≤p.control R :=
  mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

variable {lo hi:ℝ}
def ProfileAdmissible {ι:Type u} [Fintype ι] (s:Data ι) (p:Profiles lo hi)
    (Q:Ideal O) (Z B r:ℝ) (z:O):Prop:=
  (∀i,1≤s.P i) ∧ s.m≠0 ∧ s.A≠0 ∧ z≠0 ∧ goodLambda∣s.m ∧ (2:O)∣s.m ∧
  (HeckeRowClosure.rowConductorBound s.η s.m 1 (s.A*z):ℝ)≤Z^B ∧
  CenteredExceptionalProfile.FixedInducingRow s.η Q s.m s.A z ∧
  s.W₁=p.profile 0 ∧ s.W₂=p.profile 1 ∧
  Z^r≤s.X₁ ∧ Z^r≤s.X₂ ∧ Z^r≤s.Y₁ ∧ Z^r≤s.Y₂

theorem paired_amplitude_source_control (lo hi ε B:ℝ) (hlo:0<lo) (hhi:0≤hi) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∃R:Finset (ℕ×ℕ),(0,0)∈R ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(ι κ:Type u) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ],
      ∀(s:Data ι)(v:Data κ)(p q:Profiles lo hi)(Z r:ℝ),1<Z → ∀z:O,
      ProfileAdmissible s p Q Z B r z → ProfileAdmissible v q Q Z B r z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*p.control R*q.control R*Z^(2*ε)*(1+‖s.t‖)^J*(1+‖v.t‖)^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z r:=by
  obtain ⟨J,R,hR,hJ⟩:=allocated_amplitude_source_control lo hi ε B hlo hhi hε hB
  refine ⟨J,R,hR,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι κ _ _ _ _ s v p q Z r hZ z hs hv D a b
  have hpoint (α:Type u) [Fintype α] [DecidableEq α] (s:Data α)(p:Profiles lo hi)
      (hs:ProfileAdmissible s p Q Z B r z)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))):
      ‖amplitude s D a z‖≤C*p.control R*Z^ε*(1+‖s.t‖)^J*slotControl s*Real.sqrt (volume s)/
        (formalReductionFactor D a s.P*Z^(max (r-Real.logb Z (formalReductionFactor D a s.P)) 0)):=by
    have hpc := Profiles.control_nonneg p R
    obtain ⟨hP,hm,hA,hz,hml,hm2,hcond,hex,hW₁,hW₂,hX₁,hX₂,hY₁,hY₂⟩:=hs
    apply norm_le_of_squared _ _ _ _ _
    · exact mul_nonneg (by positivity) (slotControl_nonneg s)
    · exact (volume_pos s).le
    · exact s.reduction_pos D a
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact hbound (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
        α s Z hZ hP z hm hA hz hml hm2 hcond hex D a r hW₁ hW₂ hX₁ hX₂ hY₁ hY₂

  have hpc := Profiles.control_nonneg p R
  have hqc := Profiles.control_nonneg q R
  have hl:=hpoint ι s p hs a
  have hr:=hpoint κ v q hv b
  have hcap:1≤Z^(max (r-Real.logb Z (formalReductionFactor D b v.P)) 0):=
    Real.one_le_rpow hZ.le (le_max_right _ _)
  have hr':‖amplitude v D b z‖≤
      C*q.control R*Z^ε*(1+‖v.t‖)^J*slotControl v*Real.sqrt (volume v)/formalReductionFactor D b v.P:=by
    apply hr.trans
    apply div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (by positivity) (slotControl_nonneg v)) (Real.sqrt_nonneg _))
      (v.reduction_pos D b)
    exact le_mul_of_one_le_right (v.reduction_pos D b).le hcap
  apply (mul_le_mul hl hr' (norm_nonneg _) (by
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (slotControl_nonneg s)) (Real.sqrt_nonneg _)) (mul_nonneg (s.reduction_pos D a).le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))).trans_eq
  rw [←reduction_cap_identity s v D a b Z r hZ]
  have hp:Z^(2*ε)=(Z^ε)^2:=by rw [mul_comm (2:ℝ) ε,Real.rpow_mul (zero_lt_one.trans hZ).le,Real.rpow_two]
  rw [hp]
  ring

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI

end Source977

/- Original source: OAI/NumberTheory/DirichletL/Energy/State.lean; sha256: d3b480d46e850bb45422841816c644c9417b8d0f6cc651dabf3da89f1e0f5923 -/
section Source978
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyState
open HeckeFamily CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
open CenteredMomentFiniteProfileExceptional
open CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O"=>HeckeFamily.O

structure NaturalState (Z Bmask bΦ:ℝ) where
  character : Character
  fixedModulus : Ideal O
  puncture : Ideal O
  radial : Radial
  rowWidth : ℝ
  characterWidth : ℝ
  base_ge_one : 1≤Z
  row_nonneg : 0≤rowWidth
  character_nonneg : 0≤characterWidth
  scale_eq : radial.scale=Z^rowWidth
  modulus_bound : (character.modulus.absNorm:ℝ)≤Z^characterWidth
  puncture_ne_zero : puncture≠0
  puncture_bound : (puncture.absNorm:ℝ)≤Z^Bmask
  radial_support : Function.support (radial.profile:ℝ→ℂ)⊆Set.Iic bΦ
  row_ne_zero : ∀z,radial.keep z→z≠0
  nonexceptional : ∀z,radial.keep z→
    ¬FixedInducingRow character fixedModulus
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator puncture) 1 z

namespace NaturalState
variable {Z Bmask bΦ:ℝ}
def width (s:NaturalState Z Bmask bΦ):ℝ := s.rowWidth+s.characterWidth
lemma width_nonneg (s:NaturalState Z Bmask bΦ):0≤s.width :=
  add_nonneg s.row_nonneg s.character_nonneg

def mask (s:NaturalState Z Bmask bΦ):O :=
  fixedBadMask*ConcretePrimeRowBridge.idealGenerator s.puncture

def plainEnergy (s:NaturalState Z Bmask bΦ) {a b:ℝ} (p:Profiles a b)
    (t X₁ X₂:ℝ):ℝ :=
  energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
    (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
    X₁ X₂ s.radial.keep s.radial.profile s.radial.scale

lemma plainEnergy_eq_zero (s:NaturalState Z Bmask bΦ) {a b:ℝ} (p:Profiles a b)
    (t X₁ X₂:ℝ):
    s.plainEnergy p t X₁ X₂=CenteredMomentCoreFloor.zeroEnergy s.character s.mask 1 t
      (p.profile 0) (p.profile 1) X₁ X₂ s.radial :=
  (CenteredMomentCoreFloor.zero_energy_eq _ _ _ _ _ _ _ _ _).symm

lemma radical_bound (s:NaturalState Z Bmask bΦ):
    (s.puncture.radical.absNorm:ℝ)≤Z^Bmask :=by
  apply le_trans _ s.puncture_bound
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.puncture_ne_zero))
    (map_dvd Ideal.absNorm (Ideal.dvd_iff_le.mpr (Ideal.le_radical (I:=s.puncture))))
end NaturalState

def ZeroBound (Q:Ideal O) (a b bΦ Bmask M ε:ℝ)(degree:ℕ)(S:Finset (ℕ×ℕ))(C Z₀:ℝ):Prop :=
  ∀Z:ℝ,Z₀≤Z→∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤M→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,0<X₁→0<X₂→
    s.plainEnergy p t X₁ X₂≤
      C*diagonalControl s.radial.profile*(p.control S)^2*(1+‖t‖)^degree*
        Z^(s.width+ε)

end SevenEighths.CenteredMomentEnergyState

end

end OAI

end Source978

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstSectorLocalization.lean; sha256: a916b81173bd4adfc360250cd735bc841545ed7e213781ba678afcabbc652293 -/
section Source979
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstSectorLocalization
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentFirstTailAggregate
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion CenteredMomentFirstEnergy
local notation "O" => ActualEisensteinCubic.O

open CenteredMomentFirstLocalization

def retainedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalRetainedTerm I J hI hJ E W K
    (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ

def discardedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalDiscardedTerm I J hI hJ E W K
    (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ

theorem reducedFirstSum_sector_split (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) (hK : 0<K) :
    reducedFirstSum I J hI hJ W K=canonicalZeroPair I J hI hJ W K+
      retainedPair I J hI hJ W K X Z ξ+discardedPair I J hI hJ W K X Z ξ := by
  unfold reducedFirstSum canonicalZeroPair retainedPair discardedPair
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  let Tsec:=firstNominalScale I J (∏ P∈E,P.val) K X
  dsimp only [canonicalZeroTerm,canonicalRetainedTerm,canonicalDiscardedTerm]
  simp_rw [← normValue_eq_embedding]
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  have ha : a≠0 := supported_element_ne_zero _ (residualGenerator_supported I J hI)
  have hb : b≠0 := supported_element_ne_zero _ (residualGenerator_supported J I hJ)
  have hr : r≠0 := finitePrimeModulus_ne_zero _
  have he : primeSubsetGenerator (fun P : CommonIndex I J => P.val) E≠0 := primeSubsetGenerator_ne_zero _ _
  have hk : 0<(K/normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E))/normValue (a*(b*r)) :=
    div_pos (div_pos hK (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr he)))
      (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha (mul_ne_zero hb hr))))
  have hh := lattice_fourier_split W _ hk
    (tripleFourier a b r ha hb hr (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))
    (normValue (a*(b*r)))
    (tripleFourier_norm_le_full a b r ha hb hr _ _ _ (activeFunction_norm_le_one I J hI))
    (frequencyRadius Tsec Z ξ)
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let k := (K/normValue e)/normValue (a*(b*r))
  let F := tripleFourier a b r ha hb hr (residualCharacter I J hI)
    (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
  let d := (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e
  change d*((k:ℂ)*∑' h : O,F h*paperRadialFourier W ((K/normValue e)*normValue h/normValue (a*(b*r))))=
    d*((k:ℂ)*(F 0*paperRadialFourier W 0))+
      d*((k:ℂ)*∑' h : O,(retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))+
      d*((k:ℂ)*∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))
  have heq (h : O) : (K/normValue e)*normValue h/normValue (a*(b*r))=k*normValue h := by dsimp [k];ring
  simp_rw [heq]
  rw [hh]
  ring

def retainedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      retainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K X Z ξ

def discardedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      discardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K X Z ξ

theorem finiteHeckeEnergy_sector_localized (η : Character) (m A : O) (t : ℝ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ))
    (K X Z ξ : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K=
      zeroEnergy η m A t S c W K+retainedEnergy η m A t S c W K X Z ξ+
        discardedEnergy η m A t S c W K X Z ξ := by
  rw [finiteHeckeEnergy_reduced_poisson η m A t hmLam hm2 S c W K hK]
  simp_rw [reducedFirstSum_sector_split _ _ _ _ W K X Z ξ hK,mul_add,Finset.sum_add_distrib]
  rfl

end SevenEighths.CenteredMomentFirstSectorLocalization

end

end OAI

end Source979

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstCommonTransport.lean; sha256: 09f1238b1a21bab81f6f2047013d7c220ba8f0109f5f671f2a13b65962ad1eda -/
section Source980
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstCommonTransport
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentFirstSectorEnergy CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

theorem extracted_support (I J:Ideal O):
    commonSupport (commonPart I J) (commonPart J I)=commonSupport I J:=by
  rw [commonSupport,commonPart_support,commonPart_support,commonSupport_comm J I,Finset.inter_self]

def commonEquiv (I J:Ideal O):CommonIndex I J ≃ CommonIndex (commonPart I J) (commonPart J I) where
  toFun P:=⟨P.val,by rw [extracted_support];exact P.property⟩
  invFun P:=⟨P.val,by rw [←extracted_support I J];exact P.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

@[simp] theorem commonEquiv_val (I J:Ideal O)(P:CommonIndex I J):
    (commonEquiv I J P).val=P.val:=rfl

@[simp] theorem extracted_left (I J:Ideal O)(P:CommonIndex I J):
    leftExponent (commonPart I J) (commonPart J I) (commonEquiv I J P)=leftExponent I J P:=by
  simp only [leftExponent,commonEquiv_val,commonPart_valuation,ite_eq_left P.property]

@[simp] theorem extracted_right (I J:Ideal O)(P:CommonIndex I J):
    rightExponent (commonPart I J) (commonPart J I) (commonEquiv I J P)=rightExponent I J P:=by
  have hp:P.val∈commonSupport J I:=by rw [commonSupport_comm];exact P.property
  simp only [rightExponent,commonEquiv_val,commonPart_valuation,ite_eq_left hp]

def activeEquiv (I J:Ideal O):ActiveIndex I J ≃ ActiveIndex (commonPart I J) (commonPart J I) where
  toFun P:=⟨commonEquiv I J P.val,by
    simpa only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using P.property⟩
  invFun P:=⟨(commonEquiv I J).symm P.val,by
    have hp:=P.property
    have he:(commonEquiv I J) ((commonEquiv I J).symm P.val)=P.val:=(commonEquiv I J).apply_symm_apply _
    rw [←he] at hp
    simpa only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using hp⟩
  left_inv P:=by apply Subtype.ext;exact (commonEquiv I J).symm_apply_apply _
  right_inv P:=by apply Subtype.ext;exact (commonEquiv I J).apply_symm_apply _

@[simp] theorem activeEquiv_prime (I J:Ideal O)(P:ActiveIndex I J):
    activePrime (commonPart I J) (commonPart J I) (activeEquiv I J P)=activePrime I J P:=rfl

@[simp] theorem activeEquiv_exponent (I J:Ideal O)(P:ActiveIndex I J):
    activeExponent (commonPart I J) (commonPart J I) (activeEquiv I J P)=activeExponent I J P:=by
  change netExponent (leftExponent _ _ (commonEquiv I J P.val))
    (rightExponent _ _ (commonEquiv I J P.val))=_
  rw [extracted_left,extracted_right]
  rfl

theorem activeConductor_extracted (I J:Ideal O):
    activeConductor (commonPart I J) (commonPart J I)=activeConductor I J:=by
  unfold activeConductor finitePrimeModulus
  congr 1
  exact (Fintype.prod_equiv (activeEquiv I J) _ _ (fun P=>by rw [activeEquiv_prime])).symm

theorem activeRow_extracted (I J:Ideal O)(hI:Supported I)(z:O):
    finiteSexticRow (activePrime (commonPart I J) (commonPart J I))
      (activeGood _ _ (commonPart_supported I J hI))
      (activeExponent (commonPart I J) (commonPart J I)) z=
    finiteSexticRow (activePrime I J) (activeGood I J hI) (activeExponent I J) z:=by
  unfold finiteSexticRow
  apply (Fintype.prod_equiv (activeEquiv I J) _ _ ?_).symm
  intro P
  rw [activeEquiv_exponent]
  rfl

theorem activeFunction_mk_extracted (I J:Ideal O)(hI:Supported I)(z:O):
    activeFunction (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
      (Ideal.Quotient.mk _ z)=activeFunction I J hI (Ideal.Quotient.mk _ z):=by
  simp only [activeFunction]
  exact activeRow_extracted I J hI z

def mappedSubset (I J:Ideal O)(E:Finset (CommonIndex I J)):
    Finset (CommonIndex (commonPart I J) (commonPart J I)):=E.map (commonEquiv I J).toEmbedding

theorem mappedSubset_product (I J:Ideal O)(E:Finset (CommonIndex I J)):
    (∏P∈mappedSubset I J E,P.val)=∏P∈E,P.val:=by
  simp only [mappedSubset,Finset.prod_map,Equiv.toEmbedding_apply,commonEquiv_val]

theorem mappedSubset_generator (I J:Ideal O)(E:Finset (CommonIndex I J)):
    primeSubsetGenerator (fun P:CommonIndex (commonPart I J) (commonPart J I)=>P.val)
      (mappedSubset I J E)=primeSubsetGenerator (fun P:CommonIndex I J=>P.val) E:=by
  unfold primeSubsetGenerator
  rw [mappedSubset_product]

theorem mappedSubset_inactive (I J:Ideal O)(E:Finset (CommonIndex I J)):
    mappedSubset I J E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets (commonPart I J) (commonPart J I) ↔
      E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets I J:=by
  simp only [CenteredMomentFirstDiscardedEnergy.inactiveSubsets,Finset.mem_powerset]
  constructor
  · intro h P hP
    have hp:=h (Finset.mem_map.mpr ⟨P,hP,rfl⟩)
    simpa only [Equiv.toEmbedding_apply,principalSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using hp
  · intro h P hP
    obtain ⟨R,hR,rfl⟩:=Finset.mem_map.mp hP
    have hr:=h hR
    simpa only [Equiv.toEmbedding_apply,principalSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using hr

theorem nominal_extracted (I J:Ideal O)(E:Finset (CommonIndex I J))(K X:ℝ):
    CenteredMomentFirstScale.firstNominalScale (commonPart I J) (commonPart J I)
      (∏P∈mappedSubset I J E,P.val) K X=
    CenteredMomentFirstScale.firstNominalScale I J (∏P∈E,P.val) K X:=by
  obtain ⟨hc,hd⟩:=fixed_common_parts (commonPart I J) (commonPart J I)
    (commonPart_ne_zero I J) (commonPart_ne_zero J I) (commonParts_equal_support I J)
  unfold CenteredMomentFirstScale.firstNominalScale
  rw [mappedSubset_product,activeConductor_extracted,hc,hd]

end SevenEighths.CenteredMomentFirstCommonTransport

end

end OAI

end Source980

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstCommonFourierTransport.lean; sha256: 94a80550d74a1af395eb1dce1090664de7b3bf8caf90b2335f5fd4e358435e2f -/
section Source981
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonFourierTransport
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstReduced
open CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport CenteredMomentFirstLocalization CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentFirstCommonTransport
local notation "O"=>ActualEisensteinCubic.O

theorem quotient_function_heq (r r':O)(hr:r'=r)
    (G:Residue r→ℂ)(G':Residue r'→ℂ)
    (hG:∀z:O,G' (Ideal.Quotient.mk _ z)=G (Ideal.Quotient.mk _ z)):
    HEq G' G:=by
  subst r'
  apply heq_of_eq
  funext x
  obtain ⟨z,rfl⟩:=Ideal.Quotient.mk_surjective x
  exact hG z

def retainedFourierTerm (a b r:O)(ha:a≠0)(hb:b≠0)(hr:r≠0)
    (χa:MulChar (Residue a) ℂ)(χb:MulChar (Residue b) ℂ)(G:Residue r→ℂ)
    (e:O)(E:Ideal O)(W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let k:=K/normValue e
  (UniqueFactorizationMonoid.moebius E:ℂ)*tripleRow a b r χa χb G e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑'h:O,
      (retainedWeight R (normValue h):ℂ)*tripleFourier a b r ha hb hr χa χb G h*
        EisensteinSchwartzPoisson.paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

theorem retainedFourierTerm_transport (a b r r':O)(ha:a≠0)(hb:b≠0)(hr:r≠0)(hr':r'≠0)
    (χa:MulChar (Residue a) ℂ)(χb:MulChar (Residue b) ℂ)(G:Residue r→ℂ)(G':Residue r'→ℂ)
    (he:r'=r)(hG:∀z:O,G' (Ideal.Quotient.mk _ z)=G (Ideal.Quotient.mk _ z))
    (e:O)(E:Ideal O)(W:𝓢(ℝ,ℂ))(K R:ℝ):
    retainedFourierTerm a b r' ha hb hr' χa χb G' e E W K R=
      retainedFourierTerm a b r ha hb hr χa χb G e E W K R:=by
  subst r'
  have hg:G'=G:=eq_of_heq (quotient_function_heq r r rfl G G' hG)
  subst G'
  rfl

def fixedRetainedTerm (C D:Ideal O)(hC:Supported C)(a b:O)
    (ha:Supported (Ideal.span {a}))(hb:Supported (Ideal.span {b}))
    (E:Finset (CommonIndex C D))(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  retainedFourierTerm a b (activeConductor C D)
    (supported_element_ne_zero _ ha) (supported_element_ne_zero _ hb) (finitePrimeModulus_ne_zero _)
    (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ (activeFunction C D hC)
    (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E) (∏P∈E,P.val) W K
    (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ)

theorem canonicalRetainedTerm_fixed (I J:Ideal O)(hI:Supported I)(hJ:Supported J)
    (E:Finset (CommonIndex I J))(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    canonicalRetainedTerm I J hI hJ E W K
      (firstNominalScale I J (∏P∈E,P.val) K X) Z ξ=
    fixedRetainedTerm (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
      (residualGenerator I J) (residualGenerator J I)
      (residualGenerator_supported I J hI) (residualGenerator_supported J I hJ)
      (mappedSubset I J E) W K X Z ξ:=by
  unfold fixedRetainedTerm
  rw [nominal_extracted,mappedSubset_generator,mappedSubset_product]
  have hh:=retainedFourierTerm_transport (residualGenerator I J) (residualGenerator J I)
    (activeConductor I J) (activeConductor (commonPart I J) (commonPart J I))
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    (finitePrimeModulus_ne_zero _) (finitePrimeModulus_ne_zero _)
    (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹
    (activeFunction I J hI) (activeFunction (commonPart I J) (commonPart J I) (commonPart_supported I J hI))
    (activeConductor_extracted I J) (activeFunction_mk_extracted I J hI)
    (primeSubsetGenerator (fun P:CommonIndex I J=>P.val) E) (∏P∈E,P.val) W K
    (frequencyRadius (firstNominalScale I J (∏P∈E,P.val) K X) Z ξ)
  exact hh.symm

def inactiveEquiv (I J:Ideal O):
    CenteredMomentFirstDiscardedEnergy.inactiveSubsets I J ≃
      CenteredMomentFirstDiscardedEnergy.inactiveSubsets (commonPart I J) (commonPart J I):=
  (Equiv.finsetCongr (commonEquiv I J)).subtypeEquiv (fun E=>(mappedSubset_inactive I J E).symm)

@[simp] theorem inactiveEquiv_val (I J:Ideal O)
    (E:CenteredMomentFirstDiscardedEnergy.inactiveSubsets I J):
    (inactiveEquiv I J E).val=mappedSubset I J E.val:=rfl

theorem canonicalRetainedPair_fixed (I J:Ideal O)(hI:Supported I)(hJ:Supported J)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ=
    ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets (commonPart I J) (commonPart J I),
      fixedRetainedTerm (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
        (residualGenerator I J) (residualGenerator J I)
        (residualGenerator_supported I J hI) (residualGenerator_supported J I hJ) E W K X Z ξ:=by
  unfold CenteredMomentFirstSectorLocalization.retainedPair
  apply Finset.sum_bij (fun E _=>mappedSubset I J E)
  · intro E hE
    exact (mappedSubset_inactive I J E).mpr hE
  · intro E hE F hF he
    exact (Equiv.finsetCongr (commonEquiv I J)).injective he
  · intro F hF
    obtain ⟨E,he⟩:=(Equiv.finsetCongr (commonEquiv I J)).surjective F
    change mappedSubset I J E=F at he
    exact ⟨E,(mappedSubset_inactive I J E).mp (he.symm ▸ hF),he⟩
  · intro E hE
    exact canonicalRetainedTerm_fixed I J hI hJ E W K X Z ξ

end SevenEighths.CenteredMomentFirstCommonFourierTransport

end

end OAI

end Source981

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstRetainedSector.lean; sha256: 0db25cbc275e2cdfe367a7ca3a371e4b2d1f9dcf50a82a92bb09f8b9ef73b94b -/
section Source982
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedSector
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentFirstSectorLocalization CenteredMomentFirstCommonFourierTransport
open CenteredMomentHeckeExpansion CenteredMomentCommonSectors
open CenteredMomentFirstSectors CenteredMomentCompleteCommon CenteredMomentSecondSectorColumns
open CenteredMomentHeckeColumnWindow
open CenteredMomentSupport CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

def retainedKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  if hI : Supported I then if hJ : Supported J then CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ else 0 else 0

theorem retainedKernel_eq (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    retainedKernel I J W K X Z ξ=CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ := by
  simp only [retainedKernel,dite_eq_left hI,dite_eq_left hJ]

theorem retainedEnergy_common_sectors (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S β W K X Z ξ=
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((β q.1*rowWeight η m A 1 t q.1)*star (β q.2*rowWeight η m A 1 t q.2))*
            retainedKernel q.1 q.2 W K X Z ξ := by
  let F := fun I J : Ideal O=>((β I*rowWeight η m A 1 t I)*star (β J*rowWeight η m A 1 t J))*
    retainedKernel I J W K X Z ξ
  have he : CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S β W K X Z ξ=
      ∑ I : supportedColumns S,∑ J : supportedColumns S,F I J := by
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [F]
    rw [retainedKernel_eq I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2]
  rw [he]
  have hj (I : Ideal O) : (∑ J : supportedColumns S,F I J)=∑ J∈supportedColumns S,F I J :=
    Finset.sum_coe_sort _ _
  simp_rw [hj]
  rw [Finset.sum_coe_sort (supportedColumns S) (fun I=>∑ J∈supportedColumns S,F I J)]
  exact sum_common_sectors _ _ F

theorem retained_sector_independent (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*rowWeight η m A 1 t q.1)*star (β q.2*rowWeight η m A 1 t q.2))*
        retainedKernel q.1 q.2 W K X Z ξ)=
      rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
        ∑ I : sectorPool C hC S,∑ J : sectorPool D hD S,
          if IsCoprime (I:Ideal O) (J:Ideal O) then
            ((β (C*I)*rowWeight η m A 1 t I)*star (β (D*J)*rowWeight η m A 1 t J))*
              retainedKernel (C*I) (D*J) W K X Z ξ else 0 := by
  rw [←independent_sector_pools C D hC hD hCD S
    (fun I J=>((β (C*I)*rowWeight η m A 1 t I)*star (β (D*J)*rowWeight η m A 1 t J))*
      retainedKernel (C*I) (D*J) W K X Z ξ)]
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI=>(Finset.mem_filter.mp hI).2.1) (fun I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun I J=>((β I*rowWeight η m A 1 t I)*star (β J*rowWeight η m A 1 t J))*
      retainedKernel I J W K X Z ξ)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  split_ifs <;> simp only [map_mul,star_mul,mul_zero]
  ring

theorem reconstructed_residualParts (C D I J:Ideal O)(hC:C≠0)(hD:D≠0)(hI:I≠0)(hJ:J≠0)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (hCI:IsCoprime C I)(hCJ:IsCoprime C J)(hIJ:IsCoprime I J):
    residualPart (C*I) (D*J)=I ∧ residualPart (D*J) (C*I)=J:=by
  obtain ⟨hc,hd⟩:=reconstructed_commonParts C D I J hC hD hI hJ hCD hCI hCJ hIJ
  constructor
  · have hh:=reconstruct (C*I) (D*J) (mul_ne_zero hC hI)
    rw [hc] at hh
    exact (mul_left_cancel₀ hC hh).symm
  · have hh:=reconstruct (D*J) (C*I) (mul_ne_zero hD hJ)
    rw [hd] at hh
    exact (mul_left_cancel₀ hD hh).symm

theorem canonicalRetainedPair_of_common (I J C D:Ideal O)(hI:Supported I)(hJ:Supported J)
    (hC:Supported C)(hc:commonPart I J=C)(hd:commonPart J I=D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ=
      ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
        fixedRetainedTerm C D hC (CenteredMomentCanonicalFirst.residualGenerator I J)
          (CenteredMomentCanonicalFirst.residualGenerator J I)
          (CenteredMomentCanonicalFirst.residualGenerator_supported I J hI)
          (CenteredMomentCanonicalFirst.residualGenerator_supported J I hJ) E W K X Z ξ:=by
  subst C
  subst D
  exact canonicalRetainedPair_fixed I J hI hJ W K X Z ξ

theorem retainedKernel_fixed (C D I J:Ideal O)(hC:Supported C)(hD:Supported D)
    (hI:Supported I)(hJ:Supported J)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (hCI:IsCoprime C I)(hCJ:IsCoprime C J)(hIJ:IsCoprime I J)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    retainedKernel (C*I) (D*J) W K X Z ξ=
      ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
        fixedRetainedTerm C D hC (primaryGenerator I) (primaryGenerator J)
          (by rw [primary_span_supported I hI];exact hI)
          (by rw [primary_span_supported J hJ];exact hJ) E W K X Z ξ:=by
  have hCI':Supported (C*I):=(supported_mul_iff C I).mpr ⟨hC,hI⟩
  have hDJ':Supported (D*J):=(supported_mul_iff D J).mpr ⟨hD,hJ⟩
  rw [retainedKernel_eq _ _ hCI' hDJ']
  obtain ⟨hc,hd⟩:=reconstructed_commonParts C D I J hC.1 hD.1 hI.1 hJ.1 hCD hCI hCJ hIJ
  obtain ⟨hi,hj⟩:=reconstructed_residualParts C D I J hC.1 hD.1 hI.1 hJ.1 hCD hCI hCJ hIJ
  have hh:=canonicalRetainedPair_of_common (C*I) (D*J) C D hCI' hDJ' hC hc hd W K X Z ξ
  simpa only [CenteredMomentCanonicalFirst.residualGenerator,hi,hj] using hh

end SevenEighths.CenteredMomentFirstRetainedSector

end

end OAI

end Source982

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstPhysicalDyadicAssembly.lean; sha256: f84fbf537bc6523aa502030a4a55b94d2501e49be32d18aa0ab142c3621ee362 -/
section Source983
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicAssembly
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstReduced CenteredMomentFirstColumns CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentRowNorm
open CenteredMomentFirstWholeKernel CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentDyadicCount CenteredMomentPrimitive
local notation "O"=>ActualEisensteinCubic.O

def retainedBlock (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let k:=K/‖eisEmbedding e‖^2
  let r:=activeConductor C D
  inactiveWeight C D E * ∑h∈rows,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      let na:=element C C hC.1 S a
      let nb:=element C D hD.1 S b
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (tripleRow na nb r (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) e *
        ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
        tripleFourier na nb r
          (supported_element_ne_zero _ (element_supported C C hC.1 S a))
          (supported_element_ne_zero _ (element_supported C D hD.1 S b))
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) h)*
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        (retainedWeight R (‖eisEmbedding h‖^2):ℂ)*
        EisensteinSchwartzPoisson.paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
      else 0

def retainedIndices (R:ℝ):Finset ℤ := (finite_retained_integral_dyads R).toFinset

lemma mem_retainedIndices (R:ℝ)(n:ℤ):
    n∈retainedIndices R↔Retained R n ∧ ∃q:ℝ,1≤q ∧ dyadicWeight n q≠0 :=
  (finite_retained_integral_dyads R).mem_toFinset

lemma retained_partition (R q:ℝ)(hq:1≤q):
    (∑n∈retainedIndices R,dyadicWeight n q)=retainedWeight R q :=by
  unfold retainedWeight
  rw [tsum_eq_sum (s:=retainedIndices R) (fun n hn=>by
    split_ifs with hr
    · by_contra hh
      exact hn ((mem_retainedIndices R n).mpr ⟨hr,q,hq,hh⟩)
    · rfl)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [ite_eq_left ((mem_retainedIndices R n).mp hn).1]

def bands (K R A B:ℝ):Fin 4→Finset ℤ :=
  ![indices K K,retainedIndices R,indices 1 A,indices 1 B]

abbrev Blocks (K R A B:ℝ):=∀i:Fin 4,↥(bands K R A B i)

lemma product_partition (K R A B h a b:ℝ)(hK:0<K)(hh:1≤h)
    (ha:a∈Set.Icc (1:ℝ) A)(hb:b∈Set.Icc (1:ℝ) B):
    (∑n:Blocks K R A B,∏i:Fin 4,dyadicWeight (n i) (![K,h,a,b] i))=
      retainedWeight R h :=by
  have he (i:Fin 4):
      (∑n:bands K R A B i,dyadicWeight n (![K,h,a,b] i))=
        (if i=1 then retainedWeight R h else 1):=by
    fin_cases i
    · change (∑n:indices K K,dyadicWeight n K)=1
      rw [Finset.sum_coe_sort (indices K K) (fun n:ℤ=>dyadicWeight n K)]
      exact dyadic_partition_on_interval K K K hK ⟨le_rfl,le_rfl⟩
    · change (∑n:retainedIndices R,dyadicWeight n h)=retainedWeight R h
      rw [Finset.sum_coe_sort (retainedIndices R) (fun n:ℤ=>dyadicWeight n h)]
      exact retained_partition R h hh
    · change (∑n:indices 1 A,dyadicWeight n a)=1
      rw [Finset.sum_coe_sort (indices 1 A) (fun n:ℤ=>dyadicWeight n a)]
      exact dyadic_partition_on_interval 1 A a (by norm_num) ha
    · change (∑n:indices 1 B,dyadicWeight n b)=1
      rw [Finset.sum_coe_sort (indices 1 B) (fun n:ℤ=>dyadicWeight n b)]
      exact dyadic_partition_on_interval 1 B b (by norm_num) hb
  rw [←Fintype.prod_sum (fun (i:Fin 4)(n:bands K R A B i)=>
    dyadicWeight n (![K,h,a,b] i))]
  simp_rw [he]
  norm_num [Fin.prod_univ_four]

lemma windows_partition (K R A B h a b:ℝ)(hK:0<K)(hh:1≤h)
    (ha:a∈Set.Icc (1:ℝ) A)(hb:b∈Set.Icc (1:ℝ) B):
    (∑n:Blocks K R A B, windows (fun _=>logAnnulus) K h a b
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)))=
      (retainedWeight R h:ℂ):=by
  calc
    _ = ∑n:Blocks K R A B,((∏i:Fin 4,dyadicWeight (n i) (![K,h,a,b] i):ℝ):ℂ):=by
      apply Finset.sum_congr rfl
      intro n hn
      simpa [Fin.prod_univ_four] using
        (actual_product_windows K h a b hK (zero_lt_one.trans_le hh)
          (zero_lt_one.trans_le ha.1) (zero_lt_one.trans_le hb.1) (fun i=>n i)).symm
    _ = _ :=by
      rw [←Complex.ofReal_sum,product_partition K R A B h a b hK hh ha hb]

def effectiveScale (C D:Ideal O)(E:Finset (CommonIndex C D))(K:ℝ):ℝ:=
  (K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2)/
    ‖eisEmbedding (activeConductor C D)‖^2

lemma effectiveScale_pos (C D:Ideal O)(E:Finset (CommonIndex C D))(K:ℝ)(hK:0<K):
    0<effectiveScale C D E K:=by
  unfold effectiveScale
  apply div_pos (div_pos hK ?_) ?_
  · exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero _ _)))
  · exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero _)))

lemma element_norm (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    ‖eisEmbedding (element C D hD S a)‖^2=((a:Ideal O).absNorm:ℝ):=by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]

lemma element_norm_ge_one (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    1≤‖eisEmbedding (element C D hD S a)‖^2:=by
  rw [element_norm]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (column_supported C D hD S a).1)

lemma element_norm_le (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S)
    (c:Ideal O→ℂ)(H:ℝ)(hcap:∀I,c I≠0→(I.absNorm:ℝ)≤H)(ha:c (D*a)≠0):
    ‖eisEmbedding (element C D hD S a)‖^2≤H/(D.absNorm:ℝ):=by
  have hDpos:(0:ℝ)<D.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  rw [element_norm]
  apply (le_div_iff₀ hDpos).mpr
  simpa only [map_mul,Nat.cast_mul,mul_comm] using hcap (D*a) ha

theorem retainedBlock_eq_blocks
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(hrows:∀h∈rows,h≠0)(W:𝓢(ℝ,ℂ))(K R H:ℝ)(hK:0<K)
    (hcap:∀I,c I≠0→(I.absNorm:ℝ)≤H):
    retainedBlock η m A t S c C D hC hD E rows W K R=
      ∑n:Blocks (effectiveScale C D E K) R (H/(C.absNorm:ℝ)) (H/(D.absNorm:ℝ)),
        block η m A t S c C D hC hD E rows W (fun _=>logAnnulus) K
          (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)):=by
  unfold retainedBlock block
  dsimp only
  rw [←Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab:IsCoprime (a:Ideal O) (b:Ideal O)
  · simp only [hab,ite_true]
    by_cases hca:c (C*(a:Ideal O))=0
    · simp [coefficient,hca]
    by_cases hcb:c (D*(b:Ideal O))=0
    · simp [coefficient,hcb]
    have hnorm:1≤‖eisEmbedding h‖^2:=by
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr (hrows h hh)))
    have hpart:=windows_partition (effectiveScale C D E K) R
      (H/(C.absNorm:ℝ)) (H/(D.absNorm:ℝ)) (‖eisEmbedding h‖^2)
      (‖eisEmbedding (element C C hC.1 S a)‖^2) (‖eisEmbedding (element C D hD.1 S b)‖^2)
      (effectiveScale_pos C D E K hK) hnorm
      ⟨element_norm_ge_one C C hC.1 S a,element_norm_le C C hC.1 S a c H hcap hca⟩
      ⟨element_norm_ge_one C D hD.1 S b,element_norm_le C D hD.1 S b c H hcap hcb⟩
    rw [←Finset.sum_mul,←Finset.mul_sum]
    congr 1
    congr 1
    exact hpart.symm
  · simp [hab]

lemma block_retained (K R A B:ℝ)(n:Blocks K R A B):Retained R (n 1):=
  ((mem_retainedIndices R (n 1)).mp (n 1).property).1

def retainedInfiniteBlock (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let k:=K/‖eisEmbedding e‖^2
  let r:=activeConductor C D
  inactiveWeight C D E * ∑'h:O,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      let na:=element C C hC.1 S a
      let nb:=element C D hD.1 S b
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (tripleRow na nb r (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) e *
        ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
        tripleFourier na nb r
          (supported_element_ne_zero _ (element_supported C C hC.1 S a))
          (supported_element_ne_zero _ (element_supported C D hD.1 S b))
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) h)*
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        (retainedWeight R (‖eisEmbedding h‖^2):ℂ)*
        EisensteinSchwartzPoisson.paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
      else 0

lemma retained_rows_nonzero (R:ℝ):
    ∀h∈CenteredMomentSecondRetainedRows.retainedRows R 1,h≠0:=by
  intro h hh hz
  have hn:=(mem_rowNormDisk.mp hh).1
  subst h
  simp at hn

theorem retainedInfiniteBlock_eq_finite
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K R:ℝ):
    retainedInfiniteBlock η m A t S c C D hC hD E W K R=
      retainedBlock η m A t S c C D hC hD E
        (CenteredMomentSecondRetainedRows.retainedRows R 1) W K R:=by
  unfold retainedInfiniteBlock retainedBlock
  dsimp only
  congr 1
  apply tsum_eq_sum
  intro h hh
  have hz:retainedWeight R (‖eisEmbedding h‖^2)=0:=by
    by_contra hn
    apply hh
    apply CenteredMomentSecondRetainedRows.retained_mem_rows R 1 h one_ne_zero
    simpa only [one_mul,normValue_eq_embedding] using hn
  simp only [hz,Complex.ofReal_zero,mul_zero,zero_mul,ite_self,Finset.sum_const_zero]

theorem original_retained_dyadic
    {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K R:ℝ)(hK:0<K):
    retainedInfiniteBlock s.η m A t S
      (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed) C D hC hD E W K R=
      ∑n:Blocks (effectiveScale C D E K) R
          (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
          (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
        block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed)
          C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
          (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
            (dyadicScale (n 2)) (dyadicScale (n 3)):=by
  rw [retainedInfiniteBlock_eq_finite]
  exact retainedBlock_eq_blocks s.η m A t S _ C D hC hD E _
    (retained_rows_nonzero R) W K R _ hK
    (fun I hI=>(CenteredMomentOriginalCommonHarmonic.original_column_norm s Rbad seed I hz₁ hz₂ hI).2)

end SevenEighths.CenteredMomentFirstPhysicalDyadicAssembly

end

end OAI

end Source983

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstRetainedPhysical.lean; sha256: 6eecc469d8745f3a5a88b1df441a83d906679bcc837b504f227ca62c83ab92ba -/
section Source984
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedPhysical
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform CenteredMomentSourceRow
open CenteredMomentFirstRetainedSector CenteredMomentFirstCommonFourierTransport
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSupportedCorrelation CenteredMomentHeckeExpansion CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentFirstReduced
local notation "O"=>ActualEisensteinCubic.O

 theorem original_sector_columns (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:C≠0)(hD:D≠0)(hCD:primeSupport C=primeSupport D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    (∑q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*
        retainedKernel q.1 q.2 W K X Z ξ)=
    rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
      ∑a:columns C C hC S,∑b:columns C D hD S,
        if IsCoprime (a:Ideal O) (b:Ideal O) then
          (coefficient η m A t c C a*star (coefficient η m A t c D b))*
            retainedKernel (C*a) (D*b) W K X Z ξ else 0:=by
  rw [←original_pool_restriction C D hC hD S
    (fun a b=>(coefficient η m A t c C a*star (coefficient η m A t c D b))*
      retainedKernel (C*a) (D*b) W K X Z ξ)]
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI=>(Finset.mem_filter.mp hI).2.1) (fun I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun I J=>((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      retainedKernel I J W K X Z ξ)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp only [coefficient,map_mul,star_mul,mul_zero]
  ring

def fixedRetainedSector (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
          fixedRetainedTerm C D hC (element C C hC.1 S a) (element C D hD.1 S b)
            (element_supported C C hC.1 S a) (element_supported C D hD.1 S b) E W K X Z ξ
      else 0

theorem original_sector_fixed (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    (∑q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*
        retainedKernel q.1 q.2 W K X Z ξ)=
    rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
      fixedRetainedSector η m A t S c C D hC hD W K X Z ξ:=by
  rw [original_sector_columns η m A t S c C D hC.1 hD.1 hCD W K X Z ξ]
  congr 1
  let F:=fun (a:columns C C hC.1 S) (b:columns C D hD.1 S) (E:Finset (CommonIndex C D))=>
    if IsCoprime (a:Ideal O) (b:Ideal O) then
      (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        fixedRetainedTerm C D hC (element C C hC.1 S a) (element C D hD.1 S b)
          (element_supported C C hC.1 S a) (element_supported C D hD.1 S b) E W K X Z ξ
    else 0
  calc
    _=∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,F a b E:=by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hab:IsCoprime (a:Ideal O) (b:Ideal O)
      · simp only [F,hab,ite_true]
        rw [retainedKernel_fixed C D a b hC hD (column_supported C C hC.1 S a)
          (column_supported C D hD.1 S b) hCD (Finset.mem_filter.mp a.property).2
          (Finset.mem_filter.mp b.property).2 hab W K X Z ξ,Finset.mul_sum]
        rfl
      · simp only [F,hab,ite_false,Finset.sum_const_zero]
    _=∑a:columns C C hC.1 S,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
      ∑b:columns C D hD.1 S,F a b E:=by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _=fixedRetainedSector η m A t S c C D hC hD W K X Z ξ:=Finset.sum_comm

end SevenEighths.CenteredMomentFirstRetainedPhysical

end

end OAI

end Source984

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstRetainedBlock.lean; sha256: f5f0e14b6aaa93d4aa5374de4118e22478b4062d58754b3d0fc77a93b5a72a10 -/
section Source985
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedBlock
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CompletedGauss CanonicalQuadraticSieve
open CenteredMomentFirstRetainedPhysical CenteredMomentFirstCommonFourierTransport
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentRowNorm
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation CenteredMomentSectorLocalization CenteredMomentFirstScale
local notation "O"=>ActualEisensteinCubic.O

lemma retained_tsum (R:ℝ)(f:O→ℂ):
    (∑'h:O,(retainedWeight R (normValue h):ℂ)*f h)=
      ∑h∈CenteredMomentSecondRetainedRows.retainedRows R 1,
        (retainedWeight R (normValue h):ℂ)*f h:=by
  apply tsum_eq_sum
  intro h hh
  have hz:retainedWeight R (normValue h)=0:=by
    by_contra hn
    apply hh
    apply CenteredMomentSecondRetainedRows.retained_mem_rows R 1 h one_ne_zero
    simpa only [one_mul] using hn
  simp only [hz,Complex.ofReal_zero,zero_mul]

lemma retainedFourierTerm_finite (a b r:O)(ha:a≠0)(hb:b≠0)(hr:r≠0)
    (χa:MulChar (Residue a) ℂ)(χb:MulChar (Residue b) ℂ)(G:Residue r→ℂ)
    (e:O)(E:Ideal O)(W:𝓢(ℝ,ℂ))(K R:ℝ):
    retainedFourierTerm a b r ha hb hr χa χb G e E W K R=
      (UniqueFactorizationMonoid.moebius E:ℂ)*
      ∑h∈CenteredMomentSecondRetainedRows.retainedRows R 1,
        (tripleRow a b r χa χb G e *
          (((K/normValue e)/normValue (a*(b*r)):ℝ):ℂ)*
          tripleFourier a b r ha hb hr χa χb G h)*
        (retainedWeight R (normValue h):ℂ)*
        EisensteinSchwartzPoisson.paperRadialFourier W
          ((K/normValue e)*normValue h/normValue (a*(b*r))):=by
  unfold retainedFourierTerm
  dsimp only
  simp_rw [mul_assoc (retainedWeight R (normValue _):ℂ)]
  rw [retained_tsum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [show (K/normValue e)/normValue (a*(b*r))*normValue h=
    (K/normValue e)*normValue h/normValue (a*(b*r)) by ring]
  ring

lemma finite_pair_row_sum {α β:Type*}[Fintype α][Fintype β]
    (rows:Finset O)(p:α→β→Prop)[DecidableRel p]
    (c:α→β→ℂ)(μ:ℂ)(f:α→β→O→ℂ):
    (∑a:α,∑b:β,if p a b then c a b*(μ*∑h∈rows,f a b h) else 0)=
      μ*∑h∈rows,∑a:α,∑b:β,if p a b then c a b*f a b h else 0:=by
  have hp (a:α)(b:β):
      (if p a b then c a b*(μ*∑h∈rows,f a b h) else 0)=
        ∑h∈rows,μ*(if p a b then c a b*f a b h else 0):=by
    by_cases hab:p a b
    · simp only [hab,ite_true,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    · simp [hab]
  simp_rw [hp,Finset.mul_sum]
  calc
    _=∑a:α,∑h∈rows,∑b:β,μ*(if p a b then c a b*f a b h else 0):=by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _=_:=Finset.sum_comm

theorem fixed_sector_term_block
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    (∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
          fixedRetainedTerm C D hC (element C C hC.1 S a) (element C D hD.1 S b)
            (element_supported C C hC.1 S a) (element_supported C D hD.1 S b) E W K X Z ξ
      else 0)=
    retainedInfiniteBlock η m A t S c C D hC hD E W K
      (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ):=by
  unfold fixedRetainedTerm
  generalize_proofs
  simp_rw [retainedFourierTerm_finite]
  rw [finite_pair_row_sum]
  rw [retainedInfiniteBlock_eq_finite]
  unfold retainedBlock inactiveWeight
  dsimp only
  simp only [normValue_eq_embedding]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> ring

theorem fixed_sector_blocks
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    fixedRetainedSector η m A t S c C D hC hD W K X Z ξ=
      ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
        retainedInfiniteBlock η m A t S c C D hC hD E W K
          (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ):=by
  unfold fixedRetainedSector
  apply Finset.sum_congr rfl
  intro E hE
  exact fixed_sector_term_block η m A t S c C D hC hD E W K X Z ξ

end SevenEighths.CenteredMomentFirstRetainedBlock

end

end OAI

end Source985

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstRetainedAssembly.lean; sha256: fb9a72d58c205064632b3b8fb23ce1db6355f3774cf6e819b0345bbbcb87b8d2 -/
section Source986
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedAssembly
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstRetainedPhysical CenteredMomentFirstRetainedSector
open CenteredMomentFirstRetainedBlock CenteredMomentFirstSectorTransform CenteredMomentFirstSectors
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSourceRow CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentRowNorm
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation CenteredMomentHeckeExpansion
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentLogDyadic
local notation "O"=>ActualEisensteinCubic.O

def infiniteSector (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    retainedInfiniteBlock η m A t S c C D hC hD E W K
      (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ)

theorem retained_energy_blocks (η:Character)(m A:O)(t:ℝ)
    (S:Finset (Ideal O))(c:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S c W K X Z ξ=
      ∑p:commonLabels (supportedColumns S) (supportedColumns S),
        rowWeight η m A 1 t p.val.1*star (rowWeight η m A 1 t p.val.2)*
          infiniteSector η m A t S c p.val.1 p.val.2
            (commonLabels_supported S p).1 (commonLabels_supported S p).2 W K X Z ξ:=by
  rw [retainedEnergy_common_sectors]
  rw [←Finset.sum_coe_sort _ (fun p:Ideal O×Ideal O=>
    ∑q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*
        retainedKernel q.1 q.2 W K X Z ξ)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [original_sector_fixed η m A t S c p.val.1 p.val.2
    (commonLabels_supported S p).1 (commonLabels_supported S p).2
    (commonLabels_data _ _ p.val.1 p.val.2 p.property).2.2 W K X Z ξ]
  exact congrArg (fun z=>rowWeight η m A 1 t p.val.1*star (rowWeight η m A 1 t p.val.2)*z)
    (fixed_sector_blocks η m A t S c p.val.1 p.val.2
      (commonLabels_supported S p).1 (commonLabels_supported S p).2 W K X Z ξ)

def physicalSector {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    let R:=frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ
    ∑n:Blocks (effectiveScale C D E K) R
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
      block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed)
        C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))

theorem original_retained_physical
    {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ)(hK:0<K):
    CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S
      (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed) W K X Z ξ=
      ∑p:commonLabels (supportedColumns S) (supportedColumns S),
        rowWeight s.η m A 1 t p.val.1*star (rowWeight s.η m A 1 t p.val.2)*
          physicalSector s Rbad seed m A t S p.val.1 p.val.2
            (commonLabels_supported S p).1 (commonLabels_supported S p).2 W K X Z ξ:=by
  rw [retained_energy_blocks]
  apply Finset.sum_congr rfl
  intro p hp
  apply congrArg
  unfold infiniteSector physicalSector
  apply Finset.sum_congr rfl
  intro E hE
  exact original_retained_dyadic s Rbad seed hz₁ hz₂ m A t S p.val.1 p.val.2
    (commonLabels_supported S p).1 (commonLabels_supported S p).2 E W K _ hK

end SevenEighths.CenteredMomentFirstRetainedAssembly

end

end OAI

end Source986

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstRetainedActive.lean; sha256: c244abe3e0d50e6a2c39f145bca5a2e1c4ff8f3f8110039126f93ab2d2403b5b -/
section Source987
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedActive
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstRetainedSector CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentFirstSectors CenteredMomentSupportedCorrelation
open CenteredMomentActiveSource (activeSource supportedColumns_active)
local notation "O"=>ActualEisensteinCubic.O

 theorem retained_energy_sum (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S β W K X Z ξ=
      ∑I∈supportedColumns S,∑J∈supportedColumns S,
        ((β I*rowWeight η m A 1 t I)*star (β J*rowWeight η m A 1 t J))*
          CenteredMomentFirstRetainedSector.retainedKernel I J W K X Z ξ:=by
  unfold CenteredMomentFirstSectorLocalization.retainedEnergy
  conv_rhs=>rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro I hI
  conv_rhs=>rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [retainedKernel_eq I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2]

 theorem retained_energy_active (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedEnergy η m A t (activeSource S β) β W K X Z ξ=
      CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S β W K X Z ξ:=by
  rw [retained_energy_sum,retained_energy_sum,supportedColumns_active]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hi:β I=0
  · simp [hi]
  · rw [ite_eq_left hi]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hj:β J=0 <;> simp [hj]

end SevenEighths.CenteredMomentFirstRetainedActive

end

end OAI

end Source987

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstRetainedNorm.lean; sha256: 610981cd16fe70a5df992651b13b71a2e5d35fee91b6a1c426883bccdd7e7634 -/
section Source988
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedNorm
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstRetainedAssembly CenteredMomentFirstRetainedActive
open CenteredMomentFirstSectorTransform CenteredMomentFirstSectors CenteredMomentHeckeExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSourceRow CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentRowNorm
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentLogDyadic
open CenteredMomentActiveSource (activeSource)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def sector (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    let R:=frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ
    ∑n:Blocks (effectiveScale C D E K) R
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
      block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed)
        C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))

def sectorMass (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℝ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    let R:=frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ
    ∑n:Blocks (effectiveScale C D E K) R
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
      ‖block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed)
        C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))‖

omit [DecidableEq ι] in
theorem sector_norm (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    ‖sector s Rbad seed m A t S C D hC hD W K X Z ξ‖≤
      sectorMass s Rbad seed m A t S C D hC hD W K X Z ξ:=by
  unfold sector sectorMass
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro E hE
  exact norm_sum_le _ _

theorem original_active_sectors (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ)(hK:0<K):
    let β:=CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed
    let T:=activeSource S β
    CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S β W K X Z ξ=
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        rowWeight s.η m A 1 t p.val.1*star (rowWeight s.η m A 1 t p.val.2)*
        sector s Rbad seed m A t T p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 W K X Z ξ:=by
  dsimp only
  rw [←retained_energy_active s.η m A t S _ W K X Z ξ]
  exact original_retained_physical s Rbad seed hz₁ hz₂ m A t _ W K X Z ξ hK

theorem original_retained_norm (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ)(hK:0<K):
    let β:=CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed
    let T:=activeSource S β
    ‖CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S β W K X Z ξ‖≤
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s Rbad seed m A t T p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 W K X Z ξ:=by
  dsimp only
  rw [original_active_sectors s Rbad seed hz₁ hz₂ m A t S W K X Z ξ hK]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul]
  have hw:‖rowWeight s.η m A 1 t p.val.1*star (rowWeight s.η m A 1 t p.val.2)‖≤1:=by
    rw [norm_mul,norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one _ _ _ _ _ _
        (commonLabels_supported _ p).1.1)).trans
      (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one _ _ _ _ _ _
        (commonLabels_supported _ p).2.1)
  exact (mul_le_of_le_one_left (norm_nonneg _) hw).trans (sector_norm s Rbad seed m A t _ _ _ _ _ W K X Z ξ)

end SevenEighths.CenteredMomentFirstRetainedNorm

end

end OAI

end Source988

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceProfileMassUniform.lean; sha256: f3fcf86cfe16e6e62ad314547b2126989a9d002be127015f770d92111085f6e7 -/
section Source989
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap

namespace SevenEighths.CenteredMomentSourceProfileMassUniform
open ActualEisensteinCubic CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass
local notation "O" => ActualEisensteinCubic.O

theorem profile_mass_explicit {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (b D : ι → ℝ) (b₁ b₂ D₁ D₂ : ℝ)
    (hb : ∀ j,0≤b j) (hb₁ : 0≤b₁) (hb₂ : 0≤b₂)
    (hD : ∀ j,0≤D j) (hD₁ : 0≤D₁) (hD₂ : 0≤D₂)
    (hzSlot : ∀ j,Wslot j 0=0) (hz₁ : W₁ 0=0) (hz₂ : W₂ 0=0)
    (hsSlot : ∀ j x,Wslot j x≠0→x≤b j)
    (hs₁ : ∀ x,W₁ x≠0→x≤b₁) (hs₂ : ∀ x,W₂ x≠0→x≤b₂)
    (hbound : ∀ j x,‖Wslot j x‖≤D j)
    (hbound₁ : ∀ x,‖W₁ x‖≤D₁) (hbound₂ : ∀ x,‖W₂ x‖≤D₂)
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (hν : ∀ j I,‖ν j I‖≤1)
    (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j,0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (S : Finset (Tuple ι)) :
    (∑v∈S,‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖)≤
      (2*128^(Fintype.card ι+2)*(∏j,D j)*D₁*D₂*(∏j,b j)*b₁*b₂)*
        (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏j,P j) := by
  let e := Fintype.equivFin ι
  have hzero : ∀ i,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i 0=0 := by
    simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hzSlot (e.symm j)) (And.intro hz₁ hz₂)
  have hs : ∀ i x,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i x≠0→
      x≤sourceBounds (fun j => b (e.symm j)) b₁ b₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hsSlot (e.symm j)) (And.intro hs₁ hs₂)
  have hbound' : ∀ i x,‖sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i x‖≤
      sourceBounds (fun j => D (e.symm j)) D₁ D₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hbound (e.symm j)) (And.intro hbound₁ hbound₂)
  have hm := originalCoefficient_mass (Fintype.card ι) 1 one_ne_zero
    (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0 (fun j => ν (e.symm j))
    (fun j I => hν _ I) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
    (fun j => b (e.symm j)) (fun j => D (e.symm j)) W₁ W₂
    b₁ b₂ D₁ D₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    (fun j => hb _) hb₁ hb₂ (fun j => hD _) hD₁ hD₂
    (fun j => hP _) hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hzero hs hbound'
    (S.image (tupleEquiv e))
  rw [finite_original_mass_reindex] at hm
  simp_rw [profileCoefficient_eq_original]
  simpa only [sourceMassConstant,e.symm.prod_comp D,e.symm.prod_comp b,e.symm.prod_comp P] using hm

theorem profile_mass_uniform {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j)) :
    ∃ C : ℝ,0<C ∧ ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁ : ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂ : ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      ∀ (R : Ideal O) (ν : ι→Ideal O→ℂ),(∀ j I,‖ν j I‖≤1)→
      ∀ (P : ι→ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j)→0<X₁→0<X₂→0<Y₁→0<Y₂→B₁≠0→B₂≠0→
      X₁*X₂=T→Y₁*Y₂=T→∀ S : Finset (Tuple ι),
      (∑v∈S,‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖)≤
        (C*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)*
          (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏j,P j) := by
  choose D hD hbound hz hs using fun j =>
    smooth_annular_bound (Wslot j) (a j) (b j) (ha j) (hsSlot j) (hWslot j)
  let C₀ := 2*128^(Fintype.card ι+2)*(∏j,D j)*(∏j,b j)*b₁*b₂
  have hprodD : 0≤∏j,D j := Finset.prod_nonneg (fun j _ => hD j)
  have hprodb : 0≤∏j,b j := Finset.prod_nonneg (fun j _ => hb j)
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  refine ⟨1+C₀,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hzW (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
      (hs : Function.support (W : ℝ→ℂ)⊆Set.Icc a b) : W 0=0 := by
    by_contra hn
    exact (not_le_of_gt ha) (hs hn).1
  have hm := profile_mass_explicit Wslot W₁ W₂ b D b₁ b₂
    (SchwartzMap.seminorm ℝ 0 0 W₁) (SchwartzMap.seminorm ℝ 0 0 W₂)
    hb hb₁ hb₂ hD (apply_nonneg _ _) (apply_nonneg _ _) hz
    (hzW W₁ a₁ b₁ ha₁ hs₁) (hzW W₂ a₂ b₂ ha₂ hs₂) hs
    (fun x hx => (hs₁ hx).2) (fun x hx => (hs₂ hx).2) hbound
    (SchwartzMap.norm_le_seminorm ℝ W₁) (SchwartzMap.norm_le_seminorm ℝ W₂)
    R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hprodP : 0≤∏j,P j := Finset.prod_nonneg (fun j _ => (hP j).le)
  have hpos : 0≤SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂*
      (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏j,P j) := by positivity
  apply hm.trans
  have hh := mul_le_mul_of_nonneg_right (show C₀≤1+C₀ by linarith) hpos
  dsimp only [C₀] at hh
  nlinarith only [hh]
end SevenEighths.CenteredMomentSourceProfileMassUniform

end

end OAI

end Source989

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceSupportedTailUniform.lean; sha256: 0573649eccfe69cf5f1c82130ac595e3c0176a32d24179198cebbd3174559c6b -/
section Source990
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceSupportedTailUniform
open ActualEisensteinCubic HeckeFamily CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentFirstTailAggregate CenteredMomentFirstScale
open CenteredMomentSupportedTailAggregate CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceRow CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

theorem source_first_discarded_energy_bound {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j))
    (Adec : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (sΦ : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁ : ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂ : ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : ι → Ideal O → ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple ι)) (Φ : 𝓢(ℝ,ℂ)) (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      ((∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)≤Real.exp HN*X) →
      (∀ I : supportedColumns (finiteColumns S),∀ J : supportedColumns (finiteColumns S),
        finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0 →
        finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) J≠0 →
        ∀ E∈inactiveSubsets I J,firstNominalScale I J (∏ P∈E,P.val) K X≤Tsec) →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖discardedEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s))
        Φ K Tsec Z ξ‖ ≤
      ((T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j))^2*
        (Real.exp HN*X)^ε*K*(C*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*
          sΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨D,hD,hmass⟩ := CenteredMomentSourceProfileMassUniform.profile_mass_uniform
    Wslot a b a₁ b₁ a₂ b₂ ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hWslot
  obtain ⟨sΦ,C,hC,htail⟩ := first_discarded_energy_bound Adec ε hε
  refine ⟨sΦ,D^2*C,mul_pos (sq_pos_of_pos hD) hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY
    S Φ K X HN Tsec Z Csec ξ hK hXX hZ hCs hN hsec hthreshold
  let Dprofile := D*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hm := (finiteColumnCoefficient_mass S β).trans
    (hmass W₁ W₂ hs₁ hs₂ R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S)
  have hz (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
      (hs : Function.support W⊆Set.Icc a b) : W 0=0 := by
    by_contra hn
    exact (not_le_of_gt ha) (hs hn).1
  have hNN (I : Ideal O) (_hI : I∈finiteColumns S)
      (hn : finiteColumnCoefficient S β I≠0) : (Ideal.absNorm I:ℝ)≤Real.exp HN*X := by
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    have hh := profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂
      X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY
      (fun j=>hz (Wslot j) (a j) (b j) (ha j) (hsSlot j))
      (hz W₁ a₁ b₁ ha₁ hs₁) (hz W₂ a₂ b₂ ha₂ hs₂)
      (fun j x hx=>(hsSlot j hx).2) (fun x hx=>(hs₁ hx).2)
      (fun x hx=>(hs₂ hx).2) v hv0
    rw [←he]
    exact hh.2.trans hN
  have ht := htail η m A t (finiteColumns S) (finiteColumnCoefficient S β) Φ K X HN Tsec Z Csec ξ
    hK hXX hZ hCs hNN hsec hthreshold
  apply ht.trans
  have hsq := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hm 2
  calc
    _ ≤ (Dprofile*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j))^2*
        (Real.exp HN*X)^ε*K*(C*sΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hK.le
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg (by positivity) _)
    _ = _ := by dsimp [Dprofile]; ring

theorem source_second_discarded_energy_bound {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j))
    (Adec : ℕ) :
    ∃ (sΦ : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁ : ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂ : ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      ∀ (η : Character) (t : ℝ) (R : Ideal O) (ν : ι → Ideal O → ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple ι)) (Φ : 𝓢(ℝ,ℂ)) (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      ((∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)≤Real.exp HN*X) →
      X^2/K≤Tsec →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖secondDiscardedEnergy η t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s))
        Φ K Tsec Z ξ‖ ≤
      ((T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j))^2*
        K*(Real.exp HN*X)^2*(C*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*
          sΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨D,hD,hmass⟩ := CenteredMomentSourceProfileMassUniform.profile_mass_uniform
    Wslot a b a₁ b₁ a₂ b₂ ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hWslot
  obtain ⟨sΦ,C,hC,htail⟩ := second_discarded_energy_bound Adec
  refine ⟨sΦ,D^2*C,mul_pos (sq_pos_of_pos hD) hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ η t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY
    S Φ K X HN Tsec Z Csec ξ hK hXX hZ hCs hN hsec hthreshold
  let Dprofile := D*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hm := (finiteColumnCoefficient_mass S β).trans
    (hmass W₁ W₂ hs₁ hs₂ R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S)
  have hz (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
      (hs : Function.support W⊆Set.Icc a b) : W 0=0 := by
    by_contra hn
    exact (not_le_of_gt ha) (hs hn).1
  have hNN (I : Ideal O) (_hI : I∈finiteColumns S)
      (hn : finiteColumnCoefficient S β I≠0) : (Ideal.absNorm I:ℝ)≤Real.exp HN*X := by
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    have hh := profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂
      X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY
      (fun j=>hz (Wslot j) (a j) (b j) (ha j) (hsSlot j))
      (hz W₁ a₁ b₁ ha₁ hs₁) (hz W₂ a₂ b₂ ha₂ hs₂)
      (fun j x hx=>(hsSlot j hx).2) (fun x hx=>(hs₁ hx).2)
      (fun x hx=>(hs₂ hx).2) v hv0
    rw [←he]
    exact hh.2.trans hN
  have ht := htail η t (finiteColumns S) (finiteColumnCoefficient S β) Φ K X HN Tsec Z Csec ξ
    hK hXX hZ hCs hNN hsec hthreshold
  apply ht.trans
  have hsq := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hm 2
  calc
    _ ≤ (Dprofile*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j))^2*
        K*(Real.exp HN*X)^2*(C*sΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hsq hK.le
    _ = _ := by dsimp [Dprofile]; ring

end SevenEighths.CenteredMomentSourceSupportedTailUniform

end

end OAI

end Source990

/- Original source: OAI/NumberTheory/DirichletL/Moments/OriginalRadialTail.lean; sha256: 851b11d1e74816a8ac27cf0da92e9303e90f02a2d1563c4a557889615a3cc54d -/
section Source991
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentOriginalRadialTail
open HeckeFamily ConcreteTraceCRT CenteredMomentAbsoluteEnergy
open CenteredMomentPositiveSummability CenteredMomentOriginalRadialComparison
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

def tailControl (A : ℕ) (Φ : 𝓢(ℝ,ℂ)) : ℝ :=
  (2:ℝ)^(A+2)*(Finset.Iic (A+2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ

lemma cauchy_all (K : ℝ) (hK : 0<K) :
    (∑'z:O,((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹)≤4*(1+Real.pi)^2*max 1 K := by
  by_cases hk : 1≤K
  · have hh:=scaled_eisenstein_cauchy_small K⁻¹ (inv_pos.mpr hK) (inv_le_one_of_one_le₀ hk)
    rw [max_eq_right hk]
    have he : K*(K⁻¹*(∑'z:O,((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹))=
        ∑'z:O,((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹ := by rw [←mul_assoc,mul_inv_cancel₀ hK.ne',one_mul]
    have hb:=mul_le_mul_of_nonneg_left hh hK.le
    rw [he] at hb
    simpa only [mul_comm K] using hb
  · have hk' : K≤1:=(not_le.mp hk).le
    have hi : 1≤K⁻¹:=(one_le_inv₀ hK).mpr hk'
    have hs:=scaled_eisenstein_cauchy_summable K⁻¹ (inv_pos.mpr hK)
    have hh:=hs.tsum_le_tsum (g:=fun z:O=>((1+1*‖eisEmbedding z‖^2)^2)⁻¹) (fun z=>by
      apply inv_anti₀ (by positivity)
      gcongr)
      (scaled_eisenstein_cauchy_summable 1 (by norm_num))
    have hb:=scaled_eisenstein_cauchy_small 1 (by norm_num) (by norm_num)
    rw [max_eq_left hk',mul_one]
    exact hh.trans (by simpa only [one_mul] using hb)

lemma tail_pointwise (A : ℕ) (Φ : 𝓢(ℝ,ℂ)) (x r : ℝ) (hr : 0≤r) (hx : r≤x) :
    ‖Φ x‖≤tailControl A Φ*((1+r)^A)⁻¹*((1+x)^2)⁻¹ := by
  have hxp : 0≤x:=hr.trans hx
  have hh:=SchwartzMap.one_add_le_sup_seminorm_apply (𝕜:=ℝ)
    (m:=(A+2,0)) (k:=A+2) (n:=0) le_rfl le_rfl Φ x
  simp only [norm_iteratedFDeriv_zero,Real.norm_of_nonneg hxp] at hh
  change (1+x)^(A+2)*‖Φ x‖≤tailControl A Φ at hh
  have hp : (1+r)^A≤(1+x)^A:=pow_le_pow_left₀ (by positivity) (by linarith) A
  have hb : (1+r)^A*((1+x)^2*‖Φ x‖)≤tailControl A Φ := by
    apply (mul_le_mul_of_nonneg_right hp (by positivity)).trans
    simpa only [pow_add,mul_assoc] using hh
  have hd : 0<(1+r)^A*(1+x)^2:=by positivity
  rw [show tailControl A Φ*((1+r)^A)⁻¹*((1+x)^2)⁻¹=
    tailControl A Φ/((1+r)^A*(1+x)^2) by field_simp]
  exact (le_div_iff₀ hd).mpr (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hb)

theorem actual_radial_tail (A : ℕ) (F : O→ℂ) (B : ℝ) (hF : ∀z,‖F z‖≤B)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) (hR : 0≤R) :
    radialEnergy F (fun z=>keep z ∧ R<‖eisEmbedding z‖^2) Φ K≤
      4*(1+Real.pi)^2*tailControl A Φ*B^2*max 1 K*((1+R/K)^A)⁻¹ := by
  let C:=tailControl A Φ*B^2*((1+R/K)^A)⁻¹
  have hC : 0≤C:=by dsimp [C,tailControl];positivity
  have hs:=bounded_radial_summable F B hF (fun z=>keep z ∧ R<‖eisEmbedding z‖^2) Φ K hK
  have hp (z:O) :
      (if keep z ∧ R<‖eisEmbedding z‖^2 then ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0)
      ≤C*((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹ := by
    split_ifs with hz
    · have ht:=tail_pointwise A Φ (‖eisEmbedding z‖^2/K) (R/K)
        (div_nonneg hR hK.le) (div_le_div_of_nonneg_right hz.2.le hK.le)
      have hf:=pow_le_pow_left₀ (norm_nonneg _) (hF z) 2
      have hh:=(mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        (mul_le_mul hf ht (norm_nonneg _) (sq_nonneg B))
      convert hh using 1 ; dsimp [C] ; simp only [div_eq_mul_inv] ; ring
    · exact mul_nonneg hC (by positivity)
  have hb:=Summable.tsum_le_tsum hp (hs.congr (fun z=>by by_cases hz:keep z ∧ R<‖eisEmbedding z‖^2 <;> simp [hz])) ((scaled_eisenstein_cauchy_summable K⁻¹ (inv_pos.mpr hK)).mul_left C)
  rw [tsum_mul_left] at hb
  have hh:=mul_le_mul_of_nonneg_left (cauchy_all K hK) hC
  have hh' : C*(∑'z:O,((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹)≤
      4*(1+Real.pi)^2*tailControl A Φ*B^2*max 1 K*((1+R/K)^A)⁻¹ := by
    convert hh using 1 ; dsimp [C] ; ring
  convert hb.trans hh' using 1
  unfold radialEnergy
  apply tsum_congr
  intro z
  by_cases hz:keep z ∧ R<‖eisEmbedding z‖^2 <;> simp [hz]

lemma actual_radial_split (F : O→ℂ) (B : ℝ) (hF : ∀z,‖F z‖≤B)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    radialEnergy F keep Φ K=
      radialEnergy F (fun z=>keep z ∧ ‖eisEmbedding z‖^2≤R) Φ K+
      radialEnergy F (fun z=>keep z ∧ R<‖eisEmbedding z‖^2) Φ K := by
  unfold radialEnergy
  rw [←Summable.tsum_add (bounded_radial_summable F B hF _ Φ K hK)
    (bounded_radial_summable F B hF _ Φ K hK)]
  apply tsum_congr
  intro z
  by_cases hk:keep z
  · by_cases hr:‖eisEmbedding z‖^2≤R
    · simp [hk,hr,not_lt.mpr hr]
    · simp [hk,hr,not_le.mp hr]
  · simp [hk]

theorem actual_positive_row_tail {ι:Type*} [Fintype ι] [DecidableEq ι]
    (order:ℕ) (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤b₁) (hb₂:0≤b₂) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂) (hW₁:∀x,‖W₁ x‖≤B₁) (hW₂:∀x,‖W₂ x‖≤B₂)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b B:ι→ℝ)
    (hP:∀i,0<P i) (hb:∀i,0≤b i) (hB:∀i,0≤B i)
    (hβ:∀i,∀I∈S i,‖β i I‖≤B i)
    (hN:∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K R:ℝ) (hK:0<K) (hR:0≤R) :
    radialEnergy (fun z=>CenteredMomentRetainedEnergy.positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂)
      (fun z=>keep z ∧ R<‖eisEmbedding z‖^2) Φ K≤
      4*(1+Real.pi)^2*tailControl order Φ*
        (((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i))*
        max 1 K*((1+R/K)^order)⁻¹ := by
  let E:=((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i)
  have hE:0≤E:=mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hX₁.le hX₂.le)
    (Finset.prod_nonneg (fun i _=>(hP i).le)))
  have hp (z:O):‖CenteredMomentRetainedEnergy.positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2≤E:=
    CenteredMomentInductionEnergy.positive_squared_absolute η m A z t W₁ W₂
      b₁ b₂ B₁ B₂ X₁ X₂ hb₁ hb₂ hB₁ hB₂ hX₁ hX₂ hs₁ hs₂ hW₁ hW₂
      S β P b B hP hb hB hβ hN
  have hh:=actual_radial_tail order _ (Real.sqrt E)
    (fun z=>Real.le_sqrt_of_sq_le (hp z)) keep Φ K R hK hR
  simpa only [Real.sq_sqrt hE] using hh

end SevenEighths.CenteredMomentOriginalRadialTail

end

end OAI

end Source991

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalRadialCutoff.lean; sha256: 230a06100e9b4b782da7e81d5e5a07b07f63244e66f76c21b15919e99f327217 -/
section Source992
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentNaturalRadialCutoff
open HeckeFamily ConcreteTraceCRT CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialTail CenteredMomentOriginalRadialComparison
local notation "O" => HeckeFamily.O

lemma retained_conductor (η:Character) (Z m q xi Ck K:ℝ) (hZ:0<Z) (hCk:0≤Ck)
    (hη:(η.modulus.absNorm:ℝ)≤Z^m) (hK:K≤Ck*Z^q)
    (z:O) (hz:z≠0) (hrow:‖eisEmbedding z‖^2≤K*Z^xi) :
    ((naturalRow η z hz).character.modulus.absNorm:ℝ)≤
      (fixedConductorFactor:ℝ)*Ck*Z^(m+q+xi) := by
  have hn:((Ideal.span {z}).absNorm:ℝ)≤Ck*Z^(q+xi) := by
    rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    apply hrow.trans
    have hh:=mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hZ.le xi)
    simpa only [Real.rpow_add hZ,mul_assoc] using hh
  have hh:=(naturalRow η z hz).modulus_power_bound Z m (q+xi) Ck hZ hCk hη hn
  simpa only [add_assoc] using hh

lemma reciprocal_cutoff_bound (Z xi:ℝ) (order:ℕ) (hZ:0<Z) :
    ((1+Z^xi)^order)⁻¹≤Z^(-xi*(order:ℝ)) := by
  have hp : (Z^xi)^order≤(1+Z^xi)^order:=
    pow_le_pow_left₀ (Real.rpow_nonneg hZ.le _) (by linarith) order
  have hh:=inv_anti₀ (pow_pos (Real.rpow_pos_of_pos hZ _) _) hp
  have he : (Z^xi)^order=Z^(xi*(order:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  apply hh.trans_eq
  rw [he,←Real.rpow_neg hZ.le]
  congr 1
  ring

theorem actual_tail_arbitrary_saving (xi saving mass : ℝ) (hxi:0<xi) :
    ∃order:ℕ,∀(F:O→ℂ)(B:ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K Z:ℝ),
      (∀z,‖F z‖≤B) → 0<K → 1≤Z → B^2*max 1 K≤Z^mass →
      radialEnergy F (fun z=>keep z ∧ K*Z^xi<‖eisEmbedding z‖^2) Φ K≤
        (4*(1+Real.pi)^2*tailControl order Φ)*Z^(-saving) := by
  obtain ⟨order,horder⟩:=exists_nat_ge ((mass+saving)/xi)
  have ho:mass-xi*(order:ℝ)≤-saving := by
    have hh:mass+saving≤(order:ℝ)*xi:=(div_le_iff₀ hxi).mp horder
    linarith
  refine ⟨order,?_⟩
  intro F B keep Φ K Z hF hK hZ hmass
  have hz:0<Z:=by linarith
  have hh:=actual_radial_tail order F B hF keep Φ K (K*Z^xi) hK (by positivity)
  have hdiv:K*Z^xi/K=Z^xi:=by field_simp
  rw [hdiv] at hh
  have hc:0≤4*(1+Real.pi)^2*tailControl order Φ:=by unfold tailControl;positivity
  have hb:(B^2*max 1 K)*((1+Z^xi)^order)⁻¹≤Z^(-saving) := by
    calc
      _≤Z^mass*Z^(-xi*(order:ℝ)) :=
        mul_le_mul hmass (reciprocal_cutoff_bound Z xi order hz) (by positivity) (Real.rpow_nonneg hz.le _)
      _=Z^(mass-xi*(order:ℝ)) := by rw [←Real.rpow_add hz];congr 1;ring
      _≤Z^(-saving):=Real.rpow_le_rpow_of_exponent_le hZ ho
  apply hh.trans
  convert mul_le_mul_of_nonneg_left hb hc using 1 ; ring

end SevenEighths.CenteredMomentNaturalRadialCutoff

end

end OAI

end Source992

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceInputTailUniform.lean; sha256: 8fcb50b40c604b4331ee14b0096857a1a11d0f9582e864647976d37b4b7fb1ff -/
section Source993
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputTailUniform
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMassUniform CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentNaturalRadialCutoff
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def plainControl (s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)):ℝ:=
  (∏i,s.M i)*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂

omit [DecidableEq ι] in
lemma plainControl_nonneg (s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)):0≤plainControl s W₁ W₂:=by
  unfold plainControl
  exact mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun i _=>(s.M_ge_one i).trans' zero_le_one))
    (apply_nonneg _ _)) (apply_nonneg _ _)

omit [DecidableEq ι] in
lemma volume_pos (s:Input ι):0<volume s.toData:=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

omit [DecidableEq ι] in
theorem input_mass (hi:ι→ℝ)(whi:ℝ)(hhi:∀i,0≤hi i)(hwhi:0≤whi)
    (s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ))(wlo:ℝ)(hwlo:0<wlo)
    (he₁:s.W₁=W₁)(he₂:s.W₂=W₂)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hshi:∀i,s.hi i≤hi i)(R seed:Ideal O):
    (∑I∈finiteColumns (Fintype.piFinset s.pools),‖coefficient s R seed I‖)≤
      (2*128^(Fintype.card ι+2)*(∏i,hi i)*whi^2)*plainControl s W₁ W₂*volume s.toData:=by
  have hz (i:ι):s.W i 0=0:=by
    by_contra hn
    exact (not_le_of_gt (s.lo_pos i)) (s.support i hn).1
  have hzW (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (hs hn).1
  have hm:=profile_mass_explicit s.W W₁ W₂ hi s.M whi whi
    (SchwartzMap.seminorm ℝ 0 0 W₁) (SchwartzMap.seminorm ℝ 0 0 W₂)
    hhi hwhi hwhi (fun i=>zero_le_one.trans (s.M_ge_one i))
    (apply_nonneg _ _) (apply_nonneg _ _) hz (hzW W₁ hs₁) (hzW W₂ hs₂)
    (fun i x hx=>((s.support i hx).2).trans (hshi i))
    (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2) s.W_bound
    (SchwartzMap.norm_le_seminorm ℝ W₁) (SchwartzMap.norm_le_seminorm ℝ W₂)
    R s.ν s.ν_bound s.P s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed
    s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero
    rfl s.same_product (Fintype.piFinset s.pools)
  have hc:=finiteColumnCoefficient_mass (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P W₁ W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  unfold coefficient
  rw [he₁,he₂]
  change (∑I∈_,‖finiteColumnCoefficient _ _ I‖)≤_
  apply (hc.trans hm).trans_eq
  simp only [map_one,Nat.cast_one,one_mul,div_one,plainControl,volume]
  ring

omit [DecidableEq ι] in
lemma input_column_bound (hi:ι→ℝ)(whi:ℝ)
    (s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ))(wlo:ℝ)(hwlo:0<wlo)
    (he₁:s.W₁=W₁)(he₂:s.W₂=W₂)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hshi:∀i,s.hi i≤hi i)(R seed I:Ideal O)(hn:coefficient s R seed I≠0):
    (Ideal.absNorm I:ℝ)≤((∏i,hi i)*whi^2)*volume s.toData:=by
  obtain ⟨v,hv,hv0,hvI⟩:=finiteColumnCoefficient_witness _ _ I hn
  have hz (i:ι):s.W i 0=0:=by
    by_contra h
    exact (not_le_of_gt (s.lo_pos i)) (s.support i h).1
  have hzW (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra h
    exact (not_le_of_gt hwlo) (hs h).1
  unfold coefficient at hn
  rw [he₁,he₂] at hv0
  have hp:=profileCoefficient_product_bound R s.ν s.W s.P hi W₁ W₂ whi whi
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed
    s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero rfl s.same_product
    hz (hzW W₁ hs₁) (hzW W₂ hs₂) (fun i x hx=>((s.support i hx).2).trans (hshi i))
    (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2) v hv0
  rw [hvI] at hp
  apply hp.2.trans_eq
  simp only [map_one,Nat.cast_one,one_mul,div_one,volume]
  ring

lemma kernel_inverse_cap (HN Z B Tsec:ℝ)(hZ:1≤Z)(hB:0≤B)(hT:0<Tsec)(hcap:Tsec≤Z^B):
    ((min 1 (kernelReference Tsec HN))^2)⁻¹≤
      (1+Real.exp (2*HN))^2*(Z^B)^2:=by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hpow:1≤Z^B:=Real.one_le_rpow hZ hB
  have he:0<Real.exp (2*HN):=Real.exp_pos _
  have hb:(min 1 (kernelReference Tsec HN))⁻¹≤(1+Real.exp (2*HN))*Z^B:=by
    rw [min_def]
    split_ifs with h
    · simp only [inv_one]
      nlinarith
    · have hi:(kernelReference Tsec HN)⁻¹=Tsec*Real.exp (2*HN):=by
        unfold kernelReference
        rw [show -2*HN= -(2*HN) by ring,Real.exp_neg]
        field_simp
      rw [hi]
      calc
        _≤Z^B*Real.exp (2*HN):=mul_le_mul_of_nonneg_right hcap he.le
        _≤_:=by nlinarith [Real.rpow_pos_of_pos hz B]
  rw [←inv_pow]
  exact (pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt (lt_min zero_lt_one (kernelReference_pos Tsec HN hT)))) hb 2).trans_eq (mul_pow _ _ _)

lemma eventually_tail_threshold (HN ξ:ℝ)(hξ:0<ξ):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ 2*HN/Real.log Z+Real.log (4:ℝ)/Real.log Z<ξ/4:=by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop ((2*HN+Real.log (4:ℝ))/(ξ/4)))] with Z hZ hlog
  refine ⟨hZ,?_⟩
  rw [←add_div]
  apply (div_lt_iff₀ (Real.log_pos hZ)).mpr
  have ht:0<ξ/4:=by linarith
  have hh:2*HN+Real.log (4:ℝ)<Real.log Z*(ξ/4):=(div_lt_iff₀ ht).mp hlog
  nlinarith

lemma choose_tail_order (B ξ saving:ℝ)(hB:0≤B)(hξ:0<ξ):
    ∃Adec:ℕ,∀(HN Z V Tsec:ℝ),1≤Z→0<V→V≤Z^B→0<Tsec→Tsec≤Z^B→
      V^3*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹≤
        (1+Real.exp (2*HN))^2*Z^(-saving):=by
  obtain ⟨Adec,hAdec⟩:=exists_nat_ge ((5*B+saving)/(ξ/4))
  have horder:5*B-(ξ/4)*(Adec:ℝ)≤-saving:=by
    have hh:5*B+saving≤(Adec:ℝ)*(ξ/4):=(div_le_iff₀ (by linarith:0<ξ/4)).mp hAdec
    linarith
  refine ⟨Adec,?_⟩
  intro HN Z V Tsec hZ hV hVcap hT hTcap
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hk:=kernel_inverse_cap HN Z B Tsec hZ hB hT hTcap
  have hd:=reciprocal_cutoff_bound Z (ξ/4) Adec hz
  calc
    _≤(Z^B)^3*((1+Real.exp (2*HN))^2*(Z^B)^2)*Z^(-(ξ/4)*(Adec:ℝ)):=by
      apply mul_le_mul _ hd (by positivity) (by positivity)
      apply mul_le_mul (pow_le_pow_left₀ hV.le hVcap 3) hk
        (inv_nonneg.mpr (sq_nonneg _)) (by positivity)
    _=(1+Real.exp (2*HN))^2*Z^(5*B-(ξ/4)*(Adec:ℝ)):=by
      rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le]
      norm_num only [Nat.cast_ofNat]
      rw [show Z^(B*(3:ℝ))*((1+Real.exp (2*HN))^2*Z^(B*(2:ℝ)))*Z^(-(ξ/4)*(Adec:ℝ))=
        (1+Real.exp (2*HN))^2*(Z^(B*3)*Z^(B*2)*Z^(-(ξ/4)*(Adec:ℝ))) by ring]
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
      congr 2
      ring
    _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ horder) (sq_nonneg _)

omit [DecidableEq ι] in
theorem second_input_tail_arbitrary_saving (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K Tsec:ℝ),
      0<K→volume s.toData≤Z^B→Tsec≤Z^B→(volume s.toData)^2/K≤Tsec→
      ‖secondDiscardedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K Tsec Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Adec,hdecay⟩:=choose_tail_order B ξ saving hB hξ
  obtain ⟨SΦ,Ctail,hCtail,htail⟩:=second_discarded_energy_bound Adec
  let Cmass:=1+2*128^(Fintype.card ι+2)*(∏i,hi i)*whi^2
  have hprodhi:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hCmass:0<Cmass:=by dsimp [Cmass];positivity
  let HN:=Real.log (max 1 ((∏i,hi i)*whi^2))
  have hexp:(∏i,hi i)*whi^2≤Real.exp HN:=by
    dsimp [HN]
    rw [Real.exp_log (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  let C:=Cmass^2*Ctail*(Real.exp HN)^2*(1+Real.exp (2*HN))^2
  refine ⟨SΦ,C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_tail_threshold HN ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi R seed Φ K Tsec hK hVcap hTcap hnom
  let V:=volume s.toData
  have hV:0<V:=volume_pos s
  have hT:0<Tsec:=(div_pos (sq_pos_of_pos hV) hK).trans_le hnom
  have hmass:=input_mass hi whi hhi hwhi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed
  have hcontrol:=plainControl_nonneg s W₁ W₂
  have hm:(∑I∈finiteColumns (Fintype.piFinset s.pools),‖coefficient s R seed I‖)≤
      Cmass*plainControl s W₁ W₂*V:=by
    apply hmass.trans
    apply mul_le_mul_of_nonneg_right _ hV.le
    apply mul_le_mul_of_nonneg_right _ hcontrol
    dsimp [Cmass]
    linarith
  have hn (I:Ideal O)(_hI:I∈finiteColumns (Fintype.piFinset s.pools))
      (hI:coefficient s R seed I≠0):(Ideal.absNorm I:ℝ)≤Real.exp HN*V:=
    (input_column_bound hi whi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed I hI).trans
      (mul_le_mul_of_nonneg_right hexp hV.le)
  have ht:=htail s.η s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)
    Φ K V HN Tsec Z 1 ξ hK hV hZ.1 le_rfl hn hnom (by simpa using hZ.2)
  have hsquare:=pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hm 2
  have hp:0<min 1 (kernelReference Tsec HN):=lt_min zero_lt_one (kernelReference_pos _ _ hT)
  have hzpos:0<Z:=zero_lt_one.trans hZ.1
  have hzpower:0<Z^(ξ/4):=Real.rpow_pos_of_pos hzpos _
  have hden:0<(min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec:=by positivity
  have hb:=hdecay HN Z V Tsec hZ.1.le hV hVcap hT hTcap
  calc
    _≤((Cmass*plainControl s W₁ W₂*V)^2*K*(Real.exp HN*V)^2*
        (Ctail*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec))/V:=by
      apply div_le_div_of_nonneg_right _ hV.le
      apply ht.trans
      apply div_le_div_of_nonneg_right _ hden.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hsquare hK.le
    _=(Cmass^2*Ctail*(Real.exp HN)^2*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        (V^3*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹):=by
      field_simp [ne_of_gt hV,ne_of_gt hp]
    _≤(Cmass^2*Ctail*(Real.exp HN)^2*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        ((1+Real.exp (2*HN))^2*Z^(-saving)):=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _=_:=by dsimp [C];ring

end SevenEighths.CenteredMomentSourceInputTailUniform

end

end OAI

end Source993

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceInputZeroUniform.lean; sha256: 4a27009304866229653bdab8d81aa914e479195a350d38f88c39a57994b401f8 -/
section Source994
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceInputZeroUniform
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMass CenteredMomentSourceInputTailUniform
open CenteredMomentFirstLocalization EisensteinSchwartzPoisson
open CenteredMomentExceptionalAmplitudePair CenteredMomentAddedZeroUniform
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
theorem first_input_zero_bound (hi:ι→ℝ)(wlo whi ε:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(_hwhi:0≤whi)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0≤K→
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*K*‖paperRadialFourier Φ 0‖*(volume s.toData)^ε:=by
  obtain ⟨C₀,hC₀,hbound⟩:=active_tuple_zero_energy_bound (Fintype.card ι) ε hε
  let L:=1+(∏i,hi i)*whi^2
  have hprod:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hL:0<L:=by dsimp [L];positivity
  refine ⟨4*C₀*L^(1+ε),by positivity,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK
  let V:=volume s.toData
  have hV:0<V:=volume_pos s
  let β:=profileCoefficient R s.ν s.W s.P W₁ W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed
  have hc:coefficient s R seed=finiteColumnCoefficient (Fintype.piFinset s.pools) β:=by
    unfold coefficient;rw [he₁,he₂]
  have hcontrol:=plainControl_nonneg s W₁ W₂
  have hβ (v:Tuple ι):‖β v‖≤2*plainControl s W₁ W₂:=by
    have hb:=profileCoefficient_norm_le R s.ν s.ν_bound s.W s.P s.M W₁ W₂
      (SchwartzMap.seminorm ℝ 0 0 W₁) (SchwartzMap.seminorm ℝ 0 0 W₂)
      (fun i=>zero_le_one.trans (s.M_ge_one i)) (apply_nonneg _ _) (apply_nonneg _ _)
      s.W_bound (SchwartzMap.norm_le_seminorm ℝ W₁) (SchwartzMap.norm_le_seminorm ℝ W₂)
      s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v
    exact hb.trans_eq (by dsimp [plainControl];ring)
  have hz (i:ι):s.W i 0=0:=by
    by_contra hn
    exact (not_le_of_gt (s.lo_pos i)) (s.support i hn).1
  have hzW (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (hs hn).1
  have hN (v:Tuple ι)(hv:β v≠0):finiteTupleProduct v≠0 ∧
      (Ideal.absNorm (finiteTupleProduct v):ℝ)≤L*V:=by
    have hp:=profileCoefficient_product_bound R s.ν s.W s.P hi W₁ W₂ whi whi
      s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed
      s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero rfl s.same_product
      hz (hzW W₁ hs₁) (hzW W₂ hs₂) (fun i x hx=>((s.support i hx).2).trans (hshi i))
      (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2) v hv
    refine ⟨hp.1,hp.2.trans ?_⟩
    simp only [map_one,Nat.cast_one,one_mul,div_one]
    change (∏i,hi i)*whi*whi*(s.X₁*s.X₂)*(∏i,s.P i)≤_
    have hh:0≤V:=hV.le
    dsimp [L,V,volume] at *
    nlinarith
  rw [hc]
  by_cases hsmall:L*V<1
  · rw [zeroEnergy_eq_zero_of_subunit s.η m A s.t (Fintype.piFinset s.pools) β Φ K
      (L*V) hsmall (fun v _ hv=>hN v hv),norm_zero,zero_div]
    positivity
  have hb:=hbound (le_refl (Fintype.card ι)) s.η m A s.t (Fintype.piFinset s.pools) β Φ
    (L*V) K (2*plainControl s W₁ W₂) (le_of_not_gt hsmall) hK (by positivity)
    (fun v _ _=>hβ v) (fun I _ hI=>by
      obtain ⟨v,hv,hn,he⟩:=finiteColumnCoefficient_witness _ _ I hI
      rw [←he];exact (hN v hn).2)
  apply (div_le_div_of_nonneg_right hb hV.le).trans_eq
  have hp:(L*V)^(1+ε)/V=L^(1+ε)*V^ε:=by
    rw [Real.mul_rpow hL.le hV.le,Real.rpow_add hV,Real.rpow_one]
    field_simp
  change C₀*K*(2*plainControl s W₁ W₂)^2*‖paperRadialFourier Φ 0‖*(L*V)^(1+ε)/V=_
  calc
    _=4*C₀*(plainControl s W₁ W₂)^2*K*‖paperRadialFourier Φ 0‖*((L*V)^(1+ε)/V):=by ring
    _=_:=by rw [hp];ring

omit [DecidableEq ι] in
theorem first_input_zero_uniform (hi:ι→ℝ)(wlo whi ε:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hε:0<ε):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0≤K→
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*
        (volume s.toData)^ε:=by
  obtain ⟨C₀,hC₀,hb⟩:=first_input_zero_bound hi wlo whi ε hhi hwlo hwhi hε
  obtain ⟨SΦ,D,hD,hd⟩:=paperRadialFourier_euler_source_weighted_bound 0 0
  refine ⟨SΦ,C₀*D,mul_pos hC₀ hD,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK
  have hf:‖paperRadialFourier Φ 0‖≤D*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ:=by
    simpa only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,pow_zero,one_mul,zero_mul] using
      hd Φ 0 le_rfl 0 le_rfl
  have hVp:0≤(volume s.toData)^ε:=Real.rpow_nonneg (volume_pos s).le _
  apply (hb s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK).trans
  calc
    _≤C₀*(plainControl s W₁ W₂)^2*K*(D*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)*
        (volume s.toData)^ε:=by gcongr
    _=_:=by ring

omit [DecidableEq ι] in
theorem first_input_zero_capped (hi:ι→ℝ)(wlo whi B ε:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀Z:ℝ,1≤Z→
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→volume s.toData≤Z^B→
      ∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0≤K→
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε:=by
  let δ:=ε/(B+1)
  have hδ:0<δ:=div_pos hε (by linarith)
  obtain ⟨SΦ,C,hC,hb⟩:=first_input_zero_uniform hi wlo whi δ hhi hwlo hwhi hδ
  refine ⟨SΦ,C,hC,?_⟩
  intro Z hZ s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hV m A R seed Φ K hK
  have hp:(volume s.toData)^δ≤Z^ε:=by
    calc
      _≤(Z^B)^δ:=Real.rpow_le_rpow (volume_pos s).le hV hδ.le
      _=Z^(B*δ):=(Real.rpow_mul (zero_le_one.trans hZ) B δ).symm
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ (by
        have hh:δ*(B+1)=ε:=by dsimp [δ];field_simp
        nlinarith)
  exact (hb s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))

end SevenEighths.CenteredMomentSourceInputZeroUniform

end

end OAI

end Source994

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceInputFirstTailScale.lean; sha256: bfb4758a6423b4cfe08b0e19f84f51515144a0450e4e2f3a7ed6861a20ee2f2a -/
section Source995
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentSourceInputFirstTailUniform
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstScale
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

lemma common_subset_product_dvd_right (I J : Ideal O) (E : Finset (CommonIndex I J)) :
    (∏P∈E,P.val)∣commonPart J I := by
  apply (Finset.prod_dvd_prod_of_subset E Finset.univ
    (fun P : CommonIndex I J=>P.val) (Finset.subset_univ _)).trans
  rw [commonPart_right_product]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  simpa only [pow_one] using pow_dvd_pow P.val (rightExponent_pos I J P)

theorem first_nominal_scale_le (I J : Ideal O) (E : Finset (CommonIndex I J))
    (K X : ℝ) (hK : 0<K) :
    firstNominalScale I J (∏P∈E,P.val) K X≤X^2/K := by
  have hC := norm_pos (commonPart I J) (commonPart_ne_zero I J)
  have hD := norm_pos (commonPart J I) (commonPart_ne_zero J I)
  have hE : (Ideal.absNorm (∏P∈E,P.val):ℝ)≤Ideal.absNorm (commonPart J I) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero J I)))
      (map_dvd Ideal.absNorm (common_subset_product_dvd_right I J E))
  have hA : (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)≤Ideal.absNorm (commonPart I J) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J)))
      (map_dvd Ideal.absNorm (activeConductor_span_dvd I J))
  unfold firstNominalScale
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul hE hA (by positivity) hD.le) (sq_nonneg X))
    (mul_nonneg (mul_nonneg hK.le hC.le) hD.le)).trans_eq
  field_simp

end SevenEighths.CenteredMomentSourceInputFirstTailUniform

end

end OAI

end Source995

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceInputFirstTailUniform.lean; sha256: 32896927df2ea439f01fc10d3bb7d508524d67c5ce8e458a5e730638fcb0ca5b -/
section Source996
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputFirstTailUniform
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMassUniform CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentNaturalRadialCutoff
open CenteredMomentSourceInputTailUniform CenteredMomentFirstTailAggregate
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma choose_first_tail_order (B ξ saving:ℝ)(hB:0≤B)(hξ:0<ξ):
    ∃Adec:ℕ,∀(HN Z V Tsec:ℝ),1≤Z→0<V→V≤Z^B→0<Tsec→Tsec≤Z^B→
      V^2*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹≤
        (1+Real.exp (2*HN))^2*Z^(-saving):=by
  obtain ⟨Adec,hAdec⟩:=exists_nat_ge ((4*B+saving)/(ξ/4))
  have horder:4*B-(ξ/4)*(Adec:ℝ)≤-saving:=by
    have hh:4*B+saving≤(Adec:ℝ)*(ξ/4):=(div_le_iff₀ (by linarith:0<ξ/4)).mp hAdec
    linarith
  refine ⟨Adec,?_⟩
  intro HN Z V Tsec hZ hV hVcap hT hTcap
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hk:=kernel_inverse_cap HN Z B Tsec hZ hB hT hTcap
  have hd:=reciprocal_cutoff_bound Z (ξ/4) Adec hz
  calc
    _≤(Z^B)^2*((1+Real.exp (2*HN))^2*(Z^B)^2)*Z^(-(ξ/4)*(Adec:ℝ)):=by
      apply mul_le_mul _ hd (by positivity) (by positivity)
      apply mul_le_mul (pow_le_pow_left₀ hV.le hVcap 2) hk
        (inv_nonneg.mpr (sq_nonneg _)) (by positivity)
    _=(1+Real.exp (2*HN))^2*Z^(4*B-(ξ/4)*(Adec:ℝ)):=by
      rw [←Real.rpow_mul_natCast hz.le]
      norm_num only [Nat.cast_ofNat]
      rw [show Z^(B*(2:ℝ))*((1+Real.exp (2*HN))^2*Z^(B*(2:ℝ)))*Z^(-(ξ/4)*(Adec:ℝ))=
        (1+Real.exp (2*HN))^2*(Z^(B*2)*Z^(B*2)*Z^(-(ξ/4)*(Adec:ℝ))) by ring]
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
      congr 2
      ring
    _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ horder) (sq_nonneg _)

omit [DecidableEq ι] in
theorem first_input_tail_arbitrary_saving (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K Tsec:ℝ),
      0<K→volume s.toData≤Z^B→Tsec≤Z^B→(volume s.toData)^2/K≤Tsec→
      ‖discardedEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K Tsec Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Adec,hdecay⟩:=choose_first_tail_order B ξ saving hB hξ
  obtain ⟨SΦ,Ctail,hCtail,htail⟩:=first_discarded_energy_bound Adec 1 zero_lt_one
  let Cmass:=1+2*128^(Fintype.card ι+2)*(∏i,hi i)*whi^2
  have hprodhi:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hCmass:0<Cmass:=by dsimp [Cmass];positivity
  let HN:=Real.log (max 1 ((∏i,hi i)*whi^2))
  have hexp:(∏i,hi i)*whi^2≤Real.exp HN:=by
    dsimp [HN]
    rw [Real.exp_log (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  let C:=Cmass^2*Ctail*(Real.exp HN)*(1+Real.exp (2*HN))^2
  refine ⟨SΦ,C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_tail_threshold HN ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K Tsec hK hVcap hTcap hnom
  let V:=volume s.toData
  have hV:0<V:=volume_pos s
  have hT:0<Tsec:=(div_pos (sq_pos_of_pos hV) hK).trans_le hnom
  have hmass:=input_mass hi whi hhi hwhi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed
  have hcontrol:=plainControl_nonneg s W₁ W₂
  have hm:(∑I∈finiteColumns (Fintype.piFinset s.pools),‖coefficient s R seed I‖)≤
      Cmass*plainControl s W₁ W₂*V:=by
    apply hmass.trans
    apply mul_le_mul_of_nonneg_right _ hV.le
    apply mul_le_mul_of_nonneg_right _ hcontrol
    dsimp [Cmass]
    linarith
  have hn (I:Ideal O)(_hI:I∈finiteColumns (Fintype.piFinset s.pools))
      (hI:coefficient s R seed I≠0):(Ideal.absNorm I:ℝ)≤Real.exp HN*V:=
    (input_column_bound hi whi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed I hI).trans
      (mul_le_mul_of_nonneg_right hexp hV.le)
  have ht:=htail s.η m A s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)
    Φ K V HN Tsec Z 1 ξ hK hV hZ.1 le_rfl hn
    (fun I J _ _ E _=>(first_nominal_scale_le I J E K V hK).trans hnom) (by simpa using hZ.2)
  simp only [Real.rpow_one] at ht
  have hsquare:=pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hm 2
  have hp:0<min 1 (kernelReference Tsec HN):=lt_min zero_lt_one (kernelReference_pos _ _ hT)
  have hzpos:0<Z:=zero_lt_one.trans hZ.1
  have hzpower:0<Z^(ξ/4):=Real.rpow_pos_of_pos hzpos _
  have hden:0<(min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec:=by positivity
  have hb:=hdecay HN Z V Tsec hZ.1.le hV hVcap hT hTcap
  calc
    _≤((Cmass*plainControl s W₁ W₂*V)^2*K*(Real.exp HN*V)*
        (Ctail*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec))/V:=by
      apply div_le_div_of_nonneg_right _ hV.le
      apply ht.trans
      apply div_le_div_of_nonneg_right _ hden.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsquare (mul_nonneg (Real.exp_pos HN).le hV.le)) hK.le).trans_eq
        (by ring)
    _=(Cmass^2*Ctail*(Real.exp HN)*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        (V^2*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹):=by
      field_simp [ne_of_gt hV,ne_of_gt hp]
    _≤(Cmass^2*Ctail*(Real.exp HN)*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        ((1+Real.exp (2*HN))^2*Z^(-saving)):=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _=_:=by dsimp [C];ring

end SevenEighths.CenteredMomentSourceInputFirstTailUniform

end

end OAI

end Source996

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceInputFirstSectorTailPair.lean; sha256: 57884e73c894ca46be63e8e3f5bbdd9c4747582c5267e1cd1af05ba58677ff6e -/
section Source997
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceInputFirstSectorTail
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson ConcretePrimeRowBridge
open CenteredMomentFirstReduced CenteredMomentSectorLocalization CenteredMomentCorrelation
open CenteredMomentCommonSupport CenteredMomentCanonicalFirst CenteredMomentSupportedCorrelation
open CenteredMomentFirstScale CenteredMomentFirstDiscarded CenteredMomentActive
open CenteredMomentCompleteCommon IdealMobiusDivisorSum CenteredMomentFirstDiscardedEnergy
open CenteredMomentSourceInputFirstTailUniform
local notation "O"=>ActualEisensteinCubic.O

lemma local_tail_denominator_mono (Tlocal Tupper H Z ξ:ℝ)(A:ℕ)(B:ℝ)
    (hT:0<Tlocal)(hupper:Tlocal≤Tupper)(hB:0≤B)(hZ:0≤Z):
    B/((min 1 (kernelReference Tlocal H))^2*(1+Z^(ξ/4))^A)≤
      B/((min 1 (kernelReference Tupper H))^2*(1+Z^(ξ/4))^A):=by
  have hu:0<Tupper:=hT.trans_le hupper
  have hk:kernelReference Tupper H≤kernelReference Tlocal H:=by
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hT hupper
  have hm:0<min 1 (kernelReference Tupper H):=lt_min zero_lt_one (kernelReference_pos _ _ hu)
  have hp:0≤Z^(ξ/4):=Real.rpow_nonneg hZ _
  apply div_le_div_of_nonneg_left hB (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ hm.le (min_le_min_left 1 hk) 2

theorem local_discarded_pair_bound (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O)
        (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
        (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp HN*X → (Ideal.absNorm J:ℝ)≤Real.exp HN*X →
      X^2/K≤Tsec →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖∑ E∈inactiveSubsets I J,canonicalDiscardedTerm I J hI hJ E W K
        (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ‖ ≤
      (Ideal.absNorm I:ℝ)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := canonical_discarded_term_bound A
  obtain ⟨D,hD,hsub⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨s,D*C,mul_pos hD hC,?_⟩
  intro W I J hI hJ K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  have hc : ((inactiveSubsets I J).card:ℝ)≤D*(Ideal.absNorm I:ℝ)^ε := by
    apply le_trans _ (hsub I hI.1)
    exact_mod_cast inactiveSubsets_card I J
  calc
    _ ≤ ∑ E∈inactiveSubsets I J,‖canonicalDiscardedTerm I J hI hJ E W K
        (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ‖ := norm_sum_le _ _
    _ ≤ ∑ _E∈inactiveSubsets I J,
        K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) :=
      Finset.sum_le_sum (fun E hE => by
        let Tlocal:=firstNominalScale I J (∏ P∈E,P.val) K X
        have hE0:(∏ P∈E,P.val)≠(0:Ideal O):=by
          have he:=primeSubsetGenerator_ne_zero (fun P:CommonIndex I J=>P.val) E
          have hh:=Ideal.span_singleton_eq_bot.not.mpr he
          simpa only [primeSubsetGenerator,span_idealGenerator,Ideal.zero_eq_bot] using hh
        have hTl:0<Tlocal:=firstNominalScale_pos I J _ hE0 K X hK hX
        have hTu:Tlocal≤Tsec:=(first_nominal_scale_le I J E K X hK).trans hsec
        have hh:=ht W I J hI hJ E K X HN Tlocal Z Csec ξ hK hX hZ hCs hi hj le_rfl hthreshold
        exact hh.trans (local_tail_denominator_mono Tlocal Tsec HN Z ξ A
          (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)) hTl hTu (by positivity) (zero_lt_one.trans hZ).le))
    _ = ((inactiveSubsets I J).card:ℝ)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) := by simp
    _ ≤ (D*(Ideal.absNorm I:ℝ)^ε)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end SevenEighths.CenteredMomentSourceInputFirstSectorTail

end

end OAI

end Source997

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceInputFirstSectorTailAggregate.lean; sha256: 756e1cd9c2d5a11441373d1e49182fce34100bfd407aa9dba3b5a7d5d750427c -/
section Source998
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceInputFirstSectorTail
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentFirstTailAggregate CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstScale CenteredMomentSectorLocalization CenteredMomentHeckeExpansion
local notation "O"=>ActualEisensteinCubic.O

private theorem pair_mass {α : Type*} [Fintype α] (c w : α → ℂ) (F : α → α → ℂ)
    (hw : ∀ i,‖w i‖≤1) (B : ℝ) (_hB : 0≤B)
    (hF : ∀ i j,c i≠0 → c j≠0 → ‖F i j‖≤B) :
    ‖∑ i,∑ j,((c i*w i)*star (c j*w j))*F i j‖≤(∑ i,‖c i‖)^2*B := by
  have ht (i j : α) : ‖((c i*w i)*star (c j*w j))*F i j‖≤‖c i‖*‖c j‖*B := by
    by_cases hi : c i=0
    · simp [hi]
    by_cases hj : c j=0
    · simp [hj]
    rw [norm_mul,norm_mul,norm_star]
    apply mul_le_mul _ (hF i j hi hj) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    apply mul_le_mul _ _ (norm_nonneg _) (norm_nonneg _)
    · rw [norm_mul];exact mul_le_of_le_one_right (norm_nonneg _) (hw i)
    · rw [norm_mul];exact mul_le_of_le_one_right (norm_nonneg _) (hw j)
  calc
    _ ≤ ∑ i,‖∑ j,((c i*w i)*star (c j*w j))*F i j‖ := norm_sum_le _ _
    _ ≤ ∑ i,∑ j,‖c i‖*‖c j‖*B := Finset.sum_le_sum (fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ht i j)))
    _ = _ := by rw [pow_two,Finset.sum_mul,Finset.sum_mul];apply Finset.sum_congr rfl;intro i hi;rw [Finset.mul_sum,Finset.sum_mul]

theorem local_discarded_energy_bound (Adec : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
        (W : 𝓢(ℝ,ℂ)) (K X H Tsec Z Csec ξ : ℝ),0<K → 0<X → 1<Z → 1≤Csec →
      (∀ I∈S,c I≠0 → (Ideal.absNorm I:ℝ)≤Real.exp H*X) →
      X^2/K≤Tsec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy η m A t S c W K X Z ξ‖≤
        (∑ I∈S,‖c I‖)^2*(Real.exp H*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := local_discarded_pair_bound Adec ε hε
  refine ⟨s,C,hC,?_⟩
  intro η m A t S c W K X H Tsec Z Csec ξ hK hX hZ hCs hN hsec hthreshold
  let B := (Real.exp H*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec)
  have hB : 0≤B := by dsimp only [B];positivity
  have hpair (I J : supportedColumns S) (hi : c I≠0) (hj : c J≠0) :
      ‖CenteredMomentFirstSectorLocalization.discardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K X Z ξ‖≤B := by
    have hni := hN I (Finset.mem_filter.mp I.property).1 hi
    have hnj := hN J (Finset.mem_filter.mp J.property).1 hj
    apply (ht W I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2
      K X H Tsec Z Csec ξ hK hX hZ hCs hni hnj hsec hthreshold).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hni hε.le) hK.le
  have hp := pair_mass (fun I : supportedColumns S => c I)
    (fun I => CenteredMomentHeckeExpansion.rowWeight η m A 1 t I)
    (fun I J => CenteredMomentFirstSectorLocalization.discardedPair I J (Finset.mem_filter.mp I.property).2
      (Finset.mem_filter.mp J.property).2 W K X Z ξ)
    (fun I => rowWeight_norm_le_one η m A 1 t I (Finset.mem_filter.mp I.property).2.1) B hB hpair
  have hm : (∑ I : supportedColumns S,‖c I‖)≤∑ I∈S,‖c I‖ := by
    rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ‖c I‖)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)
  apply hp.trans
  convert mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (show 0 ≤ ∑ I : supportedColumns S, ‖c I‖ from
      Finset.sum_nonneg (fun I _ => norm_nonneg (c I))) hm 2) hB using 1 ; dsimp only [B];ring

end SevenEighths.CenteredMomentSourceInputFirstSectorTail

end

end OAI

end Source998

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceInputFirstSectorTailUniform.lean; sha256: 614103447f63de31be361f70cefeee41039da73fe603dca7d353812e3d714a5b -/
section Source999
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputFirstSectorTail
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMassUniform CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentNaturalRadialCutoff
open CenteredMomentSourceInputTailUniform CenteredMomentFirstTailAggregate
open CenteredMomentSourceInputFirstTailUniform
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
theorem local_input_tail_arbitrary_saving (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K Tsec:ℝ),
      0<K→volume s.toData≤Z^B→Tsec≤Z^B→(volume s.toData)^2/K≤Tsec→
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K (volume s.toData) Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Adec,hdecay⟩:=choose_first_tail_order B ξ saving hB hξ
  obtain ⟨SΦ,Ctail,hCtail,htail⟩:=local_discarded_energy_bound Adec 1 zero_lt_one
  let Cmass:=1+2*128^(Fintype.card ι+2)*(∏i,hi i)*whi^2
  have hprodhi:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hCmass:0<Cmass:=by dsimp [Cmass];positivity
  let HN:=Real.log (max 1 ((∏i,hi i)*whi^2))
  have hexp:(∏i,hi i)*whi^2≤Real.exp HN:=by
    dsimp [HN]
    rw [Real.exp_log (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  let C:=Cmass^2*Ctail*(Real.exp HN)*(1+Real.exp (2*HN))^2
  refine ⟨SΦ,C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_tail_threshold HN ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K Tsec hK hVcap hTcap hnom
  let V:=volume s.toData
  have hV:0<V:=volume_pos s
  have hT:0<Tsec:=(div_pos (sq_pos_of_pos hV) hK).trans_le hnom
  have hmass:=input_mass hi whi hhi hwhi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed
  have hcontrol:=plainControl_nonneg s W₁ W₂
  have hm:(∑I∈finiteColumns (Fintype.piFinset s.pools),‖coefficient s R seed I‖)≤
      Cmass*plainControl s W₁ W₂*V:=by
    apply hmass.trans
    apply mul_le_mul_of_nonneg_right _ hV.le
    apply mul_le_mul_of_nonneg_right _ hcontrol
    dsimp [Cmass]
    linarith
  have hn (I:Ideal O)(_hI:I∈finiteColumns (Fintype.piFinset s.pools))
      (hI:coefficient s R seed I≠0):(Ideal.absNorm I:ℝ)≤Real.exp HN*V:=
    (input_column_bound hi whi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed I hI).trans
      (mul_le_mul_of_nonneg_right hexp hV.le)
  have ht:=htail s.η m A s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)
    Φ K V HN Tsec Z 1 ξ hK hV hZ.1 le_rfl hn
    hnom (by simpa using hZ.2)
  simp only [Real.rpow_one] at ht
  have hsquare:=pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hm 2
  have hp:0<min 1 (kernelReference Tsec HN):=lt_min zero_lt_one (kernelReference_pos _ _ hT)
  have hzpos:0<Z:=zero_lt_one.trans hZ.1
  have hzpower:0<Z^(ξ/4):=Real.rpow_pos_of_pos hzpos _
  have hden:0<(min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec:=by positivity
  have hb:=hdecay HN Z V Tsec hZ.1.le hV hVcap hT hTcap
  calc
    _≤((Cmass*plainControl s W₁ W₂*V)^2*K*(Real.exp HN*V)*
        (Ctail*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec))/V:=by
      apply div_le_div_of_nonneg_right _ hV.le
      apply ht.trans
      apply div_le_div_of_nonneg_right _ hden.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsquare (mul_nonneg (Real.exp_pos HN).le hV.le)) hK.le).trans_eq
        (by ring)
    _=(Cmass^2*Ctail*(Real.exp HN)*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        (V^2*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹):=by
      field_simp [ne_of_gt hV,ne_of_gt hp]
    _≤(Cmass^2*Ctail*(Real.exp HN)*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        ((1+Real.exp (2*HN))^2*Z^(-saving)):=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _=_:=by dsimp [C];ring

end SevenEighths.CenteredMomentSourceInputFirstSectorTail

end

end OAI

end Source999
