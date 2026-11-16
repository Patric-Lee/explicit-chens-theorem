import PlattAssemblyKernel
import PlattCertificates.Count131072.C062688
import PlattCertificates.Count131072.C062689
import PlattCertificates.Count131072.C062690
import PlattCertificates.Count131072.C062691
import PlattCertificates.Count131072.C062692
import PlattCertificates.Count131072.C062693
import PlattCertificates.Count131072.C062694
import PlattCertificates.Count131072.C062695
import PlattCertificates.Count131072.C062696
import PlattCertificates.Count131072.C062697
import PlattCertificates.Count131072.C062698
import PlattCertificates.Count131072.C062699
import PlattCertificates.Count131072.C062700
import PlattCertificates.Count131072.C062701
import PlattCertificates.Count131072.C062702
import PlattCertificates.Count131072.C062703
import PlattCertificates.Count131072.C062704
import PlattCertificates.Count131072.C062705
import PlattCertificates.Count131072.C062706
import PlattCertificates.Count131072.C062707
import PlattCertificates.Count131072.C062708
import PlattCertificates.Count131072.C062709
import PlattCertificates.Count131072.C062710
import PlattCertificates.Count131072.C062711
import PlattCertificates.Count131072.C062712
import PlattCertificates.Count131072.C062713
import PlattCertificates.Count131072.C062714
import PlattCertificates.Count131072.C062715
import PlattCertificates.Count131072.C062716
import PlattCertificates.Count131072.C062717
import PlattCertificates.Count131072.C062718
import PlattCertificates.Count131072.C062719
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000084
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62688 : List PrefixCut := [⟨64,197838873,197838987⟩]
theorem checked62688 : checkPrefixCuts (2^48) 8220573697 10 Manual.Count131072.C062688.packed 64 cuts62688 = true := by
 decide +kernel
def cuts62689 : List PrefixCut := [⟨10,31055417,31055435⟩,
⟨64,199376492,199376606⟩]
theorem checked62689 : checkPrefixCuts (2^48) 8220704769 10 Manual.Count131072.C062689.packed 64 cuts62689 = true := by
 decide +kernel
def pointBounds62689 : List (Nat × Nat × Nat) := [(8220725248,114457664028907,114458052746017)]
theorem point_links_checked62689 : (cuts62689.take 1).map (fun c => (8220704769-1+2*2^10*c.k,114457632973490+c.lower,114458021690582+c.upper)) = pointBounds62689 := by
 decide +kernel
def cuts62690 : List PrefixCut := [⟨64,195401604,195401717⟩]
theorem checked62690 : checkPrefixCuts (2^48) 8220835841 10 Manual.Count131072.C062690.packed 64 cuts62690 = true := by
 decide +kernel
def cuts62691 : List PrefixCut := [⟨8,24959960,24959973⟩,
⟨64,196870734,196870845⟩]
theorem checked62691 : checkPrefixCuts (2^48) 8220966913 10 Manual.Count131072.C062691.packed 64 cuts62691 = true := by
 decide +kernel
def pointBounds62691 : List (Nat × Nat × Nat) := [(8220983296,114458052711546,114458441428878)]
theorem point_links_checked62691 : (cuts62691.take 1).map (fun c => (8220966913-1+2*2^10*c.k,114458027751586+c.lower,114458416468905+c.upper)) = pointBounds62691 := by
 decide +kernel
def cuts62692 : List PrefixCut := [⟨64,197381152,197381262⟩]
theorem checked62692 : checkPrefixCuts (2^48) 8221097985 10 Manual.Count131072.C062692.packed 64 cuts62692 = true := by
 decide +kernel
def cuts62693 : List PrefixCut := [⟨6,18145899,18145909⟩,
⟨64,196282420,196282529⟩]
theorem checked62693 : checkPrefixCuts (2^48) 8221229057 10 Manual.Count131072.C062693.packed 64 cuts62693 = true := by
 decide +kernel
def pointBounds62693 : List (Nat × Nat × Nat) := [(8221241344,114458440149371,114458828866921)]
theorem point_links_checked62693 : (cuts62693.take 1).map (fun c => (8221229057-1+2*2^10*c.k,114458422003472+c.lower,114458810721012+c.upper)) = pointBounds62693 := by
 decide +kernel
def cuts62694 : List PrefixCut := [⟨64,199497544,199497651⟩]
theorem checked62694 : checkPrefixCuts (2^48) 8221360129 10 Manual.Count131072.C062694.packed 64 cuts62694 = true := by
 decide +kernel
def cuts62695 : List PrefixCut := [⟨4,12290889,12290896⟩,
⟨64,199323181,199323293⟩]
theorem checked62695 : checkPrefixCuts (2^48) 8221491201 10 Manual.Count131072.C062695.packed 64 cuts62695 = true := by
 decide +kernel
def pointBounds62695 : List (Nat × Nat × Nat) := [(8221499392,114458830074325,114459218792088)]
theorem point_links_checked62695 : (cuts62695.take 1).map (fun c => (8221491201-1+2*2^10*c.k,114458817783436+c.lower,114459206501192+c.upper)) = pointBounds62695 := by
 decide +kernel
def cuts62696 : List PrefixCut := [⟨64,195382887,195382999⟩]
theorem checked62696 : checkPrefixCuts (2^48) 8221622273 10 Manual.Count131072.C062696.packed 64 cuts62696 = true := by
 decide +kernel
def cuts62697 : List PrefixCut := [⟨2,6402015,6402019⟩,
⟨64,196064503,196064612⟩]
theorem checked62697 : checkPrefixCuts (2^48) 8221753345 10 Manual.Count131072.C062697.packed 64 cuts62697 = true := by
 decide +kernel
def pointBounds62697 : List (Nat × Nat × Nat) := [(8221757440,114459218891519,114459607609503)]
theorem point_links_checked62697 : (cuts62697.take 1).map (fun c => (8221753345-1+2*2^10*c.k,114459212489504+c.lower,114459601207484+c.upper)) = pointBounds62697 := by
 decide +kernel
def cuts62698 : List PrefixCut := [⟨64,197054168,197054285⟩]
theorem checked62698 : checkPrefixCuts (2^48) 8221884417 10 Manual.Count131072.C062698.packed 64 cuts62698 = true := by
 decide +kernel
def pointBounds62698 : List (Nat × Nat × Nat) := [(8222015488,114459605608175,114459994326381)]
theorem point_links_checked62698 : (cuts62698.take 1).map (fun c => (8221884417-1+2*2^10*c.k,114459408554007+c.lower,114459797272096+c.upper)) = pointBounds62698 := by
 decide +kernel
def cuts62699 : List PrefixCut := [⟨64,199344691,199344806⟩]
theorem checked62699 : checkPrefixCuts (2^48) 8222015489 10 Manual.Count131072.C062699.packed 64 cuts62699 = true := by
 decide +kernel
def cuts62700 : List PrefixCut := [⟨62,189653489,189653599⟩,
⟨64,195952400,195952514⟩]
theorem checked62700 : checkPrefixCuts (2^48) 8222146561 10 Manual.Count131072.C062700.packed 64 cuts62700 = true := by
 decide +kernel
def pointBounds62700 : List (Nat × Nat × Nat) := [(8222273536,114459994606355,114460383324786)]
theorem point_links_checked62700 : (cuts62700.take 1).map (fun c => (8222146561-1+2*2^10*c.k,114459804952866+c.lower,114460193671187+c.upper)) = pointBounds62700 := by
 decide +kernel
def cuts62701 : List PrefixCut := [⟨64,198311350,198311464⟩]
theorem checked62701 : checkPrefixCuts (2^48) 8222277633 10 Manual.Count131072.C062701.packed 64 cuts62701 = true := by
 decide +kernel
def cuts62702 : List PrefixCut := [⟨60,184307258,184307366⟩,
⟨64,196083110,196083225⟩]
theorem checked62702 : checkPrefixCuts (2^48) 8222408705 10 Manual.Count131072.C062702.packed 64 cuts62702 = true := by
 decide +kernel
def pointBounds62702 : List (Nat × Nat × Nat) := [(8222531584,114460383523874,114460772242531)]
theorem point_links_checked62702 : (cuts62702.take 1).map (fun c => (8222408705-1+2*2^10*c.k,114460199216616+c.lower,114460587935165+c.upper)) = pointBounds62702 := by
 decide +kernel
def cuts62703 : List PrefixCut := [⟨64,194197219,194197328⟩]
theorem checked62703 : checkPrefixCuts (2^48) 8222539777 10 Manual.Count131072.C062703.packed 64 cuts62703 = true := by
 decide +kernel
def cuts62704 : List PrefixCut := [⟨58,179406343,179406440⟩,
⟨64,198096494,198096602⟩]
theorem checked62704 : checkPrefixCuts (2^48) 8222670849 10 Manual.Count131072.C062704.packed 64 cuts62704 = true := by
 decide +kernel
def pointBounds62704 : List (Nat × Nat × Nat) := [(8222789632,114460768903288,114461157622158)]
theorem point_links_checked62704 : (cuts62704.take 1).map (fun c => (8222670849-1+2*2^10*c.k,114460589496945+c.lower,114460978215718+c.upper)) = pointBounds62704 := by
 decide +kernel
def cuts62705 : List PrefixCut := [⟨64,194019872,194019987⟩]
theorem checked62705 : checkPrefixCuts (2^48) 8222801921 10 Manual.Count131072.C062705.packed 64 cuts62705 = true := by
 decide +kernel
def cuts62706 : List PrefixCut := [⟨56,171288111,171288208⟩,
⟨64,195762535,195762646⟩]
theorem checked62706 : checkPrefixCuts (2^48) 8222932993 10 Manual.Count131072.C062706.packed 64 cuts62706 = true := by
 decide +kernel
def pointBounds62706 : List (Nat × Nat × Nat) := [(8223047680,114461152901422,114461541620515)]
theorem point_links_checked62706 : (cuts62706.take 1).map (fun c => (8222932993-1+2*2^10*c.k,114460981613311+c.lower,114461370332307+c.upper)) = pointBounds62706 := by
 decide +kernel
def cuts62707 : List PrefixCut := [⟨64,199901187,199901300⟩]
theorem checked62707 : checkPrefixCuts (2^48) 8223064065 10 Manual.Count131072.C062707.packed 64 cuts62707 = true := by
 decide +kernel
def cuts62708 : List PrefixCut := [⟨54,166250993,166251091⟩,
⟨64,195619371,195619485⟩]
theorem checked62708 : checkPrefixCuts (2^48) 8223195137 10 Manual.Count131072.C062708.packed 64 cuts62708 = true := by
 decide +kernel
def pointBounds62708 : List (Nat × Nat × Nat) := [(8223305728,114461543528026,114461932247344)]
theorem point_links_checked62708 : (cuts62708.take 1).map (fun c => (8223195137-1+2*2^10*c.k,114461377277033+c.lower,114461765996253+c.upper)) = pointBounds62708 := by
 decide +kernel
def cuts62709 : List PrefixCut := [⟨64,196780020,196780135⟩]
theorem checked62709 : checkPrefixCuts (2^48) 8223326209 10 Manual.Count131072.C062709.packed 64 cuts62709 = true := by
 decide +kernel
def cuts62710 : List PrefixCut := [⟨52,155806177,155806271⟩,
⟨64,193114478,193114591⟩]
theorem checked62710 : checkPrefixCuts (2^48) 8223457281 10 Manual.Count131072.C062710.packed 64 cuts62710 = true := by
 decide +kernel
def pointBounds62710 : List (Nat × Nat × Nat) := [(8223563776,114461925482601,114462314202144)]
theorem point_links_checked62710 : (cuts62710.take 1).map (fun c => (8223457281-1+2*2^10*c.k,114461769676424+c.lower,114462158395873+c.upper)) = pointBounds62710 := by
 decide +kernel
def cuts62711 : List PrefixCut := [⟨64,198485125,198485240⟩]
theorem checked62711 : checkPrefixCuts (2^48) 8223588353 10 Manual.Count131072.C062711.packed 64 cuts62711 = true := by
 decide +kernel
def cuts62712 : List PrefixCut := [⟨50,151249061,151249152⟩,
⟨64,193827094,193827208⟩]
theorem checked62712 : checkPrefixCuts (2^48) 8223719425 10 Manual.Count131072.C062712.packed 64 cuts62712 = true := by
 decide +kernel
def pointBounds62712 : List (Nat × Nat × Nat) := [(8223821824,114462312525088,114462701244856)]
theorem point_links_checked62712 : (cuts62712.take 1).map (fun c => (8223719425-1+2*2^10*c.k,114462161276027+c.lower,114462549995704+c.upper)) = pointBounds62712 := by
 decide +kernel
def cuts62713 : List PrefixCut := [⟨64,197896947,197897060⟩]
theorem checked62713 : checkPrefixCuts (2^48) 8223850497 10 Manual.Count131072.C062713.packed 64 cuts62713 = true := by
 decide +kernel
def cuts62714 : List PrefixCut := [⟨48,147342523,147342608⟩,
⟨64,197722656,197722770⟩]
theorem checked62714 : checkPrefixCuts (2^48) 8223981569 10 Manual.Count131072.C062714.packed 64 cuts62714 = true := by
 decide +kernel
def pointBounds62714 : List (Nat × Nat × Nat) := [(8224079872,114462700342591,114463089062580)]
theorem point_links_checked62714 : (cuts62714.take 1).map (fun c => (8223981569-1+2*2^10*c.k,114462553000068+c.lower,114462941719972+c.upper)) = pointBounds62714 := by
 decide +kernel
def cuts62715 : List PrefixCut := [⟨64,197206126,197206242⟩]
theorem checked62715 : checkPrefixCuts (2^48) 8224112641 10 Manual.Count131072.C062715.packed 64 cuts62715 = true := by
 decide +kernel
def cuts62716 : List PrefixCut := [⟨46,142443714,142443795⟩,
⟨64,198845771,198845883⟩]
theorem checked62716 : checkPrefixCuts (2^48) 8224243713 10 Manual.Count131072.C062716.packed 64 cuts62716 = true := by
 decide +kernel
def pointBounds62716 : List (Nat × Nat × Nat) := [(8224337920,114463090372564,114463479092779)]
theorem point_links_checked62716 : (cuts62716.take 1).map (fun c => (8224243713-1+2*2^10*c.k,114462947928850+c.lower,114463336648984+c.upper)) = pointBounds62716 := by
 decide +kernel
def cuts62717 : List PrefixCut := [⟨64,195043718,195043832⟩]
theorem checked62717 : checkPrefixCuts (2^48) 8224374785 10 Manual.Count131072.C062717.packed 64 cuts62717 = true := by
 decide +kernel
def cuts62718 : List PrefixCut := [⟨44,134088615,134088692⟩,
⟨64,195348622,195348734⟩]
theorem checked62718 : checkPrefixCuts (2^48) 8224505857 10 Manual.Count131072.C062718.packed 64 cuts62718 = true := by
 decide +kernel
def pointBounds62718 : List (Nat × Nat × Nat) := [(8224595968,114463475906954,114463864627391)]
theorem point_links_checked62718 : (cuts62718.take 1).map (fun c => (8224505857-1+2*2^10*c.k,114463341818339+c.lower,114463730538699+c.upper)) = pointBounds62718 := by
 decide +kernel
def cuts62719 : List PrefixCut := [⟨64,193737026,193737136⟩]
theorem checked62719 : checkPrefixCuts (2^48) 8224636929 10 Manual.Count131072.C062719.packed 64 cuts62719 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000084
