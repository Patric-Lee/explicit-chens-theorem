import PlattAssemblyKernel
import PlattCertificates.Count131072.C074032
import PlattCertificates.Count131072.C074033
import PlattCertificates.Count131072.C074034
import PlattCertificates.Count131072.C074035
import PlattCertificates.Count131072.C074036
import PlattCertificates.Count131072.C074037
import PlattCertificates.Count131072.C074038
import PlattCertificates.Count131072.C074039
import PlattCertificates.Count131072.C074040
import PlattCertificates.Count131072.C074041
import PlattCertificates.Count131072.C074042
import PlattCertificates.Count131072.C074043
import PlattCertificates.Count131072.C074044
import PlattCertificates.Count131072.C074045
import PlattCertificates.Count131072.C074046
import PlattCertificates.Count131072.C074047
import PlattCertificates.Count131072.C074048
import PlattCertificates.Count131072.C074049
import PlattCertificates.Count131072.C074050
import PlattCertificates.Count131072.C074051
import PlattCertificates.Count131072.C074052
import PlattCertificates.Count131072.C074053
import PlattCertificates.Count131072.C074054
import PlattCertificates.Count131072.C074055
import PlattCertificates.Count131072.C074056
import PlattCertificates.Count131072.C074057
import PlattCertificates.Count131072.C074058
import PlattCertificates.Count131072.C074059
import PlattCertificates.Count131072.C074060
import PlattCertificates.Count131072.C074061
import PlattCertificates.Count131072.C074062
import PlattCertificates.Count131072.C074063
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000126
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74032 : List PrefixCut := [⟨64,164839717,164839812⟩]
theorem checked74032 : checkPrefixCuts (2^48) 9707454465 10 Manual.Count131072.C074032.packed 64 cuts74032 = true := by
 decide +kernel
def cuts74033 : List PrefixCut := [⟨37,95191380,95191433⟩,
⟨64,165243413,165243509⟩]
theorem checked74033 : checkPrefixCuts (2^48) 9707585537 10 Manual.Count131072.C074033.packed 64 cuts74033 = true := by
 decide +kernel
def pointBounds74033 : List (Nat × Nat × Nat) := [(9707661312,116500090930487,116500480842882)]
theorem point_links_checked74033 : (cuts74033.take 1).map (fun c => (9707585537-1+2*2^10*c.k,116499995739107+c.lower,116500385651449+c.upper)) = pointBounds74033 := by
 decide +kernel
def cuts74034 : List PrefixCut := [⟨64,165009226,165009321⟩]
theorem checked74034 : checkPrefixCuts (2^48) 9707716609 10 Manual.Count131072.C074034.packed 64 cuts74034 = true := by
 decide +kernel
def cuts74035 : List PrefixCut := [⟨58,149727059,149727145⟩,
⟨64,165528898,165528993⟩]
theorem checked74035 : checkPrefixCuts (2^48) 9707847681 10 Manual.Count131072.C074035.packed 64 cuts74035 = true := by
 decide +kernel
def pointBounds74035 : List (Nat × Nat × Nat) := [(9707966464,116500475718805,116500865631424)]
theorem point_links_checked74035 : (cuts74035.take 1).map (fun c => (9707847681-1+2*2^10*c.k,116500325991746+c.lower,116500715904279+c.upper)) = pointBounds74035 := by
 decide +kernel
def cuts74036 : List PrefixCut := [⟨64,165787608,165787703⟩]
theorem checked74036 : checkPrefixCuts (2^48) 9707978753 10 Manual.Count131072.C074036.packed 64 cuts74036 = true := by
 decide +kernel
def cuts74037 : List PrefixCut := [⟨64,164306692,164306792⟩]
theorem checked74037 : checkPrefixCuts (2^48) 9708109825 10 Manual.Count131072.C074037.packed 64 cuts74037 = true := by
 decide +kernel
def cuts74038 : List PrefixCut := [⟨15,37691358,37691381⟩,
⟨64,164565420,164565510⟩]
theorem checked74038 : checkPrefixCuts (2^48) 9708240897 10 Manual.Count131072.C074038.packed 64 cuts74038 = true := by
 decide +kernel
def pointBounds74038 : List (Nat × Nat × Nat) := [(9708271616,116500859306302,116501249219148)]
theorem point_links_checked74038 : (cuts74038.take 1).map (fun c => (9708240897-1+2*2^10*c.k,116500821614944+c.lower,116501211527767+c.upper)) = pointBounds74038 := by
 decide +kernel
def cuts74039 : List PrefixCut := [⟨64,165374994,165375096⟩]
theorem checked74039 : checkPrefixCuts (2^48) 9708371969 10 Manual.Count131072.C074039.packed 64 cuts74039 = true := by
 decide +kernel
def cuts74040 : List PrefixCut := [⟨36,93848737,93848792⟩,
⟨64,167083311,167083410⟩]
theorem checked74040 : checkPrefixCuts (2^48) 9708503041 10 Manual.Count131072.C074040.packed 64 cuts74040 = true := by
 decide +kernel
def pointBounds74040 : List (Nat × Nat × Nat) := [(9708576768,116501245404095,116501635317165)]
theorem point_links_checked74040 : (cuts74040.take 1).map (fun c => (9708503041-1+2*2^10*c.k,116501151555358+c.lower,116501541468373+c.upper)) = pointBounds74040 := by
 decide +kernel
def cuts74041 : List PrefixCut := [⟨64,163486042,163486148⟩]
theorem checked74041 : checkPrefixCuts (2^48) 9708634113 10 Manual.Count131072.C074041.packed 64 cuts74041 = true := by
 decide +kernel
def cuts74042 : List PrefixCut := [⟨57,147741490,147741574⟩,
⟨64,165861155,165861248⟩]
theorem checked74042 : checkPrefixCuts (2^48) 9708765185 10 Manual.Count131072.C074042.packed 64 cuts74042 = true := by
 decide +kernel
def pointBounds74042 : List (Nat × Nat × Nat) := [(9708881920,116501629866201,116502019779505)]
theorem point_links_checked74042 : (cuts74042.take 1).map (fun c => (9708765185-1+2*2^10*c.k,116501482124711+c.lower,116501872037931+c.upper)) = pointBounds74042 := by
 decide +kernel
def cuts74043 : List PrefixCut := [⟨64,163887513,163887611⟩]
theorem checked74043 : checkPrefixCuts (2^48) 9708896257 10 Manual.Count131072.C074043.packed 64 cuts74043 = true := by
 decide +kernel
def cuts74044 : List PrefixCut := [⟨64,167625116,167625213⟩]
theorem checked74044 : checkPrefixCuts (2^48) 9709027329 10 Manual.Count131072.C074044.packed 64 cuts74044 = true := by
 decide +kernel
def cuts74045 : List PrefixCut := [⟨14,35861391,35861414⟩,
⟨64,164288955,164289049⟩]
theorem checked74045 : checkPrefixCuts (2^48) 9709158401 10 Manual.Count131072.C074045.packed 64 cuts74045 = true := by
 decide +kernel
def pointBounds74045 : List (Nat × Nat × Nat) := [(9709187072,116502015359886,116502405273417)]
theorem point_links_checked74045 : (cuts74045.take 1).map (fun c => (9709158401-1+2*2^10*c.k,116501979498495+c.lower,116502369412003+c.upper)) = pointBounds74045 := by
 decide +kernel
def cuts74046 : List PrefixCut := [⟨64,164083807,164083904⟩]
theorem checked74046 : checkPrefixCuts (2^48) 9709289473 10 Manual.Count131072.C074046.packed 64 cuts74046 = true := by
 decide +kernel
def cuts74047 : List PrefixCut := [⟨35,89926266,89926318⟩,
⟨64,163849679,163849776⟩]
theorem checked74047 : checkPrefixCuts (2^48) 9709420545 10 Manual.Count131072.C074047.packed 64 cuts74047 = true := by
 decide +kernel
def pointBounds74047 : List (Nat × Nat × Nat) := [(9709492224,116502397797523,116502787711274)]
theorem point_links_checked74047 : (cuts74047.take 1).map (fun c => (9709420545-1+2*2^10*c.k,116502307871257+c.lower,116502697784956+c.upper)) = pointBounds74047 := by
 decide +kernel
def cuts74048 : List PrefixCut := [⟨64,165644783,165644888⟩]
theorem checked74048 : checkPrefixCuts (2^48) 9709551617 10 Manual.Count131072.C074048.packed 64 cuts74048 = true := by
 decide +kernel
def cuts74049 : List PrefixCut := [⟨56,146510010,146510099⟩,
⟨64,166715151,166715254⟩]
theorem checked74049 : checkPrefixCuts (2^48) 9709682689 10 Manual.Count131072.C074049.packed 64 cuts74049 = true := by
 decide +kernel
def pointBounds74049 : List (Nat × Nat × Nat) := [(9709797376,116502783875729,116503173789719)]
theorem point_links_checked74049 : (cuts74049.take 1).map (fun c => (9709682689-1+2*2^10*c.k,116502637365719+c.lower,116503027279620+c.upper)) = pointBounds74049 := by
 decide +kernel
def cuts74050 : List PrefixCut := [⟨64,167553568,167553668⟩]
theorem checked74050 : checkPrefixCuts (2^48) 9709813761 10 Manual.Count131072.C074050.packed 64 cuts74050 = true := by
 decide +kernel
def cuts74051 : List PrefixCut := [⟨64,165812019,165812111⟩]
theorem checked74051 : checkPrefixCuts (2^48) 9709944833 10 Manual.Count131072.C074051.packed 64 cuts74051 = true := by
 decide +kernel
def cuts74052 : List PrefixCut := [⟨13,34988371,34988391⟩,
⟨64,167114233,167114331⟩]
theorem checked74052 : checkPrefixCuts (2^48) 9710075905 10 Manual.Count131072.C074052.packed 64 cuts74052 = true := by
 decide +kernel
def pointBounds74052 : List (Nat × Nat × Nat) := [(9710102528,116503172434828,116503562349044)]
theorem point_links_checked74052 : (cuts74052.take 1).map (fun c => (9710075905-1+2*2^10*c.k,116503137446457+c.lower,116503527360653+c.upper)) = pointBounds74052 := by
 decide +kernel
def cuts74053 : List PrefixCut := [⟨64,164358171,164358278⟩]
theorem checked74053 : checkPrefixCuts (2^48) 9710206977 10 Manual.Count131072.C074053.packed 64 cuts74053 = true := by
 decide +kernel
def cuts74054 : List PrefixCut := [⟨34,87279953,87280008⟩,
⟨64,162558762,162558863⟩]
theorem checked74054 : checkPrefixCuts (2^48) 9710338049 10 Manual.Count131072.C074054.packed 64 cuts74054 = true := by
 decide +kernel
def pointBounds74054 : List (Nat × Nat × Nat) := [(9710407680,116503556198814,116503946113270)]
theorem point_links_checked74054 : (cuts74054.take 1).map (fun c => (9710338049-1+2*2^10*c.k,116503468918861+c.lower,116503858833262+c.upper)) = pointBounds74054 := by
 decide +kernel
def cuts74055 : List PrefixCut := [⟨64,164730564,164730661⟩]
theorem checked74055 : checkPrefixCuts (2^48) 9710469121 10 Manual.Count131072.C074055.packed 64 cuts74055 = true := by
 decide +kernel
def cuts74056 : List PrefixCut := [⟨55,143597563,143597653⟩,
⟨64,167482018,167482122⟩]
theorem checked74056 : checkPrefixCuts (2^48) 9710600193 10 Manual.Count131072.C074056.packed 64 cuts74056 = true := by
 decide +kernel
def pointBounds74056 : List (Nat × Nat × Nat) := [(9710712832,116503939805750,116504329720439)]
theorem point_links_checked74056 : (cuts74056.take 1).map (fun c => (9710600193-1+2*2^10*c.k,116503796208187+c.lower,116504186122786+c.upper)) = pointBounds74056 := by
 decide +kernel
def cuts74057 : List PrefixCut := [⟨64,164001473,164001572⟩]
theorem checked74057 : checkPrefixCuts (2^48) 9710731265 10 Manual.Count131072.C074057.packed 64 cuts74057 = true := by
 decide +kernel
def cuts74058 : List PrefixCut := [⟨64,164549983,164550076⟩]
theorem checked74058 : checkPrefixCuts (2^48) 9710862337 10 Manual.Count131072.C074058.packed 64 cuts74058 = true := by
 decide +kernel
def cuts74059 : List PrefixCut := [⟨12,31564821,31564839⟩,
⟨64,165156444,165156540⟩]
theorem checked74059 : checkPrefixCuts (2^48) 9710993409 10 Manual.Count131072.C074059.packed 64 cuts74059 = true := by
 decide +kernel
def pointBounds74059 : List (Nat × Nat × Nat) := [(9711017984,116504323806482,116504713721395)]
theorem point_links_checked74059 : (cuts74059.take 1).map (fun c => (9710993409-1+2*2^10*c.k,116504292241661+c.lower,116504682156556+c.upper)) = pointBounds74059 := by
 decide +kernel
def cuts74060 : List PrefixCut := [⟨64,166052735,166052832⟩]
theorem checked74060 : checkPrefixCuts (2^48) 9711124481 10 Manual.Count131072.C074060.packed 64 cuts74060 = true := by
 decide +kernel
def cuts74061 : List PrefixCut := [⟨33,85068913,85068961⟩,
⟨64,164949092,164949192⟩]
theorem checked74061 : checkPrefixCuts (2^48) 9711255553 10 Manual.Count131072.C074061.packed 64 cuts74061 = true := by
 decide +kernel
def pointBounds74061 : List (Nat × Nat × Nat) := [(9711323136,116504708519753,116505098434889)]
theorem point_links_checked74061 : (cuts74061.take 1).map (fun c => (9711255553-1+2*2^10*c.k,116504623450840+c.lower,116505013365928+c.upper)) = pointBounds74061 := by
 decide +kernel
def cuts74062 : List PrefixCut := [⟨64,164541099,164541195⟩]
theorem checked74062 : checkPrefixCuts (2^48) 9711386625 10 Manual.Count131072.C074062.packed 64 cuts74062 = true := by
 decide +kernel
def cuts74063 : List PrefixCut := [⟨54,140221931,140222017⟩,
⟨64,166422793,166422896⟩]
theorem checked74063 : checkPrefixCuts (2^48) 9711517697 10 Manual.Count131072.C074063.packed 64 cuts74063 = true := by
 decide +kernel
def pointBounds74063 : List (Nat × Nat × Nat) := [(9711628288,116505093162962,116505483078332)]
theorem point_links_checked74063 : (cuts74063.take 1).map (fun c => (9711517697-1+2*2^10*c.k,116504952941031+c.lower,116505342856315+c.upper)) = pointBounds74063 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000126
