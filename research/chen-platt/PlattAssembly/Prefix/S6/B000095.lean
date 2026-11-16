import PlattAssemblyKernel
import PlattCertificates.Count131072.C053040
import PlattCertificates.Count131072.C053041
import PlattCertificates.Count131072.C053042
import PlattCertificates.Count131072.C053043
import PlattCertificates.Count131072.C053044
import PlattCertificates.Count131072.C053045
import PlattCertificates.Count131072.C053046
import PlattCertificates.Count131072.C053047
import PlattCertificates.Count131072.C053048
import PlattCertificates.Count131072.C053049
import PlattCertificates.Count131072.C053050
import PlattCertificates.Count131072.C053051
import PlattCertificates.Count131072.C053052
import PlattCertificates.Count131072.C053053
import PlattCertificates.Count131072.C053054
import PlattCertificates.Count131072.C053055
import PlattCertificates.Count131072.C053056
import PlattCertificates.Count131072.C053057
import PlattCertificates.Count131072.C053058
import PlattCertificates.Count131072.C053059
import PlattCertificates.Count131072.C053060
import PlattCertificates.Count131072.C053061
import PlattCertificates.Count131072.C053062
import PlattCertificates.Count131072.C053063
import PlattCertificates.Count131072.C053064
import PlattCertificates.Count131072.C053065
import PlattCertificates.Count131072.C053066
import PlattCertificates.Count131072.C053067
import PlattCertificates.Count131072.C053068
import PlattCertificates.Count131072.C053069
import PlattCertificates.Count131072.C053070
import PlattCertificates.Count131072.C053071
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000095
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts53040 : List PrefixCut := [⟨64,233117265,233117397⟩]
theorem checked53040 : checkPrefixCuts (2^48) 6955991041 10 Manual.Count131072.C053040.packed 64 cuts53040 = true := by
 decide +kernel
def cuts53041 : List PrefixCut := [⟨6,21486546,21486558⟩,
⟨64,234569586,234569720⟩]
theorem checked53041 : checkPrefixCuts (2^48) 6956122113 10 Manual.Count131072.C053041.packed 64 cuts53041 = true := by
 decide +kernel
def pointBounds53041 : List (Nat × Nat × Nat) := [(6956134400,112390683638274,112391071177464)]
theorem point_links_checked53041 : (cuts53041.take 1).map (fun c => (6956122113-1+2*2^10*c.k,112390662151728+c.lower,112391049690906+c.upper)) = pointBounds53041 := by
 decide +kernel
def cuts53042 : List PrefixCut := [⟨49,180547198,180547299⟩,
⟨64,235698140,235698272⟩]
theorem checked53042 : checkPrefixCuts (2^48) 6956253185 10 Manual.Count131072.C053042.packed 64 cuts53042 = true := by
 decide +kernel
def pointBounds53042 : List (Nat × Nat × Nat) := [(6956353536,112391077268512,112391464807925)]
theorem point_links_checked53042 : (cuts53042.take 1).map (fun c => (6956253185-1+2*2^10*c.k,112390896721314+c.lower,112391284260626+c.upper)) = pointBounds53042 := by
 decide +kernel
def cuts53043 : List PrefixCut := [⟨64,234237038,234237171⟩]
theorem checked53043 : checkPrefixCuts (2^48) 6956384257 10 Manual.Count131072.C053043.packed 64 cuts53043 = true := by
 decide +kernel
def cuts53044 : List PrefixCut := [⟨28,102004420,102004476⟩,
⟨64,235163231,235163365⟩]
theorem checked53044 : checkPrefixCuts (2^48) 6956515329 10 Manual.Count131072.C053044.packed 64 cuts53044 = true := by
 decide +kernel
def pointBounds53044 : List (Nat × Nat × Nat) := [(6956572672,112391468660912,112391856200545)]
theorem point_links_checked53044 : (cuts53044.take 1).map (fun c => (6956515329-1+2*2^10*c.k,112391366656492+c.lower,112391754196069+c.upper)) = pointBounds53044 := by
 decide +kernel
def cuts53045 : List PrefixCut := [⟨64,234794684,234794817⟩]
theorem checked53045 : checkPrefixCuts (2^48) 6956646401 10 Manual.Count131072.C053045.packed 64 cuts53045 = true := by
 decide +kernel
def cuts53046 : List PrefixCut := [⟨7,24357213,24357227⟩,
⟨64,229975501,229975635⟩]
theorem checked53046 : checkPrefixCuts (2^48) 6956777473 10 Manual.Count131072.C053046.packed 64 cuts53046 = true := by
 decide +kernel
def pointBounds53046 : List (Nat × Nat × Nat) := [(6956791808,112391860971620,112392248511478)]
theorem point_links_checked53046 : (cuts53046.take 1).map (fun c => (6956777473-1+2*2^10*c.k,112391836614407+c.lower,112392224154251+c.upper)) = pointBounds53046 := by
 decide +kernel
def cuts53047 : List PrefixCut := [⟨50,183564607,183564711⟩,
⟨64,234178924,234179059⟩]
theorem checked53047 : checkPrefixCuts (2^48) 6956908545 10 Manual.Count131072.C053047.packed 64 cuts53047 = true := by
 decide +kernel
def pointBounds53047 : List (Nat × Nat × Nat) := [(6957010944,112392250154515,112392637694597)]
theorem point_links_checked53047 : (cuts53047.take 1).map (fun c => (6956908545-1+2*2^10*c.k,112392066589908+c.lower,112392454129886+c.upper)) = pointBounds53047 := by
 decide +kernel
def cuts53048 : List PrefixCut := [⟨64,229764539,229764673⟩]
theorem checked53048 : checkPrefixCuts (2^48) 6957039617 10 Manual.Count131072.C053048.packed 64 cuts53048 = true := by
 decide +kernel
def cuts53049 : List PrefixCut := [⟨29,106607016,106607077⟩,
⟨64,236597564,236597700⟩]
theorem checked53049 : checkPrefixCuts (2^48) 6957170689 10 Manual.Count131072.C053049.packed 64 cuts53049 = true := by
 decide +kernel
def pointBounds53049 : List (Nat × Nat × Nat) := [(6957230080,112392637140387,112393024680695)]
theorem point_links_checked53049 : (cuts53049.take 1).map (fun c => (6957170689-1+2*2^10*c.k,112392530533371+c.lower,112392918073618+c.upper)) = pointBounds53049 := by
 decide +kernel
def cuts53050 : List PrefixCut := [⟨64,236512200,236512335⟩]
theorem checked53050 : checkPrefixCuts (2^48) 6957301761 10 Manual.Count131072.C053050.packed 64 cuts53050 = true := by
 decide +kernel
def cuts53051 : List PrefixCut := [⟨8,28602868,28602884⟩,
⟨64,231288877,231289010⟩]
theorem checked53051 : checkPrefixCuts (2^48) 6957432833 10 Manual.Count131072.C053051.packed 64 cuts53051 = true := by
 decide +kernel
def pointBounds53051 : List (Nat × Nat × Nat) := [(6957449216,112393032246003,112393419786537)]
theorem point_links_checked53051 : (cuts53051.take 1).map (fun c => (6957432833-1+2*2^10*c.k,112393003643135+c.lower,112393391183653+c.upper)) = pointBounds53051 := by
 decide +kernel
def cuts53052 : List PrefixCut := [⟨51,189817932,189818039⟩,
⟨64,237757428,237757563⟩]
theorem checked53052 : checkPrefixCuts (2^48) 6957563905 10 Manual.Count131072.C053052.packed 64 cuts53052 = true := by
 decide +kernel
def pointBounds53052 : List (Nat × Nat × Nat) := [(6957668352,112393424749944,112393812290702)]
theorem point_links_checked53052 : (cuts53052.take 1).map (fun c => (6957563905-1+2*2^10*c.k,112393234932012+c.lower,112393622472663+c.upper)) = pointBounds53052 := by
 decide +kernel
def cuts53053 : List PrefixCut := [⟨64,235487474,235487614⟩]
theorem checked53053 : checkPrefixCuts (2^48) 6957694977 10 Manual.Count131072.C053053.packed 64 cuts53053 = true := by
 decide +kernel
def cuts53054 : List PrefixCut := [⟨30,108781485,108781546⟩,
⟨64,232044431,232044562⟩]
theorem checked53054 : checkPrefixCuts (2^48) 6957826049 10 Manual.Count131072.C053054.packed 64 cuts53054 = true := by
 decide +kernel
def pointBounds53054 : List (Nat × Nat × Nat) := [(6957887488,112393816958399,112394204499386)]
theorem point_links_checked53054 : (cuts53054.take 1).map (fun c => (6957826049-1+2*2^10*c.k,112393708176914+c.lower,112394095717840+c.upper)) = pointBounds53054 := by
 decide +kernel
def cuts53055 : List PrefixCut := [⟨64,236166337,236166468⟩]
theorem checked53055 : checkPrefixCuts (2^48) 6957957121 10 Manual.Count131072.C053055.packed 64 cuts53055 = true := by
 decide +kernel
def cuts53056 : List PrefixCut := [⟨9,31998209,31998227⟩,
⟨64,235676411,235676549⟩]
theorem checked53056 : checkPrefixCuts (2^48) 6958088193 10 Manual.Count131072.C053056.packed 64 cuts53056 = true := by
 decide +kernel
def pointBounds53056 : List (Nat × Nat × Nat) := [(6958106624,112394208385891,112394595927097)]
theorem point_links_checked53056 : (cuts53056.take 1).map (fun c => (6958088193-1+2*2^10*c.k,112394176387682+c.lower,112394563928870+c.upper)) = pointBounds53056 := by
 decide +kernel
def cuts53057 : List PrefixCut := [⟨52,188910080,188910189⟩,
⟨64,230939143,230939275⟩]
theorem checked53057 : checkPrefixCuts (2^48) 6958219265 10 Manual.Count131072.C053057.packed 64 cuts53057 = true := by
 decide +kernel
def pointBounds53057 : List (Nat × Nat × Nat) := [(6958325760,112394600974173,112394988515608)]
theorem point_links_checked53057 : (cuts53057.take 1).map (fun c => (6958219265-1+2*2^10*c.k,112394412064093+c.lower,112394799605419+c.upper)) = pointBounds53057 := by
 decide +kernel
def cuts53058 : List PrefixCut := [⟨64,235707961,235708094⟩]
theorem checked53058 : checkPrefixCuts (2^48) 6958350337 10 Manual.Count131072.C053058.packed 64 cuts53058 = true := by
 decide +kernel
def cuts53059 : List PrefixCut := [⟨31,111117345,111117409⟩,
⟨64,231577611,231577743⟩]
theorem checked53059 : checkPrefixCuts (2^48) 6958481409 10 Manual.Count131072.C053059.packed 64 cuts53059 = true := by
 decide +kernel
def pointBounds53059 : List (Nat × Nat × Nat) := [(6958544896,112394989828542,112395377370197)]
theorem point_links_checked53059 : (cuts53059.take 1).map (fun c => (6958481409-1+2*2^10*c.k,112394878711197+c.lower,112395266252788+c.upper)) = pointBounds53059 := by
 decide +kernel
def cuts53060 : List PrefixCut := [⟨64,232341825,232341957⟩]
theorem checked53060 : checkPrefixCuts (2^48) 6958612481 10 Manual.Count131072.C053060.packed 64 cuts53060 = true := by
 decide +kernel
def cuts53061 : List PrefixCut := [⟨10,37374915,37374935⟩,
⟨64,234602564,234602696⟩]
theorem checked53061 : checkPrefixCuts (2^48) 6958743553 10 Manual.Count131072.C053061.packed 64 cuts53061 = true := by
 decide +kernel
def pointBounds53061 : List (Nat × Nat × Nat) := [(6958764032,112395380005548,112395767547423)]
theorem point_links_checked53061 : (cuts53061.take 1).map (fun c => (6958743553-1+2*2^10*c.k,112395342630633+c.lower,112395730172488+c.upper)) = pointBounds53061 := by
 decide +kernel
def cuts53062 : List PrefixCut := [⟨53,194069590,194069705⟩,
⟨64,235407077,235407215⟩]
theorem checked53062 : checkPrefixCuts (2^48) 6958874625 10 Manual.Count131072.C053062.packed 64 cuts53062 = true := by
 decide +kernel
def pointBounds53062 : List (Nat × Nat × Nat) := [(6958983168,112395771302787,112396158844889)]
theorem point_links_checked53062 : (cuts53062.take 1).map (fun c => (6958874625-1+2*2^10*c.k,112395577233197+c.lower,112395964775184+c.upper)) = pointBounds53062 := by
 decide +kernel
def cuts53063 : List PrefixCut := [⟨64,233825210,233825342⟩]
theorem checked53063 : checkPrefixCuts (2^48) 6959005697 10 Manual.Count131072.C053063.packed 64 cuts53063 = true := by
 decide +kernel
def cuts53064 : List PrefixCut := [⟨32,116122247,116122314⟩,
⟨64,231515370,231515506⟩]
theorem checked53064 : checkPrefixCuts (2^48) 6959136769 10 Manual.Count131072.C053064.packed 64 cuts53064 = true := by
 decide +kernel
def pointBounds53064 : List (Nat × Nat × Nat) := [(6959202304,112396162587731,112396550130055)]
theorem point_links_checked53064 : (cuts53064.take 1).map (fun c => (6959136769-1+2*2^10*c.k,112396046465484+c.lower,112396434007741+c.upper)) = pointBounds53064 := by
 decide +kernel
def cuts53065 : List PrefixCut := [⟨64,233411969,233412102⟩]
theorem checked53065 : checkPrefixCuts (2^48) 6959267841 10 Manual.Count131072.C053065.packed 64 cuts53065 = true := by
 decide +kernel
def cuts53066 : List PrefixCut := [⟨11,40283443,40283464⟩,
⟨64,237896934,237897068⟩]
theorem checked53066 : checkPrefixCuts (2^48) 6959398913 10 Manual.Count131072.C053066.packed 64 cuts53066 = true := by
 decide +kernel
def pointBounds53066 : List (Nat × Nat × Nat) := [(6959421440,112396551676266,112396939218813)]
theorem point_links_checked53066 : (cuts53066.take 1).map (fun c => (6959398913-1+2*2^10*c.k,112396511392823+c.lower,112396898935349+c.upper)) = pointBounds53066 := by
 decide +kernel
def cuts53067 : List PrefixCut := [⟨54,197003740,197003850⟩,
⟨64,231380992,231381122⟩]
theorem checked53067 : checkPrefixCuts (2^48) 6959529985 10 Manual.Count131072.C053067.packed 64 cuts53067 = true := by
 decide +kernel
def pointBounds53067 : List (Nat × Nat × Nat) := [(6959640576,112396946293497,112397333836267)]
theorem point_links_checked53067 : (cuts53067.take 1).map (fun c => (6959529985-1+2*2^10*c.k,112396749289757+c.lower,112397136832417+c.upper)) = pointBounds53067 := by
 decide +kernel
def cuts53068 : List PrefixCut := [⟨64,230729506,230729636⟩]
theorem checked53068 : checkPrefixCuts (2^48) 6959661057 10 Manual.Count131072.C053068.packed 64 cuts53068 = true := by
 decide +kernel
def cuts53069 : List PrefixCut := [⟨33,119710707,119710776⟩,
⟨64,231250913,231251045⟩]
theorem checked53069 : checkPrefixCuts (2^48) 6959792129 10 Manual.Count131072.C053069.packed 64 cuts53069 = true := by
 decide +kernel
def pointBounds53069 : List (Nat × Nat × Nat) := [(6959859712,112397331110962,112397718653951)]
theorem point_links_checked53069 : (cuts53069.take 1).map (fun c => (6959792129-1+2*2^10*c.k,112397211400255+c.lower,112397598943175+c.upper)) = pointBounds53069 := by
 decide +kernel
def cuts53070 : List PrefixCut := [⟨64,234037067,234037198⟩]
theorem checked53070 : checkPrefixCuts (2^48) 6959923201 10 Manual.Count131072.C053070.packed 64 cuts53070 = true := by
 decide +kernel
def cuts53071 : List PrefixCut := [⟨12,44364227,44364251⟩,
⟨64,237874554,237874688⟩]
theorem checked53071 : checkPrefixCuts (2^48) 6960054273 10 Manual.Count131072.C053071.packed 64 cuts53071 = true := by
 decide +kernel
def pointBounds53071 : List (Nat × Nat × Nat) := [(6960078848,112397721052462,112398108595669)]
theorem point_links_checked53071 : (cuts53071.take 1).map (fun c => (6960054273-1+2*2^10*c.k,112397676688235+c.lower,112398064231418+c.upper)) = pointBounds53071 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000095
