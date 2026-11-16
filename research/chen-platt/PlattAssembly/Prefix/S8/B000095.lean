import PlattAssemblyKernel
import PlattCertificates.Count131072.C073040
import PlattCertificates.Count131072.C073041
import PlattCertificates.Count131072.C073042
import PlattCertificates.Count131072.C073043
import PlattCertificates.Count131072.C073044
import PlattCertificates.Count131072.C073045
import PlattCertificates.Count131072.C073046
import PlattCertificates.Count131072.C073047
import PlattCertificates.Count131072.C073048
import PlattCertificates.Count131072.C073049
import PlattCertificates.Count131072.C073050
import PlattCertificates.Count131072.C073051
import PlattCertificates.Count131072.C073052
import PlattCertificates.Count131072.C073053
import PlattCertificates.Count131072.C073054
import PlattCertificates.Count131072.C073055
import PlattCertificates.Count131072.C073056
import PlattCertificates.Count131072.C073057
import PlattCertificates.Count131072.C073058
import PlattCertificates.Count131072.C073059
import PlattCertificates.Count131072.C073060
import PlattCertificates.Count131072.C073061
import PlattCertificates.Count131072.C073062
import PlattCertificates.Count131072.C073063
import PlattCertificates.Count131072.C073064
import PlattCertificates.Count131072.C073065
import PlattCertificates.Count131072.C073066
import PlattCertificates.Count131072.C073067
import PlattCertificates.Count131072.C073068
import PlattCertificates.Count131072.C073069
import PlattCertificates.Count131072.C073070
import PlattCertificates.Count131072.C073071
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000095
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73040 : List PrefixCut := [⟨64,166048939,166049042⟩]
theorem checked73040 : checkPrefixCuts (2^48) 9577431041 10 Manual.Count131072.C073040.packed 64 cuts73040 = true := by
 decide +kernel
def cuts73041 : List PrefixCut := [⟨45,119201170,119201242⟩,
⟨64,168897374,168897476⟩]
theorem checked73041 : checkPrefixCuts (2^48) 9577562113 10 Manual.Count131072.C073041.packed 64 cuts73041 = true := by
 decide +kernel
def pointBounds73041 : List (Nat × Nat × Nat) := [(9577654272,116334951105404,116335340919300)]
theorem point_links_checked73041 : (cuts73041.take 1).map (fun c => (9577562113-1+2*2^10*c.k,116334831904234+c.lower,116335221718058+c.upper)) = pointBounds73041 := by
 decide +kernel
def cuts73042 : List PrefixCut := [⟨64,167807697,167807803⟩]
theorem checked73042 : checkPrefixCuts (2^48) 9577693185 10 Manual.Count131072.C073042.packed 64 cuts73042 = true := by
 decide +kernel
def cuts73043 : List PrefixCut := [⟨64,165395589,165395693⟩]
theorem checked73043 : checkPrefixCuts (2^48) 9577824257 10 Manual.Count131072.C073043.packed 64 cuts73043 = true := by
 decide +kernel
def pointBounds73043 : List (Nat × Nat × Nat) := [(9577955328,116335334004894,116335723819030)]
theorem point_links_checked73043 : (cuts73043.take 1).map (fun c => (9577824257-1+2*2^10*c.k,116335168609305+c.lower,116335558423337+c.upper)) = pointBounds73043 := by
 decide +kernel
def cuts73044 : List PrefixCut := [⟨64,167127182,167127273⟩]
theorem checked73044 : checkPrefixCuts (2^48) 9577955329 10 Manual.Count131072.C073044.packed 64 cuts73044 = true := by
 decide +kernel
def cuts73045 : List PrefixCut := [⟨64,167947749,167947848⟩]
theorem checked73045 : checkPrefixCuts (2^48) 9578086401 10 Manual.Count131072.C073045.packed 64 cuts73045 = true := by
 decide +kernel
def cuts73046 : List PrefixCut := [⟨19,51103852,51103885⟩,
⟨64,169591112,169591214⟩]
theorem checked73046 : checkPrefixCuts (2^48) 9578217473 10 Manual.Count131072.C073046.packed 64 cuts73046 = true := by
 decide +kernel
def pointBounds73046 : List (Nat × Nat × Nat) := [(9578256384,116335720183677,116336109998036)]
theorem point_links_checked73046 : (cuts73046.take 1).map (fun c => (9578217473-1+2*2^10*c.k,116335669079825+c.lower,116336058894151+c.upper)) = pointBounds73046 := by
 decide +kernel
def cuts73047 : List PrefixCut := [⟨64,167414200,167414295⟩]
theorem checked73047 : checkPrefixCuts (2^48) 9578348545 10 Manual.Count131072.C073047.packed 64 cuts73047 = true := by
 decide +kernel
def cuts73048 : List PrefixCut := [⟨38,99530574,99530633⟩,
⟨64,167529448,167529545⟩]
theorem checked73048 : checkPrefixCuts (2^48) 9578479617 10 Manual.Count131072.C073048.packed 64 cuts73048 = true := by
 decide +kernel
def pointBounds73048 : List (Nat × Nat × Nat) := [(9578557440,116336105615711,116336495430293)]
theorem point_links_checked73048 : (cuts73048.take 1).map (fun c => (9578479617-1+2*2^10*c.k,116336006085137+c.lower,116336395899660+c.upper)) = pointBounds73048 := by
 decide +kernel
def cuts73049 : List PrefixCut := [⟨64,169731053,169731160⟩]
theorem checked73049 : checkPrefixCuts (2^48) 9578610689 10 Manual.Count131072.C073049.packed 64 cuts73049 = true := by
 decide +kernel
def cuts73050 : List PrefixCut := [⟨57,146661492,146661581⟩,
⟨64,163881097,163881196⟩]
theorem checked73050 : checkPrefixCuts (2^48) 9578741761 10 Manual.Count131072.C073050.packed 64 cuts73050 = true := by
 decide +kernel
def pointBounds73050 : List (Nat × Nat × Nat) := [(9578858496,116336490007130,116336879821946)]
theorem point_links_checked73050 : (cuts73050.take 1).map (fun c => (9578741761-1+2*2^10*c.k,116336343345638+c.lower,116336733160365+c.upper)) = pointBounds73050 := by
 decide +kernel
def cuts73051 : List PrefixCut := [⟨64,168227801,168227899⟩]
theorem checked73051 : checkPrefixCuts (2^48) 9578872833 10 Manual.Count131072.C073051.packed 64 cuts73051 = true := by
 decide +kernel
def cuts73052 : List PrefixCut := [⟨64,167902266,167902363⟩]
theorem checked73052 : checkPrefixCuts (2^48) 9579003905 10 Manual.Count131072.C073052.packed 64 cuts73052 = true := by
 decide +kernel
def cuts73053 : List PrefixCut := [⟨12,32410693,32410711⟩,
⟨64,164432689,164432777⟩]
theorem checked73053 : checkPrefixCuts (2^48) 9579134977 10 Manual.Count131072.C073053.packed 64 cuts73053 = true := by
 decide +kernel
def pointBounds73053 : List (Nat × Nat × Nat) := [(9579159552,116336875767495,116337265582534)]
theorem point_links_checked73053 : (cuts73053.take 1).map (fun c => (9579134977-1+2*2^10*c.k,116336843356802+c.lower,116337233171823+c.upper)) = pointBounds73053 := by
 decide +kernel
def cuts73054 : List PrefixCut := [⟨64,168514737,168514837⟩]
theorem checked73054 : checkPrefixCuts (2^48) 9579266049 10 Manual.Count131072.C073054.packed 64 cuts73054 = true := by
 decide +kernel
def cuts73055 : List PrefixCut := [⟨31,81127193,81127245⟩,
⟨64,169246998,169247106⟩]
theorem checked73055 : checkPrefixCuts (2^48) 9579397121 10 Manual.Count131072.C073055.packed 64 cuts73055 = true := by
 decide +kernel
def pointBounds73055 : List (Nat × Nat × Nat) := [(9579460608,116337257431421,116337647246682)]
theorem point_links_checked73055 : (cuts73055.take 1).map (fun c => (9579397121-1+2*2^10*c.k,116337176304228+c.lower,116337566119437+c.upper)) = pointBounds73055 := by
 decide +kernel
def cuts73056 : List PrefixCut := [⟨64,167246651,167246751⟩]
theorem checked73056 : checkPrefixCuts (2^48) 9579528193 10 Manual.Count131072.C073056.packed 64 cuts73056 = true := by
 decide +kernel
def cuts73057 : List PrefixCut := [⟨50,131456860,131456934⟩,
⟨64,167626348,167626443⟩]
theorem checked73057 : checkPrefixCuts (2^48) 9579659265 10 Manual.Count131072.C073057.packed 64 cuts73057 = true := by
 decide +kernel
def pointBounds73057 : List (Nat × Nat × Nat) := [(9579761664,116337644254737,116338034070228)]
theorem point_links_checked73057 : (cuts73057.take 1).map (fun c => (9579659265-1+2*2^10*c.k,116337512797877+c.lower,116337902613294+c.upper)) = pointBounds73057 := by
 decide +kernel
def cuts73058 : List PrefixCut := [⟨64,165567329,165567429⟩]
theorem checked73058 : checkPrefixCuts (2^48) 9579790337 10 Manual.Count131072.C073058.packed 64 cuts73058 = true := by
 decide +kernel
def cuts73059 : List PrefixCut := [⟨64,164331027,164331126⟩]
theorem checked73059 : checkPrefixCuts (2^48) 9579921409 10 Manual.Count131072.C073059.packed 64 cuts73059 = true := by
 decide +kernel
def cuts73060 : List PrefixCut := [⟨5,12457685,12457694⟩,
⟨64,168500892,168500997⟩]
theorem checked73060 : checkPrefixCuts (2^48) 9580052481 10 Manual.Count131072.C073060.packed 64 cuts73060 = true := by
 decide +kernel
def pointBounds73060 : List (Nat × Nat × Nat) := [(9580062720,116338022780266,116338412595986)]
theorem point_links_checked73060 : (cuts73060.take 1).map (fun c => (9580052481-1+2*2^10*c.k,116338010322581+c.lower,116338400138292+c.upper)) = pointBounds73060 := by
 decide +kernel
def cuts73061 : List PrefixCut := [⟨64,164679103,164679195⟩]
theorem checked73061 : checkPrefixCuts (2^48) 9580183553 10 Manual.Count131072.C073061.packed 64 cuts73061 = true := by
 decide +kernel
def cuts73062 : List PrefixCut := [⟨24,62580407,62580446⟩,
⟨64,167467978,167468082⟩]
theorem checked73062 : checkPrefixCuts (2^48) 9580314625 10 Manual.Count131072.C073062.packed 64 cuts73062 = true := by
 decide +kernel
def pointBounds73062 : List (Nat × Nat × Nat) := [(9580363776,116338406082983,116338795898930)]
theorem point_links_checked73062 : (cuts73062.take 1).map (fun c => (9580314625-1+2*2^10*c.k,116338343502576+c.lower,116338733318484+c.upper)) = pointBounds73062 := by
 decide +kernel
def cuts73063 : List PrefixCut := [⟨64,166672424,166672522⟩]
theorem checked73063 : checkPrefixCuts (2^48) 9580445697 10 Manual.Count131072.C073063.packed 64 cuts73063 = true := by
 decide +kernel
def cuts73064 : List PrefixCut := [⟨43,111524994,111525062⟩,
⟨64,166728903,166729001⟩]
theorem checked73064 : checkPrefixCuts (2^48) 9580576769 10 Manual.Count131072.C073064.packed 64 cuts73064 = true := by
 decide +kernel
def pointBounds73064 : List (Nat × Nat × Nat) := [(9580664832,116338789167972,116339178984150)]
theorem point_links_checked73064 : (cuts73064.take 1).map (fun c => (9580576769-1+2*2^10*c.k,116338677642978+c.lower,116339067459088+c.upper)) = pointBounds73064 := by
 decide +kernel
def cuts73065 : List PrefixCut := [⟨64,170957231,170957325⟩]
theorem checked73065 : checkPrefixCuts (2^48) 9580707841 10 Manual.Count131072.C073065.packed 64 cuts73065 = true := by
 decide +kernel
def cuts73066 : List PrefixCut := [⟨62,164785390,164785484⟩,
⟨64,170279178,170279275⟩]
theorem checked73066 : checkPrefixCuts (2^48) 9580838913 10 Manual.Count131072.C073066.packed 64 cuts73066 = true := by
 decide +kernel
def pointBounds73066 : List (Nat × Nat × Nat) := [(9580965888,116339180114502,116339569930898)]
theorem point_links_checked73066 : (cuts73066.take 1).map (fun c => (9580838913-1+2*2^10*c.k,116339015329112+c.lower,116339405145414+c.upper)) = pointBounds73066 := by
 decide +kernel
def cuts73067 : List PrefixCut := [⟨64,166810200,166810301⟩]
theorem checked73067 : checkPrefixCuts (2^48) 9580969985 10 Manual.Count131072.C073067.packed 64 cuts73067 = true := by
 decide +kernel
def cuts73068 : List PrefixCut := [⟨64,166484769,166484861⟩]
theorem checked73068 : checkPrefixCuts (2^48) 9581101057 10 Manual.Count131072.C073068.packed 64 cuts73068 = true := by
 decide +kernel
def cuts73069 : List PrefixCut := [⟨17,45212253,45212281⟩,
⟨64,168920827,168920927⟩]
theorem checked73069 : checkPrefixCuts (2^48) 9581232129 10 Manual.Count131072.C073069.packed 64 cuts73069 = true := by
 decide +kernel
def pointBounds73069 : List (Nat × Nat × Nat) := [(9581266944,116339564115512,116339953932132)]
theorem point_links_checked73069 : (cuts73069.take 1).map (fun c => (9581232129-1+2*2^10*c.k,116339518903259+c.lower,116339908719851+c.upper)) = pointBounds73069 := by
 decide +kernel
def cuts73070 : List PrefixCut := [⟨64,167860930,167861033⟩]
theorem checked73070 : checkPrefixCuts (2^48) 9581363201 10 Manual.Count131072.C073070.packed 64 cuts73070 = true := by
 decide +kernel
def cuts73071 : List PrefixCut := [⟨36,93594538,93594594⟩,
⟨64,168093638,168093742⟩]
theorem checked73071 : checkPrefixCuts (2^48) 9581494273 10 Manual.Count131072.C073071.packed 64 cuts73071 = true := by
 decide +kernel
def pointBounds73071 : List (Nat × Nat × Nat) := [(9581568000,116339949279554,116340339096405)]
theorem point_links_checked73071 : (cuts73071.take 1).map (fun c => (9581494273-1+2*2^10*c.k,116339855685016+c.lower,116340245501811+c.upper)) = pointBounds73071 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000095
