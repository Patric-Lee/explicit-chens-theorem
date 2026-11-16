import PlattAssemblyKernel
import PlattCertificates.Count131072.C074992
import PlattCertificates.Count131072.C074993
import PlattCertificates.Count131072.C074994
import PlattCertificates.Count131072.C074995
import PlattCertificates.Count131072.C074996
import PlattCertificates.Count131072.C074997
import PlattCertificates.Count131072.C074998
import PlattCertificates.Count131072.C074999
import PlattCertificates.Count131072.C075000
import PlattCertificates.Count131072.C075001
import PlattCertificates.Count131072.C075002
import PlattCertificates.Count131072.C075003
import PlattCertificates.Count131072.C075004
import PlattCertificates.Count131072.C075005
import PlattCertificates.Count131072.C075006
import PlattCertificates.Count131072.C075007
import PlattCertificates.Count131072.C075008
import PlattCertificates.Count131072.C075009
import PlattCertificates.Count131072.C075010
import PlattCertificates.Count131072.C075011
import PlattCertificates.Count131072.C075012
import PlattCertificates.Count131072.C075013
import PlattCertificates.Count131072.C075014
import PlattCertificates.Count131072.C075015
import PlattCertificates.Count131072.C075016
import PlattCertificates.Count131072.C075017
import PlattCertificates.Count131072.C075018
import PlattCertificates.Count131072.C075019
import PlattCertificates.Count131072.C075020
import PlattCertificates.Count131072.C075021
import PlattCertificates.Count131072.C075022
import PlattCertificates.Count131072.C075023
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000156
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74992 : List PrefixCut := [⟨64,162759020,162759114⟩]
theorem checked74992 : checkPrefixCuts (2^48) 9833283585 10 Manual.Count131072.C074992.packed 64 cuts74992 = true := by
 decide +kernel
def cuts74993 : List PrefixCut := [⟨64,163873191,163873280⟩]
theorem checked74993 : checkPrefixCuts (2^48) 9833414657 10 Manual.Count131072.C074993.packed 64 cuts74993 = true := by
 decide +kernel
def cuts74994 : List PrefixCut := [⟨5,12766274,12766282⟩,
⟨64,161638359,161638462⟩]
theorem checked74994 : checkPrefixCuts (2^48) 9833545729 10 Manual.Count131072.C074994.packed 64 cuts74994 = true := by
 decide +kernel
def pointBounds74994 : List (Nat × Nat × Nat) := [(9833555968,116657746386320,116658136393125)]
theorem point_links_checked74994 : (cuts74994.take 1).map (fun c => (9833545729-1+2*2^10*c.k,116657733620046+c.lower,116658123626843+c.upper)) = pointBounds74994 := by
 decide +kernel
def cuts74995 : List PrefixCut := [⟨64,162752517,162752610⟩]
theorem checked74995 : checkPrefixCuts (2^48) 9833676801 10 Manual.Count131072.C074995.packed 64 cuts74995 = true := by
 decide +kernel
def cuts74996 : List PrefixCut := [⟨28,73332386,73332426⟩,
⟨64,165469529,165469630⟩]
theorem checked74996 : checkPrefixCuts (2^48) 9833807873 10 Manual.Count131072.C074996.packed 64 cuts74996 = true := by
 decide +kernel
def pointBounds74996 : List (Nat × Nat × Nat) := [(9833865216,116658131343308,116658521350341)]
theorem point_links_checked74996 : (cuts74996.take 1).map (fun c => (9833807873-1+2*2^10*c.k,116658058010922+c.lower,116658448017915+c.upper)) = pointBounds74996 := by
 decide +kernel
def cuts74997 : List PrefixCut := [⟨64,165553181,165553280⟩]
theorem checked74997 : checkPrefixCuts (2^48) 9833938945 10 Manual.Count131072.C074997.packed 64 cuts74997 = true := by
 decide +kernel
def cuts74998 : List PrefixCut := [⟨51,131261718,131261799⟩,
⟨64,164921283,164921384⟩]
theorem checked74998 : checkPrefixCuts (2^48) 9834070017 10 Manual.Count131072.C074998.packed 64 cuts74998 = true := by
 decide +kernel
def pointBounds74998 : List (Nat × Nat × Nat) := [(9834174464,116658520295350,116658910302624)]
theorem point_links_checked74998 : (cuts74998.take 1).map (fun c => (9834070017-1+2*2^10*c.k,116658389033632+c.lower,116658779040825+c.upper)) = pointBounds74998 := by
 decide +kernel
def cuts74999 : List PrefixCut := [⟨64,162056910,162057007⟩]
theorem checked74999 : checkPrefixCuts (2^48) 9834201089 10 Manual.Count131072.C074999.packed 64 cuts74999 = true := by
 decide +kernel
def cuts75000 : List PrefixCut := [⟨64,164716545,164716635⟩]
theorem checked75000 : checkPrefixCuts (2^48) 9834332161 10 Manual.Count131072.C075000.packed 64 cuts75000 = true := by
 decide +kernel
def cuts75001 : List PrefixCut := [⟨10,25043590,25043605⟩,
⟨64,161365678,161365767⟩]
theorem checked75001 : checkPrefixCuts (2^48) 9834463233 10 Manual.Count131072.C075001.packed 64 cuts75001 = true := by
 decide +kernel
def pointBounds75001 : List (Nat × Nat × Nat) := [(9834483712,116658905771960,116659295779456)]
theorem point_links_checked75001 : (cuts75001.take 1).map (fun c => (9834463233-1+2*2^10*c.k,116658880728370+c.lower,116659270735851+c.upper)) = pointBounds75001 := by
 decide +kernel
def cuts75002 : List PrefixCut := [⟨64,164139741,164139848⟩]
theorem checked75002 : checkPrefixCuts (2^48) 9834594305 10 Manual.Count131072.C075002.packed 64 cuts75002 = true := by
 decide +kernel
def cuts75003 : List PrefixCut := [⟨33,82627137,82627186⟩,
⟨64,159901739,159901841⟩]
theorem checked75003 : checkPrefixCuts (2^48) 9834725377 10 Manual.Count131072.C075003.packed 64 cuts75003 = true := by
 decide +kernel
def pointBounds75003 : List (Nat × Nat × Nat) := [(9834792960,116659288860926,116659678868652)]
theorem point_links_checked75003 : (cuts75003.take 1).map (fun c => (9834725377-1+2*2^10*c.k,116659206233789+c.lower,116659596241466+c.upper)) = pointBounds75003 := by
 decide +kernel
def cuts75004 : List PrefixCut := [⟨64,163133659,163133758⟩]
theorem checked75004 : checkPrefixCuts (2^48) 9834856449 10 Manual.Count131072.C075004.packed 64 cuts75004 = true := by
 decide +kernel
def cuts75005 : List PrefixCut := [⟨56,142840349,142840432⟩,
⟨64,163875604,163875700⟩]
theorem checked75005 : checkPrefixCuts (2^48) 9834987521 10 Manual.Count131072.C075005.packed 64 cuts75005 = true := by
 decide +kernel
def pointBounds75005 : List (Nat × Nat × Nat) := [(9835102208,116659672109536,116660062117497)]
theorem point_links_checked75005 : (cuts75005.take 1).map (fun c => (9834987521-1+2*2^10*c.k,116659529269187+c.lower,116659919277065+c.upper)) = pointBounds75005 := by
 decide +kernel
def cuts75006 : List PrefixCut := [⟨64,163186563,163186659⟩]
theorem checked75006 : checkPrefixCuts (2^48) 9835118593 10 Manual.Count131072.C075006.packed 64 cuts75006 = true := by
 decide +kernel
def cuts75007 : List PrefixCut := [⟨64,163957087,163957187⟩]
theorem checked75007 : checkPrefixCuts (2^48) 9835249665 10 Manual.Count131072.C075007.packed 64 cuts75007 = true := by
 decide +kernel
def cuts75008 : List PrefixCut := [⟨15,37633408,37633434⟩,
⟨64,164641746,164641847⟩]
theorem checked75008 : checkPrefixCuts (2^48) 9835380737 10 Manual.Count131072.C075008.packed 64 cuts75008 = true := by
 decide +kernel
def pointBounds75008 : List (Nat × Nat × Nat) := [(9835411456,116660057921849,116660447930045)]
theorem point_links_checked75008 : (cuts75008.take 1).map (fun c => (9835380737-1+2*2^10*c.k,116660020288441+c.lower,116660410296611+c.upper)) = pointBounds75008 := by
 decide +kernel
def cuts75009 : List PrefixCut := [⟨64,163695165,163695257⟩]
theorem checked75009 : checkPrefixCuts (2^48) 9835511809 10 Manual.Count131072.C075009.packed 64 cuts75009 = true := by
 decide +kernel
def cuts75010 : List PrefixCut := [⟨38,97243051,97243109⟩,
⟨64,162834452,162834552⟩]
theorem checked75010 : checkPrefixCuts (2^48) 9835642881 10 Manual.Count131072.C075010.packed 64 cuts75010 = true := by
 decide +kernel
def pointBounds75010 : List (Nat × Nat × Nat) := [(9835720704,116660445868403,116660835876824)]
theorem point_links_checked75010 : (cuts75010.take 1).map (fun c => (9835642881-1+2*2^10*c.k,116660348625352+c.lower,116660738633715+c.upper)) = pointBounds75010 := by
 decide +kernel
def cuts75011 : List PrefixCut := [⟨64,164434835,164434932⟩]
theorem checked75011 : checkPrefixCuts (2^48) 9835773953 10 Manual.Count131072.C075011.packed 64 cuts75011 = true := by
 decide +kernel
def cuts75012 : List PrefixCut := [⟨61,153930294,153930391⟩,
⟨64,162028822,162028924⟩]
theorem checked75012 : checkPrefixCuts (2^48) 9835905025 10 Manual.Count131072.C075012.packed 64 cuts75012 = true := by
 decide +kernel
def pointBounds75012 : List (Nat × Nat × Nat) := [(9836029952,116660829824933,116661219833590)]
theorem point_links_checked75012 : (cuts75012.take 1).map (fun c => (9835905025-1+2*2^10*c.k,116660675894639+c.lower,116661065903199+c.upper)) = pointBounds75012 := by
 decide +kernel
def cuts75013 : List PrefixCut := [⟨64,161339882,161339982⟩]
theorem checked75013 : checkPrefixCuts (2^48) 9836036097 10 Manual.Count131072.C075013.packed 64 cuts75013 = true := by
 decide +kernel
def cuts75014 : List PrefixCut := [⟨64,164256572,164256669⟩]
theorem checked75014 : checkPrefixCuts (2^48) 9836167169 10 Manual.Count131072.C075014.packed 64 cuts75014 = true := by
 decide +kernel
def cuts75015 : List PrefixCut := [⟨20,50621486,50621519⟩,
⟨64,162794981,162795083⟩]
theorem checked75015 : checkPrefixCuts (2^48) 9836298241 10 Manual.Count131072.C075015.packed 64 cuts75015 = true := by
 decide +kernel
def pointBounds75015 : List (Nat × Nat × Nat) := [(9836339200,116661214141401,116661604150293)]
theorem point_links_checked75015 : (cuts75015.take 1).map (fun c => (9836298241-1+2*2^10*c.k,116661163519915+c.lower,116661553528774+c.upper)) = pointBounds75015 := by
 decide +kernel
def cuts75016 : List PrefixCut := [⟨64,164280808,164280902⟩]
theorem checked75016 : checkPrefixCuts (2^48) 9836429313 10 Manual.Count131072.C075016.packed 64 cuts75016 = true := by
 decide +kernel
def cuts75017 : List PrefixCut := [⟨43,109853164,109853230⟩,
⟨64,165308754,165308855⟩]
theorem checked75017 : checkPrefixCuts (2^48) 9836560385 10 Manual.Count131072.C075017.packed 64 cuts75017 = true := by
 decide +kernel
def pointBounds75017 : List (Nat × Nat × Nat) := [(9836648448,116661600448868,116661990457989)]
theorem point_links_checked75017 : (cuts75017.take 1).map (fun c => (9836560385-1+2*2^10*c.k,116661490595704+c.lower,116661880604759+c.upper)) = pointBounds75017 := by
 decide +kernel
def cuts75018 : List PrefixCut := [⟨64,162731236,162731333⟩]
theorem checked75018 : checkPrefixCuts (2^48) 9836691457 10 Manual.Count131072.C075018.packed 64 cuts75018 = true := by
 decide +kernel
def cuts75019 : List PrefixCut := [⟨64,162900763,162900858⟩]
theorem checked75019 : checkPrefixCuts (2^48) 9836822529 10 Manual.Count131072.C075019.packed 64 cuts75019 = true := by
 decide +kernel
def cuts75020 : List PrefixCut := [⟨2,5007455,5007457⟩,
⟨64,164815722,164815817⟩]
theorem checked75020 : checkPrefixCuts (2^48) 9836953601 10 Manual.Count131072.C075020.packed 64 cuts75020 = true := by
 decide +kernel
def pointBounds75020 : List (Nat × Nat × Nat) := [(9836957696,116661986543912,116662376553262)]
theorem point_links_checked75020 : (cuts75020.take 1).map (fun c => (9836953601-1+2*2^10*c.k,116661981536457+c.lower,116662371545805+c.upper)) = pointBounds75020 := by
 decide +kernel
def cuts75021 : List PrefixCut := [⟨64,165528871,165528966⟩]
theorem checked75021 : checkPrefixCuts (2^48) 9837084673 10 Manual.Count131072.C075021.packed 64 cuts75021 = true := by
 decide +kernel
def cuts75022 : List PrefixCut := [⟨25,63607130,63607165⟩,
⟨64,162350601,162350695⟩]
theorem checked75022 : checkPrefixCuts (2^48) 9837215745 10 Manual.Count131072.C075022.packed 64 cuts75022 = true := by
 decide +kernel
def pointBounds75022 : List (Nat × Nat × Nat) := [(9837266944,116662375488180,116662765497753)]
theorem point_links_checked75022 : (cuts75022.take 1).map (fun c => (9837215745-1+2*2^10*c.k,116662311881050+c.lower,116662701890588+c.upper)) = pointBounds75022 := by
 decide +kernel
def cuts75023 : List PrefixCut := [⟨64,163092369,163092472⟩]
theorem checked75023 : checkPrefixCuts (2^48) 9837346817 10 Manual.Count131072.C075023.packed 64 cuts75023 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000156
