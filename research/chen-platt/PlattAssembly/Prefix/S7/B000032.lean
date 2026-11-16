import PlattAssemblyKernel
import PlattCertificates.Count131072.C061024
import PlattCertificates.Count131072.C061025
import PlattCertificates.Count131072.C061026
import PlattCertificates.Count131072.C061027
import PlattCertificates.Count131072.C061028
import PlattCertificates.Count131072.C061029
import PlattCertificates.Count131072.C061030
import PlattCertificates.Count131072.C061031
import PlattCertificates.Count131072.C061032
import PlattCertificates.Count131072.C061033
import PlattCertificates.Count131072.C061034
import PlattCertificates.Count131072.C061035
import PlattCertificates.Count131072.C061036
import PlattCertificates.Count131072.C061037
import PlattCertificates.Count131072.C061038
import PlattCertificates.Count131072.C061039
import PlattCertificates.Count131072.C061040
import PlattCertificates.Count131072.C061041
import PlattCertificates.Count131072.C061042
import PlattCertificates.Count131072.C061043
import PlattCertificates.Count131072.C061044
import PlattCertificates.Count131072.C061045
import PlattCertificates.Count131072.C061046
import PlattCertificates.Count131072.C061047
import PlattCertificates.Count131072.C061048
import PlattCertificates.Count131072.C061049
import PlattCertificates.Count131072.C061050
import PlattCertificates.Count131072.C061051
import PlattCertificates.Count131072.C061052
import PlattCertificates.Count131072.C061053
import PlattCertificates.Count131072.C061054
import PlattCertificates.Count131072.C061055
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000032
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61024 : List PrefixCut := [⟨56,175690388,175690484⟩,
⟨64,200733537,200733648⟩]
theorem checked61024 : checkPrefixCuts (2^48) 8002469889 10 Manual.Count131072.C061024.packed 64 cuts61024 = true := by
 decide +kernel
def pointBounds61024 : List (Nat × Nat × Nat) := [(8002584576,114125854641381,114126243168138)]
theorem point_links_checked61024 : (cuts61024.take 1).map (fun c => (8002469889-1+2*2^10*c.k,114125678950993+c.lower,114126067477654+c.upper)) = pointBounds61024 := by
 decide +kernel
def cuts61025 : List PrefixCut := [⟨64,201117148,201117260⟩]
theorem checked61025 : checkPrefixCuts (2^48) 8002600961 10 Manual.Count131072.C061025.packed 64 cuts61025 = true := by
 decide +kernel
def cuts61026 : List PrefixCut := [⟨51,161053158,161053248⟩,
⟨64,202591093,202591206⟩]
theorem checked61026 : checkPrefixCuts (2^48) 8002732033 10 Manual.Count131072.C061026.packed 64 cuts61026 = true := by
 decide +kernel
def pointBounds61026 : List (Nat × Nat × Nat) := [(8002836480,114126241854836,114126630381810)]
theorem point_links_checked61026 : (cuts61026.take 1).map (fun c => (8002732033-1+2*2^10*c.k,114126080801678+c.lower,114126469328562+c.upper)) = pointBounds61026 := by
 decide +kernel
def cuts61027 : List PrefixCut := [⟨64,203185686,203185804⟩]
theorem checked61027 : checkPrefixCuts (2^48) 8002863105 10 Manual.Count131072.C061027.packed 64 cuts61027 = true := by
 decide +kernel
def cuts61028 : List PrefixCut := [⟨46,146979569,146979654⟩,
⟨64,204729866,204729984⟩]
theorem checked61028 : checkPrefixCuts (2^48) 8002994177 10 Manual.Count131072.C061028.packed 64 cuts61028 = true := by
 decide +kernel
def pointBounds61028 : List (Nat × Nat × Nat) := [(8003088384,114126633558026,114127022085226)]
theorem point_links_checked61028 : (cuts61028.take 1).map (fun c => (8002994177-1+2*2^10*c.k,114126486578457+c.lower,114126875105572+c.upper)) = pointBounds61028 := by
 decide +kernel
def cuts61029 : List PrefixCut := [⟨64,202299755,202299874⟩]
theorem checked61029 : checkPrefixCuts (2^48) 8003125249 10 Manual.Count131072.C061029.packed 64 cuts61029 = true := by
 decide +kernel
def cuts61030 : List PrefixCut := [⟨41,130093327,130093404⟩,
⟨64,203668078,203668197⟩]
theorem checked61030 : checkPrefixCuts (2^48) 8003256321 10 Manual.Count131072.C061030.packed 64 cuts61030 = true := by
 decide +kernel
def pointBounds61030 : List (Nat × Nat × Nat) := [(8003340288,114127023701405,114127412228834)]
theorem point_links_checked61030 : (cuts61030.take 1).map (fun c => (8003256321-1+2*2^10*c.k,114126893608078+c.lower,114127282135430+c.upper)) = pointBounds61030 := by
 decide +kernel
def cuts61031 : List PrefixCut := [⟨64,201906271,201906388⟩]
theorem checked61031 : checkPrefixCuts (2^48) 8003387393 10 Manual.Count131072.C061031.packed 64 cuts61031 = true := by
 decide +kernel
def cuts61032 : List PrefixCut := [⟨36,112891633,112891697⟩,
⟨64,200988588,200988702⟩]
theorem checked61032 : checkPrefixCuts (2^48) 8003518465 10 Manual.Count131072.C061032.packed 64 cuts61032 = true := by
 decide +kernel
def pointBounds61032 : List (Nat × Nat × Nat) := [(8003592192,114127412074060,114127800601712)]
theorem point_links_checked61032 : (cuts61032.take 1).map (fun c => (8003518465-1+2*2^10*c.k,114127299182427+c.lower,114127687710015+c.upper)) = pointBounds61032 := by
 decide +kernel
def cuts61033 : List PrefixCut := [⟨64,206682503,206682616⟩]
theorem checked61033 : checkPrefixCuts (2^48) 8003649537 10 Manual.Count131072.C061033.packed 64 cuts61033 = true := by
 decide +kernel
def cuts61034 : List PrefixCut := [⟨31,98012115,98012167⟩,
⟨64,202388708,202388820⟩]
theorem checked61034 : checkPrefixCuts (2^48) 8003780609 10 Manual.Count131072.C061034.packed 64 cuts61034 = true := by
 decide +kernel
def pointBounds61034 : List (Nat × Nat × Nat) := [(8003844096,114127804865633,114128193393500)]
theorem point_links_checked61034 : (cuts61034.take 1).map (fun c => (8003780609-1+2*2^10*c.k,114127706853518+c.lower,114128095381333+c.upper)) = pointBounds61034 := by
 decide +kernel
def cuts61035 : List PrefixCut := [⟨64,203264558,203264673⟩]
theorem checked61035 : checkPrefixCuts (2^48) 8003911681 10 Manual.Count131072.C061035.packed 64 cuts61035 = true := by
 decide +kernel
def cuts61036 : List PrefixCut := [⟨26,81375218,81375265⟩,
⟨64,202171068,202171184⟩]
theorem checked61036 : checkPrefixCuts (2^48) 8004042753 10 Manual.Count131072.C061036.packed 64 cuts61036 = true := by
 decide +kernel
def pointBounds61036 : List (Nat × Nat × Nat) := [(8004096000,114128193882002,114128582410091)]
theorem point_links_checked61036 : (cuts61036.take 1).map (fun c => (8004042753-1+2*2^10*c.k,114128112506784+c.lower,114128501034826+c.upper)) = pointBounds61036 := by
 decide +kernel
def cuts61037 : List PrefixCut := [⟨64,200620465,200620581⟩]
theorem checked61037 : checkPrefixCuts (2^48) 8004173825 10 Manual.Count131072.C061037.packed 64 cuts61037 = true := by
 decide +kernel
def cuts61038 : List PrefixCut := [⟨21,66357005,66357040⟩,
⟨64,203008417,203008532⟩]
theorem checked61038 : checkPrefixCuts (2^48) 8004304897 10 Manual.Count131072.C061038.packed 64 cuts61038 = true := by
 decide +kernel
def pointBounds61038 : List (Nat × Nat × Nat) := [(8004347904,114128581655322,114128970183631)]
theorem point_links_checked61038 : (cuts61038.take 1).map (fun c => (8004304897-1+2*2^10*c.k,114128515298317+c.lower,114128903826591+c.upper)) = pointBounds61038 := by
 decide +kernel
def cuts61039 : List PrefixCut := [⟨64,200121598,200121719⟩]
theorem checked61039 : checkPrefixCuts (2^48) 8004435969 10 Manual.Count131072.C061039.packed 64 cuts61039 = true := by
 decide +kernel
def cuts61040 : List PrefixCut := [⟨16,49898023,49898052⟩,
⟨64,201419378,201419494⟩]
theorem checked61040 : checkPrefixCuts (2^48) 8004567041 10 Manual.Count131072.C061040.packed 64 cuts61040 = true := by
 decide +kernel
def pointBounds61040 : List (Nat × Nat × Nat) := [(8004599808,114128968326355,114129356854894)]
theorem point_links_checked61040 : (cuts61040.take 1).map (fun c => (8004567041-1+2*2^10*c.k,114128918428332+c.lower,114129306956842+c.upper)) = pointBounds61040 := by
 decide +kernel
def cuts61041 : List PrefixCut := [⟨64,202435835,202435956⟩]
theorem checked61041 : checkPrefixCuts (2^48) 8004698113 10 Manual.Count131072.C061041.packed 64 cuts61041 = true := by
 decide +kernel
def cuts61042 : List PrefixCut := [⟨11,35303739,35303760⟩,
⟨64,205667492,205667610⟩]
theorem checked61042 : checkPrefixCuts (2^48) 8004829185 10 Manual.Count131072.C061042.packed 64 cuts61042 = true := by
 decide +kernel
def pointBounds61042 : List (Nat × Nat × Nat) := [(8004851712,114129357587284,114129746116052)]
theorem point_links_checked61042 : (cuts61042.take 1).map (fun c => (8004829185-1+2*2^10*c.k,114129322283545+c.lower,114129710812292+c.upper)) = pointBounds61042 := by
 decide +kernel
def cuts61043 : List PrefixCut := [⟨64,200073325,200073442⟩]
theorem checked61043 : checkPrefixCuts (2^48) 8004960257 10 Manual.Count131072.C061043.packed 64 cuts61043 = true := by
 decide +kernel
def cuts61044 : List PrefixCut := [⟨6,19796183,19796194⟩,
⟨64,202847839,202847950⟩]
theorem checked61044 : checkPrefixCuts (2^48) 8005091329 10 Manual.Count131072.C061044.packed 64 cuts61044 = true := by
 decide +kernel
def pointBounds61044 : List (Nat × Nat × Nat) := [(8005103616,114129747820545,114130136349538)]
theorem point_links_checked61044 : (cuts61044.take 1).map (fun c => (8005091329-1+2*2^10*c.k,114129728024362+c.lower,114130116553344+c.upper)) = pointBounds61044 := by
 decide +kernel
def cuts61045 : List PrefixCut := [⟨64,202985162,202985276⟩]
theorem checked61045 : checkPrefixCuts (2^48) 8005222401 10 Manual.Count131072.C061045.packed 64 cuts61045 = true := by
 decide +kernel
def cuts61046 : List PrefixCut := [⟨1,3199635,3199637⟩,
⟨64,202735709,202735824⟩]
theorem checked61046 : checkPrefixCuts (2^48) 8005353473 10 Manual.Count131072.C061046.packed 64 cuts61046 = true := by
 decide +kernel
def pointBounds61046 : List (Nat × Nat × Nat) := [(8005355520,114130137056998,114130525586207)]
theorem point_links_checked61046 : (cuts61046.take 1).map (fun c => (8005353473-1+2*2^10*c.k,114130133857363+c.lower,114130522386570+c.upper)) = pointBounds61046 := by
 decide +kernel
def cuts61047 : List PrefixCut := [⟨60,189020094,189020198⟩,
⟨64,201325990,201326099⟩]
theorem checked61047 : checkPrefixCuts (2^48) 8005484545 10 Manual.Count131072.C061047.packed 64 cuts61047 = true := by
 decide +kernel
def pointBounds61047 : List (Nat × Nat × Nat) := [(8005607424,114130525613166,114130914142592)]
theorem point_links_checked61047 : (cuts61047.take 1).map (fun c => (8005484545-1+2*2^10*c.k,114130336593072+c.lower,114130725122394+c.upper)) = pointBounds61047 := by
 decide +kernel
def cuts61048 : List PrefixCut := [⟨64,201814930,201815044⟩]
theorem checked61048 : checkPrefixCuts (2^48) 8005615617 10 Manual.Count131072.C061048.packed 64 cuts61048 = true := by
 decide +kernel
def cuts61049 : List PrefixCut := [⟨55,175161425,175161528⟩,
⟨64,204132086,204132206⟩]
theorem checked61049 : checkPrefixCuts (2^48) 8005746689 10 Manual.Count131072.C061049.packed 64 cuts61049 = true := by
 decide +kernel
def pointBounds61049 : List (Nat × Nat × Nat) := [(8005859328,114130914895417,114131303425065)]
theorem point_links_checked61049 : (cuts61049.take 1).map (fun c => (8005746689-1+2*2^10*c.k,114130739733992+c.lower,114131128263537+c.upper)) = pointBounds61049 := by
 decide +kernel
def cuts61050 : List PrefixCut := [⟨64,204234231,204234345⟩]
theorem checked61050 : checkPrefixCuts (2^48) 8005877761 10 Manual.Count131072.C061050.packed 64 cuts61050 = true := by
 decide +kernel
def cuts61051 : List PrefixCut := [⟨50,160916925,160917014⟩,
⟨64,203949634,203949746⟩]
theorem checked61051 : checkPrefixCuts (2^48) 8006008833 10 Manual.Count131072.C061051.packed 64 cuts61051 = true := by
 decide +kernel
def pointBounds61051 : List (Nat × Nat × Nat) := [(8006111232,114131309017234,114131697547102)]
theorem point_links_checked61051 : (cuts61051.take 1).map (fun c => (8006008833-1+2*2^10*c.k,114131148100309+c.lower,114131536630088+c.upper)) = pointBounds61051 := by
 decide +kernel
def cuts61052 : List PrefixCut := [⟨64,202856419,202856537⟩]
theorem checked61052 : checkPrefixCuts (2^48) 8006139905 10 Manual.Count131072.C061052.packed 64 cuts61052 = true := by
 decide +kernel
def cuts61053 : List PrefixCut := [⟨45,143755344,143755423⟩,
⟨64,203942952,203943065⟩]
theorem checked61053 : checkPrefixCuts (2^48) 8006270977 10 Manual.Count131072.C061053.packed 64 cuts61053 = true := by
 decide +kernel
def pointBounds61053 : List (Nat × Nat × Nat) := [(8006363136,114131698661706,114132087191794)]
theorem point_links_checked61053 : (cuts61053.take 1).map (fun c => (8006270977-1+2*2^10*c.k,114131554906362+c.lower,114131943436371+c.upper)) = pointBounds61053 := by
 decide +kernel
def cuts61054 : List PrefixCut := [⟨64,199966992,199967106⟩]
theorem checked61054 : checkPrefixCuts (2^48) 8006402049 10 Manual.Count131072.C061054.packed 64 cuts61054 = true := by
 decide +kernel
def cuts61055 : List PrefixCut := [⟨40,125012866,125012940⟩,
⟨64,200807444,200807562⟩]
theorem checked61055 : checkPrefixCuts (2^48) 8006533121 10 Manual.Count131072.C061055.packed 64 cuts61055 = true := by
 decide +kernel
def pointBounds61055 : List (Nat × Nat × Nat) := [(8006615040,114132083829172,114132472359482)]
theorem point_links_checked61055 : (cuts61055.take 1).map (fun c => (8006533121-1+2*2^10*c.k,114131958816306+c.lower,114132347346542+c.upper)) = pointBounds61055 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000032
