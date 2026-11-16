import PlattAssemblyKernel
import PlattCertificates.Count131072.C039024
import PlattCertificates.Count131072.C039025
import PlattCertificates.Count131072.C039026
import PlattCertificates.Count131072.C039027
import PlattCertificates.Count131072.C039028
import PlattCertificates.Count131072.C039029
import PlattCertificates.Count131072.C039030
import PlattCertificates.Count131072.C039031
import PlattCertificates.Count131072.C039032
import PlattCertificates.Count131072.C039033
import PlattCertificates.Count131072.C039034
import PlattCertificates.Count131072.C039035
import PlattCertificates.Count131072.C039036
import PlattCertificates.Count131072.C039037
import PlattCertificates.Count131072.C039038
import PlattCertificates.Count131072.C039039
import PlattCertificates.Count131072.C039040
import PlattCertificates.Count131072.C039041
import PlattCertificates.Count131072.C039042
import PlattCertificates.Count131072.C039043
import PlattCertificates.Count131072.C039044
import PlattCertificates.Count131072.C039045
import PlattCertificates.Count131072.C039046
import PlattCertificates.Count131072.C039047
import PlattCertificates.Count131072.C039048
import PlattCertificates.Count131072.C039049
import PlattCertificates.Count131072.C039050
import PlattCertificates.Count131072.C039051
import PlattCertificates.Count131072.C039052
import PlattCertificates.Count131072.C039053
import PlattCertificates.Count131072.C039054
import PlattCertificates.Count131072.C039055
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000282
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts39024 : List PrefixCut := [⟨30,151654704,151654791⟩,
⟨64,327721468,327721660⟩]
theorem checked39024 : checkPrefixCuts (2^48) 5118885889 10 Manual.Count131072.C039024.packed 64 cuts39024 = true := by
 decide +kernel
def pointBounds39024 : List (Nat × Nat × Nat) := [(5118947328,108555757596097,108556142916684)]
theorem point_links_checked39024 : (cuts39024.take 1).map (fun c => (5118885889-1+2*2^10*c.k,108555605941393+c.lower,108555991261893+c.upper)) = pointBounds39024 := by
 decide +kernel
def cuts39025 : List PrefixCut := [⟨45,229400053,229400191⟩,
⟨64,326393454,326393649⟩]
theorem checked39025 : checkPrefixCuts (2^48) 5119016961 10 Manual.Count131072.C039025.packed 64 cuts39025 = true := by
 decide +kernel
def pointBounds39025 : List (Nat × Nat × Nat) := [(5119109120,108556163062914,108556548383744)]
theorem point_links_checked39025 : (cuts39025.take 1).map (fun c => (5119016961-1+2*2^10*c.k,108555933662861+c.lower,108556318983553+c.upper)) = pointBounds39025 := by
 decide +kernel
def cuts39026 : List PrefixCut := [⟨60,303731918,303732093⟩,
⟨64,324350675,324350862⟩]
theorem checked39026 : checkPrefixCuts (2^48) 5119148033 10 Manual.Count131072.C039026.packed 64 cuts39026 = true := by
 decide +kernel
def pointBounds39026 : List (Nat × Nat × Nat) := [(5119270912,108556563788233,108556949109295)]
theorem point_links_checked39026 : (cuts39026.take 1).map (fun c => (5119148033-1+2*2^10*c.k,108556260056315+c.lower,108556645377202+c.upper)) = pointBounds39026 := by
 decide +kernel
def cuts39027 : List PrefixCut := [⟨64,317744435,317744627⟩]
theorem checked39027 : checkPrefixCuts (2^48) 5119279105 10 Manual.Count131072.C039027.packed 64 cuts39027 = true := by
 decide +kernel
def cuts39028 : List PrefixCut := [⟨11,54596906,54596940⟩,
⟨64,325378680,325378878⟩]
theorem checked39028 : checkPrefixCuts (2^48) 5119410177 10 Manual.Count131072.C039028.packed 64 cuts39028 = true := by
 decide +kernel
def pointBounds39028 : List (Nat × Nat × Nat) := [(5119432704,108556956748331,108557342069631)]
theorem point_links_checked39028 : (cuts39028.take 1).map (fun c => (5119410177-1+2*2^10*c.k,108556902151425+c.lower,108557287472691+c.upper)) = pointBounds39028 := by
 decide +kernel
def cuts39029 : List PrefixCut := [⟨26,131622608,131622685⟩,
⟨64,323885918,323886111⟩]
theorem checked39029 : checkPrefixCuts (2^48) 5119541249 10 Manual.Count131072.C039029.packed 64 cuts39029 = true := by
 decide +kernel
def pointBounds39029 : List (Nat × Nat × Nat) := [(5119594496,108557359152713,108557744474254)]
theorem point_links_checked39029 : (cuts39029.take 1).map (fun c => (5119541249-1+2*2^10*c.k,108557227530105+c.lower,108557612851569+c.upper)) = pointBounds39029 := by
 decide +kernel
def cuts39030 : List PrefixCut := [⟨41,206334808,206334933⟩,
⟨64,323107930,323108124⟩]
theorem checked39030 : checkPrefixCuts (2^48) 5119672321 10 Manual.Count131072.C039030.packed 64 cuts39030 = true := by
 decide +kernel
def pointBounds39030 : List (Nat × Nat × Nat) := [(5119756288,108557757750831,108558143072613)]
theorem point_links_checked39030 : (cuts39030.take 1).map (fun c => (5119672321-1+2*2^10*c.k,108557551416023+c.lower,108557936737680+c.upper)) = pointBounds39030 := by
 decide +kernel
def cuts39031 : List PrefixCut := [⟨56,280657907,280658073⟩,
⟨64,320020977,320021167⟩]
theorem checked39031 : checkPrefixCuts (2^48) 5119803393 10 Manual.Count131072.C039031.packed 64 cuts39031 = true := by
 decide +kernel
def pointBounds39031 : List (Nat × Nat × Nat) := [(5119918080,108558155181860,108558540503877)]
theorem point_links_checked39031 : (cuts39031.take 1).map (fun c => (5119803393-1+2*2^10*c.k,108557874523953+c.lower,108558259845804+c.upper)) = pointBounds39031 := by
 decide +kernel
def cuts39032 : List PrefixCut := [⟨64,318693341,318693535⟩]
theorem checked39032 : checkPrefixCuts (2^48) 5119934465 10 Manual.Count131072.C039032.packed 64 cuts39032 = true := by
 decide +kernel
def cuts39033 : List PrefixCut := [⟨7,35073913,35073934⟩,
⟨64,321983634,321983827⟩]
theorem checked39033 : checkPrefixCuts (2^48) 5120065537 10 Manual.Count131072.C039033.packed 64 cuts39033 = true := by
 decide +kernel
def pointBounds39033 : List (Nat × Nat × Nat) := [(5120079872,108558548312184,108558933634440)]
theorem point_links_checked39033 : (cuts39033.take 1).map (fun c => (5120065537-1+2*2^10*c.k,108558513238271+c.lower,108558898560506+c.upper)) = pointBounds39033 := by
 decide +kernel
def cuts39034 : List PrefixCut := [⟨22,110661072,110661143⟩,
⟨64,318677034,318677233⟩]
theorem checked39034 : checkPrefixCuts (2^48) 5120196609 10 Manual.Count131072.C039034.packed 64 cuts39034 = true := by
 decide +kernel
def pointBounds39034 : List (Nat × Nat × Nat) := [(5120241664,108558945882977,108559331205476)]
theorem point_links_checked39034 : (cuts39034.take 1).map (fun c => (5120196609-1+2*2^10*c.k,108558835221905+c.lower,108559220544333+c.upper)) = pointBounds39034 := by
 decide +kernel
def cuts39035 : List PrefixCut := [⟨37,184100011,184100119⟩,
⟨64,318778797,318778988⟩]
theorem checked39035 : checkPrefixCuts (2^48) 5120327681 10 Manual.Count131072.C039035.packed 64 cuts39035 = true := by
 decide +kernel
def pointBounds39035 : List (Nat × Nat × Nat) := [(5120403456,108559337998950,108559723321685)]
theorem point_links_checked39035 : (cuts39035.take 1).map (fun c => (5120327681-1+2*2^10*c.k,108559153898939+c.lower,108559539221566+c.upper)) = pointBounds39035 := by
 decide +kernel
def cuts39036 : List PrefixCut := [⟨52,261437614,261437769⟩,
⟨64,322233733,322233925⟩]
theorem checked39036 : checkPrefixCuts (2^48) 5120458753 10 Manual.Count131072.C039036.packed 64 cuts39036 = true := by
 decide +kernel
def pointBounds39036 : List (Nat × Nat × Nat) := [(5120565248,108559734115350,108560119438323)]
theorem point_links_checked39036 : (cuts39036.take 1).map (fun c => (5120458753-1+2*2^10*c.k,108559472677736+c.lower,108559858000554+c.upper)) = pointBounds39036 := by
 decide +kernel
def cuts39037 : List PrefixCut := [⟨64,323984508,323984701⟩]
theorem checked39037 : checkPrefixCuts (2^48) 5120589825 10 Manual.Count131072.C039037.packed 64 cuts39037 = true := by
 decide +kernel
def cuts39038 : List PrefixCut := [⟨3,14676400,14676409⟩,
⟨64,320458339,320458528⟩]
theorem checked39038 : checkPrefixCuts (2^48) 5120720897 10 Manual.Count131072.C039038.packed 64 cuts39038 = true := by
 decide +kernel
def pointBounds39038 : List (Nat × Nat × Nat) := [(5120727040,108560133572377,108560518895589)]
theorem point_links_checked39038 : (cuts39038.take 1).map (fun c => (5120720897-1+2*2^10*c.k,108560118895977+c.lower,108560504219180+c.upper)) = pointBounds39038 := by
 decide +kernel
def cuts39039 : List PrefixCut := [⟨18,91903524,91903580⟩,
⟨64,324187798,324187994⟩]
theorem checked39039 : checkPrefixCuts (2^48) 5120851969 10 Manual.Count131072.C039039.packed 64 cuts39039 = true := by
 decide +kernel
def pointBounds39039 : List (Nat × Nat × Nat) := [(5120888832,108560531257840,108560916581288)]
theorem point_links_checked39039 : (cuts39039.take 1).map (fun c => (5120851969-1+2*2^10*c.k,108560439354316+c.lower,108560824677708+c.upper)) = pointBounds39039 := by
 decide +kernel
def cuts39040 : List PrefixCut := [⟨33,167477283,167477380⟩,
⟨64,322860362,322860552⟩]
theorem checked39040 : checkPrefixCuts (2^48) 5120983041 10 Manual.Count131072.C039040.packed 64 cuts39040 = true := by
 decide +kernel
def pointBounds39040 : List (Nat × Nat × Nat) := [(5121050624,108560931019397,108561316343082)]
theorem point_links_checked39040 : (cuts39040.take 1).map (fun c => (5120983041-1+2*2^10*c.k,108560763542114+c.lower,108561148865702+c.upper)) = pointBounds39040 := by
 decide +kernel
def cuts39041 : List PrefixCut := [⟨48,247278897,247279045⟩,
⟨64,327249154,327249349⟩]
theorem checked39041 : checkPrefixCuts (2^48) 5121114113 10 Manual.Count131072.C039041.packed 64 cuts39041 = true := by
 decide +kernel
def pointBounds39041 : List (Nat × Nat × Nat) := [(5121212416,108561333681373,108561719005299)]
theorem point_links_checked39041 : (cuts39041.take 1).map (fun c => (5121114113-1+2*2^10*c.k,108561086402476+c.lower,108561471726254+c.upper)) = pointBounds39041 := by
 decide +kernel
def cuts39042 : List PrefixCut := [⟨63,316853052,316853247⟩,
⟨64,321689603,321689801⟩]
theorem checked39042 : checkPrefixCuts (2^48) 5121245185 10 Manual.Count131072.C039042.packed 64 cuts39042 = true := by
 decide +kernel
def pointBounds39042 : List (Nat × Nat × Nat) := [(5121374208,108561730504682,108562115828850)]
theorem point_links_checked39042 : (cuts39042.take 1).map (fun c => (5121245185-1+2*2^10*c.k,108561413651630+c.lower,108561798975603+c.upper)) = pointBounds39042 := by
 decide +kernel
def cuts39043 : List PrefixCut := [⟨64,319208212,319208400⟩]
theorem checked39043 : checkPrefixCuts (2^48) 5121376257 10 Manual.Count131072.C039043.packed 64 cuts39043 = true := by
 decide +kernel
def cuts39044 : List PrefixCut := [⟨14,71996595,71996637⟩,
⟨64,323157057,323157250⟩]
theorem checked39044 : checkPrefixCuts (2^48) 5121507329 10 Manual.Count131072.C039044.packed 64 cuts39044 = true := by
 decide +kernel
def pointBounds39044 : List (Nat × Nat × Nat) := [(5121536000,108562126546040,108562511870441)]
theorem point_links_checked39044 : (cuts39044.take 1).map (fun c => (5121507329-1+2*2^10*c.k,108562054549445+c.lower,108562439873804+c.upper)) = pointBounds39044 := by
 decide +kernel
def cuts39045 : List PrefixCut := [⟨29,144428719,144428806⟩,
⟨64,319796375,319796569⟩]
theorem checked39045 : checkPrefixCuts (2^48) 5121638401 10 Manual.Count131072.C039045.packed 64 cuts39045 = true := by
 decide +kernel
def pointBounds39045 : List (Nat × Nat × Nat) := [(5121697792,108562522135221,108562907459860)]
theorem point_links_checked39045 : (cuts39045.take 1).map (fun c => (5121638401-1+2*2^10*c.k,108562377706502+c.lower,108562763031054+c.upper)) = pointBounds39045 := by
 decide +kernel
def cuts39046 : List PrefixCut := [⟨44,221637914,221638048⟩,
⟨64,319128766,319128959⟩]
theorem checked39046 : checkPrefixCuts (2^48) 5121769473 10 Manual.Count131072.C039046.packed 64 cuts39046 = true := by
 decide +kernel
def pointBounds39046 : List (Nat × Nat × Nat) := [(5121859584,108562919140791,108563304465671)]
theorem point_links_checked39046 : (cuts39046.take 1).map (fun c => (5121769473-1+2*2^10*c.k,108562697502877+c.lower,108563082827623+c.upper)) = pointBounds39046 := by
 decide +kernel
def cuts39047 : List PrefixCut := [⟨59,295985021,295985196⟩,
⟨64,321483590,321483781⟩]
theorem checked39047 : checkPrefixCuts (2^48) 5121900545 10 Manual.Count131072.C039047.packed 64 cuts39047 = true := by
 decide +kernel
def pointBounds39047 : List (Nat × Nat × Nat) := [(5122021376,108563312616664,108563697941778)]
theorem point_links_checked39047 : (cuts39047.take 1).map (fun c => (5121900545-1+2*2^10*c.k,108563016631643+c.lower,108563401956582+c.upper)) = pointBounds39047 := by
 decide +kernel
def cuts39048 : List PrefixCut := [⟨64,324113104,324113296⟩]
theorem checked39048 : checkPrefixCuts (2^48) 5122031617 10 Manual.Count131072.C039048.packed 64 cuts39048 = true := by
 decide +kernel
def cuts39049 : List PrefixCut := [⟨10,50336257,50336286⟩,
⟨64,320368126,320368320⟩]
theorem checked39049 : checkPrefixCuts (2^48) 5122162689 10 Manual.Count131072.C039049.packed 64 cuts39049 = true := by
 decide +kernel
def pointBounds39049 : List (Nat × Nat × Nat) := [(5122183168,108563712564594,108564097889945)]
theorem point_links_checked39049 : (cuts39049.take 1).map (fun c => (5122162689-1+2*2^10*c.k,108563662228337+c.lower,108564047553659+c.upper)) = pointBounds39049 := by
 decide +kernel
def cuts39050 : List PrefixCut := [⟨25,124902873,124902949⟩,
⟨64,316073817,316074009⟩]
theorem checked39050 : checkPrefixCuts (2^48) 5122293761 10 Manual.Count131072.C039050.packed 64 cuts39050 = true := by
 decide +kernel
def pointBounds39050 : List (Nat × Nat × Nat) := [(5122344960,108564107499336,108564492824928)]
theorem point_links_checked39050 : (cuts39050.take 1).map (fun c => (5122293761-1+2*2^10*c.k,108563982596463+c.lower,108564367921979+c.upper)) = pointBounds39050 := by
 decide +kernel
def cuts39051 : List PrefixCut := [⟨40,201498367,201498485⟩,
⟨64,324472889,324473079⟩]
theorem checked39051 : checkPrefixCuts (2^48) 5122424833 10 Manual.Count131072.C039051.packed 64 cuts39051 = true := by
 decide +kernel
def pointBounds39051 : List (Nat × Nat × Nat) := [(5122506752,108564500168647,108564885494473)]
theorem point_links_checked39051 : (cuts39051.take 1).map (fun c => (5122424833-1+2*2^10*c.k,108564298670280+c.lower,108564683995988+c.upper)) = pointBounds39051 := by
 decide +kernel
def cuts39052 : List PrefixCut := [⟨55,275946532,275946698⟩,
⟨64,321277664,321277857⟩]
theorem checked39052 : checkPrefixCuts (2^48) 5122555905 10 Manual.Count131072.C039052.packed 64 cuts39052 = true := by
 decide +kernel
def pointBounds39052 : List (Nat × Nat × Nat) := [(5122668544,108564899089701,108565284415765)]
theorem point_links_checked39052 : (cuts39052.take 1).map (fun c => (5122555905-1+2*2^10*c.k,108564623143169+c.lower,108565008469067+c.upper)) = pointBounds39052 := by
 decide +kernel
def cuts39053 : List PrefixCut := [⟨64,320335335,320335527⟩]
theorem checked39053 : checkPrefixCuts (2^48) 5122686977 10 Manual.Count131072.C039053.packed 64 cuts39053 = true := by
 decide +kernel
def cuts39054 : List PrefixCut := [⟨6,29670438,29670457⟩,
⟨64,322964506,322964696⟩]
theorem checked39054 : checkPrefixCuts (2^48) 5122818049 10 Manual.Count131072.C039054.packed 64 cuts39054 = true := by
 decide +kernel
def pointBounds39054 : List (Nat × Nat × Nat) := [(5122830336,108565294426606,108565679752908)]
theorem point_links_checked39054 : (cuts39054.take 1).map (fun c => (5122818049-1+2*2^10*c.k,108565264756168+c.lower,108565650082451+c.upper)) = pointBounds39054 := by
 decide +kernel
def cuts39055 : List PrefixCut := [⟨21,105546828,105546888⟩,
⟨64,323890289,323890476⟩]
theorem checked39055 : checkPrefixCuts (2^48) 5122949121 10 Manual.Count131072.C039055.packed 64 cuts39055 = true := by
 decide +kernel
def pointBounds39055 : List (Nat × Nat × Nat) := [(5122992128,108565693267502,108566078594035)]
theorem point_links_checked39055 : (cuts39055.take 1).map (fun c => (5122949121-1+2*2^10*c.k,108565587720674+c.lower,108565973047147+c.upper)) = pointBounds39055 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000282
