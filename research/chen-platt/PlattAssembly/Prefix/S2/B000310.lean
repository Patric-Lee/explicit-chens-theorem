import PlattAssemblyKernel
import PlattCertificates.Count131072.C019920
import PlattCertificates.Count131072.C019921
import PlattCertificates.Count131072.C019922
import PlattCertificates.Count131072.C019923
import PlattCertificates.Count131072.C019924
import PlattCertificates.Count131072.C019925
import PlattCertificates.Count131072.C019926
import PlattCertificates.Count131072.C019927
import PlattCertificates.Count131072.C019928
import PlattCertificates.Count131072.C019929
import PlattCertificates.Count131072.C019930
import PlattCertificates.Count131072.C019931
import PlattCertificates.Count131072.C019932
import PlattCertificates.Count131072.C019933
import PlattCertificates.Count131072.C019934
import PlattCertificates.Count131072.C019935
import PlattCertificates.Count131072.C019936
import PlattCertificates.Count131072.C019937
import PlattCertificates.Count131072.C019938
import PlattCertificates.Count131072.C019939
import PlattCertificates.Count131072.C019940
import PlattCertificates.Count131072.C019941
import PlattCertificates.Count131072.C019942
import PlattCertificates.Count131072.C019943
import PlattCertificates.Count131072.C019944
import PlattCertificates.Count131072.C019945
import PlattCertificates.Count131072.C019946
import PlattCertificates.Count131072.C019947
import PlattCertificates.Count131072.C019948
import PlattCertificates.Count131072.C019949
import PlattCertificates.Count131072.C019950
import PlattCertificates.Count131072.C019951
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000310
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19920 : List PrefixCut := [⟨45,228094059,228094192⟩,
⟨125,636156068,636156446⟩,
⟨128,652194119,652194506⟩]
theorem checked19920 : checkPrefixCuts (2^48) 2614886401 9 Manual.Count131072.C019920.packed 128 cuts19920 = true := by
 decide +kernel
def pointBounds19920 : List (Nat × Nat × Nat) := [(2614932480,99969145729098,99969526068456),(2615014400,99969553791107,99969934130710)]
theorem point_links_checked19920 : (cuts19920.take 2).map (fun c => (2614886401-1+2*2^9*c.k,99968917635039+c.lower,99969297974264+c.upper)) = pointBounds19920 := by
 decide +kernel
def cuts19921 : List PrefixCut := [⟨77,395025024,395025251⟩,
⟨128,651946314,651946690⟩]
theorem checked19921 : checkPrefixCuts (2^48) 2615017473 9 Manual.Count131072.C019921.packed 128 cuts19921 = true := by
 decide +kernel
def pointBounds19921 : List (Nat × Nat × Nat) := [(2615096320,99969964854182,99970345194021)]
theorem point_links_checked19921 : (cuts19921.take 1).map (fun c => (2615017473-1+2*2^9*c.k,99969569829158+c.lower,99969950168770+c.upper)) = pointBounds19921 := by
 decide +kernel
def cuts19922 : List PrefixCut := [⟨29,141751156,141751244⟩,
⟨109,544823817,544824142⟩,
⟨128,646854668,646855053⟩]
theorem checked19922 : checkPrefixCuts (2^48) 2615148545 9 Manual.Count131072.C019922.packed 128 cuts19922 = true := by
 decide +kernel
def pointBounds19922 : List (Nat × Nat × Nat) := [(2615178240,99970363526628,99970743866704),(2615260160,99970766599289,99971146939602)]
theorem point_links_checked19922 : (cuts19922.take 2).map (fun c => (2615148545-1+2*2^9*c.k,99970221775472+c.lower,99970602115460+c.upper)) = pointBounds19922 := by
 decide +kernel
def cuts19923 : List PrefixCut := [⟨61,311684312,311684492⟩,
⟨128,656078224,656078600⟩]
theorem checked19923 : checkPrefixCuts (2^48) 2615279617 9 Manual.Count131072.C019923.packed 128 cuts19923 = true := by
 decide +kernel
def pointBounds19923 : List (Nat × Nat × Nat) := [(2615342080,99971180314452,99971560655005)]
theorem point_links_checked19923 : (cuts19923.take 1).map (fun c => (2615279617-1+2*2^9*c.k,99970868630140+c.lower,99971248970513+c.upper)) = pointBounds19923 := by
 decide +kernel
def cuts19924 : List PrefixCut := [⟨13,63604253,63604290⟩,
⟨93,474495297,474495571⟩,
⟨128,651202456,651202834⟩]
theorem checked19924 : checkPrefixCuts (2^48) 2615410689 9 Manual.Count131072.C019924.packed 128 cuts19924 = true := by
 decide +kernel
def pointBounds19924 : List (Nat × Nat × Nat) := [(2615424000,99971588312617,99971968653403),(2615505920,99971999203661,99972379544684)]
theorem point_links_checked19924 : (cuts19924.take 2).map (fun c => (2615410689-1+2*2^9*c.k,99971524708364+c.lower,99971905049113+c.upper)) = pointBounds19924 := by
 decide +kernel
def cuts19925 : List PrefixCut := [⟨45,227498815,227498949⟩,
⟨125,638794594,638794975⟩,
⟨128,655689515,655689905⟩]
theorem checked19925 : checkPrefixCuts (2^48) 2615541761 9 Manual.Count131072.C019925.packed 128 cuts19925 = true := by
 decide +kernel
def pointBounds19925 : List (Nat × Nat × Nat) := [(2615587840,99972403409635,99972783750896),(2615669760,99972814705414,99973195046922)]
theorem point_links_checked19925 : (cuts19925.take 2).map (fun c => (2615541761-1+2*2^9*c.k,99972175910820+c.lower,99972556251947+c.upper)) = pointBounds19925 := by
 decide +kernel
def cuts19926 : List PrefixCut := [⟨77,386747746,386747976⟩,
⟨128,646940462,646940840⟩]
theorem checked19926 : checkPrefixCuts (2^48) 2615672833 9 Manual.Count131072.C019926.packed 128 cuts19926 = true := by
 decide +kernel
def pointBounds19926 : List (Nat × Nat × Nat) := [(2615751680,99973218348081,99973598689828)]
theorem point_links_checked19926 : (cuts19926.take 1).map (fun c => (2615672833-1+2*2^9*c.k,99972831600335+c.lower,99973211941852+c.upper)) = pointBounds19926 := by
 decide +kernel
def cuts19927 : List PrefixCut := [⟨29,142684074,142684160⟩,
⟨109,550820713,550821035⟩,
⟨128,639913935,639914311⟩]
theorem checked19927 : checkPrefixCuts (2^48) 2615803905 9 Manual.Count131072.C019927.packed 128 cuts19927 = true := by
 decide +kernel
def pointBounds19927 : List (Nat × Nat × Nat) := [(2615833600,99973621224871,99974001566852),(2615915520,99974029361510,99974409703727)]
theorem point_links_checked19927 : (cuts19927.take 2).map (fun c => (2615803905-1+2*2^9*c.k,99973478540797+c.lower,99973858882692+c.upper)) = pointBounds19927 := by
 decide +kernel
def cuts19928 : List PrefixCut := [⟨61,309131423,309131606⟩,
⟨128,650641563,650641951⟩]
theorem checked19928 : checkPrefixCuts (2^48) 2615934977 9 Manual.Count131072.C019928.packed 128 cuts19928 = true := by
 decide +kernel
def pointBounds19928 : List (Nat × Nat × Nat) := [(2615997440,99974427586155,99974807928609)]
theorem point_links_checked19928 : (cuts19928.take 1).map (fun c => (2615934977-1+2*2^9*c.k,99974118454732+c.lower,99974498797003+c.upper)) = pointBounds19928 := by
 decide +kernel
def cuts19929 : List PrefixCut := [⟨13,68214882,68214922⟩,
⟨93,478572694,478572978⟩,
⟨128,655343177,655343567⟩]
theorem checked19929 : checkPrefixCuts (2^48) 2616066049 9 Manual.Count131072.C019929.packed 128 cuts19929 = true := by
 decide +kernel
def pointBounds19929 : List (Nat × Nat × Nat) := [(2616079360,99974837311177,99975217653876),(2616161280,99975247668989,99975628011932)]
theorem point_links_checked19929 : (cuts19929.take 2).map (fun c => (2616066049-1+2*2^9*c.k,99974769096295+c.lower,99975149438954+c.upper)) = pointBounds19929 := by
 decide +kernel
def cuts19930 : List PrefixCut := [⟨45,229270840,229270973⟩,
⟨125,640356024,640356398⟩,
⟨128,655525368,655525751⟩]
theorem checked19930 : checkPrefixCuts (2^48) 2616197121 9 Manual.Count131072.C019930.packed 128 cuts19930 = true := by
 decide +kernel
def pointBounds19930 : List (Nat × Nat × Nat) := [(2616243200,99975653710312,99976034053494),(2616325120,99976064795496,99976445138919)]
theorem point_links_checked19930 : (cuts19930.take 2).map (fun c => (2616197121-1+2*2^9*c.k,99975424439472+c.lower,99975804782521+c.upper)) = pointBounds19930 := by
 decide +kernel
def cuts19931 : List PrefixCut := [⟨77,391492066,391492300⟩,
⟨128,650113465,650113846⟩]
theorem checked19931 : checkPrefixCuts (2^48) 2616328193 9 Manual.Count131072.C019931.packed 128 cuts19931 = true := by
 decide +kernel
def pointBounds19931 : List (Nat × Nat × Nat) := [(2616407040,99976471456906,99976851800572)]
theorem point_links_checked19931 : (cuts19931.take 1).map (fun c => (2616328193-1+2*2^9*c.k,99976079964840+c.lower,99976460308272+c.upper)) = pointBounds19931 := by
 decide +kernel
def cuts19932 : List PrefixCut := [⟨29,139958903,139958985⟩,
⟨109,543797841,543798161⟩,
⟨128,643410970,643411348⟩]
theorem checked19932 : checkPrefixCuts (2^48) 2616459265 9 Manual.Count131072.C019932.packed 128 cuts19932 = true := by
 decide +kernel
def pointBounds19932 : List (Nat × Nat × Nat) := [(2616488960,99976870037208,99977250381103),(2616570880,99977273876146,99977654220279)]
theorem point_links_checked19932 : (cuts19932.take 2).map (fun c => (2616459265-1+2*2^9*c.k,99976730078305+c.lower,99977110422118+c.upper)) = pointBounds19932 := by
 decide +kernel
def cuts19933 : List PrefixCut := [⟨61,314109904,314110086⟩,
⟨128,657255613,657255996⟩]
theorem checked19933 : checkPrefixCuts (2^48) 2616590337 9 Manual.Count131072.C019933.packed 128 cuts19933 = true := by
 decide +kernel
def pointBounds19933 : List (Nat × Nat × Nat) := [(2616652800,99977687599179,99978067943552)]
theorem point_links_checked19933 : (cuts19933.take 1).map (fun c => (2616590337-1+2*2^9*c.k,99977373489275+c.lower,99977753833466+c.upper)) = pointBounds19933 := by
 decide +kernel
def cuts19934 : List PrefixCut := [⟨13,64540503,64540540⟩,
⟨93,462533031,462533302⟩,
⟨128,643776896,643777273⟩]
theorem checked19934 : checkPrefixCuts (2^48) 2616721409 9 Manual.Count131072.C019934.packed 128 cuts19934 = true := by
 decide +kernel
def pointBounds19934 : List (Nat × Nat × Nat) := [(2616734720,99978095285391,99978475630002),(2616816640,99978493277919,99978873622764)]
theorem point_links_checked19934 : (cuts19934.take 2).map (fun c => (2616721409-1+2*2^9*c.k,99978030744888+c.lower,99978411089462+c.upper)) = pointBounds19934 := by
 decide +kernel
def cuts19935 : List PrefixCut := [⟨45,235236856,235236991⟩,
⟨125,644498098,644498474⟩,
⟨128,659125859,659126244⟩]
theorem checked19935 : checkPrefixCuts (2^48) 2616852481 9 Manual.Count131072.C019935.packed 128 cuts19935 = true := by
 decide +kernel
def pointBounds19935 : List (Nat × Nat × Nat) := [(2616898560,99978909758640,99979290103726),(2616980480,99979319019882,99979699365209)]
theorem point_links_checked19935 : (cuts19935.take 2).map (fun c => (2616852481-1+2*2^9*c.k,99978674521784+c.lower,99979054866735+c.upper)) = pointBounds19935 := by
 decide +kernel
def cuts19936 : List PrefixCut := [⟨77,393330037,393330268⟩,
⟨128,646724178,646724562⟩]
theorem checked19936 : checkPrefixCuts (2^48) 2616983553 9 Manual.Count131072.C019936.packed 128 cuts19936 = true := by
 decide +kernel
def pointBounds19936 : List (Nat × Nat × Nat) := [(2617062400,99979726977680,99980107323247)]
theorem point_links_checked19936 : (cuts19936.take 1).map (fun c => (2616983553-1+2*2^9*c.k,99979333647643+c.lower,99979713992979+c.upper)) = pointBounds19936 := by
 decide +kernel
def cuts19937 : List PrefixCut := [⟨29,147990175,147990263⟩,
⟨109,553126208,553126534⟩,
⟨128,649810621,649811003⟩]
theorem checked19937 : checkPrefixCuts (2^48) 2617114625 9 Manual.Count131072.C019937.packed 128 cuts19937 = true := by
 decide +kernel
def pointBounds19937 : List (Nat × Nat × Nat) := [(2617144320,99980128361996,99980508707804),(2617226240,99980533498029,99980913844075)]
theorem point_links_checked19937 : (cuts19937.take 2).map (fun c => (2617114625-1+2*2^9*c.k,99979980371821+c.lower,99980360717541+c.upper)) = pointBounds19937 := by
 decide +kernel
def cuts19938 : List PrefixCut := [⟨61,312202984,312203166⟩,
⟨128,649025301,649025677⟩]
theorem checked19938 : checkPrefixCuts (2^48) 2617245697 9 Manual.Count131072.C019938.packed 128 cuts19938 = true := by
 decide +kernel
def pointBounds19938 : List (Nat × Nat × Nat) := [(2617308160,99980942385426,99981322731710)]
theorem point_links_checked19938 : (cuts19938.take 1).map (fun c => (2617245697-1+2*2^9*c.k,99980630182442+c.lower,99981010528544+c.upper)) = pointBounds19938 := by
 decide +kernel
def cuts19939 : List PrefixCut := [⟨13,66567605,66567644⟩,
⟨93,474999251,474999530⟩,
⟨128,654907301,654907688⟩]
theorem checked19939 : checkPrefixCuts (2^48) 2617376769 9 Manual.Count131072.C019939.packed 128 cuts19939 = true := by
 decide +kernel
def pointBounds19939 : List (Nat × Nat × Nat) := [(2617390080,99981345775348,99981726121865),(2617472000,99981754206994,99982134553751)]
theorem point_links_checked19939 : (cuts19939.take 2).map (fun c => (2617376769-1+2*2^9*c.k,99981279207743+c.lower,99981659554221+c.upper)) = pointBounds19939 := by
 decide +kernel
def cuts19940 : List PrefixCut := [⟨45,227865614,227865747⟩,
⟨125,629819709,629820082⟩,
⟨128,646379349,646379732⟩]
theorem checked19940 : checkPrefixCuts (2^48) 2617507841 9 Manual.Count131072.C019940.packed 128 cuts19940 = true := by
 decide +kernel
def pointBounds19940 : List (Nat × Nat × Nat) := [(2617553920,99982161980658,99982542327656),(2617635840,99982563934753,99982944281991)]
theorem point_links_checked19940 : (cuts19940.take 2).map (fun c => (2617507841-1+2*2^9*c.k,99981934115044+c.lower,99982314461909+c.upper)) = pointBounds19940 := by
 decide +kernel
def cuts19941 : List PrefixCut := [⟨77,383231390,383231623⟩,
⟨128,642583520,642583905⟩]
theorem checked19941 : checkPrefixCuts (2^48) 2617638913 9 Manual.Count131072.C019941.packed 128 cuts19941 = true := by
 decide +kernel
def pointBounds19941 : List (Nat × Nat × Nat) := [(2617717760,99982963725783,99983344073264)]
theorem point_links_checked19941 : (cuts19941.take 1).map (fun c => (2617638913-1+2*2^9*c.k,99982580494393+c.lower,99982960841641+c.upper)) = pointBounds19941 := by
 decide +kernel
def cuts19942 : List PrefixCut := [⟨29,143437119,143437206⟩,
⟨109,550084539,550084866⟩,
⟨128,647282350,647282733⟩]
theorem checked19942 : checkPrefixCuts (2^48) 2617769985 9 Manual.Count131072.C019942.packed 128 cuts19942 = true := by
 decide +kernel
def pointBounds19942 : List (Nat × Nat × Nat) := [(2617799680,99983366515032,99983746862752),(2617881600,99983773162452,99984153510412)]
theorem point_links_checked19942 : (cuts19942.take 2).map (fun c => (2617769985-1+2*2^9*c.k,99983223077913+c.lower,99983603425546+c.upper)) = pointBounds19942 := by
 decide +kernel
def cuts19943 : List PrefixCut := [⟨61,308146651,308146832⟩,
⟨128,652410734,652411119⟩]
theorem checked19943 : checkPrefixCuts (2^48) 2617901057 9 Manual.Count131072.C019943.packed 128 cuts19943 = true := by
 decide +kernel
def pointBounds19943 : List (Nat × Nat × Nat) := [(2617963520,99984178506914,99984558855111)]
theorem point_links_checked19943 : (cuts19943.take 1).map (fun c => (2617901057-1+2*2^9*c.k,99983870360263+c.lower,99984250708279+c.upper)) = pointBounds19943 := by
 decide +kernel
def cuts19944 : List PrefixCut := [⟨13,66658461,66658502⟩,
⟨93,474235292,474235573⟩,
⟨128,655818438,655818821⟩]
theorem checked19944 : checkPrefixCuts (2^48) 2618032129 9 Manual.Count131072.C019944.packed 128 cuts19944 = true := by
 decide +kernel
def pointBounds19944 : List (Nat × Nat × Nat) := [(2618045440,99984589429458,99984969777900),(2618127360,99984997006289,99985377354971)]
theorem point_links_checked19944 : (cuts19944.take 2).map (fun c => (2618032129-1+2*2^9*c.k,99984522770997+c.lower,99984903119398+c.upper)) = pointBounds19944 := by
 decide +kernel
def cuts19945 : List PrefixCut := [⟨45,227056041,227056177⟩,
⟨125,636972533,636972911⟩,
⟨128,653098015,653098403⟩]
theorem checked19945 : checkPrefixCuts (2^48) 2618163201 9 Manual.Count131072.C019945.packed 128 cuts19945 = true := by
 decide +kernel
def pointBounds19945 : List (Nat × Nat × Nat) := [(2618209280,99985405645476,99985785994396),(2618291200,99985815561968,99986195911130)]
theorem point_links_checked19945 : (cuts19945.take 2).map (fun c => (2618163201-1+2*2^9*c.k,99985178589435+c.lower,99985558938219+c.upper)) = pointBounds19945 := by
 decide +kernel
def cuts19946 : List PrefixCut := [⟨77,393133119,393133348⟩,
⟨128,651130316,651130698⟩]
theorem checked19946 : checkPrefixCuts (2^48) 2618294273 9 Manual.Count131072.C019946.packed 128 cuts19946 = true := by
 decide +kernel
def pointBounds19946 : List (Nat × Nat × Nat) := [(2618373120,99986224820569,99986605169970)]
theorem point_links_checked19946 : (cuts19946.take 1).map (fun c => (2618294273-1+2*2^9*c.k,99985831687450+c.lower,99986212036622+c.upper)) = pointBounds19946 := by
 decide +kernel
def cuts19947 : List PrefixCut := [⟨29,149743548,149743633⟩,
⟨109,557686647,557686970⟩,
⟨128,648733041,648733417⟩]
theorem checked19947 : checkPrefixCuts (2^48) 2618425345 9 Manual.Count131072.C019947.packed 128 cuts19947 = true := by
 decide +kernel
def pointBounds19947 : List (Nat × Nat × Nat) := [(2618455040,99986632561314,99987012910953),(2618536960,99987040504413,99987420854290)]
theorem point_links_checked19947 : (cuts19947.take 2).map (fun c => (2618425345-1+2*2^9*c.k,99986482817766+c.lower,99986863167320+c.upper)) = pointBounds19947 := by
 decide +kernel
def cuts19948 : List PrefixCut := [⟨61,311294328,311294513⟩,
⟨128,647625553,647625938⟩]
theorem checked19948 : checkPrefixCuts (2^48) 2618556417 9 Manual.Count131072.C019948.packed 128 cuts19948 = true := by
 decide +kernel
def pointBounds19948 : List (Nat × Nat × Nat) := [(2618618880,99987442845135,99987823195250)]
theorem point_links_checked19948 : (cuts19948.take 1).map (fun c => (2618556417-1+2*2^9*c.k,99987131550807+c.lower,99987511900737+c.upper)) = pointBounds19948 := by
 decide +kernel
def cuts19949 : List PrefixCut := [⟨13,64492042,64492080⟩,
⟨93,471536965,471537241⟩,
⟨128,646948181,646948561⟩]
theorem checked19949 : checkPrefixCuts (2^48) 2618687489 9 Manual.Count131072.C019949.packed 128 cuts19949 = true := by
 decide +kernel
def pointBounds19949 : List (Nat × Nat × Nat) := [(2618700800,99987843668402,99988224018755),(2618782720,99988250713325,99988631063916)]
theorem point_links_checked19949 : (cuts19949.take 2).map (fun c => (2618687489-1+2*2^9*c.k,99987779176360+c.lower,99988159526675+c.upper)) = pointBounds19949 := by
 decide +kernel
def cuts19950 : List PrefixCut := [⟨45,225924411,225924549⟩,
⟨125,631439122,631439503⟩,
⟨128,648312903,648313295⟩]
theorem checked19950 : checkPrefixCuts (2^48) 2618818561 9 Manual.Count131072.C019950.packed 128 cuts19950 = true := by
 decide +kernel
def pointBounds19950 : List (Nat × Nat × Nat) := [(2618864640,99988652048952,99989032399785),(2618946560,99989057563663,99989437914739)]
theorem point_links_checked19950 : (cuts19950.take 2).map (fun c => (2618818561-1+2*2^9*c.k,99988426124541+c.lower,99988806475236+c.upper)) = pointBounds19950 := by
 decide +kernel
def cuts19951 : List PrefixCut := [⟨77,391530044,391530268⟩,
⟨128,652149487,652149863⟩]
theorem checked19951 : checkPrefixCuts (2^48) 2618949633 9 Manual.Count131072.C019951.packed 128 cuts19951 = true := by
 decide +kernel
def pointBounds19951 : List (Nat × Nat × Nat) := [(2619028480,99989465967488,99989846318799)]
theorem point_links_checked19951 : (cuts19951.take 1).map (fun c => (2618949633-1+2*2^9*c.k,99989074437444+c.lower,99989454788531+c.upper)) = pointBounds19951 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000310
