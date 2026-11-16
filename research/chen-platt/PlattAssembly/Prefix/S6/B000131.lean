import PlattAssemblyKernel
import PlattCertificates.Count131072.C054192
import PlattCertificates.Count131072.C054193
import PlattCertificates.Count131072.C054194
import PlattCertificates.Count131072.C054195
import PlattCertificates.Count131072.C054196
import PlattCertificates.Count131072.C054197
import PlattCertificates.Count131072.C054198
import PlattCertificates.Count131072.C054199
import PlattCertificates.Count131072.C054200
import PlattCertificates.Count131072.C054201
import PlattCertificates.Count131072.C054202
import PlattCertificates.Count131072.C054203
import PlattCertificates.Count131072.C054204
import PlattCertificates.Count131072.C054205
import PlattCertificates.Count131072.C054206
import PlattCertificates.Count131072.C054207
import PlattCertificates.Count131072.C054208
import PlattCertificates.Count131072.C054209
import PlattCertificates.Count131072.C054210
import PlattCertificates.Count131072.C054211
import PlattCertificates.Count131072.C054212
import PlattCertificates.Count131072.C054213
import PlattCertificates.Count131072.C054214
import PlattCertificates.Count131072.C054215
import PlattCertificates.Count131072.C054216
import PlattCertificates.Count131072.C054217
import PlattCertificates.Count131072.C054218
import PlattCertificates.Count131072.C054219
import PlattCertificates.Count131072.C054220
import PlattCertificates.Count131072.C054221
import PlattCertificates.Count131072.C054222
import PlattCertificates.Count131072.C054223
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000131
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts54192 : List PrefixCut := [⟨64,227728832,227728957⟩]
theorem checked54192 : checkPrefixCuts (2^48) 7106985985 10 Manual.Count131072.C054192.packed 64 cuts54192 = true := by
 decide +kernel
def cuts54193 : List PrefixCut := [⟨24,85545750,85545799⟩,
⟨64,229388021,229388149⟩]
theorem checked54193 : checkPrefixCuts (2^48) 7107117057 10 Manual.Count131072.C054193.packed 64 cuts54193 = true := by
 decide +kernel
def pointBounds54193 : List (Nat × Nat × Nat) := [(7107166208,112657381089295,112657768779926)]
theorem point_links_checked54193 : (cuts54193.take 1).map (fun c => (7107117057-1+2*2^10*c.k,112657295543545+c.lower,112657683234127+c.upper)) = pointBounds54193 := by
 decide +kernel
def cuts54194 : List PrefixCut := [⟨64,231839214,231839344⟩]
theorem checked54194 : checkPrefixCuts (2^48) 7107248129 10 Manual.Count131072.C054194.packed 64 cuts54194 = true := by
 decide +kernel
def cuts54195 : List PrefixCut := [⟨5,17742215,17742225⟩,
⟨64,227993459,227993590⟩]
theorem checked54195 : checkPrefixCuts (2^48) 7107379201 10 Manual.Count131072.C054195.packed 64 cuts54195 = true := by
 decide +kernel
def pointBounds54195 : List (Nat × Nat × Nat) := [(7107389440,112657774512995,112658162203845)]
theorem point_links_checked54195 : (cuts54195.take 1).map (fun c => (7107379201-1+2*2^10*c.k,112657756770780+c.lower,112658144461620+c.upper)) = pointBounds54195 := by
 decide +kernel
def cuts54196 : List PrefixCut := [⟨50,181298766,181298871⟩,
⟨64,231791074,231791208⟩]
theorem checked54196 : checkPrefixCuts (2^48) 7107510273 10 Manual.Count131072.C054196.packed 64 cuts54196 = true := by
 decide +kernel
def pointBounds54196 : List (Nat × Nat × Nat) := [(7107612672,112658166063005,112658553754081)]
theorem point_links_checked54196 : (cuts54196.take 1).map (fun c => (7107510273-1+2*2^10*c.k,112657984764239+c.lower,112658372455210+c.upper)) = pointBounds54196 := by
 decide +kernel
def cuts54197 : List PrefixCut := [⟨64,230163156,230163285⟩]
theorem checked54197 : checkPrefixCuts (2^48) 7107641345 10 Manual.Count131072.C054197.packed 64 cuts54197 = true := by
 decide +kernel
def cuts54198 : List PrefixCut := [⟨31,110525901,110525963⟩,
⟨64,228812460,228812588⟩]
theorem checked54198 : checkPrefixCuts (2^48) 7107772417 10 Manual.Count131072.C054198.packed 64 cuts54198 = true := by
 decide +kernel
def pointBounds54198 : List (Nat × Nat × Nat) := [(7107835904,112658557244370,112658944935666)]
theorem point_links_checked54198 : (cuts54198.take 1).map (fun c => (7107772417-1+2*2^10*c.k,112658446718469+c.lower,112658834409703+c.upper)) = pointBounds54198 := by
 decide +kernel
def cuts54199 : List PrefixCut := [⟨64,231817834,231817965⟩]
theorem checked54199 : checkPrefixCuts (2^48) 7107903489 10 Manual.Count131072.C054199.packed 64 cuts54199 = true := by
 decide +kernel
def cuts54200 : List PrefixCut := [⟨12,44113810,44113834⟩,
⟨64,233951919,233952048⟩]
theorem checked54200 : checkPrefixCuts (2^48) 7108034561 10 Manual.Count131072.C054200.packed 64 cuts54200 = true := by
 decide +kernel
def pointBounds54200 : List (Nat × Nat × Nat) := [(7108059136,112658951462573,112659339154090)]
theorem point_links_checked54200 : (cuts54200.take 1).map (fun c => (7108034561-1+2*2^10*c.k,112658907348763+c.lower,112659295040256+c.upper)) = pointBounds54200 := by
 decide +kernel
def cuts54201 : List PrefixCut := [⟨57,200091133,200091246⟩,
⟨64,225117144,225117271⟩]
theorem checked54201 : checkPrefixCuts (2^48) 7108165633 10 Manual.Count131072.C054201.packed 64 cuts54201 = true := by
 decide +kernel
def pointBounds54201 : List (Nat × Nat × Nat) := [(7108282368,112659341391815,112659729083550)]
theorem point_links_checked54201 : (cuts54201.take 1).map (fun c => (7108165633-1+2*2^10*c.k,112659141300682+c.lower,112659528992304+c.upper)) = pointBounds54201 := by
 decide +kernel
def cuts54202 : List PrefixCut := [⟨64,224400241,224400374⟩]
theorem checked54202 : checkPrefixCuts (2^48) 7108296705 10 Manual.Count131072.C054202.packed 64 cuts54202 = true := by
 decide +kernel
def cuts54203 : List PrefixCut := [⟨38,134828229,134828306⟩,
⟨64,228474580,228474710⟩]
theorem checked54203 : checkPrefixCuts (2^48) 7108427777 10 Manual.Count131072.C054203.packed 64 cuts54203 = true := by
 decide +kernel
def pointBounds54203 : List (Nat × Nat × Nat) := [(7108505600,112659725646296,112660113338255)]
theorem point_links_checked54203 : (cuts54203.take 1).map (fun c => (7108427777-1+2*2^10*c.k,112659590818067+c.lower,112659978509949+c.upper)) = pointBounds54203 := by
 decide +kernel
def cuts54204 : List PrefixCut := [⟨64,227599262,227599393⟩]
theorem checked54204 : checkPrefixCuts (2^48) 7108558849 10 Manual.Count131072.C054204.packed 64 cuts54204 = true := by
 decide +kernel
def cuts54205 : List PrefixCut := [⟨19,68857065,68857104⟩,
⟨64,229297666,229297800⟩]
theorem checked54205 : checkPrefixCuts (2^48) 7108689921 10 Manual.Count131072.C054205.packed 64 cuts54205 = true := by
 decide +kernel
def pointBounds54205 : List (Nat × Nat × Nat) := [(7108728832,112660115748974,112660503441156)]
theorem point_links_checked54205 : (cuts54205.take 1).map (fun c => (7108689921-1+2*2^10*c.k,112660046891909+c.lower,112660434584052+c.upper)) = pointBounds54205 := by
 decide +kernel
def cuts54206 : List PrefixCut := [⟨64,224938024,224938150⟩]
theorem checked54206 : checkPrefixCuts (2^48) 7108820993 10 Manual.Count131072.C054206.packed 64 cuts54206 = true := by
 decide +kernel
def pointBounds54206 : List (Nat × Nat × Nat) := [(7108952064,112660501127599,112660888820002)]
theorem point_links_checked54206 : (cuts54206.take 1).map (fun c => (7108820993-1+2*2^10*c.k,112660276189575+c.lower,112660663881852+c.upper)) = pointBounds54206 := by
 decide +kernel
def cuts54207 : List PrefixCut := [⟨64,226240461,226240591⟩]
theorem checked54207 : checkPrefixCuts (2^48) 7108952065 10 Manual.Count131072.C054207.packed 64 cuts54207 = true := by
 decide +kernel
def cuts54208 : List PrefixCut := [⟨45,159957510,159957601⟩,
⟨64,226948995,226949126⟩]
theorem checked54208 : checkPrefixCuts (2^48) 7109083137 10 Manual.Count131072.C054208.packed 64 cuts54208 = true := by
 decide +kernel
def pointBounds54208 : List (Nat × Nat × Nat) := [(7109175296,112660887325570,112661275018194)]
theorem point_links_checked54208 : (cuts54208.take 1).map (fun c => (7109083137-1+2*2^10*c.k,112660727368060+c.lower,112661115060593+c.upper)) = pointBounds54208 := by
 decide +kernel
def cuts54209 : List PrefixCut := [⟨64,231062435,231062565⟩]
theorem checked54209 : checkPrefixCuts (2^48) 7109214209 10 Manual.Count131072.C054209.packed 64 cuts54209 = true := by
 decide +kernel
def cuts54210 : List PrefixCut := [⟨26,94466722,94466777⟩,
⟨64,231929195,231929324⟩]
theorem checked54210 : checkPrefixCuts (2^48) 7109345281 10 Manual.Count131072.C054210.packed 64 cuts54210 = true := by
 decide +kernel
def pointBounds54210 : List (Nat × Nat × Nat) := [(7109398528,112661279846212,112661667539061)]
theorem point_links_checked54210 : (cuts54210.take 1).map (fun c => (7109345281-1+2*2^10*c.k,112661185379490+c.lower,112661573072284+c.upper)) = pointBounds54210 := by
 decide +kernel
def cuts54211 : List PrefixCut := [⟨64,226421743,226421873⟩]
theorem checked54211 : checkPrefixCuts (2^48) 7109476353 10 Manual.Count131072.C054211.packed 64 cuts54211 = true := by
 decide +kernel
def cuts54212 : List PrefixCut := [⟨7,24348305,24348318⟩,
⟨64,228080381,228080512⟩]
theorem checked54212 : checkPrefixCuts (2^48) 7109607425 10 Manual.Count131072.C054212.packed 64 cuts54212 = true := by
 decide +kernel
def pointBounds54212 : List (Nat × Nat × Nat) := [(7109621760,112661668078733,112662055771799)]
theorem point_links_checked54212 : (cuts54212.take 1).map (fun c => (7109607425-1+2*2^10*c.k,112661643730428+c.lower,112662031423481+c.upper)) = pointBounds54212 := by
 decide +kernel
def cuts54213 : List PrefixCut := [⟨52,184013171,184013276⟩,
⟨64,226334229,226334357⟩]
theorem checked54213 : checkPrefixCuts (2^48) 7109738497 10 Manual.Count131072.C054213.packed 64 cuts54213 = true := by
 decide +kernel
def pointBounds54213 : List (Nat × Nat × Nat) := [(7109844992,112662055823980,112662443517269)]
theorem point_links_checked54213 : (cuts54213.take 1).map (fun c => (7109738497-1+2*2^10*c.k,112661871810809+c.lower,112662259503993+c.upper)) = pointBounds54213 := by
 decide +kernel
def cuts54214 : List PrefixCut := [⟨64,230605680,230605812⟩]
theorem checked54214 : checkPrefixCuts (2^48) 7109869569 10 Manual.Count131072.C054214.packed 64 cuts54214 = true := by
 decide +kernel
def cuts54215 : List PrefixCut := [⟨33,119279860,119279930⟩,
⟨64,230047187,230047319⟩]
theorem checked54215 : checkPrefixCuts (2^48) 7110000641 10 Manual.Count131072.C054215.packed 64 cuts54215 = true := by
 decide +kernel
def pointBounds54215 : List (Nat × Nat × Nat) := [(7110068224,112662448030578,112662835724092)]
theorem point_links_checked54215 : (cuts54215.take 1).map (fun c => (7110000641-1+2*2^10*c.k,112662328750718+c.lower,112662716444162+c.upper)) = pointBounds54215 := by
 decide +kernel
def cuts54216 : List PrefixCut := [⟨64,227509323,227509452⟩]
theorem checked54216 : checkPrefixCuts (2^48) 7110131713 10 Manual.Count131072.C054216.packed 64 cuts54216 = true := by
 decide +kernel
def cuts54217 : List PrefixCut := [⟨14,52848711,52848741⟩,
⟨64,229524091,229524220⟩]
theorem checked54217 : checkPrefixCuts (2^48) 7110262785 10 Manual.Count131072.C054217.packed 64 cuts54217 = true := by
 decide +kernel
def pointBounds54217 : List (Nat × Nat × Nat) := [(7110291456,112662839155939,112663226849674)]
theorem point_links_checked54217 : (cuts54217.take 1).map (fun c => (7110262785-1+2*2^10*c.k,112662786307228+c.lower,112663174000933+c.upper)) = pointBounds54217 := by
 decide +kernel
def cuts54218 : List PrefixCut := [⟨59,210479092,210479209⟩,
⟨64,228173898,228174026⟩]
theorem checked54218 : checkPrefixCuts (2^48) 7110393857 10 Manual.Count131072.C054218.packed 64 cuts54218 = true := by
 decide +kernel
def pointBounds54218 : List (Nat × Nat × Nat) := [(7110514688,112663226310411,112663614004362)]
theorem point_links_checked54218 : (cuts54218.take 1).map (fun c => (7110393857-1+2*2^10*c.k,112663015831319+c.lower,112663403525153+c.upper)) = pointBounds54218 := by
 decide +kernel
def cuts54219 : List PrefixCut := [⟨64,229476003,229476131⟩]
theorem checked54219 : checkPrefixCuts (2^48) 7110524929 10 Manual.Count131072.C054219.packed 64 cuts54219 = true := by
 decide +kernel
def cuts54220 : List PrefixCut := [⟨40,141950781,141950861⟩,
⟨64,227215464,227215592⟩]
theorem checked54220 : checkPrefixCuts (2^48) 7110656001 10 Manual.Count131072.C054220.packed 64 cuts54220 = true := by
 decide +kernel
def pointBounds54220 : List (Nat × Nat × Nat) := [(7110737920,112663615432001,112664003126171)]
theorem point_links_checked54220 : (cuts54220.take 1).map (fun c => (7110656001-1+2*2^10*c.k,112663473481220+c.lower,112663861175310+c.upper)) = pointBounds54220 := by
 decide +kernel
def cuts54221 : List PrefixCut := [⟨64,227725854,227725985⟩]
theorem checked54221 : checkPrefixCuts (2^48) 7110787073 10 Manual.Count131072.C054221.packed 64 cuts54221 = true := by
 decide +kernel
def cuts54222 : List PrefixCut := [⟨21,75643807,75643849⟩,
⟨64,229621668,229621797⟩]
theorem checked54222 : checkPrefixCuts (2^48) 7110918145 10 Manual.Count131072.C054222.packed 64 cuts54222 = true := by
 decide +kernel
def pointBounds54222 : List (Nat × Nat × Nat) := [(7110961152,112664004066345,112664391760736)]
theorem point_links_checked54222 : (cuts54222.take 1).map (fun c => (7110918145-1+2*2^10*c.k,112663928422538+c.lower,112664316116887+c.upper)) = pointBounds54222 := by
 decide +kernel
def cuts54223 : List PrefixCut := [⟨64,231517356,231517487⟩]
theorem checked54223 : checkPrefixCuts (2^48) 7111049217 10 Manual.Count131072.C054223.packed 64 cuts54223 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000131
