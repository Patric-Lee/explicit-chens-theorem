import PlattAssemblyKernel
import PlattCertificates.Count131072.C028512
import PlattCertificates.Count131072.C028513
import PlattCertificates.Count131072.C028514
import PlattCertificates.Count131072.C028515
import PlattCertificates.Count131072.C028516
import PlattCertificates.Count131072.C028517
import PlattCertificates.Count131072.C028518
import PlattCertificates.Count131072.C028519
import PlattCertificates.Count131072.C028520
import PlattCertificates.Count131072.C028521
import PlattCertificates.Count131072.C028522
import PlattCertificates.Count131072.C028523
import PlattCertificates.Count131072.C028524
import PlattCertificates.Count131072.C028525
import PlattCertificates.Count131072.C028526
import PlattCertificates.Count131072.C028527
import PlattCertificates.Count131072.C028528
import PlattCertificates.Count131072.C028529
import PlattCertificates.Count131072.C028530
import PlattCertificates.Count131072.C028531
import PlattCertificates.Count131072.C028532
import PlattCertificates.Count131072.C028533
import PlattCertificates.Count131072.C028534
import PlattCertificates.Count131072.C028535
import PlattCertificates.Count131072.C028536
import PlattCertificates.Count131072.C028537
import PlattCertificates.Count131072.C028538
import PlattCertificates.Count131072.C028539
import PlattCertificates.Count131072.C028540
import PlattCertificates.Count131072.C028541
import PlattCertificates.Count131072.C028542
import PlattCertificates.Count131072.C028543
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000266
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28512 : List PrefixCut := [⟨51,178090433,178090531⟩,
⟨128,444581835,444582082⟩]
theorem checked28512 : checkPrefixCuts (2^48) 3741057025 9 Manual.Count131072.C028512.packed 128 cuts28512 = true := by
 decide +kernel
def pointBounds28512 : List (Nat × Nat × Nat) := [(3741109248,104580026610101,104580409568139)]
theorem point_links_checked28512 : (cuts28512.take 1).map (fun c => (3741057025-1+2*2^9*c.k,104579848519668+c.lower,104580231477608+c.upper)) = pointBounds28512 := by
 decide +kernel
def cuts28513 : List PrefixCut := [⟨38,132641726,132641802⟩,
⟨128,448478449,448478706⟩]
theorem checked28513 : checkPrefixCuts (2^48) 3741188097 9 Manual.Count131072.C028513.packed 128 cuts28513 = true := by
 decide +kernel
def pointBounds28513 : List (Nat × Nat × Nat) := [(3741227008,104580425743229,104580808701492)]
theorem point_links_checked28513 : (cuts28513.take 1).map (fun c => (3741188097-1+2*2^9*c.k,104580293101503+c.lower,104580676059690+c.upper)) = pointBounds28513 := by
 decide +kernel
def cuts28514 : List PrefixCut := [⟨25,85917085,85917132⟩,
⟨128,445829570,445829823⟩]
theorem checked28514 : checkPrefixCuts (2^48) 3741319169 9 Manual.Count131072.C028514.packed 128 cuts28514 = true := by
 decide +kernel
def pointBounds28514 : List (Nat × Nat × Nat) := [(3741344768,104580827497037,104581210455528)]
theorem point_links_checked28514 : (cuts28514.take 1).map (fun c => (3741319169-1+2*2^9*c.k,104580741579952+c.lower,104581124538396+c.upper)) = pointBounds28514 := by
 decide +kernel
def cuts28515 : List PrefixCut := [⟨12,42656186,42656210⟩,
⟨127,448447137,448447390⟩,
⟨128,452283809,452284065⟩]
theorem checked28515 : checkPrefixCuts (2^48) 3741450241 9 Manual.Count131072.C028515.packed 128 cuts28515 = true := by
 decide +kernel
def pointBounds28515 : List (Nat × Nat × Nat) := [(3741462528,104581230065708,104581613024429),(3741580288,104581635856659,104582018815609)]
theorem point_links_checked28515 : (cuts28515.take 2).map (fun c => (3741450241-1+2*2^9*c.k,104581187409522+c.lower,104581570368219+c.upper)) = pointBounds28515 := by
 decide +kernel
def cuts28516 : List PrefixCut := [⟨114,394719668,394719891⟩,
⟨128,443917713,443917964⟩]
theorem checked28516 : checkPrefixCuts (2^48) 3741581313 9 Manual.Count131072.C028516.packed 128 cuts28516 = true := by
 decide +kernel
def pointBounds28516 : List (Nat × Nat × Nat) := [(3741698048,104582034412999,104582417372175)]
theorem point_links_checked28516 : (cuts28516.take 1).map (fun c => (3741581313-1+2*2^9*c.k,104581639693331+c.lower,104582022652284+c.upper)) = pointBounds28516 := by
 decide +kernel
def cuts28517 : List PrefixCut := [⟨101,352429982,352430184⟩,
⟨128,447588172,447588425⟩]
theorem checked28517 : checkPrefixCuts (2^48) 3741712385 9 Manual.Count131072.C028517.packed 128 cuts28517 = true := by
 decide +kernel
def pointBounds28517 : List (Nat × Nat × Nat) := [(3741815808,104582436041026,104582819000432)]
theorem point_links_checked28517 : (cuts28517.take 1).map (fun c => (3741712385-1+2*2^9*c.k,104582083611044+c.lower,104582466570248+c.upper)) = pointBounds28517 := by
 decide +kernel
def cuts28518 : List PrefixCut := [⟨88,303448329,303448499⟩,
⟨128,440652110,440652360⟩]
theorem checked28518 : checkPrefixCuts (2^48) 3741843457 9 Manual.Count131072.C028518.packed 128 cuts28518 = true := by
 decide +kernel
def pointBounds28518 : List (Nat × Nat × Nat) := [(3741933568,104582834647545,104583217607172)]
theorem point_links_checked28518 : (cuts28518.take 1).map (fun c => (3741843457-1+2*2^9*c.k,104582531199216+c.lower,104582914158673+c.upper)) = pointBounds28518 := by
 decide +kernel
def cuts28519 : List PrefixCut := [⟨75,265452013,265452162⟩,
⟨128,445977284,445977535⟩]
theorem checked28519 : checkPrefixCuts (2^48) 3741974529 9 Manual.Count131072.C028519.packed 128 cuts28519 = true := by
 decide +kernel
def pointBounds28519 : List (Nat × Nat × Nat) := [(3742051328,104583237303339,104583620263195)]
theorem point_links_checked28519 : (cuts28519.take 1).map (fun c => (3741974529-1+2*2^9*c.k,104582971851326+c.lower,104583354811033+c.upper)) = pointBounds28519 := by
 decide +kernel
def cuts28520 : List PrefixCut := [⟨62,219861295,219861416⟩,
⟨128,454160266,454160515⟩]
theorem checked28520 : checkPrefixCuts (2^48) 3742105601 9 Manual.Count131072.C028520.packed 128 cuts28520 = true := by
 decide +kernel
def pointBounds28520 : List (Nat × Nat × Nat) := [(3742169088,104583637689905,104584020649984)]
theorem point_links_checked28520 : (cuts28520.take 1).map (fun c => (3742105601-1+2*2^9*c.k,104583417828610+c.lower,104583800788568+c.upper)) = pointBounds28520 := by
 decide +kernel
def cuts28521 : List PrefixCut := [⟨49,173671855,173671953⟩,
⟨128,450759728,450759983⟩]
theorem checked28521 : checkPrefixCuts (2^48) 3742236673 9 Manual.Count131072.C028521.packed 128 cuts28521 = true := by
 decide +kernel
def pointBounds28521 : List (Nat × Nat × Nat) := [(3742286848,104584045660731,104584428621036)]
theorem point_links_checked28521 : (cuts28521.take 1).map (fun c => (3742236673-1+2*2^9*c.k,104583871988876+c.lower,104584254949083+c.upper)) = pointBounds28521 := by
 decide +kernel
def cuts28522 : List PrefixCut := [⟨36,126733363,126733430⟩,
⟨128,446381716,446381961⟩]
theorem checked28522 : checkPrefixCuts (2^48) 3742367745 9 Manual.Count131072.C028522.packed 128 cuts28522 = true := by
 decide +kernel
def pointBounds28522 : List (Nat × Nat × Nat) := [(3742404608,104584449481967,104584832442496)]
theorem point_links_checked28522 : (cuts28522.take 1).map (fun c => (3742367745-1+2*2^9*c.k,104584322748604+c.lower,104584705709066+c.upper)) = pointBounds28522 := by
 decide +kernel
def cuts28523 : List PrefixCut := [⟨23,81377424,81377469⟩,
⟨128,450577702,450577952⟩]
theorem checked28523 : checkPrefixCuts (2^48) 3742498817 9 Manual.Count131072.C028523.packed 128 cuts28523 = true := by
 decide +kernel
def pointBounds28523 : List (Nat × Nat × Nat) := [(3742522368,104584850507744,104585233468496)]
theorem point_links_checked28523 : (cuts28523.take 1).map (fun c => (3742498817-1+2*2^9*c.k,104584769130320+c.lower,104585152091027+c.upper)) = pointBounds28523 := by
 decide +kernel
def cuts28524 : List PrefixCut := [⟨10,33768249,33768268⟩,
⟨125,437927388,437927634⟩,
⟨128,448305703,448305955⟩]
theorem checked28524 : checkPrefixCuts (2^48) 3742629889 9 Manual.Count131072.C028524.packed 128 cuts28524 = true := by
 decide +kernel
def pointBounds28524 : List (Nat × Nat × Nat) := [(3742640128,104585253476271,104585636437247),(3742757888,104585657635410,104586040596613)]
theorem point_links_checked28524 : (cuts28524.take 2).map (fun c => (3742629889-1+2*2^9*c.k,104585219708022+c.lower,104585602668979+c.upper)) = pointBounds28524 := by
 decide +kernel
def cuts28525 : List PrefixCut := [⟨112,395196962,395197181⟩,
⟨128,452501403,452501654⟩]
theorem checked28525 : checkPrefixCuts (2^48) 3742760961 9 Manual.Count131072.C028525.packed 128 cuts28525 = true := by
 decide +kernel
def pointBounds28525 : List (Nat × Nat × Nat) := [(3742875648,104586063210687,104586446172115)]
theorem point_links_checked28525 : (cuts28525.take 1).map (fun c => (3742760961-1+2*2^9*c.k,104585668013725+c.lower,104586050974934+c.upper)) = pointBounds28525 := by
 decide +kernel
def cuts28526 : List PrefixCut := [⟨99,342091647,342091844⟩,
⟨128,444514297,444514552⟩]
theorem checked28526 : checkPrefixCuts (2^48) 3742892033 9 Manual.Count131072.C028526.packed 128 cuts28526 = true := by
 decide +kernel
def pointBounds28526 : List (Nat × Nat × Nat) := [(3742993408,104586462606775,104586845568432)]
theorem point_links_checked28526 : (cuts28526.take 1).map (fun c => (3742892033-1+2*2^9*c.k,104586120515128+c.lower,104586503476588+c.upper)) = pointBounds28526 := by
 decide +kernel
def cuts28527 : List PrefixCut := [⟨86,298013643,298013809⟩,
⟨128,444874720,444874966⟩]
theorem checked28527 : checkPrefixCuts (2^48) 3743023105 9 Manual.Count131072.C028527.packed 128 cuts28527 = true := by
 decide +kernel
def pointBounds28527 : List (Nat × Nat × Nat) := [(3743111168,104586863043068,104587246004949)]
theorem point_links_checked28527 : (cuts28527.take 1).map (fun c => (3743023105-1+2*2^9*c.k,104586565029425+c.lower,104586947991140+c.upper)) = pointBounds28527 := by
 decide +kernel
def cuts28528 : List PrefixCut := [⟨73,255743282,255743426⟩,
⟨128,451025160,451025411⟩]
theorem checked28528 : checkPrefixCuts (2^48) 3743154177 9 Manual.Count131072.C028528.packed 128 cuts28528 = true := by
 decide +kernel
def pointBounds28528 : List (Nat × Nat × Nat) := [(3743228928,104587265647427,104587648609532)]
theorem point_links_checked28528 : (cuts28528.take 1).map (fun c => (3743154177-1+2*2^9*c.k,104587009904145+c.lower,104587392866106+c.upper)) = pointBounds28528 := by
 decide +kernel
def cuts28529 : List PrefixCut := [⟨60,205730761,205730879⟩,
⟨128,439880769,439881016⟩]
theorem checked28529 : checkPrefixCuts (2^48) 3743285249 9 Manual.Count131072.C028529.packed 128 cuts28529 = true := by
 decide +kernel
def pointBounds28529 : List (Nat × Nat × Nat) := [(3743346688,104587666660066,104588049622396)]
theorem point_links_checked28529 : (cuts28529.take 1).map (fun c => (3743285249-1+2*2^9*c.k,104587460929305+c.lower,104587843891517+c.upper)) = pointBounds28529 := by
 decide +kernel
def cuts28530 : List PrefixCut := [⟨47,164143044,164143134⟩,
⟨128,454226778,454227030⟩]
theorem checked28530 : checkPrefixCuts (2^48) 3743416321 9 Manual.Count131072.C028530.packed 128 cuts28530 = true := by
 decide +kernel
def pointBounds28530 : List (Nat × Nat × Nat) := [(3743464448,104588064953118,104588447915667)]
theorem point_links_checked28530 : (cuts28530.take 1).map (fun c => (3743416321-1+2*2^9*c.k,104587900810074+c.lower,104588283772533+c.upper)) = pointBounds28530 := by
 decide +kernel
def cuts28531 : List PrefixCut := [⟨34,117896356,117896422⟩,
⟨128,448421409,448421661⟩]
theorem checked28531 : checkPrefixCuts (2^48) 3743547393 9 Manual.Count131072.C028531.packed 128 cuts28531 = true := by
 decide +kernel
def pointBounds28531 : List (Nat × Nat × Nat) := [(3743582208,104588472933208,104588855895985)]
theorem point_links_checked28531 : (cuts28531.take 1).map (fun c => (3743547393-1+2*2^9*c.k,104588355036852+c.lower,104588737999563+c.upper)) = pointBounds28531 := by
 decide +kernel
def cuts28532 : List PrefixCut := [⟨21,71351988,71352029⟩,
⟨128,447804192,447804446⟩]
theorem checked28532 : checkPrefixCuts (2^48) 3743678465 9 Manual.Count131072.C028532.packed 128 cuts28532 = true := by
 decide +kernel
def pointBounds28532 : List (Nat × Nat × Nat) := [(3743699968,104588874810249,104589257773253)]
theorem point_links_checked28532 : (cuts28532.take 1).map (fun c => (3743678465-1+2*2^9*c.k,104588803458261+c.lower,104589186421224+c.upper)) = pointBounds28532 := by
 decide +kernel
def cuts28533 : List PrefixCut := [⟨8,25863299,25863315⟩,
⟨123,430271210,430271452⟩,
⟨128,448690680,448690931⟩]
theorem checked28533 : checkPrefixCuts (2^48) 3743809537 9 Manual.Count131072.C028533.packed 128 cuts28533 = true := by
 decide +kernel
def pointBounds28533 : List (Nat × Nat × Nat) := [(3743817728,104589277125752,104589660088985),(3743935488,104589681533663,104590064497122)]
theorem point_links_checked28533 : (cuts28533.take 2).map (fun c => (3743809537-1+2*2^9*c.k,104589251262453+c.lower,104589634225670+c.upper)) = pointBounds28533 := by
 decide +kernel
def cuts28534 : List PrefixCut := [⟨110,378608082,378608294⟩,
⟨128,443713104,443713352⟩]
theorem checked28534 : checkPrefixCuts (2^48) 3743940609 9 Manual.Count131072.C028534.packed 128 cuts28534 = true := by
 decide +kernel
def pointBounds28534 : List (Nat × Nat × Nat) := [(3744053248,104590078561215,104590461524895)]
theorem point_links_checked28534 : (cuts28534.take 1).map (fun c => (3743940609-1+2*2^9*c.k,104589699953133+c.lower,104590082916601+c.upper)) = pointBounds28534 := by
 decide +kernel
def cuts28535 : List PrefixCut := [⟨97,345066240,345066432⟩,
⟨128,451065124,451065377⟩]
theorem checked28535 : checkPrefixCuts (2^48) 3744071681 9 Manual.Count131072.C028535.packed 128 cuts28535 = true := by
 decide +kernel
def pointBounds28535 : List (Nat × Nat × Nat) := [(3744171008,104590488732477,104590871696385)]
theorem point_links_checked28535 : (cuts28535.take 1).map (fun c => (3744071681-1+2*2^9*c.k,104590143666237+c.lower,104590526629953+c.upper)) = pointBounds28535 := by
 decide +kernel
def cuts28536 : List PrefixCut := [⟨84,287620777,287620939⟩,
⟨128,443832377,443832623⟩]
theorem checked28536 : checkPrefixCuts (2^48) 3744202753 9 Manual.Count131072.C028536.packed 128 cuts28536 = true := by
 decide +kernel
def pointBounds28536 : List (Nat × Nat × Nat) := [(3744288768,104590882352138,104591265316269)]
theorem point_links_checked28536 : (cuts28536.take 1).map (fun c => (3744202753-1+2*2^9*c.k,104590594731361+c.lower,104590977695330+c.upper)) = pointBounds28536 := by
 decide +kernel
def cuts28537 : List PrefixCut := [⟨71,245364083,245364223⟩,
⟨128,445470649,445470903⟩]
theorem checked28537 : checkPrefixCuts (2^48) 3744333825 9 Manual.Count131072.C028537.packed 128 cuts28537 = true := by
 decide +kernel
def pointBounds28537 : List (Nat × Nat × Nat) := [(3744406528,104591283927821,104591666892176)]
theorem point_links_checked28537 : (cuts28537.take 1).map (fun c => (3744333825-1+2*2^9*c.k,104591038563738+c.lower,104591421527953+c.upper)) = pointBounds28537 := by
 decide +kernel
def cuts28538 : List PrefixCut := [⟨58,202659217,202659329⟩,
⟨128,447409534,447409786⟩]
theorem checked28538 : checkPrefixCuts (2^48) 3744464897 9 Manual.Count131072.C028538.packed 128 cuts28538 = true := by
 decide +kernel
def pointBounds28538 : List (Nat × Nat × Nat) := [(3744524288,104591686693604,104592069658185)]
theorem point_links_checked28538 : (cuts28538.take 1).map (fun c => (3744464897-1+2*2^9*c.k,104591484034387+c.lower,104591866998856+c.upper)) = pointBounds28538 := by
 decide +kernel
def cuts28539 : List PrefixCut := [⟨45,157551766,157551851⟩,
⟨128,445589871,445590117⟩]
theorem checked28539 : checkPrefixCuts (2^48) 3744595969 9 Manual.Count131072.C028539.packed 128 cuts28539 = true := by
 decide +kernel
def pointBounds28539 : List (Nat × Nat × Nat) := [(3744642048,104592088995687,104592471960493)]
theorem point_links_checked28539 : (cuts28539.take 1).map (fun c => (3744595969-1+2*2^9*c.k,104591931443921+c.lower,104592314408642+c.upper)) = pointBounds28539 := by
 decide +kernel
def cuts28540 : List PrefixCut := [⟨32,110868870,110868932⟩,
⟨128,451662514,451662766⟩]
theorem checked28540 : checkPrefixCuts (2^48) 3744727041 9 Manual.Count131072.C028540.packed 128 cuts28540 = true := by
 decide +kernel
def pointBounds28540 : List (Nat × Nat × Nat) := [(3744759808,104592487902662,104592870867691)]
theorem point_links_checked28540 : (cuts28540.take 1).map (fun c => (3744727041-1+2*2^9*c.k,104592377033792+c.lower,104592759998759+c.upper)) = pointBounds28540 := by
 decide +kernel
def cuts28541 : List PrefixCut := [⟨19,67496224,67496263⟩,
⟨128,446159997,446160252⟩]
theorem checked28541 : checkPrefixCuts (2^48) 3744858113 9 Manual.Count131072.C028541.packed 128 cuts28541 = true := by
 decide +kernel
def pointBounds28541 : List (Nat × Nat × Nat) := [(3744877568,104592896192530,104593279157788)]
theorem point_links_checked28541 : (cuts28541.take 1).map (fun c => (3744858113-1+2*2^9*c.k,104592828696306+c.lower,104593211661525+c.upper)) = pointBounds28541 := by
 decide +kernel
def cuts28542 : List PrefixCut := [⟨6,22021981,22021994⟩,
⟨121,426002141,426002375⟩,
⟨128,451255178,451255426⟩]
theorem checked28542 : checkPrefixCuts (2^48) 3744989185 9 Manual.Count131072.C028542.packed 128 cuts28542 = true := by
 decide +kernel
def pointBounds28542 : List (Nat × Nat × Nat) := [(3744995328,104593296878284,104593679843771),(3745113088,104593700858444,104594083824152)]
theorem point_links_checked28542 : (cuts28542.take 2).map (fun c => (3744989185-1+2*2^9*c.k,104593274856303+c.lower,104593657821777+c.upper)) = pointBounds28542 := by
 decide +kernel
def cuts28543 : List PrefixCut := [⟨108,375106896,375107107⟩,
⟨128,445452308,445452558⟩]
theorem checked28543 : checkPrefixCuts (2^48) 3745120257 9 Manual.Count131072.C028543.packed 128 cuts28543 = true := by
 decide +kernel
def pointBounds28543 : List (Nat × Nat × Nat) := [(3745230848,104594101218377,104594484184310)]
theorem point_links_checked28543 : (cuts28543.take 1).map (fun c => (3745120257-1+2*2^9*c.k,104593726111481+c.lower,104594109077203+c.upper)) = pointBounds28543 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000266
