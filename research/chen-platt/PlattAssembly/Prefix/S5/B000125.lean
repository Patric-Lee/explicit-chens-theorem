import PlattAssemblyKernel
import PlattCertificates.Count131072.C044000
import PlattCertificates.Count131072.C044001
import PlattCertificates.Count131072.C044002
import PlattCertificates.Count131072.C044003
import PlattCertificates.Count131072.C044004
import PlattCertificates.Count131072.C044005
import PlattCertificates.Count131072.C044006
import PlattCertificates.Count131072.C044007
import PlattCertificates.Count131072.C044008
import PlattCertificates.Count131072.C044009
import PlattCertificates.Count131072.C044010
import PlattCertificates.Count131072.C044011
import PlattCertificates.Count131072.C044012
import PlattCertificates.Count131072.C044013
import PlattCertificates.Count131072.C044014
import PlattCertificates.Count131072.C044015
import PlattCertificates.Count131072.C044016
import PlattCertificates.Count131072.C044017
import PlattCertificates.Count131072.C044018
import PlattCertificates.Count131072.C044019
import PlattCertificates.Count131072.C044020
import PlattCertificates.Count131072.C044021
import PlattCertificates.Count131072.C044022
import PlattCertificates.Count131072.C044023
import PlattCertificates.Count131072.C044024
import PlattCertificates.Count131072.C044025
import PlattCertificates.Count131072.C044026
import PlattCertificates.Count131072.C044027
import PlattCertificates.Count131072.C044028
import PlattCertificates.Count131072.C044029
import PlattCertificates.Count131072.C044030
import PlattCertificates.Count131072.C044031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000125
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts44000 : List PrefixCut := [⟨51,226890770,226890905⟩,
⟨64,283954225,283954390⟩]
theorem checked44000 : checkPrefixCuts (2^48) 5771100161 10 Manual.Count131072.C044000.packed 64 cuts44000 = true := by
 decide +kernel
def pointBounds44000 : List (Nat × Nat × Nat) := [(5771204608,110061772251843,110062158458755)]
theorem point_links_checked44000 : (cuts44000.take 1).map (fun c => (5771100161-1+2*2^10*c.k,110061545361073+c.lower,110061931567850+c.upper)) = pointBounds44000 := by
 decide +kernel
def cuts44001 : List PrefixCut := [⟨64,285703564,285703730⟩]
theorem checked44001 : checkPrefixCuts (2^48) 5771231233 10 Manual.Count131072.C044001.packed 64 cuts44001 = true := by
 decide +kernel
def cuts44002 : List PrefixCut := [⟨12,52331128,52331159⟩,
⟨64,285697041,285697205⟩]
theorem checked44002 : checkPrefixCuts (2^48) 5771362305 10 Manual.Count131072.C044002.packed 64 cuts44002 = true := by
 decide +kernel
def pointBounds44002 : List (Nat × Nat × Nat) := [(5771386880,110062167349990,110062553557129)]
theorem point_links_checked44002 : (cuts44002.take 1).map (fun c => (5771362305-1+2*2^10*c.k,110062115018862+c.lower,110062501225970+c.upper)) = pointBounds44002 := by
 decide +kernel
def cuts44003 : List PrefixCut := [⟨37,160988235,160988331⟩,
⟨64,280082081,280082248⟩]
theorem checked44003 : checkPrefixCuts (2^48) 5771493377 10 Manual.Count131072.C044003.packed 64 cuts44003 = true := by
 decide +kernel
def pointBounds44003 : List (Nat × Nat × Nat) := [(5771569152,110062561704138,110062947911506)]
theorem point_links_checked44003 : (cuts44003.take 1).map (fun c => (5771493377-1+2*2^10*c.k,110062400715903+c.lower,110062786923175+c.upper)) = pointBounds44003 := by
 decide +kernel
def cuts44004 : List PrefixCut := [⟨62,275784226,275784389⟩,
⟨64,285342687,285342856⟩]
theorem checked44004 : checkPrefixCuts (2^48) 5771624449 10 Manual.Count131072.C044004.packed 64 cuts44004 = true := by
 decide +kernel
def pointBounds44004 : List (Nat × Nat × Nat) := [(5771751424,110062956582210,110063342789812)]
theorem point_links_checked44004 : (cuts44004.take 1).map (fun c => (5771624449-1+2*2^10*c.k,110062680797984+c.lower,110063067005423+c.upper)) = pointBounds44004 := by
 decide +kernel
def cuts44005 : List PrefixCut := [⟨64,282654017,282654188⟩]
theorem checked44005 : checkPrefixCuts (2^48) 5771755521 10 Manual.Count131072.C044005.packed 64 cuts44005 = true := by
 decide +kernel
def cuts44006 : List PrefixCut := [⟨23,101190144,101190200⟩,
⟨64,284549469,284549630⟩]
theorem checked44006 : checkPrefixCuts (2^48) 5771886593 10 Manual.Count131072.C044006.packed 64 cuts44006 = true := by
 decide +kernel
def pointBounds44006 : List (Nat × Nat × Nat) := [(5771933696,110063349984832,110063736192667)]
theorem point_links_checked44006 : (cuts44006.take 1).map (fun c => (5771886593-1+2*2^10*c.k,110063248794688+c.lower,110063635002467+c.upper)) = pointBounds44006 := by
 decide +kernel
def cuts44007 : List PrefixCut := [⟨48,213737038,213737163⟩,
⟨64,284933147,284933313⟩]
theorem checked44007 : checkPrefixCuts (2^48) 5772017665 10 Manual.Count131072.C044007.packed 64 cuts44007 = true := by
 decide +kernel
def pointBounds44007 : List (Nat × Nat × Nat) := [(5772115968,110063747081195,110064133289260)]
theorem point_links_checked44007 : (cuts44007.take 1).map (fun c => (5772017665-1+2*2^10*c.k,110063533344157+c.lower,110063919552097+c.upper)) = pointBounds44007 := by
 decide +kernel
def cuts44008 : List PrefixCut := [⟨64,281854554,281854719⟩]
theorem checked44008 : checkPrefixCuts (2^48) 5772148737 10 Manual.Count131072.C044008.packed 64 cuts44008 = true := by
 decide +kernel
def cuts44009 : List PrefixCut := [⟨9,39498137,39498162⟩,
⟨64,282628373,282628537⟩]
theorem checked44009 : checkPrefixCuts (2^48) 5772279809 10 Manual.Count131072.C044009.packed 64 cuts44009 = true := by
 decide +kernel
def pointBounds44009 : List (Nat × Nat × Nat) := [(5772298240,110064139629995,110064525838291)]
theorem point_links_checked44009 : (cuts44009.take 1).map (fun c => (5772279809-1+2*2^10*c.k,110064100131858+c.lower,110064486340129+c.upper)) = pointBounds44009 := by
 decide +kernel
def cuts44010 : List PrefixCut := [⟨34,151259132,151259224⟩,
⟨64,285986482,285986651⟩]
theorem checked44010 : checkPrefixCuts (2^48) 5772410881 10 Manual.Count131072.C044010.packed 64 cuts44010 = true := by
 decide +kernel
def pointBounds44010 : List (Nat × Nat × Nat) := [(5772480512,110064534019363,110064920227890)]
theorem point_links_checked44010 : (cuts44010.take 1).map (fun c => (5772410881-1+2*2^10*c.k,110064382760231+c.lower,110064768968666+c.upper)) = pointBounds44010 := by
 decide +kernel
def cuts44011 : List PrefixCut := [⟨59,265890944,265891093⟩,
⟨64,288076714,288076875⟩]
theorem checked44011 : checkPrefixCuts (2^48) 5772541953 10 Manual.Count131072.C044011.packed 64 cuts44011 = true := by
 decide +kernel
def pointBounds44011 : List (Nat × Nat × Nat) := [(5772662784,110064934637657,110065320846410)]
theorem point_links_checked44011 : (cuts44011.take 1).map (fun c => (5772541953-1+2*2^10*c.k,110064668746713+c.lower,110065054955317+c.upper)) = pointBounds44011 := by
 decide +kernel
def cuts44012 : List PrefixCut := [⟨64,281877714,281877880⟩]
theorem checked44012 : checkPrefixCuts (2^48) 5772673025 10 Manual.Count131072.C044012.packed 64 cuts44012 = true := by
 decide +kernel
def cuts44013 : List PrefixCut := [⟨20,89520807,89520858⟩,
⟨64,286162047,286162213⟩]
theorem checked44013 : checkPrefixCuts (2^48) 5772804097 10 Manual.Count131072.C044013.packed 64 cuts44013 = true := by
 decide +kernel
def pointBounds44013 : List (Nat × Nat × Nat) := [(5772845056,110065328221948,110065714430930)]
theorem point_links_checked44013 : (cuts44013.take 1).map (fun c => (5772804097-1+2*2^10*c.k,110065238701141+c.lower,110065624910072+c.upper)) = pointBounds44013 := by
 decide +kernel
def cuts44014 : List PrefixCut := [⟨45,198295874,198295989⟩,
⟨64,283668912,283669076⟩]
theorem checked44014 : checkPrefixCuts (2^48) 5772935169 10 Manual.Count131072.C044014.packed 64 cuts44014 = true := by
 decide +kernel
def pointBounds44014 : List (Nat × Nat × Nat) := [(5773027328,110065723159062,110066109368274)]
theorem point_links_checked44014 : (cuts44014.take 1).map (fun c => (5772935169-1+2*2^10*c.k,110065524863188+c.lower,110065911072285+c.upper)) = pointBounds44014 := by
 decide +kernel
def cuts44015 : List PrefixCut := [⟨64,280688379,280688546⟩]
theorem checked44015 : checkPrefixCuts (2^48) 5773066241 10 Manual.Count131072.C044015.packed 64 cuts44015 = true := by
 decide +kernel
def cuts44016 : List PrefixCut := [⟨6,26181655,26181670⟩,
⟨64,286045038,286045198⟩]
theorem checked44016 : checkPrefixCuts (2^48) 5773197313 10 Manual.Count131072.C044016.packed 64 cuts44016 = true := by
 decide +kernel
def pointBounds44016 : List (Nat × Nat × Nat) := [(5773209600,110066115402134,110066501611577)]
theorem point_links_checked44016 : (cuts44016.take 1).map (fun c => (5773197313-1+2*2^10*c.k,110066089220479+c.lower,110066475429907+c.upper)) = pointBounds44016 := by
 decide +kernel
def cuts44017 : List PrefixCut := [⟨31,134317504,134317584⟩,
⟨64,281650674,281650837⟩]
theorem checked44017 : checkPrefixCuts (2^48) 5773328385 10 Manual.Count131072.C044017.packed 64 cuts44017 = true := by
 decide +kernel
def pointBounds44017 : List (Nat × Nat × Nat) := [(5773391872,110066509583021,110066895792689)]
theorem point_links_checked44017 : (cuts44017.take 1).map (fun c => (5773328385-1+2*2^10*c.k,110066375265517+c.lower,110066761475105+c.upper)) = pointBounds44017 := by
 decide +kernel
def cuts44018 : List PrefixCut := [⟨56,244982617,244982756⟩,
⟨64,280815491,280815651⟩]
theorem checked44018 : checkPrefixCuts (2^48) 5773459457 10 Manual.Count131072.C044018.packed 64 cuts44018 = true := by
 decide +kernel
def pointBounds44018 : List (Nat × Nat × Nat) := [(5773574144,110066901898808,110067288108698)]
theorem point_links_checked44018 : (cuts44018.take 1).map (fun c => (5773459457-1+2*2^10*c.k,110066656916191+c.lower,110067043125942+c.upper)) = pointBounds44018 := by
 decide +kernel
def cuts44019 : List PrefixCut := [⟨64,284221757,284221929⟩]
theorem checked44019 : checkPrefixCuts (2^48) 5773590529 10 Manual.Count131072.C044019.packed 64 cuts44019 = true := by
 decide +kernel
def cuts44020 : List PrefixCut := [⟨17,76538896,76538942⟩,
⟨64,283435302,283435464⟩]
theorem checked44020 : checkPrefixCuts (2^48) 5773721601 10 Manual.Count131072.C044020.packed 64 cuts44020 = true := by
 decide +kernel
def pointBounds44020 : List (Nat × Nat × Nat) := [(5773756416,110067298492335,110067684702464)]
theorem point_links_checked44020 : (cuts44020.take 1).map (fun c => (5773721601-1+2*2^10*c.k,110067221953439+c.lower,110067608163522+c.upper)) = pointBounds44020 := by
 decide +kernel
def cuts44021 : List PrefixCut := [⟨42,185345839,185345946⟩,
⟨64,285183812,285183974⟩]
theorem checked44021 : checkPrefixCuts (2^48) 5773852673 10 Manual.Count131072.C044021.packed 64 cuts44021 = true := by
 decide +kernel
def pointBounds44021 : List (Nat × Nat × Nat) := [(5773938688,110067690734580,110068076944932)]
theorem point_links_checked44021 : (cuts44021.take 1).map (fun c => (5773852673-1+2*2^10*c.k,110067505388741+c.lower,110067891598986+c.upper)) = pointBounds44021 := by
 decide +kernel
def cuts44022 : List PrefixCut := [⟨64,284884861,284885026⟩]
theorem checked44022 : checkPrefixCuts (2^48) 5773983745 10 Manual.Count131072.C044022.packed 64 cuts44022 = true := by
 decide +kernel
def cuts44023 : List PrefixCut := [⟨3,13064381,13064388⟩,
⟨64,282830995,282831156⟩]
theorem checked44023 : checkPrefixCuts (2^48) 5774114817 10 Manual.Count131072.C044023.packed 64 cuts44023 = true := by
 decide +kernel
def pointBounds44023 : List (Nat × Nat × Nat) := [(5774120960,110068088521795,110068474732374)]
theorem point_links_checked44023 : (cuts44023.take 1).map (fun c => (5774114817-1+2*2^10*c.k,110068075457414+c.lower,110068461667986+c.upper)) = pointBounds44023 := by
 decide +kernel
def cuts44024 : List PrefixCut := [⟨28,124205737,124205808⟩,
⟨64,283702032,283702195⟩]
theorem checked44024 : checkPrefixCuts (2^48) 5774245889 10 Manual.Count131072.C044024.packed 64 cuts44024 = true := by
 decide +kernel
def pointBounds44024 : List (Nat × Nat × Nat) := [(5774303232,110068482494146,110068868704950)]
theorem point_links_checked44024 : (cuts44024.take 1).map (fun c => (5774245889-1+2*2^10*c.k,110068358288409+c.lower,110068744499142+c.upper)) = pointBounds44024 := by
 decide +kernel
def cuts44025 : List PrefixCut := [⟨53,239338174,239338316⟩,
⟨64,287205262,287205433⟩]
theorem checked44025 : checkPrefixCuts (2^48) 5774376961 10 Manual.Count131072.C044025.packed 64 cuts44025 = true := by
 decide +kernel
def pointBounds44025 : List (Nat × Nat × Nat) := [(5774485504,110068881328615,110069267539653)]
theorem point_links_checked44025 : (cuts44025.take 1).map (fun c => (5774376961-1+2*2^10*c.k,110068641990441+c.lower,110069028201337+c.upper)) = pointBounds44025 := by
 decide +kernel
def cuts44026 : List PrefixCut := [⟨64,282763037,282763197⟩]
theorem checked44026 : checkPrefixCuts (2^48) 5774508033 10 Manual.Count131072.C044026.packed 64 cuts44026 = true := by
 decide +kernel
def cuts44027 : List PrefixCut := [⟨14,64097266,64097301⟩,
⟨64,283000341,283000506⟩]
theorem checked44027 : checkPrefixCuts (2^48) 5774639105 10 Manual.Count131072.C044027.packed 64 cuts44027 = true := by
 decide +kernel
def pointBounds44027 : List (Nat × Nat × Nat) := [(5774667776,110069276056006,110069662267268)]
theorem point_links_checked44027 : (cuts44027.take 1).map (fun c => (5774639105-1+2*2^10*c.k,110069211958740+c.lower,110069598169967+c.upper)) = pointBounds44027 := by
 decide +kernel
def cuts44028 : List PrefixCut := [⟨39,174398306,174398404⟩,
⟨64,283530056,283530218⟩]
theorem checked44028 : checkPrefixCuts (2^48) 5774770177 10 Manual.Count131072.C044028.packed 64 cuts44028 = true := by
 decide +kernel
def pointBounds44028 : List (Nat × Nat × Nat) := [(5774850048,110069669357387,110070055568877)]
theorem point_links_checked44028 : (cuts44028.take 1).map (fun c => (5774770177-1+2*2^10*c.k,110069494959081+c.lower,110069881170473+c.upper)) = pointBounds44028 := by
 decide +kernel
def cuts44029 : List PrefixCut := [⟨64,284888342,284888505⟩]
theorem checked44029 : checkPrefixCuts (2^48) 5774901249 10 Manual.Count131072.C044029.packed 64 cuts44029 = true := by
 decide +kernel
def pointBounds44029 : List (Nat × Nat × Nat) := [(5775032320,110070063377479,110070449589196)]
theorem point_links_checked44029 : (cuts44029.take 1).map (fun c => (5774901249-1+2*2^10*c.k,110069778489137+c.lower,110070164700691+c.upper)) = pointBounds44029 := by
 decide +kernel
def cuts44030 : List PrefixCut := [⟨64,286977673,286977839⟩]
theorem checked44030 : checkPrefixCuts (2^48) 5775032321 10 Manual.Count131072.C044030.packed 64 cuts44030 = true := by
 decide +kernel
def cuts44031 : List PrefixCut := [⟨25,109272045,109272108⟩,
⟨64,284436757,284436920⟩]
theorem checked44031 : checkPrefixCuts (2^48) 5775163393 10 Manual.Count131072.C044031.packed 64 cuts44031 = true := by
 decide +kernel
def pointBounds44031 : List (Nat × Nat × Nat) := [(5775214592,110070459627197,110070845839143)]
theorem point_links_checked44031 : (cuts44031.take 1).map (fun c => (5775163393-1+2*2^10*c.k,110070350355152+c.lower,110070736567035+c.upper)) = pointBounds44031 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000125
