import PlattAssemblyKernel
import PlattCertificates.Count131072.C018320
import PlattCertificates.Count131072.C018321
import PlattCertificates.Count131072.C018322
import PlattCertificates.Count131072.C018323
import PlattCertificates.Count131072.C018324
import PlattCertificates.Count131072.C018325
import PlattCertificates.Count131072.C018326
import PlattCertificates.Count131072.C018327
import PlattCertificates.Count131072.C018328
import PlattCertificates.Count131072.C018329
import PlattCertificates.Count131072.C018330
import PlattCertificates.Count131072.C018331
import PlattCertificates.Count131072.C018332
import PlattCertificates.Count131072.C018333
import PlattCertificates.Count131072.C018334
import PlattCertificates.Count131072.C018335
import PlattCertificates.Count131072.C018336
import PlattCertificates.Count131072.C018337
import PlattCertificates.Count131072.C018338
import PlattCertificates.Count131072.C018339
import PlattCertificates.Count131072.C018340
import PlattCertificates.Count131072.C018341
import PlattCertificates.Count131072.C018342
import PlattCertificates.Count131072.C018343
import PlattCertificates.Count131072.C018344
import PlattCertificates.Count131072.C018345
import PlattCertificates.Count131072.C018346
import PlattCertificates.Count131072.C018347
import PlattCertificates.Count131072.C018348
import PlattCertificates.Count131072.C018349
import PlattCertificates.Count131072.C018350
import PlattCertificates.Count131072.C018351
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000260
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18320 : List PrefixCut := [⟨52,291399092,291399270⟩,
⟨126,699932028,699932452⟩,
⟨128,711517277,711517709⟩]
theorem checked18320 : checkPrefixCuts (2^48) 2405171201 9 Manual.Count131072.C018320.packed 128 cuts18320 = true := by
 decide +kernel
def pointBounds18320 : List (Nat × Nat × Nat) := [(2405224448,98881825041830,98882204732054),(2405300224,98882233574766,98882613265236)]
theorem point_links_checked18320 : (cuts18320.take 2).map (fun c => (2405171201-1+2*2^9*c.k,98881533642738+c.lower,98881913332784+c.upper)) = pointBounds18320 := by
 decide +kernel
def cuts18321 : List PrefixCut := [⟨72,399509310,399509551⟩,
⟨128,716042178,716042611⟩]
theorem checked18321 : checkPrefixCuts (2^48) 2405302273 9 Manual.Count131072.C018321.packed 128 cuts18321 = true := by
 decide +kernel
def pointBounds18321 : List (Nat × Nat × Nat) := [(2405376000,98882644669325,98883024360044)]
theorem point_links_checked18321 : (cuts18321.take 1).map (fun c => (2405302273-1+2*2^9*c.k,98882245160015+c.lower,98882624850493+c.upper)) = pointBounds18321 := by
 decide +kernel
def cuts18322 : List PrefixCut := [⟨18,101803774,101803834⟩,
⟨92,511702210,511702524⟩,
⟨128,709216440,709216875⟩]
theorem checked18322 : checkPrefixCuts (2^48) 2405433345 9 Manual.Count131072.C018322.packed 128 cuts18322 = true := by
 decide +kernel
def pointBounds18322 : List (Nat × Nat × Nat) := [(2405451776,98883063005967,98883442696938),(2405527552,98883472904403,98883852595628)]
theorem point_links_checked18322 : (cuts18322.take 2).map (fun c => (2405433345-1+2*2^9*c.k,98882961202193+c.lower,98883340893104+c.upper)) = pointBounds18322 := by
 decide +kernel
def cuts18323 : List PrefixCut := [⟨38,218338742,218338874⟩,
⟨112,630434530,630434914⟩,
⟨128,717251448,717251887⟩]
theorem checked18323 : checkPrefixCuts (2^48) 2405564417 9 Manual.Count131072.C018323.packed 128 cuts18323 = true := by
 decide +kernel
def pointBounds18323 : List (Nat × Nat × Nat) := [(2405603328,98883888757375,98884268448853),(2405679104,98884300853163,98884680544893)]
theorem point_links_checked18323 : (cuts18323.take 2).map (fun c => (2405564417-1+2*2^9*c.k,98883670418633+c.lower,98884050109979+c.upper)) = pointBounds18323 := by
 decide +kernel
def cuts18324 : List PrefixCut := [⟨58,316958706,316958900⟩,
⟨128,709373024,709373458⟩]
theorem checked18324 : checkPrefixCuts (2^48) 2405695489 9 Manual.Count131072.C018324.packed 128 cuts18324 = true := by
 decide +kernel
def pointBounds18324 : List (Nat × Nat × Nat) := [(2405754880,98884704628787,98885084320766)]
theorem point_links_checked18324 : (cuts18324.take 1).map (fun c => (2405695489-1+2*2^9*c.k,98884387670081+c.lower,98884767361866+c.upper)) = pointBounds18324 := by
 decide +kernel
def cuts18325 : List PrefixCut := [⟨4,23165419,23165432⟩,
⟨78,428436458,428436718⟩,
⟨128,704303707,704304136⟩]
theorem checked18325 : checkPrefixCuts (2^48) 2405826561 9 Manual.Count131072.C018325.packed 128 cuts18325 = true := by
 decide +kernel
def pointBounds18325 : List (Nat × Nat × Nat) := [(2405830656,98885120208524,98885499900756),(2405906432,98885525479563,98885905172042)]
theorem point_links_checked18325 : (cuts18325.take 2).map (fun c => (2405826561-1+2*2^9*c.k,98885097043105+c.lower,98885476735324+c.upper)) = pointBounds18325 := by
 decide +kernel
def cuts18326 : List PrefixCut := [⟨24,128572218,128572296⟩,
⟨98,539199310,539199634⟩,
⟨128,702861572,702861994⟩]
theorem checked18326 : checkPrefixCuts (2^48) 2405957633 9 Manual.Count131072.C018326.packed 128 cuts18326 = true := by
 decide +kernel
def pointBounds18326 : List (Nat × Nat × Nat) := [(2405982208,98885929919030,98886309611756),(2406057984,98886340546122,98886720239094)]
theorem point_links_checked18326 : (cuts18326.take 2).map (fun c => (2405957633-1+2*2^9*c.k,98885801346812+c.lower,98886181039460+c.upper)) = pointBounds18326 := by
 decide +kernel
def cuts18327 : List PrefixCut := [⟨44,255725583,255725740⟩,
⟨118,659775851,659776255⟩,
⟨128,715574500,715574937⟩]
theorem checked18327 : checkPrefixCuts (2^48) 2406088705 9 Manual.Count131072.C018327.packed 128 cuts18327 = true := by
 decide +kernel
def pointBounds18327 : List (Nat × Nat × Nat) := [(2406133760,98886759933967,98887139627194),(2406209536,98887163984235,98887543677709)]
theorem point_links_checked18327 : (cuts18327.take 2).map (fun c => (2406088705-1+2*2^9*c.k,98886504208384+c.lower,98886883901454+c.upper)) = pointBounds18327 := by
 decide +kernel
def cuts18328 : List PrefixCut := [⟨64,355023584,355023796⟩,
⟨128,702551157,702551585⟩]
theorem checked18328 : checkPrefixCuts (2^48) 2406219777 9 Manual.Count131072.C018328.packed 128 cuts18328 = true := by
 decide +kernel
def pointBounds18328 : List (Nat × Nat × Nat) := [(2406285312,98887574806468,98887954500187)]
theorem point_links_checked18328 : (cuts18328.take 1).map (fun c => (2406219777-1+2*2^9*c.k,98887219782884+c.lower,98887599476391+c.upper)) = pointBounds18328 := by
 decide +kernel
def cuts18329 : List PrefixCut := [⟨10,53455941,53455973⟩,
⟨84,463316465,463316742⟩,
⟨128,709881651,709882072⟩]
theorem checked18329 : checkPrefixCuts (2^48) 2406350849 9 Manual.Count131072.C018329.packed 128 cuts18329 = true := by
 decide +kernel
def pointBounds18329 : List (Nat × Nat × Nat) := [(2406361088,98887975789982,98888355483949),(2406436864,98888385650506,98888765344718)]
theorem point_links_checked18329 : (cuts18329.take 2).map (fun c => (2406350849-1+2*2^9*c.k,98887922334041+c.lower,98888302027976+c.upper)) = pointBounds18329 := by
 decide +kernel
def cuts18330 : List PrefixCut := [⟨30,170651301,170651406⟩,
⟨104,581538699,581539049⟩,
⟨128,716510007,716510437⟩]
theorem checked18330 : checkPrefixCuts (2^48) 2406481921 9 Manual.Count131072.C018330.packed 128 cuts18330 = true := by
 decide +kernel
def pointBounds18330 : List (Nat × Nat × Nat) := [(2406512640,98888802866993,98889182561454),(2406588416,98889213754391,98889593449097)]
theorem point_links_checked18330 : (cuts18330.take 2).map (fun c => (2406481921-1+2*2^9*c.k,98888632215692+c.lower,98889011910048+c.upper)) = pointBounds18330 := by
 decide +kernel
def cuts18331 : List PrefixCut := [⟨50,272511417,272511582⟩,
⟨124,678226931,678227337⟩,
⟨128,700447936,700448357⟩]
theorem checked18331 : checkPrefixCuts (2^48) 2406612993 9 Manual.Count131072.C018331.packed 128 cuts18331 = true := by
 decide +kernel
def pointBounds18331 : List (Nat × Nat × Nat) := [(2406664192,98889621237116,98890000932067),(2406739968,98890026952630,98890406647822)]
theorem point_links_checked18331 : (cuts18331.take 2).map (fun c => (2406612993-1+2*2^9*c.k,98889348725699+c.lower,98889728420485+c.upper)) = pointBounds18331 := by
 decide +kernel
def cuts18332 : List PrefixCut := [⟨70,386288567,386288804⟩,
⟨128,712104671,712105103⟩]
theorem checked18332 : checkPrefixCuts (2^48) 2406744065 9 Manual.Count131072.C018332.packed 128 cuts18332 = true := by
 decide +kernel
def pointBounds18332 : List (Nat × Nat × Nat) := [(2406815744,98890435462202,98890815157646)]
theorem point_links_checked18332 : (cuts18332.take 1).map (fun c => (2406744065-1+2*2^9*c.k,98890049173635+c.lower,98890428868842+c.upper)) = pointBounds18332 := by
 decide +kernel
def cuts18333 : List PrefixCut := [⟨16,91919407,91919461⟩,
⟨90,503326816,503327121⟩,
⟨128,715574334,715574767⟩]
theorem checked18333 : checkPrefixCuts (2^48) 2406875137 9 Manual.Count131072.C018333.packed 128 cuts18333 = true := by
 decide +kernel
def pointBounds18333 : List (Nat × Nat × Nat) := [(2406891520,98890853197713,98891232893406),(2406967296,98891264605122,98891644301066)]
theorem point_links_checked18333 : (cuts18333.take 2).map (fun c => (2406875137-1+2*2^9*c.k,98890761278306+c.lower,98891140973945+c.upper)) = pointBounds18333 := by
 decide +kernel
def cuts18334 : List PrefixCut := [⟨36,196925149,196925267⟩,
⟨110,610060823,610061188⟩,
⟨128,707349838,707350260⟩]
theorem checked18334 : checkPrefixCuts (2^48) 2407006209 9 Manual.Count131072.C018334.packed 128 cuts18334 = true := by
 decide +kernel
def pointBounds18334 : List (Nat × Nat × Nat) := [(2407043072,98891673777789,98892053473979),(2407118848,98892086913463,98892466609900)]
theorem point_links_checked18334 : (cuts18334.take 2).map (fun c => (2407006209-1+2*2^9*c.k,98891476852640+c.lower,98891856548712+c.upper)) = pointBounds18334 := by
 decide +kernel
def cuts18335 : List PrefixCut := [⟨56,306245101,306245290⟩,
⟨128,707311169,707311598⟩]
theorem checked18335 : checkPrefixCuts (2^48) 2407137281 9 Manual.Count131072.C018335.packed 128 cuts18335 = true := by
 decide +kernel
def pointBounds18335 : List (Nat × Nat × Nat) := [(2407194624,98892490447579,98892870144262)]
theorem point_links_checked18335 : (cuts18335.take 1).map (fun c => (2407137281-1+2*2^9*c.k,98892184202478+c.lower,98892563898972+c.upper)) = pointBounds18335 := by
 decide +kernel
def cuts18336 : List PrefixCut := [⟨2,10991143,10991149⟩,
⟨76,414499811,414500064⟩,
⟨128,701192666,701193097⟩]
theorem checked18336 : checkPrefixCuts (2^48) 2407268353 9 Manual.Count131072.C018336.packed 128 cuts18336 = true := by
 decide +kernel
def pointBounds18336 : List (Nat × Nat × Nat) := [(2407270400,98892902504790,98893282201719),(2407346176,98893306013458,98893685710634)]
theorem point_links_checked18336 : (cuts18336.take 2).map (fun c => (2407268353-1+2*2^9*c.k,98892891513647+c.lower,98893271210570+c.upper)) = pointBounds18336 := by
 decide +kernel
def cuts18337 : List PrefixCut := [⟨22,121830824,121830896⟩,
⟨96,534784481,534784804⟩,
⟨128,709455723,709456154⟩]
theorem checked18337 : checkPrefixCuts (2^48) 2407399425 9 Manual.Count131072.C018337.packed 128 cuts18337 = true := by
 decide +kernel
def pointBounds18337 : List (Nat × Nat × Nat) := [(2407421952,98893714537137,98894094234563),(2407497728,98894127490794,98894507188471)]
theorem point_links_checked18337 : (cuts18337.take 2).map (fun c => (2407399425-1+2*2^9*c.k,98893592706313+c.lower,98893972403667+c.upper)) = pointBounds18337 := by
 decide +kernel
def cuts18338 : List PrefixCut := [⟨42,239204669,239204813⟩,
⟨116,662069664,662070065⟩,
⟨128,726836857,726837297⟩]
theorem checked18338 : checkPrefixCuts (2^48) 2407530497 9 Manual.Count131072.C018338.packed 128 cuts18338 = true := by
 decide +kernel
def pointBounds18338 : List (Nat × Nat × Nat) := [(2407573504,98894541366705,98894921064634),(2407649280,98894964231700,98895343929886)]
theorem point_links_checked18338 : (cuts18338.take 2).map (fun c => (2407530497-1+2*2^9*c.k,98894302162036+c.lower,98894681859821+c.upper)) = pointBounds18338 := by
 decide +kernel
def cuts18339 : List PrefixCut := [⟨62,343821839,343822046⟩,
⟨128,703767028,703767456⟩]
theorem checked18339 : checkPrefixCuts (2^48) 2407661569 9 Manual.Count131072.C018339.packed 128 cuts18339 = true := by
 decide +kernel
def pointBounds18339 : List (Nat × Nat × Nat) := [(2407725056,98895372820732,98895752519164)]
theorem point_links_checked18339 : (cuts18339.take 1).map (fun c => (2407661569-1+2*2^9*c.k,98895028998893+c.lower,98895408697118+c.upper)) = pointBounds18339 := by
 decide +kernel
def cuts18340 : List PrefixCut := [⟨8,42785924,42785950⟩,
⟨82,452868995,452869271⟩,
⟨128,710391811,710392242⟩]
theorem checked18340 : checkPrefixCuts (2^48) 2407792641 9 Manual.Count131072.C018340.packed 128 cuts18340 = true := by
 decide +kernel
def pointBounds18340 : List (Nat × Nat × Nat) := [(2407800832,98895775551845,98896155250524),(2407876608,98896185634916,98896565333845)]
theorem point_links_checked18340 : (cuts18340.take 2).map (fun c => (2407792641-1+2*2^9*c.k,98895732765921+c.lower,98896112464574+c.upper)) = pointBounds18340 := by
 decide +kernel
def cuts18341 : List PrefixCut := [⟨28,156404947,156405039⟩,
⟨102,572423683,572424026⟩,
⟨128,713860059,713860490⟩]
theorem checked18341 : checkPrefixCuts (2^48) 2407923713 9 Manual.Count131072.C018341.packed 128 cuts18341 = true := by
 decide +kernel
def pointBounds18341 : List (Nat × Nat × Nat) := [(2407952384,98896599562679,98896979261855),(2408028160,98897015581415,98897395280842)]
theorem point_links_checked18341 : (cuts18341.take 2).map (fun c => (2407923713-1+2*2^9*c.k,98896443157732+c.lower,98896822856816+c.upper)) = pointBounds18341 := by
 decide +kernel
def cuts18342 : List PrefixCut := [⟨48,262412942,262413102⟩,
⟨122,677119792,677120202⟩,
⟨128,712184599,712185031⟩]
theorem checked18342 : checkPrefixCuts (2^48) 2408054785 9 Manual.Count131072.C018342.packed 128 cuts18342 = true := by
 decide +kernel
def pointBounds18342 : List (Nat × Nat × Nat) := [(2408103936,98897419430733,98897799130408),(2408179712,98897834137583,98898213837508)]
theorem point_links_checked18342 : (cuts18342.take 2).map (fun c => (2408054785-1+2*2^9*c.k,98897157017791+c.lower,98897536717306+c.upper)) = pointBounds18342 := by
 decide +kernel
def cuts18343 : List PrefixCut := [⟨68,368875939,368876167⟩,
⟨128,704899288,704899719⟩]
theorem checked18343 : checkPrefixCuts (2^48) 2408185857 9 Manual.Count131072.C018343.packed 128 cuts18343 = true := by
 decide +kernel
def pointBounds18343 : List (Nat × Nat × Nat) := [(2408255488,98898238078329,98898617778504)]
theorem point_links_checked18343 : (cuts18343.take 1).map (fun c => (2408185857-1+2*2^9*c.k,98897869202390+c.lower,98898248902337+c.upper)) = pointBounds18343 := by
 decide +kernel
def cuts18344 : List PrefixCut := [⟨14,80293700,80293748⟩,
⟨88,500454450,500454752⟩,
⟨128,721106547,721106983⟩]
theorem checked18344 : checkPrefixCuts (2^48) 2408316929 9 Manual.Count131072.C018344.packed 128 cuts18344 = true := by
 decide +kernel
def pointBounds18344 : List (Nat × Nat × Nat) := [(2408331264,98898654395378,98899034095804),(2408407040,98899074556128,98899454256808)]
theorem point_links_checked18344 : (cuts18344.take 2).map (fun c => (2408316929-1+2*2^9*c.k,98898574101678+c.lower,98898953802056+c.upper)) = pointBounds18344 := by
 decide +kernel
def cuts18345 : List PrefixCut := [⟨34,183834907,183835014⟩,
⟨108,596022338,596022698⟩,
⟨128,705407015,705407439⟩]
theorem checked18345 : checkPrefixCuts (2^48) 2408448001 9 Manual.Count131072.C018345.packed 128 cuts18345 = true := by
 decide +kernel
def pointBounds18345 : List (Nat × Nat × Nat) := [(2408482816,98899479043132,98899858744053),(2408558592,98899891230563,98900270931737)]
theorem point_links_checked18345 : (cuts18345.take 2).map (fun c => (2408448001-1+2*2^9*c.k,98899295208225+c.lower,98899674909039+c.upper)) = pointBounds18345 := by
 decide +kernel
def cuts18346 : List PrefixCut := [⟨54,295894898,295895077⟩,
⟨128,703031471,703031895⟩]
theorem checked18346 : checkPrefixCuts (2^48) 2408579073 9 Manual.Count131072.C018346.packed 128 cuts18346 = true := by
 decide +kernel
def pointBounds18346 : List (Nat × Nat × Nat) := [(2408634368,98900296510138,98900676211555),(2408710144,98900703646711,98901083348373)]
theorem point_links_checked18346 : (cuts18346.take 2).map (fun c => (2408579073-1+2*2^9*c.k,98900000615240+c.lower,98900380316478+c.upper)) = pointBounds18346 := by
 decide +kernel
def cuts18347 : List PrefixCut := [⟨74,411096823,411097071⟩,
⟨128,708952761,708953186⟩]
theorem checked18347 : checkPrefixCuts (2^48) 2408710145 9 Manual.Count131072.C018347.packed 128 cuts18347 = true := by
 decide +kernel
def pointBounds18347 : List (Nat × Nat × Nat) := [(2408785920,98901114743534,98901494445444)]
theorem point_links_checked18347 : (cuts18347.take 1).map (fun c => (2408710145-1+2*2^9*c.k,98900703646711+c.lower,98901083348373+c.upper)) = pointBounds18347 := by
 decide +kernel
def cuts18348 : List PrefixCut := [⟨20,110890889,110890956⟩,
⟨94,520442869,520443183⟩,
⟨128,708563677,708564105⟩]
theorem checked18348 : checkPrefixCuts (2^48) 2408841217 9 Manual.Count131072.C018348.packed 128 cuts18348 = true := by
 decide +kernel
def pointBounds18348 : List (Nat × Nat × Nat) := [(2408861696,98901523490361,98901903192515),(2408937472,98901933042341,98902312744742)]
theorem point_links_checked18348 : (cuts18348.take 2).map (fun c => (2408841217-1+2*2^9*c.k,98901412599472+c.lower,98901792301559+c.upper)) = pointBounds18348 := by
 decide +kernel
def cuts18349 : List PrefixCut := [⟨40,223054025,223054161⟩,
⟨114,632112801,632113185⟩,
⟨128,709342971,709343402⟩]
theorem checked18349 : checkPrefixCuts (2^48) 2408972289 9 Manual.Count131072.C018349.packed 128 cuts18349 = true := by
 decide +kernel
def pointBounds18349 : List (Nat × Nat × Nat) := [(2409013248,98902344217174,98902723919825),(2409089024,98902753275950,98903132978849)]
theorem point_links_checked18349 : (cuts18349.take 2).map (fun c => (2408972289-1+2*2^9*c.k,98902121163149+c.lower,98902500865664+c.upper)) = pointBounds18349 := by
 decide +kernel
def cuts18350 : List PrefixCut := [⟨60,326324536,326324732⟩,
⟨128,701593337,701593760⟩]
theorem checked18350 : checkPrefixCuts (2^48) 2409103361 9 Manual.Count131072.C018350.packed 128 cuts18350 = true := by
 decide +kernel
def pointBounds18350 : List (Nat × Nat × Nat) := [(2409164800,98903156830656,98903536533798)]
theorem point_links_checked18350 : (cuts18350.take 1).map (fun c => (2409103361-1+2*2^9*c.k,98902830506120+c.lower,98903210209066+c.upper)) = pointBounds18350 := by
 decide +kernel
def cuts18351 : List PrefixCut := [⟨6,32362333,32362353⟩,
⟨80,442433964,442434232⟩,
⟨128,704008503,704008930⟩]
theorem checked18351 : checkPrefixCuts (2^48) 2409234433 9 Manual.Count131072.C018351.packed 128 cuts18351 = true := by
 decide +kernel
def pointBounds18351 : List (Nat × Nat × Nat) := [(2409240576,98903564461790,98903944165179),(2409316352,98903974533421,98904354237058)]
theorem point_links_checked18351 : (cuts18351.take 2).map (fun c => (2409234433-1+2*2^9*c.k,98903532099457+c.lower,98903911802826+c.upper)) = pointBounds18351 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000260
