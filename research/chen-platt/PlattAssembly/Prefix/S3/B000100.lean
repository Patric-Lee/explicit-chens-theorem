import PlattAssemblyKernel
import PlattCertificates.Count131072.C023200
import PlattCertificates.Count131072.C023201
import PlattCertificates.Count131072.C023202
import PlattCertificates.Count131072.C023203
import PlattCertificates.Count131072.C023204
import PlattCertificates.Count131072.C023205
import PlattCertificates.Count131072.C023206
import PlattCertificates.Count131072.C023207
import PlattCertificates.Count131072.C023208
import PlattCertificates.Count131072.C023209
import PlattCertificates.Count131072.C023210
import PlattCertificates.Count131072.C023211
import PlattCertificates.Count131072.C023212
import PlattCertificates.Count131072.C023213
import PlattCertificates.Count131072.C023214
import PlattCertificates.Count131072.C023215
import PlattCertificates.Count131072.C023216
import PlattCertificates.Count131072.C023217
import PlattCertificates.Count131072.C023218
import PlattCertificates.Count131072.C023219
import PlattCertificates.Count131072.C023220
import PlattCertificates.Count131072.C023221
import PlattCertificates.Count131072.C023222
import PlattCertificates.Count131072.C023223
import PlattCertificates.Count131072.C023224
import PlattCertificates.Count131072.C023225
import PlattCertificates.Count131072.C023226
import PlattCertificates.Count131072.C023227
import PlattCertificates.Count131072.C023228
import PlattCertificates.Count131072.C023229
import PlattCertificates.Count131072.C023230
import PlattCertificates.Count131072.C023231
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000100
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23200 : List PrefixCut := [⟨44,195888194,195888300⟩,
⟨128,561125350,561125669⟩]
theorem checked23200 : checkPrefixCuts (2^48) 3044802561 9 Manual.Count131072.C023200.packed 128 cuts23200 = true := by
 decide +kernel
def pointBounds23200 : List (Nat × Nat × Nat) := [(3044847616,101937902483693,101938283958523)]
theorem point_links_checked23200 : (cuts23200.take 1).map (fun c => (3044802561-1+2*2^9*c.k,101937706595499+c.lower,101938088070223+c.upper)) = pointBounds23200 := by
 decide +kernel
def cuts23201 : List PrefixCut := [⟨9,36513905,36513926⟩,
⟨102,438252450,438252692⟩,
⟨128,551117821,551118127⟩]
theorem checked23201 : checkPrefixCuts (2^48) 3044933633 9 Manual.Count131072.C023201.packed 128 cuts23201 = true := by
 decide +kernel
def pointBounds23201 : List (Nat × Nat × Nat) := [(3044942848,101938304234754,101938685709818),(3045038080,101938705973299,101939087448584)]
theorem point_links_checked23201 : (cuts23201.take 2).map (fun c => (3044933633-1+2*2^9*c.k,101938267720849+c.lower,101938649195892+c.upper)) = pointBounds23201 := by
 decide +kernel
def cuts23202 : List PrefixCut := [⟨67,293020224,293020389⟩,
⟨128,556085639,556085950⟩]
theorem checked23202 : checkPrefixCuts (2^48) 3045064705 9 Manual.Count131072.C023202.packed 128 cuts23202 = true := by
 decide +kernel
def pointBounds23202 : List (Nat × Nat × Nat) := [(3045133312,101939111858894,101939493334408)]
theorem point_links_checked23202 : (cuts23202.take 1).map (fun c => (3045064705-1+2*2^9*c.k,101938818838670+c.lower,101939200314019+c.upper)) = pointBounds23202 := by
 decide +kernel
def cuts23203 : List PrefixCut := [⟨32,135597669,135597747⟩,
⟨125,540256276,540256587⟩,
⟨128,553473553,553473872⟩]
theorem checked23203 : checkPrefixCuts (2^48) 3045195777 9 Manual.Count131072.C023203.packed 128 cuts23203 = true := by
 decide +kernel
def pointBounds23203 : List (Nat × Nat × Nat) := [(3045228544,101939510521978,101939891997716),(3045323776,101939915180585,101940296656556)]
theorem point_links_checked23203 : (cuts23203.take 2).map (fun c => (3045195777-1+2*2^9*c.k,101939374924309+c.lower,101939756399969+c.upper)) = pointBounds23203 := by
 decide +kernel
def cuts23204 : List PrefixCut := [⟨90,388655843,388656063⟩,
⟨128,552433102,552433413⟩]
theorem checked23204 : checkPrefixCuts (2^48) 3045326849 9 Manual.Count131072.C023204.packed 128 cuts23204 = true := by
 decide +kernel
def pointBounds23204 : List (Nat × Nat × Nat) := [(3045419008,101940317053705,101940698529904)]
theorem point_links_checked23204 : (cuts23204.take 1).map (fun c => (3045326849-1+2*2^9*c.k,101939928397862+c.lower,101940309873841+c.upper)) = pointBounds23204 := by
 decide +kernel
def cuts23205 : List PrefixCut := [⟨55,243536259,243536404⟩,
⟨128,554812354,554812677⟩]
theorem checked23205 : checkPrefixCuts (2^48) 3045457921 9 Manual.Count131072.C023205.packed 128 cuts23205 = true := by
 decide +kernel
def pointBounds23205 : List (Nat × Nat × Nat) := [(3045514240,101940724367223,101941105843658)]
theorem point_links_checked23205 : (cuts23205.take 1).map (fun c => (3045457921-1+2*2^9*c.k,101940480830964+c.lower,101940862307254+c.upper)) = pointBounds23205 := by
 decide +kernel
def cuts23206 : List PrefixCut := [⟨20,89647601,89647651⟩,
⟨113,497767450,497767731⟩,
⟨128,565971030,565971351⟩]
theorem checked23206 : checkPrefixCuts (2^48) 3045588993 9 Manual.Count131072.C023206.packed 128 cuts23206 = true := by
 decide +kernel
def pointBounds23206 : List (Nat × Nat × Nat) := [(3045609472,101941125290919,101941506767582),(3045704704,101941533410768,101941914887662)]
theorem point_links_checked23206 : (cuts23206.take 2).map (fun c => (3045588993-1+2*2^9*c.k,101941035643318+c.lower,101941417119931+c.upper)) = pointBounds23206 := by
 decide +kernel
def cuts23207 : List PrefixCut := [⟨78,339903513,339903708⟩,
⟨128,554949327,554949641⟩]
theorem checked23207 : checkPrefixCuts (2^48) 3045720065 9 Manual.Count131072.C023207.packed 128 cuts23207 = true := by
 decide +kernel
def pointBounds23207 : List (Nat × Nat × Nat) := [(3045799936,101941941517861,101942322994990)]
theorem point_links_checked23207 : (cuts23207.take 1).map (fun c => (3045720065-1+2*2^9*c.k,101941601614348+c.lower,101941983091282+c.upper)) = pointBounds23207 := by
 decide +kernel
def cuts23208 : List PrefixCut := [⟨43,182328656,182328758⟩,
⟨128,550027677,550027987⟩]
theorem checked23208 : checkPrefixCuts (2^48) 3045851137 9 Manual.Count131072.C023208.packed 128 cuts23208 = true := by
 decide +kernel
def pointBounds23208 : List (Nat × Nat × Nat) := [(3045895168,101942338892331,101942720369681)]
theorem point_links_checked23208 : (cuts23208.take 1).map (fun c => (3045851137-1+2*2^9*c.k,101942156563675+c.lower,101942538040923+c.upper)) = pointBounds23208 := by
 decide +kernel
def cuts23209 : List PrefixCut := [⟨8,34560766,34560783⟩,
⟨101,439302865,439303109⟩,
⟨128,555086370,555086679⟩]
theorem checked23209 : checkPrefixCuts (2^48) 3045982209 9 Manual.Count131072.C023209.packed 128 cuts23209 = true := by
 decide +kernel
def pointBounds23209 : List (Nat × Nat × Nat) := [(3045990400,101942741152118,101943122629693),(3046085632,101943145894217,101943527372019)]
theorem point_links_checked23209 : (cuts23209.take 2).map (fun c => (3045982209-1+2*2^9*c.k,101942706591352+c.lower,101943088068910+c.upper)) = pointBounds23209 := by
 decide +kernel
def cuts23210 : List PrefixCut := [⟨66,284880242,284880406⟩,
⟨128,554230876,554231192⟩]
theorem checked23210 : checkPrefixCuts (2^48) 3046113281 9 Manual.Count131072.C023210.packed 128 cuts23210 = true := by
 decide +kernel
def pointBounds23210 : List (Nat × Nat × Nat) := [(3046180864,101943546557964,101943928035995)]
theorem point_links_checked23210 : (cuts23210.take 1).map (fun c => (3046113281-1+2*2^9*c.k,101943261677722+c.lower,101943643155589+c.upper)) = pointBounds23210 := by
 decide +kernel
def cuts23211 : List PrefixCut := [⟨31,134904227,134904303⟩,
⟨124,534341765,534342064⟩,
⟨128,551250364,551250672⟩]
theorem checked23211 : checkPrefixCuts (2^48) 3046244353 9 Manual.Count131072.C023211.packed 128 cuts23211 = true := by
 decide +kernel
def pointBounds23211 : List (Nat × Nat × Nat) := [(3046276096,101943950812825,101944332291084),(3046371328,101944350250363,101944731728845)]
theorem point_links_checked23211 : (cuts23211.take 2).map (fun c => (3046244353-1+2*2^9*c.k,101943815908598+c.lower,101944197386781+c.upper)) = pointBounds23211 := by
 decide +kernel
def cuts23212 : List PrefixCut := [⟨89,385842644,385842867⟩,
⟨128,555938687,555939009⟩]
theorem checked23212 : checkPrefixCuts (2^48) 3046375425 9 Manual.Count131072.C023212.packed 128 cuts23212 = true := by
 decide +kernel
def pointBounds23212 : List (Nat × Nat × Nat) := [(3046466560,101944753001606,101945134480320)]
theorem point_links_checked23212 : (cuts23212.take 1).map (fun c => (3046375425-1+2*2^9*c.k,101944367158962+c.lower,101944748637453+c.upper)) = pointBounds23212 := by
 decide +kernel
def cuts23213 : List PrefixCut := [⟨54,232827423,232827555⟩,
⟨128,552219178,552219491⟩]
theorem checked23213 : checkPrefixCuts (2^48) 3046506497 9 Manual.Count131072.C023213.packed 128 cuts23213 = true := by
 decide +kernel
def pointBounds23213 : List (Nat × Nat × Nat) := [(3046561792,101945155925072,101945537404017)]
theorem point_links_checked23213 : (cuts23213.take 1).map (fun c => (3046506497-1+2*2^9*c.k,101944923097649+c.lower,101945304576462+c.upper)) = pointBounds23213 := by
 decide +kernel
def cuts23214 : List PrefixCut := [⟨19,85551657,85551706⟩,
⟨112,486602245,486602515⟩,
⟨128,556352905,556353212⟩]
theorem checked23214 : checkPrefixCuts (2^48) 3046637569 9 Manual.Count131072.C023214.packed 128 cuts23214 = true := by
 decide +kernel
def pointBounds23214 : List (Nat × Nat × Nat) := [(3046657024,101945560868484,101945942347659),(3046752256,101945961919072,101946343398468)]
theorem point_links_checked23214 : (cuts23214.take 2).map (fun c => (3046637569-1+2*2^9*c.k,101945475316827+c.lower,101945856795953+c.upper)) = pointBounds23214 := by
 decide +kernel
def cuts23215 : List PrefixCut := [⟨77,333596969,333597157⟩,
⟨128,550785978,550786287⟩]
theorem checked23215 : checkPrefixCuts (2^48) 3046768641 9 Manual.Count131072.C023215.packed 128 cuts23215 = true := by
 decide +kernel
def pointBounds23215 : List (Nat × Nat × Nat) := [(3046847488,101946365266701,101946746746322)]
theorem point_links_checked23215 : (cuts23215.take 1).map (fun c => (3046768641-1+2*2^9*c.k,101946031669732+c.lower,101946413149165+c.upper)) = pointBounds23215 := by
 decide +kernel
def cuts23216 : List PrefixCut := [⟨42,182635466,182635568⟩,
⟨128,562678990,562679303⟩]
theorem checked23216 : checkPrefixCuts (2^48) 3046899713 9 Manual.Count131072.C023216.packed 128 cuts23216 = true := by
 decide +kernel
def pointBounds23216 : List (Nat × Nat × Nat) := [(3046942720,101946765091176,101947146571020)]
theorem point_links_checked23216 : (cuts23216.take 1).map (fun c => (3046899713-1+2*2^9*c.k,101946582455710+c.lower,101946963935452+c.upper)) = pointBounds23216 := by
 decide +kernel
def cuts23217 : List PrefixCut := [⟨7,32424210,32424229⟩,
⟨100,432962724,432962972⟩,
⟨128,555819133,555819448⟩]
theorem checked23217 : checkPrefixCuts (2^48) 3047030785 9 Manual.Count131072.C023217.packed 128 cuts23217 = true := by
 decide +kernel
def pointBounds23217 : List (Nat × Nat × Nat) := [(3047037952,101947177558910,101947559038984),(3047133184,101947578097424,101947959577727)]
theorem point_links_checked23217 : (cuts23217.take 2).map (fun c => (3047030785-1+2*2^9*c.k,101947145134700+c.lower,101947526614755+c.upper)) = pointBounds23217 := by
 decide +kernel
def cuts23218 : List PrefixCut := [⟨65,280533137,280533294⟩,
⟨128,553947801,553948108⟩]
theorem checked23218 : checkPrefixCuts (2^48) 3047161857 9 Manual.Count131072.C023218.packed 128 cuts23218 = true := by
 decide +kernel
def pointBounds23218 : List (Nat × Nat × Nat) := [(3047228416,101947981486970,101948362967497)]
theorem point_links_checked23218 : (cuts23218.take 1).map (fun c => (3047161857-1+2*2^9*c.k,101947700953833+c.lower,101948082434203+c.upper)) = pointBounds23218 := by
 decide +kernel
def cuts23219 : List PrefixCut := [⟨30,134395970,134396048⟩,
⟨123,538222134,538222438⟩,
⟨128,557341675,557341991⟩]
theorem checked23219 : checkPrefixCuts (2^48) 3047292929 9 Manual.Count131072.C023219.packed 128 cuts23219 = true := by
 decide +kernel
def pointBounds23219 : List (Nat × Nat × Nat) := [(3047323648,101948389297604,101948770778359),(3047418880,101948793123768,101949174604749)]
theorem point_links_checked23219 : (cuts23219.take 2).map (fun c => (3047292929-1+2*2^9*c.k,101948254901634+c.lower,101948636382311+c.upper)) = pointBounds23219 := by
 decide +kernel
def cuts23220 : List PrefixCut := [⟨88,375365280,375365494⟩,
⟨128,547342422,547342735⟩]
theorem checked23220 : checkPrefixCuts (2^48) 3047424001 9 Manual.Count131072.C023220.packed 128 cuts23220 = true := by
 decide +kernel
def pointBounds23220 : List (Nat × Nat × Nat) := [(3047514112,101949187608589,101949569089796)]
theorem point_links_checked23220 : (cuts23220.take 1).map (fun c => (3047424001-1+2*2^9*c.k,101948812243309+c.lower,101949193724302+c.upper)) = pointBounds23220 := by
 decide +kernel
def cuts23221 : List PrefixCut := [⟨54,233393850,233393982⟩,
⟨128,556092938,556093257⟩]
theorem checked23221 : checkPrefixCuts (2^48) 3047555073 9 Manual.Count131072.C023221.packed 128 cuts23221 = true := by
 decide +kernel
def pointBounds23221 : List (Nat × Nat × Nat) := [(3047610368,101949592979581,101949974461019)]
theorem point_links_checked23221 : (cuts23221.take 1).map (fun c => (3047555073-1+2*2^9*c.k,101949359585731+c.lower,101949741067037+c.upper)) = pointBounds23221 := by
 decide +kernel
def cuts23222 : List PrefixCut := [⟨20,84044514,84044563⟩,
⟨114,485788077,485788357⟩,
⟨128,546371753,546372068⟩]
theorem checked23222 : checkPrefixCuts (2^48) 3047686145 9 Manual.Count131072.C023222.packed 128 cuts23222 = true := by
 decide +kernel
def pointBounds23222 : List (Nat × Nat × Nat) := [(3047706624,101949999723183,101950381204857),(3047802880,101950401466746,101950782948651)]
theorem point_links_checked23222 : (cuts23222.take 2).map (fun c => (3047686145-1+2*2^9*c.k,101949915678669+c.lower,101950297160294+c.upper)) = pointBounds23222 := by
 decide +kernel
def cuts23223 : List PrefixCut := [⟨80,346411245,346411443⟩,
⟨128,554013419,554013733⟩]
theorem checked23223 : checkPrefixCuts (2^48) 3047817217 9 Manual.Count131072.C023223.packed 128 cuts23223 = true := by
 decide +kernel
def pointBounds23223 : List (Nat × Nat × Nat) := [(3047899136,101950808461667,101951189943805)]
theorem point_links_checked23223 : (cuts23223.take 1).map (fun c => (3047817217-1+2*2^9*c.k,101950462050422+c.lower,101950843532362+c.upper)) = pointBounds23223 := by
 decide +kernel
def cuts23224 : List PrefixCut := [⟨46,204828450,204828570⟩,
⟨128,563963123,563963441⟩]
theorem checked23224 : checkPrefixCuts (2^48) 3047948289 9 Manual.Count131072.C023224.packed 128 cuts23224 = true := by
 decide +kernel
def pointBounds23224 : List (Nat × Nat × Nat) := [(3047995392,101951220892291,101951602374665)]
theorem point_links_checked23224 : (cuts23224.take 1).map (fun c => (3047948289-1+2*2^9*c.k,101951016063841+c.lower,101951397546095+c.upper)) = pointBounds23224 := by
 decide +kernel
def cuts23225 : List PrefixCut := [⟨12,51528408,51528438⟩,
⟨106,455899210,455899462⟩,
⟨128,550549105,550549413⟩]
theorem checked23225 : checkPrefixCuts (2^48) 3048079361 9 Manual.Count131072.C023225.packed 128 cuts23225 = true := by
 decide +kernel
def pointBounds23225 : List (Nat × Nat × Nat) := [(3048091648,101951631555372,101952013037974),(3048187904,101952035926174,101952417408998)]
theorem point_links_checked23225 : (cuts23225.take 2).map (fun c => (3048079361-1+2*2^9*c.k,101951580026964+c.lower,101951961509536+c.upper)) = pointBounds23225 := by
 decide +kernel
def cuts23226 : List PrefixCut := [⟨72,306199220,306199390⟩,
⟨128,543877041,543877348⟩]
theorem checked23226 : checkPrefixCuts (2^48) 3048210433 9 Manual.Count131072.C023226.packed 128 cuts23226 = true := by
 decide +kernel
def pointBounds23226 : List (Nat × Nat × Nat) := [(3048284160,101952436775289,101952818258339)]
theorem point_links_checked23226 : (cuts23226.take 1).map (fun c => (3048210433-1+2*2^9*c.k,101952130576069+c.lower,101952512058949+c.upper)) = pointBounds23226 := by
 decide +kernel
def cuts23227 : List PrefixCut := [⟨38,163897232,163897324⟩,
⟨128,553087121,553087428⟩]
theorem checked23227 : checkPrefixCuts (2^48) 3048341505 9 Manual.Count131072.C023227.packed 128 cuts23227 = true := by
 decide +kernel
def pointBounds23227 : List (Nat × Nat × Nat) := [(3048380416,101952838350342,101953219833621)]
theorem point_links_checked23227 : (cuts23227.take 1).map (fun c => (3048341505-1+2*2^9*c.k,101952674453110+c.lower,101953055936297+c.upper)) = pointBounds23227 := by
 decide +kernel
def cuts23228 : List PrefixCut := [⟨4,18651272,18651283⟩,
⟨98,423802007,423802242⟩,
⟨128,552417133,552417438⟩]
theorem checked23228 : checkPrefixCuts (2^48) 3048472577 9 Manual.Count131072.C023228.packed 128 cuts23228 = true := by
 decide +kernel
def pointBounds23228 : List (Nat × Nat × Nat) := [(3048476672,101953246191503,101953627675008),(3048572928,101953651342238,101954032825967)]
theorem point_links_checked23228 : (cuts23228.take 2).map (fun c => (3048472577-1+2*2^9*c.k,101953227540231+c.lower,101953609023725+c.upper)) = pointBounds23228 := by
 decide +kernel
def cuts23229 : List PrefixCut := [⟨64,278923261,278923417⟩,
⟨128,556178670,556178979⟩]
theorem checked23229 : checkPrefixCuts (2^48) 3048603649 9 Manual.Count131072.C023229.packed 128 cuts23229 = true := by
 decide +kernel
def pointBounds23229 : List (Nat × Nat × Nat) := [(3048669184,101954058880625,101954440364580)]
theorem point_links_checked23229 : (cuts23229.take 1).map (fun c => (3048603649-1+2*2^9*c.k,101953779957364+c.lower,101954161441163+c.upper)) = pointBounds23229 := by
 decide +kernel
def cuts23230 : List PrefixCut := [⟨30,127777369,127777443⟩,
⟨124,535474714,535475015⟩,
⟨128,551353967,551354279⟩]
theorem checked23230 : checkPrefixCuts (2^48) 3048734721 9 Manual.Count131072.C023230.packed 128 cuts23230 = true := by
 decide +kernel
def pointBounds23230 : List (Nat × Nat × Nat) := [(3048765440,101954463913403,101954845397585),(3048861696,101954871610748,101955253095157)]
theorem point_links_checked23230 : (cuts23230.take 2).map (fun c => (3048734721-1+2*2^9*c.k,101954336136034+c.lower,101954717620142+c.upper)) = pointBounds23230 := by
 decide +kernel
def cuts23231 : List PrefixCut := [⟨90,388943293,388943513⟩,
⟨128,557515599,557515915⟩]
theorem checked23231 : checkPrefixCuts (2^48) 3048865793 9 Manual.Count131072.C023231.packed 128 cuts23231 = true := by
 decide +kernel
def pointBounds23231 : List (Nat × Nat × Nat) := [(3048957952,101955276433294,101955657917934)]
theorem point_links_checked23231 : (cuts23231.take 1).map (fun c => (3048865793-1+2*2^9*c.k,101954887490001+c.lower,101955268974421+c.upper)) = pointBounds23231 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000100
