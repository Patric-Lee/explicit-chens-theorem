import PlattAssemblyKernel
import PlattCertificates.Count131072.C016176
import PlattCertificates.Count131072.C016177
import PlattCertificates.Count131072.C016178
import PlattCertificates.Count131072.C016179
import PlattCertificates.Count131072.C016180
import PlattCertificates.Count131072.C016181
import PlattCertificates.Count131072.C016182
import PlattCertificates.Count131072.C016183
import PlattCertificates.Count131072.C016184
import PlattCertificates.Count131072.C016185
import PlattCertificates.Count131072.C016186
import PlattCertificates.Count131072.C016187
import PlattCertificates.Count131072.C016188
import PlattCertificates.Count131072.C016189
import PlattCertificates.Count131072.C016190
import PlattCertificates.Count131072.C016191
import PlattCertificates.Count131072.C016192
import PlattCertificates.Count131072.C016193
import PlattCertificates.Count131072.C016194
import PlattCertificates.Count131072.C016195
import PlattCertificates.Count131072.C016196
import PlattCertificates.Count131072.C016197
import PlattCertificates.Count131072.C016198
import PlattCertificates.Count131072.C016199
import PlattCertificates.Count131072.C016200
import PlattCertificates.Count131072.C016201
import PlattCertificates.Count131072.C016202
import PlattCertificates.Count131072.C016203
import PlattCertificates.Count131072.C016204
import PlattCertificates.Count131072.C016205
import PlattCertificates.Count131072.C016206
import PlattCertificates.Count131072.C016207
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000193
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16176 : List PrefixCut := [⟨60,382555496,382555741⟩,
⟨125,791600581,791601081⟩,
⟨128,810681087,810681599⟩]
theorem checked16176 : checkPrefixCuts (2^48) 2124152833 9 Manual.Count131072.C016176.packed 128 cuts16176 = true := by
 decide +kernel
def pointBounds16176 : List (Nat × Nat × Nat) := [(2124214272,97258301773308,97258680453370),(2124280832,97258710818393,97259089498710)]
theorem point_links_checked16176 : (cuts16176.take 2).map (fun c => (2124152833-1+2*2^9*c.k,97257919217812+c.lower,97258297897629+c.upper)) = pointBounds16176 := by
 decide +kernel
def cuts16177 : List PrefixCut := [⟨62,400949433,400949687⟩,
⟨127,813811273,813811787⟩,
⟨128,819376075,819376592⟩]
theorem checked16177 : checkPrefixCuts (2^48) 2124283905 9 Manual.Count131072.C016177.packed 128 cuts16177 = true := by
 decide +kernel
def pointBounds16177 : List (Nat × Nat × Nat) := [(2124347392,97259130848332,97259509528915),(2124413952,97259543710172,97259922391015)]
theorem point_links_checked16177 : (cuts16177.take 2).map (fun c => (2124283905-1+2*2^9*c.k,97258729898899+c.lower,97259108579228+c.upper)) = pointBounds16177 := by
 decide +kernel
def cuts16178 : List PrefixCut := [⟨64,405031665,405031922⟩,
⟨128,809520915,809521432⟩]
theorem checked16178 : checkPrefixCuts (2^48) 2124414977 9 Manual.Count131072.C016178.packed 128 cuts16178 = true := by
 decide +kernel
def pointBounds16178 : List (Nat × Nat × Nat) := [(2124480512,97259954306639,97260332987742)]
theorem point_links_checked16178 : (cuts16178.take 1).map (fun c => (2124414977-1+2*2^9*c.k,97259549274974+c.lower,97259927955820+c.upper)) = pointBounds16178 := by
 decide +kernel
def cuts16179 : List PrefixCut := [⟨1,5829430,5829434⟩,
⟨66,414280458,414280726⟩,
⟨128,810663231,810663756⟩]
theorem checked16179 : checkPrefixCuts (2^48) 2124546049 9 Manual.Count131072.C016179.packed 128 cuts16179 = true := by
 decide +kernel
def pointBounds16179 : List (Nat × Nat × Nat) := [(2124547072,97260364625319,97260743306686),(2124613632,97260773076347,97261151757978)]
theorem point_links_checked16179 : (cuts16179.take 2).map (fun c => (2124546049-1+2*2^9*c.k,97260358795889+c.lower,97260737477252+c.upper)) = pointBounds16179 := by
 decide +kernel
def cuts16180 : List PrefixCut := [⟨3,17089766,17089777⟩,
⟨68,428297231,428297504⟩,
⟨128,806506577,806507089⟩]
theorem checked16180 : checkPrefixCuts (2^48) 2124677121 9 Manual.Count131072.C016180.packed 128 cuts16180 = true := by
 decide +kernel
def pointBounds16180 : List (Nat × Nat × Nat) := [(2124680192,97261186548886,97261565230785),(2124746752,97261597756351,97261976438512)]
theorem point_links_checked16180 : (cuts16180.take 2).map (fun c => (2124677121-1+2*2^9*c.k,97261169459120+c.lower,97261548141008+c.upper)) = pointBounds16180 := by
 decide +kernel
def cuts16181 : List PrefixCut := [⟨5,27156466,27156483⟩,
⟨70,431052368,431052638⟩,
⟨128,799435921,799436427⟩]
theorem checked16181 : checkPrefixCuts (2^48) 2124808193 9 Manual.Count131072.C016181.packed 128 cuts16181 = true := by
 decide +kernel
def pointBounds16181 : List (Nat × Nat × Nat) := [(2124813312,97262003122163,97262381804580),(2124879872,97262407018065,97262785700735)]
theorem point_links_checked16181 : (cuts16181.take 2).map (fun c => (2124808193-1+2*2^9*c.k,97261975965697+c.lower,97262354648097+c.upper)) = pointBounds16181 := by
 decide +kernel
def cuts16182 : List PrefixCut := [⟨7,44904731,44904759⟩,
⟨72,455133465,455133759⟩,
⟨128,807864201,807864720⟩]
theorem checked16182 : checkPrefixCuts (2^48) 2124939265 9 Manual.Count131072.C016182.packed 128 cuts16182 = true := by
 decide +kernel
def pointBounds16182 : List (Nat × Nat × Nat) := [(2124946432,97262820306349,97263198989283),(2125012992,97263230535083,97263609218283)]
theorem point_links_checked16182 : (cuts16182.take 2).map (fun c => (2124939265-1+2*2^9*c.k,97262775401618+c.lower,97263154084524+c.upper)) = pointBounds16182 := by
 decide +kernel
def cuts16183 : List PrefixCut := [⟨9,58412258,58412296⟩,
⟨74,465303986,465304284⟩,
⟨128,799602604,799603123⟩]
theorem checked16183 : checkPrefixCuts (2^48) 2125070337 9 Manual.Count131072.C016183.packed 128 cuts16183 = true := by
 decide +kernel
def pointBounds16183 : List (Nat × Nat × Nat) := [(2125079552,97263641678077,97264020361540),(2125146112,97264048569805,97264427253528)]
theorem point_links_checked16183 : (cuts16183.take 2).map (fun c => (2125070337-1+2*2^9*c.k,97263583265819+c.lower,97263961949244+c.upper)) = pointBounds16183 := by
 decide +kernel
def cuts16184 : List PrefixCut := [⟨11,68606957,68607001⟩,
⟨76,488982381,488982686⟩,
⟨128,810810934,810811448⟩]
theorem checked16184 : checkPrefixCuts (2^48) 2125201409 9 Manual.Count131072.C016184.packed 128 cuts16184 = true := by
 decide +kernel
def pointBounds16184 : List (Nat × Nat × Nat) := [(2125212672,97264451475380,97264830159368),(2125279232,97264871850804,97265250535053)]
theorem point_links_checked16184 : (cuts16184.take 2).map (fun c => (2125201409-1+2*2^9*c.k,97264382868423+c.lower,97264761552367+c.upper)) = pointBounds16184 := by
 decide +kernel
def cuts16185 : List PrefixCut := [⟨13,80124768,80124819⟩,
⟨78,490673651,490673967⟩,
⟨128,814998358,814998880⟩]
theorem checked16185 : checkPrefixCuts (2^48) 2125332481 9 Manual.Count131072.C016185.packed 128 cuts16185 = true := by
 decide +kernel
def pointBounds16185 : List (Nat × Nat × Nat) := [(2125345792,97265273804125,97265652488634),(2125412352,97265684353008,97266063037782)]
theorem point_links_checked16185 : (cuts16185.take 2).map (fun c => (2125332481-1+2*2^9*c.k,97265193679357+c.lower,97265572363815+c.upper)) = pointBounds16185 := by
 decide +kernel
def cuts16186 : List PrefixCut := [⟨15,95084317,95084375⟩,
⟨80,509580394,509580719⟩,
⟨128,812564758,812565279⟩]
theorem checked16186 : checkPrefixCuts (2^48) 2125463553 9 Manual.Count131072.C016186.packed 128 cuts16186 = true := by
 decide +kernel
def pointBounds16186 : List (Nat × Nat × Nat) := [(2125478912,97266103762032,97266482447070),(2125545472,97266518258109,97266896943414)]
theorem point_links_checked16186 : (cuts16186.take 2).map (fun c => (2125463553-1+2*2^9*c.k,97266008677715+c.lower,97266387362695+c.upper)) = pointBounds16186 := by
 decide +kernel
def cuts16187 : List PrefixCut := [⟨17,108320523,108320592⟩,
⟨82,522128515,522128851⟩,
⟨128,804834548,804835065⟩]
theorem checked16187 : checkPrefixCuts (2^48) 2125594625 9 Manual.Count131072.C016187.packed 128 cuts16187 = true := by
 decide +kernel
def pointBounds16187 : List (Nat × Nat × Nat) := [(2125612032,97266929562996,97267308248566),(2125678592,97267343370988,97267722056825)]
theorem point_links_checked16187 : (cuts16187.take 2).map (fun c => (2125594625-1+2*2^9*c.k,97266821242473+c.lower,97267199927974+c.upper)) = pointBounds16187 := by
 decide +kernel
def cuts16188 : List PrefixCut := [⟨19,119966128,119966207⟩,
⟨84,521831206,521831541⟩,
⟨128,799223406,799223917⟩]
theorem checked16188 : checkPrefixCuts (2^48) 2125725697 9 Manual.Count131072.C016188.packed 128 cuts16188 = true := by
 decide +kernel
def pointBounds16188 : List (Nat × Nat × Nat) := [(2125745152,97267746043149,97268124729246),(2125811712,97268147908227,97268526594580)]
theorem point_links_checked16188 : (cuts16188.take 2).map (fun c => (2125725697-1+2*2^9*c.k,97267626077021+c.lower,97268004763039+c.upper)) = pointBounds16188 := by
 decide +kernel
def cuts16189 : List PrefixCut := [⟨21,130021427,130021510⟩,
⟨86,542586062,542586406⟩,
⟨128,811619961,811620479⟩]
theorem checked16189 : checkPrefixCuts (2^48) 2125856769 9 Manual.Count131072.C016189.packed 128 cuts16189 = true := by
 decide +kernel
def pointBounds16189 : List (Nat × Nat × Nat) := [(2125878272,97268555321854,97268934008466),(2125944832,97268967886489,97269346573362)]
theorem point_links_checked16189 : (cuts16189.take 2).map (fun c => (2125856769-1+2*2^9*c.k,97268425300427+c.lower,97268803986956+c.upper)) = pointBounds16189 := by
 decide +kernel
def cuts16190 : List PrefixCut := [⟨23,145636145,145636241⟩,
⟨88,556586117,556586472⟩,
⟨128,812099428,812099944⟩]
theorem checked16190 : checkPrefixCuts (2^48) 2125987841 9 Manual.Count131072.C016190.packed 128 cuts16190 = true := by
 decide +kernel
def pointBounds16190 : List (Nat × Nat × Nat) := [(2126011392,97269382556533,97269761243676),(2126077952,97269793506505,97270172193907)]
theorem point_links_checked16190 : (cuts16190.take 2).map (fun c => (2125987841-1+2*2^9*c.k,97269236920388+c.lower,97269615607435+c.upper)) = pointBounds16190 := by
 decide +kernel
def cuts16191 : List PrefixCut := [⟨25,152114129,152114228⟩,
⟨90,557875377,557875740⟩,
⟨128,800134640,800135160⟩]
theorem checked16191 : checkPrefixCuts (2^48) 2126118913 9 Manual.Count131072.C016191.packed 128 cuts16191 = true := by
 decide +kernel
def pointBounds16191 : List (Nat × Nat × Nat) := [(2126144512,97270201133945,97270579821607),(2126211072,97270606895193,97270985583119)]
theorem point_links_checked16191 : (cuts16191.take 2).map (fun c => (2126118913-1+2*2^9*c.k,97270049019816+c.lower,97270427707379+c.upper)) = pointBounds16191 := by
 decide +kernel
def cuts16192 : List PrefixCut := [⟨27,166004563,166004668⟩,
⟨92,574520355,574520719⟩,
⟨128,800614922,800615430⟩]
theorem checked16192 : checkPrefixCuts (2^48) 2126249985 9 Manual.Count131072.C016192.packed 128 cuts16192 = true := by
 decide +kernel
def pointBounds16192 : List (Nat × Nat × Nat) := [(2126277632,97271015159019,97271393847207),(2126344192,97271423674811,97271802363258)]
theorem point_links_checked16192 : (cuts16192.take 2).map (fun c => (2126249985-1+2*2^9*c.k,97270849154456+c.lower,97271227842539+c.upper)) = pointBounds16192 := by
 decide +kernel
def cuts16193 : List PrefixCut := [⟨29,182276006,182276122⟩,
⟨94,591295654,591296026⟩,
⟨128,802286530,802287038⟩]
theorem checked16193 : checkPrefixCuts (2^48) 2126381057 9 Manual.Count131072.C016193.packed 128 cuts16193 = true := by
 decide +kernel
def pointBounds16193 : List (Nat × Nat × Nat) := [(2126410752,97271832045384,97272210734091),(2126477312,97272241065032,97272619753995)]
theorem point_links_checked16193 : (cuts16193.take 2).map (fun c => (2126381057-1+2*2^9*c.k,97271649769378+c.lower,97272028457969+c.upper)) = pointBounds16193 := by
 decide +kernel
def cuts16194 : List PrefixCut := [⟨31,198545400,198545525⟩,
⟨96,617731173,617731565⟩,
⟨128,813487819,813488340⟩]
theorem checked16194 : checkPrefixCuts (2^48) 2126512129 9 Manual.Count131072.C016194.packed 128 cuts16194 = true := by
 decide +kernel
def pointBounds16194 : List (Nat × Nat × Nat) := [(2126543872,97272650601308,97273029290532),(2126610432,97273069787081,97273448476572)]
theorem point_links_checked16194 : (cuts16194.take 2).map (fun c => (2126512129-1+2*2^9*c.k,97272452055908+c.lower,97272830745007+c.upper)) = pointBounds16194 := by
 decide +kernel
def cuts16195 : List PrefixCut := [⟨33,207136141,207136276⟩,
⟨98,621795704,621796104⟩,
⟨128,809202198,809202718⟩]
theorem checked16195 : checkPrefixCuts (2^48) 2126643201 9 Manual.Count131072.C016195.packed 128 cuts16195 = true := by
 decide +kernel
def pointBounds16195 : List (Nat × Nat × Nat) := [(2126676992,97273472679868,97273851369623),(2126743552,97273887339431,97274266029451)]
theorem point_links_checked16195 : (cuts16195.take 2).map (fun c => (2126643201-1+2*2^9*c.k,97273265543727+c.lower,97273644233347+c.upper)) = pointBounds16195 := by
 decide +kernel
def cuts16196 : List PrefixCut := [⟨35,214402389,214402531⟩,
⟨100,622154130,622154536⟩,
⟨128,799358734,799359253⟩]
theorem checked16196 : checkPrefixCuts (2^48) 2126774273 9 Manual.Count131072.C016196.packed 128 cuts16196 = true := by
 decide +kernel
def pointBounds16196 : List (Nat × Nat × Nat) := [(2126810112,97274289148314,97274667838596),(2126876672,97274696900055,97275075590601)]
theorem point_links_checked16196 : (cuts16196.take 2).map (fun c => (2126774273-1+2*2^9*c.k,97274074745925+c.lower,97274453436065+c.upper)) = pointBounds16196 := by
 decide +kernel
def cuts16197 : List PrefixCut := [⟨37,231063777,231063927⟩,
⟨102,641833751,641834163⟩,
⟨128,807779067,807779585⟩]
theorem checked16197 : checkPrefixCuts (2^48) 2126905345 9 Manual.Count131072.C016197.packed 128 cuts16197 = true := by
 decide +kernel
def pointBounds16197 : List (Nat × Nat × Nat) := [(2126943232,97275105168436,97275483859245),(2127009792,97275515938410,97275894629481)]
theorem point_links_checked16197 : (cuts16197.take 2).map (fun c => (2126905345-1+2*2^9*c.k,97274874104659+c.lower,97275252795318+c.upper)) = pointBounds16197 := by
 decide +kernel
def cuts16198 : List PrefixCut := [⟨39,244282516,244282669⟩,
⟨104,649733687,649734099⟩,
⟨128,797275561,797276068⟩]
theorem checked16198 : checkPrefixCuts (2^48) 2127036417 9 Manual.Count131072.C016198.packed 128 cuts16198 = true := by
 decide +kernel
def pointBounds16198 : List (Nat × Nat × Nat) := [(2127076352,97275926166242,97276304857572),(2127142912,97276331617413,97276710309002)]
theorem point_links_checked16198 : (cuts16198.take 2).map (fun c => (2127036417-1+2*2^9*c.k,97275681883726+c.lower,97276060574903+c.upper)) = pointBounds16198 := by
 decide +kernel
def cuts16199 : List PrefixCut := [⟨41,261072280,261072449⟩,
⟨106,671129269,671129702⟩,
⟨128,808209021,808209542⟩]
theorem checked16199 : checkPrefixCuts (2^48) 2127167489 9 Manual.Count131072.C016199.packed 128 cuts16199 = true := by
 decide +kernel
def pointBounds16199 : List (Nat × Nat × Nat) := [(2127209472,97276740231567,97277118923420),(2127276032,97277150288556,97277528980673)]
theorem point_links_checked16199 : (cuts16199.take 2).map (fun c => (2127167489-1+2*2^9*c.k,97276479159287+c.lower,97276857850971+c.upper)) = pointBounds16199 := by
 decide +kernel
def cuts16200 : List PrefixCut := [⟨43,278256937,278257113⟩,
⟨108,680085008,680085440⟩,
⟨128,812657761,812658274⟩]
theorem checked16200 : checkPrefixCuts (2^48) 2127298561 9 Manual.Count131072.C016200.packed 128 cuts16200 = true := by
 decide +kernel
def pointBounds16200 : List (Nat × Nat × Nat) := [(2127342592,97277565625245,97277944317626),(2127409152,97277967453316,97278346145953)]
theorem point_links_checked16200 : (cuts16200.take 2).map (fun c => (2127298561-1+2*2^9*c.k,97277287368308+c.lower,97277666060513+c.upper)) = pointBounds16200 := by
 decide +kernel
def cuts16201 : List PrefixCut := [⟨45,286574919,286575105⟩,
⟨110,696183639,696184087⟩,
⟨128,810887658,810888178⟩]
theorem checked16201 : checkPrefixCuts (2^48) 2127429633 9 Manual.Count131072.C016201.packed 128 cuts16201 = true := by
 decide +kernel
def pointBounds16201 : List (Nat × Nat × Nat) := [(2127475712,97278386600988,97278765293892),(2127542272,97278796209708,97279174902874)]
theorem point_links_checked16201 : (cuts16201.take 2).map (fun c => (2127429633-1+2*2^9*c.k,97278100026069+c.lower,97278478718787+c.upper)) = pointBounds16201 := by
 decide +kernel
def cuts16202 : List PrefixCut := [⟨47,289070756,289070943⟩,
⟨112,699579853,699580304⟩,
⟨128,801973621,801974138⟩]
theorem checked16202 : checkPrefixCuts (2^48) 2127560705 9 Manual.Count131072.C016202.packed 128 cuts16202 = true := by
 decide +kernel
def pointBounds16202 : List (Nat × Nat × Nat) := [(2127608832,97279199984483,97279578677908),(2127675392,97279610493580,97279989187269)]
theorem point_links_checked16202 : (cuts16202.take 2).map (fun c => (2127560705-1+2*2^9*c.k,97278910913727+c.lower,97279289606965+c.upper)) = pointBounds16202 := by
 decide +kernel
def cuts16203 : List PrefixCut := [⟨49,312864955,312865157⟩,
⟨114,720967380,720967842⟩,
⟨128,809729595,809730114⟩]
theorem checked16203 : checkPrefixCuts (2^48) 2127691777 9 Manual.Count131072.C016203.packed 128 cuts16203 = true := by
 decide +kernel
def pointBounds16203 : List (Nat × Nat × Nat) := [(2127741952,97280025752303,97280404446260),(2127808512,97280433854728,97280812548945)]
theorem point_links_checked16203 : (cuts16203.take 2).map (fun c => (2127691777-1+2*2^9*c.k,97279712887348+c.lower,97280091581103+c.upper)) = pointBounds16203 := by
 decide +kernel
def cuts16204 : List PrefixCut := [⟨51,319195078,319195281⟩,
⟨116,729785085,729785548⟩,
⟨128,801346018,801346528⟩]
theorem checked16204 : checkPrefixCuts (2^48) 2127822849 9 Manual.Count131072.C016204.packed 128 cuts16204 = true := by
 decide +kernel
def pointBounds16204 : List (Nat × Nat × Nat) := [(2127875072,97280841812021,97281220506498),(2127941632,97281252402028,97281631096765)]
theorem point_links_checked16204 : (cuts16204.take 2).map (fun c => (2127822849-1+2*2^9*c.k,97280522616943+c.lower,97280901311217+c.upper)) = pointBounds16204 := by
 decide +kernel
def cuts16205 : List PrefixCut := [⟨53,340868094,340868312⟩,
⟨118,760294630,760295112⟩,
⟨128,824708691,824709215⟩]
theorem checked16205 : checkPrefixCuts (2^48) 2127953921 9 Manual.Count131072.C016205.packed 128 cuts16205 = true := by
 decide +kernel
def pointBounds16205 : List (Nat × Nat × Nat) := [(2128008192,97281664831055,97282043526057),(2128074752,97282084257591,97282462952857)]
theorem point_links_checked16205 : (cuts16205.take 2).map (fun c => (2127953921-1+2*2^9*c.k,97281323962961+c.lower,97281702657745+c.upper)) = pointBounds16205 := by
 decide +kernel
def cuts16206 : List PrefixCut := [⟨55,347989147,347989368⟩,
⟨120,759982723,759983214⟩,
⟨128,811695939,811696464⟩]
theorem checked16206 : checkPrefixCuts (2^48) 2128084993 9 Manual.Count131072.C016206.packed 128 cuts16206 = true := by
 decide +kernel
def pointBounds16206 : List (Nat × Nat × Nat) := [(2128141312,97282496660799,97282875356328),(2128207872,97282908654375,97283287350174)]
theorem point_links_checked16206 : (cuts16206.take 2).map (fun c => (2128084993-1+2*2^9*c.k,97282148671652+c.lower,97282527366960+c.upper)) = pointBounds16206 := by
 decide +kernel
def cuts16207 : List PrefixCut := [⟨57,360399712,360399942⟩,
⟨122,765754849,765755340⟩,
⟨128,802123779,802124294⟩]
theorem checked16207 : checkPrefixCuts (2^48) 2128216065 9 Manual.Count131072.C016207.packed 128 cuts16207 = true := by
 decide +kernel
def pointBounds16207 : List (Nat × Nat × Nat) := [(2128274432,97283320767303,97283699463366),(2128340992,97283726122440,97284104818764)]
theorem point_links_checked16207 : (cuts16207.take 2).map (fun c => (2128216065-1+2*2^9*c.k,97282960367591+c.lower,97283339063424+c.upper)) = pointBounds16207 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000193
