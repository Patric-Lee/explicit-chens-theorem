import PlattAssemblyKernel
import PlattCertificates.Count131072.C014288
import PlattCertificates.Count131072.C014289
import PlattCertificates.Count131072.C014290
import PlattCertificates.Count131072.C014291
import PlattCertificates.Count131072.C014292
import PlattCertificates.Count131072.C014293
import PlattCertificates.Count131072.C014294
import PlattCertificates.Count131072.C014295
import PlattCertificates.Count131072.C014296
import PlattCertificates.Count131072.C014297
import PlattCertificates.Count131072.C014298
import PlattCertificates.Count131072.C014299
import PlattCertificates.Count131072.C014300
import PlattCertificates.Count131072.C014301
import PlattCertificates.Count131072.C014302
import PlattCertificates.Count131072.C014303
import PlattCertificates.Count131072.C014304
import PlattCertificates.Count131072.C014305
import PlattCertificates.Count131072.C014306
import PlattCertificates.Count131072.C014307
import PlattCertificates.Count131072.C014308
import PlattCertificates.Count131072.C014309
import PlattCertificates.Count131072.C014310
import PlattCertificates.Count131072.C014311
import PlattCertificates.Count131072.C014312
import PlattCertificates.Count131072.C014313
import PlattCertificates.Count131072.C014314
import PlattCertificates.Count131072.C014315
import PlattCertificates.Count131072.C014316
import PlattCertificates.Count131072.C014317
import PlattCertificates.Count131072.C014318
import PlattCertificates.Count131072.C014319
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000134
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14288 : List PrefixCut := [⟨40,284968086,284968285⟩,
⟨98,711958866,711959355⟩,
⟨128,928523641,928524277⟩]
theorem checked14288 : checkPrefixCuts (2^48) 1876688897 9 Manual.Count131072.C014288.packed 128 cuts14288 = true := by
 decide +kernel
def pointBounds14288 : List (Nat × Nat × Nat) := [(1876729856,95630080640729,95630458243629),(1876789248,95630507631509,95630885234699)]
theorem point_links_checked14288 : (cuts14288.take 2).map (fun c => (1876688897-1+2*2^9*c.k,95629795672643+c.lower,95630173275344+c.upper)) = pointBounds14288 := by
 decide +kernel
def cuts14289 : List PrefixCut := [⟨28,202313877,202314015⟩,
⟨86,615030493,615030917⟩,
⟨128,915261687,915262314⟩]
theorem checked14289 : checkPrefixCuts (2^48) 1876819969 9 Manual.Count131072.C014289.packed 128 cuts14289 = true := by
 decide +kernel
def pointBounds14289 : List (Nat × Nat × Nat) := [(1876848640,95630926510161,95631304113636),(1876908032,95631339226777,95631716830538)]
theorem point_links_checked14289 : (cuts14289.take 2).map (fun c => (1876819969-1+2*2^9*c.k,95630724196284+c.lower,95631101799621+c.upper)) = pointBounds14289 := by
 decide +kernel
def cuts14290 : List PrefixCut := [⟨16,118021076,118021156⟩,
⟨74,528312079,528312443⟩,
⟨128,915497465,915498096⟩]
theorem checked14290 : checkPrefixCuts (2^48) 1876951041 9 Manual.Count131072.C014290.packed 128 cuts14290 = true := by
 decide +kernel
def pointBounds14290 : List (Nat × Nat × Nat) := [(1876967424,95631757479047,95632135083091),(1877026816,95632167770050,95632545374378)]
theorem point_links_checked14290 : (cuts14290.take 2).map (fun c => (1876951041-1+2*2^9*c.k,95631639457971+c.lower,95632017061935+c.upper)) = pointBounds14290 := by
 decide +kernel
def cuts14291 : List PrefixCut := [⟨4,31040325,31040345⟩,
⟨62,451652114,451652417⟩,
⟨120,867602276,867602859⟩,
⟨128,923831002,923831622⟩]
theorem checked14291 : checkPrefixCuts (2^48) 1877082113 9 Manual.Count131072.C014291.packed 128 cuts14291 = true := by
 decide +kernel
def pointBounds14291 : List (Nat × Nat × Nat) := [(1877086208,95632585995761,95632963600376),(1877145600,95633006607550,95633384212448),(1877204992,95633422557712,95633800162890)]
theorem point_links_checked14291 : (cuts14291.take 3).map (fun c => (1877082113-1+2*2^9*c.k,95632554955436+c.lower,95632932560031+c.upper)) = pointBounds14291 := by
 decide +kernel
def cuts14292 : List PrefixCut := [⟨50,359258483,359258733⟩,
⟨108,779830345,779830880⟩,
⟨128,928714121,928714759⟩]
theorem checked14292 : checkPrefixCuts (2^48) 1877213185 9 Manual.Count131072.C014292.packed 128 cuts14292 = true := by
 decide +kernel
def pointBounds14292 : List (Nat × Nat × Nat) := [(1877264384,95633838044921,95634215650386),(1877323776,95634258616783,95634636222533)]
theorem point_links_checked14292 : (cuts14292.take 2).map (fun c => (1877213185-1+2*2^9*c.k,95633478786438+c.lower,95633856391653+c.upper)) = pointBounds14292 := by
 decide +kernel
def cuts14293 : List PrefixCut := [⟨38,277072283,277072470⟩,
⟨96,695518613,695519083⟩,
⟨128,928799322,928799951⟩]
theorem checked14293 : checkPrefixCuts (2^48) 1877344257 9 Manual.Count131072.C014293.packed 128 cuts14293 = true := by
 decide +kernel
def pointBounds14293 : List (Nat × Nat × Nat) := [(1877383168,95634684572842,95635062178882),(1877442560,95635103019172,95635480625495)]
theorem point_links_checked14293 : (cuts14293.take 2).map (fun c => (1877344257-1+2*2^9*c.k,95634407500559+c.lower,95634785106412+c.upper)) = pointBounds14293 := by
 decide +kernel
def cuts14294 : List PrefixCut := [⟨26,181404367,181404491⟩,
⟨84,589929613,589930015⟩,
⟨128,905647161,905647777⟩]
theorem checked14294 : checkPrefixCuts (2^48) 1877475329 9 Manual.Count131072.C014294.packed 128 cuts14294 = true := by
 decide +kernel
def pointBounds14294 : List (Nat × Nat × Nat) := [(1877501952,95635517704248,95635895310854),(1877561344,95635926229494,95636303836378)]
theorem point_links_checked14294 : (cuts14294.take 2).map (fun c => (1877475329-1+2*2^9*c.k,95635336299881+c.lower,95635713906363+c.upper)) = pointBounds14294 := by
 decide +kernel
def cuts14295 : List PrefixCut := [⟨14,99241070,99241138⟩,
⟨72,521681902,521682254⟩,
⟨128,921474193,921474817⟩]
theorem checked14295 : checkPrefixCuts (2^48) 1877606401 9 Manual.Count131072.C014295.packed 128 cuts14295 = true := by
 decide +kernel
def pointBounds14295 : List (Nat × Nat × Nat) := [(1877620736,95636341188112,95636718795278),(1877680128,95636763628944,95637141236394)]
theorem point_links_checked14295 : (cuts14295.take 2).map (fun c => (1877606401-1+2*2^9*c.k,95636241947042+c.lower,95636619554140+c.upper)) = pointBounds14295 := by
 decide +kernel
def cuts14296 : List PrefixCut := [⟨2,14840199,14840209⟩,
⟨60,428110509,428110801⟩,
⟨118,838669639,838670213⟩,
⟨128,914514504,914515128⟩]
theorem checked14296 : checkPrefixCuts (2^48) 1877737473 9 Manual.Count131072.C014296.packed 128 cuts14296 = true := by
 decide +kernel
def pointBounds14296 : List (Nat × Nat × Nat) := [(1877739520,95637178261434,95637555869166),(1877798912,95637591531744,95637969139758),(1877858304,95638002090874,95638379699170)]
theorem point_links_checked14296 : (cuts14296.take 3).map (fun c => (1877737473-1+2*2^9*c.k,95637163421235+c.lower,95637541028957+c.upper)) = pointBounds14296 := by
 decide +kernel
def cuts14297 : List PrefixCut := [⟨48,342795392,342795629⟩,
⟨106,763820537,763821062⟩,
⟨128,924343157,924343792⟩]
theorem checked14297 : checkPrefixCuts (2^48) 1877868545 9 Manual.Count131072.C014297.packed 128 cuts14297 = true := by
 decide +kernel
def pointBounds14297 : List (Nat × Nat × Nat) := [(1877917696,95638420731131,95638798339714),(1877977088,95638841756276,95639219365147)]
theorem point_links_checked14297 : (cuts14297.take 2).map (fun c => (1877868545-1+2*2^9*c.k,95638077935739+c.lower,95638455544085+c.upper)) = pointBounds14297 := by
 decide +kernel
def cuts14298 : List PrefixCut := [⟨36,261838037,261838216⟩,
⟨94,684934717,684935184⟩,
⟨128,927875755,927876386⟩]
theorem checked14298 : checkPrefixCuts (2^48) 1877999617 9 Manual.Count131072.C014298.packed 128 cuts14298 = true := by
 decide +kernel
def pointBounds14298 : List (Nat × Nat × Nat) := [(1878036480,95639264116933,95639641726093),(1878095872,95639687213613,95640064823061)]
theorem point_links_checked14298 : (cuts14298.take 2).map (fun c => (1877999617-1+2*2^9*c.k,95639002278896+c.lower,95639379887877+c.upper)) = pointBounds14298 := by
 decide +kernel
def cuts14299 : List PrefixCut := [⟨24,175196532,175196652⟩,
⟨82,592571563,592571964⟩,
⟨128,924214183,924214815⟩]
theorem checked14299 : checkPrefixCuts (2^48) 1878130689 9 Manual.Count131072.C014299.packed 128 cuts14299 = true := by
 decide +kernel
def pointBounds14299 : List (Nat × Nat × Nat) := [(1878155264,95640105351183,95640482960915),(1878214656,95640522726214,95640900336227)]
theorem point_links_checked14299 : (cuts14299.take 2).map (fun c => (1878130689-1+2*2^9*c.k,95639930154651+c.lower,95640307764263+c.upper)) = pointBounds14299 := by
 decide +kernel
def cuts14300 : List PrefixCut := [⟨12,84520337,84520395⟩,
⟨70,493626881,493627215⟩,
⟨128,912460885,912461509⟩]
theorem checked14300 : checkPrefixCuts (2^48) 1878261761 9 Manual.Count131072.C014300.packed 128 cuts14300 = true := by
 decide +kernel
def pointBounds14300 : List (Nat × Nat × Nat) := [(1878274048,95640938889171,95641316499473),(1878333440,95641347995715,95641725606293),(1878392832,95641766829719,95642144440587)]
theorem point_links_checked14300 : (cuts14300.take 3).map (fun c => (1878261761-1+2*2^9*c.k,95640854368834+c.lower,95641231979078+c.upper)) = pointBounds14300 := by
 decide +kernel
def cuts14301 : List PrefixCut := [⟨58,414475134,414475418⟩,
⟨116,839575942,839576514⟩,
⟨128,924834228,924834859⟩]
theorem checked14301 : checkPrefixCuts (2^48) 1878392833 9 Manual.Count131072.C014301.packed 128 cuts14301 = true := by
 decide +kernel
def pointBounds14301 : List (Nat × Nat × Nat) := [(1878452224,95642181304853,95642558916005),(1878511616,95642606405661,95642984017101)]
theorem point_links_checked14301 : (cuts14301.take 2).map (fun c => (1878392833-1+2*2^9*c.k,95641766829719+c.lower,95642144440587+c.upper)) = pointBounds14301 := by
 decide +kernel
def cuts14302 : List PrefixCut := [⟨46,334584742,334584969⟩,
⟨104,750069432,750069942⟩,
⟨128,924769863,924770495⟩]
theorem checked14302 : checkPrefixCuts (2^48) 1878523905 9 Manual.Count131072.C014302.packed 128 cuts14302 = true := by
 decide +kernel
def pointBounds14302 : List (Nat × Nat × Nat) := [(1878571008,95643026248689,95643403860415),(1878630400,95643441733379,95643819345388)]
theorem point_links_checked14302 : (cuts14302.take 2).map (fun c => (1878523905-1+2*2^9*c.k,95642691663947+c.lower,95643069275446+c.upper)) = pointBounds14302 := by
 decide +kernel
def cuts14303 : List PrefixCut := [⟨34,240771114,240771279⟩,
⟨92,654431690,654432138⟩,
⟨128,912869261,912869884⟩]
theorem checked14303 : checkPrefixCuts (2^48) 1878654977 9 Manual.Count131072.C014303.packed 128 cuts14303 = true := by
 decide +kernel
def pointBounds14303 : List (Nat × Nat × Nat) := [(1878689792,95643857204924,95644234817220),(1878749184,95644270865500,95644648478079)]
theorem point_links_checked14303 : (cuts14303.take 2).map (fun c => (1878654977-1+2*2^9*c.k,95643616433810+c.lower,95643994045941+c.upper)) = pointBounds14303 := by
 decide +kernel
def cuts14304 : List PrefixCut := [⟨22,155060092,155060201⟩,
⟨80,579480922,579481321⟩,
⟨128,923142622,923143257⟩]
theorem checked14304 : checkPrefixCuts (2^48) 1878786049 9 Manual.Count131072.C014304.packed 128 cuts14304 = true := by
 decide +kernel
def pointBounds14304 : List (Nat × Nat × Nat) := [(1878808576,95644684363163,95645061976026),(1878867968,95645108783993,95645486397146)]
theorem point_links_checked14304 : (cuts14304.take 2).map (fun c => (1878786049-1+2*2^9*c.k,95644529303071+c.lower,95644906915825+c.upper)) = pointBounds14304 := by
 decide +kernel
def cuts14305 : List PrefixCut := [⟨10,68611408,68611455⟩,
⟨68,490009477,490009810⟩,
⟨126,901357602,901358217⟩,
⟨128,917086246,917086872⟩]
theorem checked14305 : checkPrefixCuts (2^48) 1878917121 9 Manual.Count131072.C014305.packed 128 cuts14305 = true := by
 decide +kernel
def pointBounds14305 : List (Nat × Nat × Nat) := [(1878927360,95645521057101,95645898670537),(1878986752,95645942455170,95646320068892),(1879046144,95646353803295,95646731417299)]
theorem point_links_checked14305 : (cuts14305.take 3).map (fun c => (1878917121-1+2*2^9*c.k,95645452445693+c.lower,95645830059082+c.upper)) = pointBounds14305 := by
 decide +kernel
def cuts14306 : List PrefixCut := [⟨56,417027166,417027448⟩,
⟨114,831944333,831944906⟩,
⟨128,937843503,937844149⟩]
theorem checked14306 : checkPrefixCuts (2^48) 1879048193 9 Manual.Count131072.C014306.packed 128 cuts14306 = true := by
 decide +kernel
def pointBounds14306 : List (Nat × Nat × Nat) := [(1879105536,95646786559105,95647164173402),(1879164928,95647201476272,95647579090860)]
theorem point_links_checked14306 : (cuts14306.take 2).map (fun c => (1879048193-1+2*2^9*c.k,95646369531939+c.lower,95646747145954+c.upper)) = pointBounds14306 := by
 decide +kernel
def cuts14307 : List PrefixCut := [⟨44,313648335,313648550⟩,
⟨102,726442316,726442816⟩,
⟨128,912614747,912615373⟩]
theorem checked14307 : checkPrefixCuts (2^48) 1879179265 9 Manual.Count131072.C014307.packed 128 cuts14307 = true := by
 decide +kernel
def pointBounds14307 : List (Nat × Nat × Nat) := [(1879224320,95647621023777,95647998638653),(1879283712,95648033817758,95648411432919)]
theorem point_links_checked14307 : (cuts14307.take 2).map (fun c => (1879179265-1+2*2^9*c.k,95647307375442+c.lower,95647684990103+c.upper)) = pointBounds14307 := by
 decide +kernel
def cuts14308 : List PrefixCut := [⟨32,230652430,230652590⟩,
⟨90,645517063,645517504⟩,
⟨128,918392050,918392678⟩]
theorem checked14308 : checkPrefixCuts (2^48) 1879310337 9 Manual.Count131072.C014308.packed 128 cuts14308 = true := by
 decide +kernel
def pointBounds14308 : List (Nat × Nat × Nat) := [(1879343104,95648450642619,95648828258066),(1879402496,95648865507252,95649243122980)]
theorem point_links_checked14308 : (cuts14308.take 2).map (fun c => (1879310337-1+2*2^9*c.k,95648219990189+c.lower,95648597605476+c.upper)) = pointBounds14308 := by
 decide +kernel
def cuts14309 : List PrefixCut := [⟨20,145570962,145571060⟩,
⟨78,559061673,559062053⟩,
⟨128,921922322,921922952⟩]
theorem checked14309 : checkPrefixCuts (2^48) 1879441409 9 Manual.Count131072.C014309.packed 128 cuts14309 = true := by
 decide +kernel
def pointBounds14309 : List (Nat × Nat × Nat) := [(1879461888,95649283953201,95649661569214),(1879521280,95649697443912,95650075060207)]
theorem point_links_checked14309 : (cuts14309.take 2).map (fun c => (1879441409-1+2*2^9*c.k,95649138382239+c.lower,95649515998154+c.upper)) = pointBounds14309 := by
 decide +kernel
def cuts14310 : List PrefixCut := [⟨8,56607165,56607205⟩,
⟨66,465728779,465729092⟩,
⟨124,885020327,885020930⟩,
⟨128,910327141,910327760⟩]
theorem checked14310 : checkPrefixCuts (2^48) 1879572481 9 Manual.Count131072.C014310.packed 128 cuts14310 = true := by
 decide +kernel
def pointBounds14310 : List (Nat × Nat × Nat) := [(1879580672,95650116911726,95650494528311),(1879640064,95650526033340,95650903650198),(1879699456,95650945324888,95651322942036)]
theorem point_links_checked14310 : (cuts14310.take 3).map (fun c => (1879572481-1+2*2^9*c.k,95650060304561+c.lower,95650437921106+c.upper)) = pointBounds14310 := by
 decide +kernel
def cuts14311 : List PrefixCut := [⟨54,379296727,379296988⟩,
⟨112,799759649,799760198⟩,
⟨128,911761059,911761685⟩]
theorem checked14311 : checkPrefixCuts (2^48) 1879703553 9 Manual.Count131072.C014311.packed 128 cuts14311 = true := by
 decide +kernel
def pointBounds14311 : List (Nat × Nat × Nat) := [(1879758848,95651349928429,95651727545854),(1879818240,95651770391351,95652148009064)]
theorem point_links_checked14311 : (cuts14311.take 2).map (fun c => (1879703553-1+2*2^9*c.k,95650970631702+c.lower,95651348248866+c.upper)) = pointBounds14311 := by
 decide +kernel
def cuts14312 : List PrefixCut := [⟨42,304255724,304255933⟩,
⟨100,722296374,722296869⟩,
⟨128,917237736,917238360⟩]
theorem checked14312 : checkPrefixCuts (2^48) 1879834625 9 Manual.Count131072.C014312.packed 128 cuts14312 = true := by
 decide +kernel
def pointBounds14312 : List (Nat × Nat × Nat) := [(1879877632,95652186648485,95652564266484),(1879937024,95652604689135,95652982307420)]
theorem point_links_checked14312 : (cuts14312.take 2).map (fun c => (1879834625-1+2*2^9*c.k,95651882392761+c.lower,95652260010551+c.upper)) = pointBounds14312 := by
 decide +kernel
def cuts14313 : List PrefixCut := [⟨30,212156345,212156491⟩,
⟨88,633165081,633165513⟩,
⟨128,915227388,915228015⟩]
theorem checked14313 : checkPrefixCuts (2^48) 1879965697 9 Manual.Count131072.C014313.packed 128 cuts14313 = true := by
 decide +kernel
def pointBounds14313 : List (Nat × Nat × Nat) := [(1879996416,95653011786842,95653389405402),(1880055808,95653432795578,95653810414424)]
theorem point_links_checked14313 : (cuts14313.take 2).map (fun c => (1879965697-1+2*2^9*c.k,95652799630497+c.lower,95653177248911+c.upper)) = pointBounds14313 := by
 decide +kernel
def cuts14314 : List PrefixCut := [⟨18,128453099,128453188⟩,
⟨76,540602315,540602689⟩,
⟨128,912318899,912319524⟩]
theorem checked14314 : checkPrefixCuts (2^48) 1880096769 9 Manual.Count131072.C014314.packed 128 cuts14314 = true := by
 decide +kernel
def pointBounds14314 : List (Nat × Nat × Nat) := [(1880115200,95653843310984,95654220930114),(1880174592,95654255460200,95654633079615)]
theorem point_links_checked14314 : (cuts14314.take 2).map (fun c => (1880096769-1+2*2^9*c.k,95653714857885+c.lower,95654092476926+c.upper)) = pointBounds14314 := by
 decide +kernel
def cuts14315 : List PrefixCut := [⟨6,43263963,43263991⟩,
⟨64,468111689,468112009⟩,
⟨122,881120063,881120672⟩,
⟨128,925728384,925729023⟩]
theorem checked14315 : checkPrefixCuts (2^48) 1880227841 9 Manual.Count131072.C014315.packed 128 cuts14315 = true := by
 decide +kernel
def pointBounds14315 : List (Nat × Nat × Nat) := [(1880233984,95654670440747,95655048060441),(1880293376,95655095288473,95655472908459),(1880352768,95655508296847,95655885917122)]
theorem point_links_checked14315 : (cuts14315.take 3).map (fun c => (1880227841-1+2*2^9*c.k,95654627176784+c.lower,95655004796450+c.upper)) = pointBounds14315 := by
 decide +kernel
def cuts14316 : List PrefixCut := [⟨52,370033643,370033898⟩,
⟨110,786758100,786758642⟩,
⟨128,918927673,918928303⟩]
theorem checked14316 : checkPrefixCuts (2^48) 1880358913 9 Manual.Count131072.C014316.packed 128 cuts14316 = true := by
 decide +kernel
def pointBounds14316 : List (Nat × Nat × Nat) := [(1880412160,95655922938811,95656300559371),(1880471552,95656339663268,95656717284115)]
theorem point_links_checked14316 : (cuts14316.take 2).map (fun c => (1880358913-1+2*2^9*c.k,95655552905168+c.lower,95655930525473+c.upper)) = pointBounds14316 := by
 decide +kernel
def cuts14317 : List PrefixCut := [⟨40,283344366,283344561⟩,
⟨98,696300528,696301006⟩,
⟨128,906590344,906590964⟩]
theorem checked14317 : checkPrefixCuts (2^48) 1880489985 9 Manual.Count131072.C014317.packed 128 cuts14317 = true := by
 decide +kernel
def pointBounds14317 : List (Nat × Nat × Nat) := [(1880530944,95656755177207,95657132798337),(1880590336,95657168133369,95657545754782)]
theorem point_links_checked14317 : (cuts14317.take 2).map (fun c => (1880489985-1+2*2^9*c.k,95656471832841+c.lower,95656849453776+c.upper)) = pointBounds14317 := by
 decide +kernel
def cuts14318 : List PrefixCut := [⟨28,201455961,201456097⟩,
⟨86,616032332,616032748⟩,
⟨128,915207707,915208325⟩]
theorem checked14318 : checkPrefixCuts (2^48) 1880621057 9 Manual.Count131072.C014318.packed 128 cuts14318 = true := by
 decide +kernel
def pointBounds14318 : List (Nat × Nat × Nat) := [(1880649728,95657579879146,95657957500837),(1880709120,95657994455517,95658372077488)]
theorem point_links_checked14318 : (cuts14318.take 2).map (fun c => (1880621057-1+2*2^9*c.k,95657378423185+c.lower,95657756044740+c.upper)) = pointBounds14318 := by
 decide +kernel
def cuts14319 : List PrefixCut := [⟨16,115986614,115986694⟩,
⟨74,522455465,522455820⟩,
⟨128,917388629,917389252⟩]
theorem checked14319 : checkPrefixCuts (2^48) 1880752129 9 Manual.Count131072.C014319.packed 128 cuts14319 = true := by
 decide +kernel
def pointBounds14319 : List (Nat × Nat × Nat) := [(1880768512,95658409617506,95658787239759),(1880827904,95658816086357,95659193708885)]
theorem point_links_checked14319 : (cuts14319.take 2).map (fun c => (1880752129-1+2*2^9*c.k,95658293630892+c.lower,95658671253065+c.upper)) = pointBounds14319 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000134
