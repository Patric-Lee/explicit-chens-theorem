import PlattAssemblyKernel
import PlattCertificates.Count131072.C029248
import PlattCertificates.Count131072.C029249
import PlattCertificates.Count131072.C029250
import PlattCertificates.Count131072.C029251
import PlattCertificates.Count131072.C029252
import PlattCertificates.Count131072.C029253
import PlattCertificates.Count131072.C029254
import PlattCertificates.Count131072.C029255
import PlattCertificates.Count131072.C029256
import PlattCertificates.Count131072.C029257
import PlattCertificates.Count131072.C029258
import PlattCertificates.Count131072.C029259
import PlattCertificates.Count131072.C029260
import PlattCertificates.Count131072.C029261
import PlattCertificates.Count131072.C029262
import PlattCertificates.Count131072.C029263
import PlattCertificates.Count131072.C029264
import PlattCertificates.Count131072.C029265
import PlattCertificates.Count131072.C029266
import PlattCertificates.Count131072.C029267
import PlattCertificates.Count131072.C029268
import PlattCertificates.Count131072.C029269
import PlattCertificates.Count131072.C029270
import PlattCertificates.Count131072.C029271
import PlattCertificates.Count131072.C029272
import PlattCertificates.Count131072.C029273
import PlattCertificates.Count131072.C029274
import PlattCertificates.Count131072.C029275
import PlattCertificates.Count131072.C029276
import PlattCertificates.Count131072.C029277
import PlattCertificates.Count131072.C029278
import PlattCertificates.Count131072.C029279
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000289
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts29248 : List PrefixCut := [⟨20,67846728,67846765⟩,
⟨128,436559878,436560123⟩]
theorem checked29248 : checkPrefixCuts (2^48) 3837526017 9 Manual.Count131072.C029248.packed 128 cuts29248 = true := by
 decide +kernel
def pointBounds29248 : List (Nat × Nat × Nat) := [(3837546496,104904831508987,104905214648949)]
theorem point_links_checked29248 : (cuts29248.take 1).map (fun c => (3837526017-1+2*2^9*c.k,104904763662259+c.lower,104905146802184+c.upper)) = pointBounds29248 := by
 decide +kernel
def cuts29249 : List PrefixCut := [⟨10,34325649,34325669⟩,
⟨128,432071016,432071262⟩]
theorem checked29249 : checkPrefixCuts (2^48) 3837657089 9 Manual.Count131072.C029249.packed 128 cuts29249 = true := by
 decide +kernel
def pointBounds29249 : List (Nat × Nat × Nat) := [(3837667328,104905234547786,104905617687976),(3837788160,104905632293153,104906015433569)]
theorem point_links_checked29249 : (cuts29249.take 2).map (fun c => (3837657089-1+2*2^9*c.k,104905200222137+c.lower,104905583362307+c.upper)) = pointBounds29249 := by
 decide +kernel
def cuts29250 : List PrefixCut := [⟨118,402793430,402793659⟩,
⟨128,434989948,434990197⟩]
theorem checked29250 : checkPrefixCuts (2^48) 3837788161 9 Manual.Count131072.C029250.packed 128 cuts29250 = true := by
 decide +kernel
def pointBounds29250 : List (Nat × Nat × Nat) := [(3837908992,104906035086583,104906418227228)]
theorem point_links_checked29250 : (cuts29250.take 1).map (fun c => (3837788161-1+2*2^9*c.k,104905632293153+c.lower,104906015433569+c.upper)) = pointBounds29250 := by
 decide +kernel
def cuts29251 : List PrefixCut := [⟨108,365597105,365597311⟩,
⟨128,432774880,432775126⟩]
theorem checked29251 : checkPrefixCuts (2^48) 3837919233 9 Manual.Count131072.C029251.packed 128 cuts29251 = true := by
 decide +kernel
def pointBounds29251 : List (Nat × Nat × Nat) := [(3838029824,104906432880206,104906816021077)]
theorem point_links_checked29251 : (cuts29251.take 1).map (fun c => (3837919233-1+2*2^9*c.k,104906067283101+c.lower,104906450423766+c.upper)) = pointBounds29251 := by
 decide +kernel
def cuts29252 : List PrefixCut := [⟨98,337423676,337423863⟩,
⟨128,440827122,440827367⟩]
theorem checked29252 : checkPrefixCuts (2^48) 3838050305 9 Manual.Count131072.C029252.packed 128 cuts29252 = true := by
 decide +kernel
def pointBounds29252 : List (Nat × Nat × Nat) := [(3838150656,104906837481657,104907220622755)]
theorem point_links_checked29252 : (cuts29252.take 1).map (fun c => (3838050305-1+2*2^9*c.k,104906500057981+c.lower,104906883198892+c.upper)) = pointBounds29252 := by
 decide +kernel
def cuts29253 : List PrefixCut := [⟨88,298178538,298178705⟩,
⟨128,437071953,437072195⟩]
theorem checked29253 : checkPrefixCuts (2^48) 3838181377 9 Manual.Count131072.C029253.packed 128 cuts29253 = true := by
 decide +kernel
def pointBounds29253 : List (Nat × Nat × Nat) := [(3838271488,104907239063641,104907622204964)]
theorem point_links_checked29253 : (cuts29253.take 1).map (fun c => (3838181377-1+2*2^9*c.k,104906940885103+c.lower,104907324026259+c.upper)) = pointBounds29253 := by
 decide +kernel
def cuts29254 : List PrefixCut := [⟨78,267515900,267516051⟩,
⟨128,437790419,437790664⟩]
theorem checked29254 : checkPrefixCuts (2^48) 3838312449 9 Manual.Count131072.C029254.packed 128 cuts29254 = true := by
 decide +kernel
def pointBounds29254 : List (Nat × Nat × Nat) := [(3838392320,104907645472956,104908028614505)]
theorem point_links_checked29254 : (cuts29254.take 1).map (fun c => (3838312449-1+2*2^9*c.k,104907377957056+c.lower,104907761098454+c.upper)) = pointBounds29254 := by
 decide +kernel
def cuts29255 : List PrefixCut := [⟨68,230475619,230475749⟩,
⟨128,436088903,436089147⟩]
theorem checked29255 : checkPrefixCuts (2^48) 3838443521 9 Manual.Count131072.C029255.packed 128 cuts29255 = true := by
 decide +kernel
def pointBounds29255 : List (Nat × Nat × Nat) := [(3838513152,104908046223094,104908429364867)]
theorem point_links_checked29255 : (cuts29255.take 1).map (fun c => (3838443521-1+2*2^9*c.k,104907815747475+c.lower,104908198889118+c.upper)) = pointBounds29255 := by
 decide +kernel
def cuts29256 : List PrefixCut := [⟨58,195857499,195857605⟩,
⟨128,437247194,437247434⟩]
theorem checked29256 : checkPrefixCuts (2^48) 3838574593 9 Manual.Count131072.C029256.packed 128 cuts29256 = true := by
 decide +kernel
def pointBounds29256 : List (Nat × Nat × Nat) := [(3838633984,104908447693877,104908830835870)]
theorem point_links_checked29256 : (cuts29256.take 1).map (fun c => (3838574593-1+2*2^9*c.k,104908251836378+c.lower,104908634978265+c.upper)) = pointBounds29256 := by
 decide +kernel
def cuts29257 : List PrefixCut := [⟨48,165494517,165494611⟩,
⟨128,439505371,439505620⟩]
theorem checked29257 : checkPrefixCuts (2^48) 3838705665 9 Manual.Count131072.C029257.packed 128 cuts29257 = true := by
 decide +kernel
def pointBounds29257 : List (Nat × Nat × Nat) := [(3838754816,104908854578089,104909237720310)]
theorem point_links_checked29257 : (cuts29257.take 1).map (fun c => (3838705665-1+2*2^9*c.k,104908689083572+c.lower,104909072225699+c.upper)) = pointBounds29257 := by
 decide +kernel
def cuts29258 : List PrefixCut := [⟨38,126628122,126628192⟩,
⟨128,430545088,430545327⟩]
theorem checked29258 : checkPrefixCuts (2^48) 3838836737 9 Manual.Count131072.C029258.packed 128 cuts29258 = true := by
 decide +kernel
def pointBounds29258 : List (Nat × Nat × Nat) := [(3838875648,104909255217065,104909638359511)]
theorem point_links_checked29258 : (cuts29258.take 1).map (fun c => (3838836737-1+2*2^9*c.k,104909128588943+c.lower,104909511731319+c.upper)) = pointBounds29258 := by
 decide +kernel
def cuts29259 : List PrefixCut := [⟨28,93263279,93263333⟩,
⟨128,433243174,433243416⟩]
theorem checked29259 : checkPrefixCuts (2^48) 3838967809 9 Manual.Count131072.C029259.packed 128 cuts29259 = true := by
 decide +kernel
def pointBounds29259 : List (Nat × Nat × Nat) := [(3838996480,104909652397310,104910035539979)]
theorem point_links_checked29259 : (cuts29259.take 1).map (fun c => (3838967809-1+2*2^9*c.k,104909559134031+c.lower,104909942276646+c.upper)) = pointBounds29259 := by
 decide +kernel
def cuts29260 : List PrefixCut := [⟨18,60267216,60267251⟩,
⟨128,434401515,434401764⟩]
theorem checked29260 : checkPrefixCuts (2^48) 3839098881 9 Manual.Count131072.C029260.packed 128 cuts29260 = true := by
 decide +kernel
def pointBounds29260 : List (Nat × Nat × Nat) := [(3839117312,104910052644421,104910435787313)]
theorem point_links_checked29260 : (cuts29260.take 1).map (fun c => (3839098881-1+2*2^9*c.k,104909992377205+c.lower,104910375520062+c.upper)) = pointBounds29260 := by
 decide +kernel
def cuts29261 : List PrefixCut := [⟨8,29106207,29106222⟩,
⟨126,432773880,432774118⟩,
⟨128,439152108,439152350⟩]
theorem checked29261 : checkPrefixCuts (2^48) 3839229953 9 Manual.Count131072.C029261.packed 128 cuts29261 = true := by
 decide +kernel
def pointBounds29261 : List (Nat × Nat × Nat) := [(3839238144,104910455884927,104910839028048),(3839358976,104910859552600,104911242695944)]
theorem point_links_checked29261 : (cuts29261.take 2).map (fun c => (3839229953-1+2*2^9*c.k,104910426778720+c.lower,104910809921826+c.upper)) = pointBounds29261 := by
 decide +kernel
def cuts29262 : List PrefixCut := [⟨116,394124356,394124577⟩,
⟨128,433931996,433932238⟩]
theorem checked29262 : checkPrefixCuts (2^48) 3839361025 9 Manual.Count131072.C029262.packed 128 cuts29262 = true := by
 decide +kernel
def pointBounds29262 : List (Nat × Nat × Nat) := [(3839479808,104911260055184,104911643198753)]
theorem point_links_checked29262 : (cuts29262.take 1).map (fun c => (3839361025-1+2*2^9*c.k,104910865930828+c.lower,104911249074176+c.upper)) = pointBounds29262 := by
 decide +kernel
def cuts29263 : List PrefixCut := [⟨106,361855268,361855472⟩,
⟨128,436116442,436116687⟩]
theorem checked29263 : checkPrefixCuts (2^48) 3839492097 9 Manual.Count131072.C029263.packed 128 cuts29263 = true := by
 decide +kernel
def pointBounds29263 : List (Nat × Nat × Nat) := [(3839600640,104911661718092,104912044861886)]
theorem point_links_checked29263 : (cuts29263.take 1).map (fun c => (3839492097-1+2*2^9*c.k,104911299862824+c.lower,104911683006414+c.upper)) = pointBounds29263 := by
 decide +kernel
def cuts29264 : List PrefixCut := [⟨96,323943714,323943891⟩,
⟨128,436907893,436908133⟩]
theorem checked29264 : checkPrefixCuts (2^48) 3839623169 9 Manual.Count131072.C029264.packed 128 cuts29264 = true := by
 decide +kernel
def pointBounds29264 : List (Nat × Nat × Nat) := [(3839721472,104912059922980,104912443066992)]
theorem point_links_checked29264 : (cuts29264.take 1).map (fun c => (3839623169-1+2*2^9*c.k,104911735979266+c.lower,104912119123101+c.upper)) = pointBounds29264 := by
 decide +kernel
def cuts29265 : List PrefixCut := [⟨86,296810315,296810478⟩,
⟨128,438212491,438212737⟩]
theorem checked29265 : checkPrefixCuts (2^48) 3839754241 9 Manual.Count131072.C029265.packed 128 cuts29265 = true := by
 decide +kernel
def pointBounds29265 : List (Nat × Nat × Nat) := [(3839842304,104912469697474,104912852841712)]
theorem point_links_checked29265 : (cuts29265.take 1).map (fun c => (3839754241-1+2*2^9*c.k,104912172887159+c.lower,104912556031234+c.upper)) = pointBounds29265 := by
 decide +kernel
def cuts29266 : List PrefixCut := [⟨76,254871744,254871887⟩,
⟨128,432186746,432186987⟩]
theorem checked29266 : checkPrefixCuts (2^48) 3839885313 9 Manual.Count131072.C029266.packed 128 cuts29266 = true := by
 decide +kernel
def pointBounds29266 : List (Nat × Nat × Nat) := [(3839963136,104912865971394,104913249115858)]
theorem point_links_checked29266 : (cuts29266.take 1).map (fun c => (3839885313-1+2*2^9*c.k,104912611099650+c.lower,104912994243971+c.upper)) = pointBounds29266 := by
 decide +kernel
def cuts29267 : List PrefixCut := [⟨66,225177006,225177134⟩,
⟨128,438915559,438915801⟩]
theorem checked29267 : checkPrefixCuts (2^48) 3840016385 9 Manual.Count131072.C029267.packed 128 cuts29267 = true := by
 decide +kernel
def pointBounds29267 : List (Nat × Nat × Nat) := [(3840083968,104913268463402,104913651608092)]
theorem point_links_checked29267 : (cuts29267.take 1).map (fun c => (3840016385-1+2*2^9*c.k,104913043286396+c.lower,104913426430958+c.upper)) = pointBounds29267 := by
 decide +kernel
def cuts29268 : List PrefixCut := [⟨56,189473748,189473852⟩,
⟨128,432083949,432084189⟩]
theorem checked29268 : checkPrefixCuts (2^48) 3840147457 9 Manual.Count131072.C029268.packed 128 cuts29268 = true := by
 decide +kernel
def pointBounds29268 : List (Nat × Nat × Nat) := [(3840204800,104913671675703,104914054820611)]
theorem point_links_checked29268 : (cuts29268.take 1).map (fun c => (3840147457-1+2*2^9*c.k,104913482201955+c.lower,104913865346759+c.upper)) = pointBounds29268 := by
 decide +kernel
def cuts29269 : List PrefixCut := [⟨46,153846182,153846269⟩,
⟨128,432948726,432948972⟩]
theorem checked29269 : checkPrefixCuts (2^48) 3840278529 9 Manual.Count131072.C029269.packed 128 cuts29269 = true := by
 decide +kernel
def pointBounds29269 : List (Nat × Nat × Nat) := [(3840325632,104914068132086,104914451277217)]
theorem point_links_checked29269 : (cuts29269.take 1).map (fun c => (3840278529-1+2*2^9*c.k,104913914285904+c.lower,104914297430948+c.upper)) = pointBounds29269 := by
 decide +kernel
def cuts29270 : List PrefixCut := [⟨36,121885572,121885642⟩,
⟨128,435425921,435426168⟩]
theorem checked29270 : checkPrefixCuts (2^48) 3840409601 9 Manual.Count131072.C029270.packed 128 cuts29270 = true := by
 decide +kernel
def pointBounds29270 : List (Nat × Nat × Nat) := [(3840446464,104914469120202,104914852265562)]
theorem point_links_checked29270 : (cuts29270.take 1).map (fun c => (3840409601-1+2*2^9*c.k,104914347234630+c.lower,104914730379920+c.upper)) = pointBounds29270 := by
 decide +kernel
def cuts29271 : List PrefixCut := [⟨26,87435190,87435239⟩,
⟨128,431086988,431087235⟩]
theorem checked29271 : checkPrefixCuts (2^48) 3840540673 9 Manual.Count131072.C029271.packed 128 cuts29271 = true := by
 decide +kernel
def pointBounds29271 : List (Nat × Nat × Nat) := [(3840567296,104914870095741,104915253241327)]
theorem point_links_checked29271 : (cuts29271.take 1).map (fun c => (3840540673-1+2*2^9*c.k,104914782660551+c.lower,104915165806088+c.upper)) = pointBounds29271 := by
 decide +kernel
def cuts29272 : List PrefixCut := [⟨16,54819258,54819289⟩,
⟨128,430412702,430412950⟩]
theorem checked29272 : checkPrefixCuts (2^48) 3840671745 9 Manual.Count131072.C029272.packed 128 cuts29272 = true := by
 decide +kernel
def pointBounds29272 : List (Nat × Nat × Nat) := [(3840688128,104915268566797,104915651712612)]
theorem point_links_checked29272 : (cuts29272.take 1).map (fun c => (3840671745-1+2*2^9*c.k,104915213747539+c.lower,104915596893323+c.upper)) = pointBounds29272 := by
 decide +kernel
def cuts29273 : List PrefixCut := [⟨6,20153478,20153489⟩,
⟨124,427833275,427833514⟩,
⟨128,440657794,440658041⟩]
theorem checked29273 : checkPrefixCuts (2^48) 3840802817 9 Manual.Count131072.C029273.packed 128 cuts29273 = true := by
 decide +kernel
def pointBounds29273 : List (Nat × Nat × Nat) := [(3840808960,104915664313719,104916047459762),(3840929792,104916071993516,104916455139787)]
theorem point_links_checked29273 : (cuts29273.take 2).map (fun c => (3840802817-1+2*2^9*c.k,104915644160241+c.lower,104916027306273+c.upper)) = pointBounds29273 := by
 decide +kernel
def cuts29274 : List PrefixCut := [⟨114,388320367,388320582⟩,
⟨128,436612263,436612505⟩]
theorem checked29274 : checkPrefixCuts (2^48) 3840933889 9 Manual.Count131072.C029274.packed 128 cuts29274 = true := by
 decide +kernel
def pointBounds29274 : List (Nat × Nat × Nat) := [(3841050624,104916473138402,104916856284896)]
theorem point_links_checked29274 : (cuts29274.take 1).map (fun c => (3840933889-1+2*2^9*c.k,104916084818035+c.lower,104916467964314+c.upper)) = pointBounds29274 := by
 decide +kernel
def cuts29275 : List PrefixCut := [⟨104,352107588,352107787⟩,
⟨128,433446346,433446591⟩]
theorem checked29275 : checkPrefixCuts (2^48) 3841064961 9 Manual.Count131072.C029275.packed 128 cuts29275 = true := by
 decide +kernel
def pointBounds29275 : List (Nat × Nat × Nat) := [(3841171456,104916873537886,104917256684606)]
theorem point_links_checked29275 : (cuts29275.take 1).map (fun c => (3841064961-1+2*2^9*c.k,104916521430298+c.lower,104916904576819+c.upper)) = pointBounds29275 := by
 decide +kernel
def cuts29276 : List PrefixCut := [⟨94,321832611,321832787⟩,
⟨128,437828145,437828387⟩]
theorem checked29276 : checkPrefixCuts (2^48) 3841196033 9 Manual.Count131072.C029276.packed 128 cuts29276 = true := by
 decide +kernel
def pointBounds29276 : List (Nat × Nat × Nat) := [(3841292288,104917276709255,104917659856197)]
theorem point_links_checked29276 : (cuts29276.take 1).map (fun c => (3841196033-1+2*2^9*c.k,104916954876644+c.lower,104917338023410+c.upper)) = pointBounds29276 := by
 decide +kernel
def cuts29277 : List PrefixCut := [⟨84,288189001,288189163⟩,
⟨128,436787374,436787621⟩]
theorem checked29277 : checkPrefixCuts (2^48) 3841327105 9 Manual.Count131072.C029277.packed 128 cuts29277 = true := by
 decide +kernel
def pointBounds29277 : List (Nat × Nat × Nat) := [(3841413120,104917680893790,104918064040960)]
theorem point_links_checked29277 : (cuts29277.take 1).map (fun c => (3841327105-1+2*2^9*c.k,104917392704789+c.lower,104917775851797+c.upper)) = pointBounds29277 := by
 decide +kernel
def cuts29278 : List PrefixCut := [⟨74,252202946,252203087⟩,
⟨128,434720914,434721157⟩]
theorem checked29278 : checkPrefixCuts (2^48) 3841458177 9 Manual.Count131072.C029278.packed 128 cuts29278 = true := by
 decide +kernel
def pointBounds29278 : List (Nat × Nat × Nat) := [(3841533952,104918081695109,104918464842505)]
theorem point_links_checked29278 : (cuts29278.take 1).map (fun c => (3841458177-1+2*2^9*c.k,104917829492163+c.lower,104918212639418+c.upper)) = pointBounds29278 := by
 decide +kernel
def cuts29279 : List PrefixCut := [⟨64,218124210,218124332⟩,
⟨128,440347743,440347987⟩]
theorem checked29279 : checkPrefixCuts (2^48) 3841589249 9 Manual.Count131072.C029279.packed 128 cuts29279 = true := by
 decide +kernel
def pointBounds29279 : List (Nat × Nat × Nat) := [(3841654784,104918482337287,104918865484907)]
theorem point_links_checked29279 : (cuts29279.take 1).map (fun c => (3841589249-1+2*2^9*c.k,104918264213077+c.lower,104918647360575+c.upper)) = pointBounds29279 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000289
