import PlattAssemblyKernel
import PlattCertificates.Count131072.C039248
import PlattCertificates.Count131072.C039249
import PlattCertificates.Count131072.C039250
import PlattCertificates.Count131072.C039251
import PlattCertificates.Count131072.C039252
import PlattCertificates.Count131072.C039253
import PlattCertificates.Count131072.C039254
import PlattCertificates.Count131072.C039255
import PlattCertificates.Count131072.C039256
import PlattCertificates.Count131072.C039257
import PlattCertificates.Count131072.C039258
import PlattCertificates.Count131072.C039259
import PlattCertificates.Count131072.C039260
import PlattCertificates.Count131072.C039261
import PlattCertificates.Count131072.C039262
import PlattCertificates.Count131072.C039263
import PlattCertificates.Count131072.C039264
import PlattCertificates.Count131072.C039265
import PlattCertificates.Count131072.C039266
import PlattCertificates.Count131072.C039267
import PlattCertificates.Count131072.C039268
import PlattCertificates.Count131072.C039269
import PlattCertificates.Count131072.C039270
import PlattCertificates.Count131072.C039271
import PlattCertificates.Count131072.C039272
import PlattCertificates.Count131072.C039273
import PlattCertificates.Count131072.C039274
import PlattCertificates.Count131072.C039275
import PlattCertificates.Count131072.C039276
import PlattCertificates.Count131072.C039277
import PlattCertificates.Count131072.C039278
import PlattCertificates.Count131072.C039279
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000289
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts39248 : List PrefixCut := [⟨64,324376378,324376570⟩]
theorem checked39248 : checkPrefixCuts (2^48) 5148246017 10 Manual.Count131072.C039248.packed 64 cuts39248 = true := by
 decide +kernel
def cuts39249 : List PrefixCut := [⟨8,39145482,39145506⟩,
⟨64,318135475,318135663⟩]
theorem checked39249 : checkPrefixCuts (2^48) 5148377089 10 Manual.Count131072.C039249.packed 64 cuts39249 = true := by
 decide +kernel
def pointBounds39249 : List (Nat × Nat × Nat) := [(5148393472,108627971865616,108628357229353)]
theorem point_links_checked39249 : (cuts39249.take 1).map (fun c => (5148377089-1+2*2^10*c.k,108627932720134+c.lower,108628318083847+c.upper)) = pointBounds39249 := by
 decide +kernel
def cuts39250 : List PrefixCut := [⟨23,119182571,119182639⟩,
⟨64,324469202,324469389⟩]
theorem checked39250 : checkPrefixCuts (2^48) 5148508161 10 Manual.Count131072.C039250.packed 64 cuts39250 = true := by
 decide +kernel
def pointBounds39250 : List (Nat × Nat × Nat) := [(5148555264,108628370038180,108628755402149)]
theorem point_links_checked39250 : (cuts39250.take 1).map (fun c => (5148508161-1+2*2^10*c.k,108628250855609+c.lower,108628636219510+c.upper)) = pointBounds39250 := by
 decide +kernel
def cuts39251 : List PrefixCut := [⟨38,189647987,189648101⟩,
⟨64,319759391,319759581⟩]
theorem checked39251 : checkPrefixCuts (2^48) 5148639233 10 Manual.Count131072.C039251.packed 64 cuts39251 = true := by
 decide +kernel
def pointBounds39251 : List (Nat × Nat × Nat) := [(5148717056,108628764972798,108629150337000)]
theorem point_links_checked39251 : (cuts39251.take 1).map (fun c => (5148639233-1+2*2^10*c.k,108628575324811+c.lower,108628960688899+c.upper)) = pointBounds39251 := by
 decide +kernel
def cuts39252 : List PrefixCut := [⟨53,268746880,268747040⟩,
⟨64,324452653,324452847⟩]
theorem checked39252 : checkPrefixCuts (2^48) 5148770305 10 Manual.Count131072.C039252.packed 64 cuts39252 = true := by
 decide +kernel
def pointBounds39252 : List (Nat × Nat × Nat) := [(5148878848,108629163831082,108629549195520)]
theorem point_links_checked39252 : (cuts39252.take 1).map (fun c => (5148770305-1+2*2^10*c.k,108628895084202+c.lower,108629280448480+c.upper)) = pointBounds39252 := by
 decide +kernel
def cuts39253 : List PrefixCut := [⟨64,320891098,320891288⟩]
theorem checked39253 : checkPrefixCuts (2^48) 5148901377 10 Manual.Count131072.C039253.packed 64 cuts39253 = true := by
 decide +kernel
def cuts39254 : List PrefixCut := [⟨4,20335583,20335596⟩,
⟨64,321648273,321648464⟩]
theorem checked39254 : checkPrefixCuts (2^48) 5149032449 10 Manual.Count131072.C039254.packed 64 cuts39254 = true := by
 decide +kernel
def pointBounds39254 : List (Nat × Nat × Nat) := [(5149040640,108629560763536,108629946128211)]
theorem point_links_checked39254 : (cuts39254.take 1).map (fun c => (5149032449-1+2*2^10*c.k,108629540427953+c.lower,108629925792615+c.upper)) = pointBounds39254 := by
 decide +kernel
def cuts39255 : List PrefixCut := [⟨19,98231196,98231255⟩,
⟨64,322022719,322022912⟩]
theorem checked39255 : checkPrefixCuts (2^48) 5149163521 10 Manual.Count131072.C039255.packed 64 cuts39255 = true := by
 decide +kernel
def pointBounds39255 : List (Nat × Nat × Nat) := [(5149202432,108629960307422,108630345672334)]
theorem point_links_checked39255 : (cuts39255.take 1).map (fun c => (5149163521-1+2*2^10*c.k,108629862076226+c.lower,108630247441079+c.upper)) = pointBounds39255 := by
 decide +kernel
def cuts39256 : List PrefixCut := [⟨34,168196325,168196425⟩,
⟨64,317914818,317915007⟩]
theorem checked39256 : checkPrefixCuts (2^48) 5149294593 10 Manual.Count131072.C039256.packed 64 cuts39256 = true := by
 decide +kernel
def pointBounds39256 : List (Nat × Nat × Nat) := [(5149364224,108630352295270,108630737660416)]
theorem point_links_checked39256 : (cuts39256.take 1).map (fun c => (5149294593-1+2*2^10*c.k,108630184098945+c.lower,108630569463991+c.upper)) = pointBounds39256 := by
 decide +kernel
def cuts39257 : List PrefixCut := [⟨49,242366334,242366483⟩,
⟨64,316813508,316813701⟩]
theorem checked39257 : checkPrefixCuts (2^48) 5149425665 10 Manual.Count131072.C039257.packed 64 cuts39257 = true := by
 decide +kernel
def pointBounds39257 : List (Nat × Nat × Nat) := [(5149526016,108630744380097,108631129745481)]
theorem point_links_checked39257 : (cuts39257.take 1).map (fun c => (5149425665-1+2*2^10*c.k,108630502013763+c.lower,108630887378998+c.upper)) = pointBounds39257 := by
 decide +kernel
def cuts39258 : List PrefixCut := [⟨64,317734698,317734889⟩]
theorem checked39258 : checkPrefixCuts (2^48) 5149556737 10 Manual.Count131072.C039258.packed 64 cuts39258 = true := by
 decide +kernel
def pointBounds39258 : List (Nat × Nat × Nat) := [(5149687808,108631136561969,108631521927588)]
theorem point_links_checked39258 : (cuts39258.take 1).map (fun c => (5149556737-1+2*2^10*c.k,108630818827271+c.lower,108631204192699+c.upper)) = pointBounds39258 := by
 decide +kernel
def cuts39259 : List PrefixCut := [⟨64,319912932,319913123⟩]
theorem checked39259 : checkPrefixCuts (2^48) 5149687809 10 Manual.Count131072.C039259.packed 64 cuts39259 = true := by
 decide +kernel
def cuts39260 : List PrefixCut := [⟨15,73240487,73240532⟩,
⟨64,317991774,317991962⟩]
theorem checked39260 : checkPrefixCuts (2^48) 5149818881 10 Manual.Count131072.C039260.packed 64 cuts39260 = true := by
 decide +kernel
def pointBounds39260 : List (Nat × Nat × Nat) := [(5149849600,108631529715388,108631915081243)]
theorem point_links_checked39260 : (cuts39260.take 1).map (fun c => (5149818881-1+2*2^10*c.k,108631456474901+c.lower,108631841840711+c.upper)) = pointBounds39260 := by
 decide +kernel
def cuts39261 : List PrefixCut := [⟨30,152051671,152051760⟩,
⟨64,320935084,320935274⟩]
theorem checked39261 : checkPrefixCuts (2^48) 5149949953 10 Manual.Count131072.C039261.packed 64 cuts39261 = true := by
 decide +kernel
def pointBounds39261 : List (Nat × Nat × Nat) := [(5150011392,108631926518346,108632311884433)]
theorem point_links_checked39261 : (cuts39261.take 1).map (fun c => (5149949953-1+2*2^10*c.k,108631774466675+c.lower,108632159832673+c.upper)) = pointBounds39261 := by
 decide +kernel
def cuts39262 : List PrefixCut := [⟨45,222660266,222660401⟩,
⟨64,320762892,320763084⟩]
theorem checked39262 : checkPrefixCuts (2^48) 5150081025 10 Manual.Count131072.C039262.packed 64 cuts39262 = true := by
 decide +kernel
def pointBounds39262 : List (Nat × Nat × Nat) := [(5150173184,108632318062025,108632703428348)]
theorem point_links_checked39262 : (cuts39262.take 1).map (fun c => (5150081025-1+2*2^10*c.k,108632095401759+c.lower,108632480767947+c.upper)) = pointBounds39262 := by
 decide +kernel
def cuts39263 : List PrefixCut := [⟨60,301189471,301189648⟩,
⟨64,322503641,322503831⟩]
theorem checked39263 : checkPrefixCuts (2^48) 5150212097 10 Manual.Count131072.C039263.packed 64 cuts39263 = true := by
 decide +kernel
def pointBounds39263 : List (Nat × Nat × Nat) := [(5150334976,108632717354122,108633102720679)]
theorem point_links_checked39263 : (cuts39263.take 1).map (fun c => (5150212097-1+2*2^10*c.k,108632416164651+c.lower,108632801531031+c.upper)) = pointBounds39263 := by
 decide +kernel
def cuts39264 : List PrefixCut := [⟨64,323479138,323479331⟩]
theorem checked39264 : checkPrefixCuts (2^48) 5150343169 10 Manual.Count131072.C039264.packed 64 cuts39264 = true := by
 decide +kernel
def cuts39265 : List PrefixCut := [⟨11,56125719,56125752⟩,
⟨64,320847757,320847947⟩]
theorem checked39265 : checkPrefixCuts (2^48) 5150474241 10 Manual.Count131072.C039265.packed 64 cuts39265 = true := by
 decide +kernel
def pointBounds39265 : List (Nat × Nat × Nat) := [(5150496768,108633118273149,108633503639945)]
theorem point_links_checked39265 : (cuts39265.take 1).map (fun c => (5150474241-1+2*2^10*c.k,108633062147430+c.lower,108633447514193+c.upper)) = pointBounds39265 := by
 decide +kernel
def cuts39266 : List PrefixCut := [⟨26,131593874,131593954⟩,
⟨64,322041880,322042071⟩]
theorem checked39266 : checkPrefixCuts (2^48) 5150605313 10 Manual.Count131072.C039266.packed 64 cuts39266 = true := by
 decide +kernel
def pointBounds39266 : List (Nat × Nat × Nat) := [(5150658560,108633514589061,108633899956094)]
theorem point_links_checked39266 : (cuts39266.take 1).map (fun c => (5150605313-1+2*2^10*c.k,108633382995187+c.lower,108633768362140+c.upper)) = pointBounds39266 := by
 decide +kernel
def cuts39267 : List PrefixCut := [⟨41,208861049,208861171⟩,
⟨64,326842550,326842738⟩]
theorem checked39267 : checkPrefixCuts (2^48) 5150736385 10 Manual.Count131072.C039267.packed 64 cuts39267 = true := by
 decide +kernel
def pointBounds39267 : List (Nat × Nat × Nat) := [(5150820352,108633913898116,108634299265382)]
theorem point_links_checked39267 : (cuts39267.take 1).map (fun c => (5150736385-1+2*2^10*c.k,108633705037067+c.lower,108634090404211+c.upper)) = pointBounds39267 := by
 decide +kernel
def cuts39268 : List PrefixCut := [⟨56,280987176,280987341⟩,
⟨64,318856029,318856217⟩]
theorem checked39268 : checkPrefixCuts (2^48) 5150867457 10 Manual.Count131072.C039268.packed 64 cuts39268 = true := by
 decide +kernel
def pointBounds39268 : List (Nat × Nat × Nat) := [(5150982144,108634312866793,108634698234290)]
theorem point_links_checked39268 : (cuts39268.take 1).map (fun c => (5150867457-1+2*2^10*c.k,108634031879617+c.lower,108634417246949+c.upper)) = pointBounds39268 := by
 decide +kernel
def cuts39269 : List PrefixCut := [⟨64,319503679,319503865⟩]
theorem checked39269 : checkPrefixCuts (2^48) 5150998529 10 Manual.Count131072.C039269.packed 64 cuts39269 = true := by
 decide +kernel
def cuts39270 : List PrefixCut := [⟨7,35026328,35026348⟩,
⟨64,325943345,325943537⟩]
theorem checked39270 : checkPrefixCuts (2^48) 5151129601 10 Manual.Count131072.C039270.packed 64 cuts39270 = true := by
 decide +kernel
def pointBounds39270 : List (Nat × Nat × Nat) := [(5151143936,108634705265653,108635090633379)]
theorem point_links_checked39270 : (cuts39270.take 1).map (fun c => (5151129601-1+2*2^10*c.k,108634670239325+c.lower,108635055607031+c.upper)) = pointBounds39270 := by
 decide +kernel
def cuts39271 : List PrefixCut := [⟨22,111523717,111523783⟩,
⟨64,323749388,323749580⟩]
theorem checked39271 : checkPrefixCuts (2^48) 5151260673 10 Manual.Count131072.C039271.packed 64 cuts39271 = true := by
 decide +kernel
def pointBounds39271 : List (Nat × Nat × Nat) := [(5151305728,108635107706387,108635493074351)]
theorem point_links_checked39271 : (cuts39271.take 1).map (fun c => (5151260673-1+2*2^10*c.k,108634996182670+c.lower,108635381550568+c.upper)) = pointBounds39271 := by
 decide +kernel
def cuts39272 : List PrefixCut := [⟨37,183590910,183591019⟩,
⟨64,317293659,317293846⟩]
theorem checked39272 : checkPrefixCuts (2^48) 5151391745 10 Manual.Count131072.C039272.packed 64 cuts39272 = true := by
 decide +kernel
def pointBounds39272 : List (Nat × Nat × Nat) := [(5151467520,108635503522968,108635888891167)]
theorem point_links_checked39272 : (cuts39272.take 1).map (fun c => (5151391745-1+2*2^10*c.k,108635319932058+c.lower,108635705300148+c.upper)) = pointBounds39272 := by
 decide +kernel
def cuts39273 : List PrefixCut := [⟨52,260844680,260844834⟩,
⟨64,320181443,320181632⟩]
theorem checked39273 : checkPrefixCuts (2^48) 5151522817 10 Manual.Count131072.C039273.packed 64 cuts39273 = true := by
 decide +kernel
def pointBounds39273 : List (Nat × Nat × Nat) := [(5151629312,108635898070397,108636283438828)]
theorem point_links_checked39273 : (cuts39273.take 1).map (fun c => (5151522817-1+2*2^10*c.k,108635637225717+c.lower,108636022593994+c.upper)) = pointBounds39273 := by
 decide +kernel
def cuts39274 : List PrefixCut := [⟨64,320173250,320173441⟩]
theorem checked39274 : checkPrefixCuts (2^48) 5151653889 10 Manual.Count131072.C039274.packed 64 cuts39274 = true := by
 decide +kernel
def cuts39275 : List PrefixCut := [⟨3,14642542,14642551⟩,
⟨64,313117122,313117309⟩]
theorem checked39275 : checkPrefixCuts (2^48) 5151784961 10 Manual.Count131072.C039275.packed 64 cuts39275 = true := by
 decide +kernel
def pointBounds39275 : List (Nat × Nat × Nat) := [(5151791104,108636292222952,108636677591618)]
theorem point_links_checked39275 : (cuts39275.take 1).map (fun c => (5151784961-1+2*2^10*c.k,108636277580410+c.lower,108636662949067+c.upper)) = pointBounds39275 := by
 decide +kernel
def cuts39276 : List PrefixCut := [⟨18,91622546,91622600⟩,
⟨64,315677038,315677224⟩]
theorem checked39276 : checkPrefixCuts (2^48) 5151916033 10 Manual.Count131072.C039276.packed 64 cuts39276 = true := by
 decide +kernel
def pointBounds39276 : List (Nat × Nat × Nat) := [(5151952896,108636682320078,108637067688976)]
theorem point_links_checked39276 : (cuts39276.take 1).map (fun c => (5151916033-1+2*2^10*c.k,108636590697532+c.lower,108636976066376+c.upper)) = pointBounds39276 := by
 decide +kernel
def cuts39277 : List PrefixCut := [⟨33,165484103,165484204⟩,
⟨64,319493252,319493447⟩]
theorem checked39277 : checkPrefixCuts (2^48) 5152047105 10 Manual.Count131072.C039277.packed 64 cuts39277 = true := by
 decide +kernel
def pointBounds39277 : List (Nat × Nat × Nat) := [(5152114688,108637071858673,108637457227804)]
theorem point_links_checked39277 : (cuts39277.take 1).map (fun c => (5152047105-1+2*2^10*c.k,108636906374570+c.lower,108637291743600+c.upper)) = pointBounds39277 := by
 decide +kernel
def cuts39278 : List PrefixCut := [⟨48,243111046,243111192⟩,
⟨64,323200089,323200283⟩]
theorem checked39278 : checkPrefixCuts (2^48) 5152178177 10 Manual.Count131072.C039278.packed 64 cuts39278 = true := by
 decide +kernel
def pointBounds39278 : List (Nat × Nat × Nat) := [(5152276480,108637468978868,108637854348239)]
theorem point_links_checked39278 : (cuts39278.take 1).map (fun c => (5152178177-1+2*2^10*c.k,108637225867822+c.lower,108637611237047+c.upper)) = pointBounds39278 := by
 decide +kernel
def cuts39279 : List PrefixCut := [⟨63,317455693,317455885⟩,
⟨64,321771419,321771614⟩]
theorem checked39279 : checkPrefixCuts (2^48) 5152309249 10 Manual.Count131072.C039279.packed 64 cuts39279 = true := by
 decide +kernel
def pointBounds39279 : List (Nat × Nat × Nat) := [(5152438272,108637866523604,108638251893215)]
theorem point_links_checked39279 : (cuts39279.take 1).map (fun c => (5152309249-1+2*2^10*c.k,108637549067911+c.lower,108637934437330+c.upper)) = pointBounds39279 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000289
