import PlattAssemblyKernel
import PlattCertificates.Count131072.C038384
import PlattCertificates.Count131072.C038385
import PlattCertificates.Count131072.C038386
import PlattCertificates.Count131072.C038387
import PlattCertificates.Count131072.C038388
import PlattCertificates.Count131072.C038389
import PlattCertificates.Count131072.C038390
import PlattCertificates.Count131072.C038391
import PlattCertificates.Count131072.C038392
import PlattCertificates.Count131072.C038393
import PlattCertificates.Count131072.C038394
import PlattCertificates.Count131072.C038395
import PlattCertificates.Count131072.C038396
import PlattCertificates.Count131072.C038397
import PlattCertificates.Count131072.C038398
import PlattCertificates.Count131072.C038399
import PlattCertificates.Count131072.C038400
import PlattCertificates.Count131072.C038401
import PlattCertificates.Count131072.C038402
import PlattCertificates.Count131072.C038403
import PlattCertificates.Count131072.C038404
import PlattCertificates.Count131072.C038405
import PlattCertificates.Count131072.C038406
import PlattCertificates.Count131072.C038407
import PlattCertificates.Count131072.C038408
import PlattCertificates.Count131072.C038409
import PlattCertificates.Count131072.C038410
import PlattCertificates.Count131072.C038411
import PlattCertificates.Count131072.C038412
import PlattCertificates.Count131072.C038413
import PlattCertificates.Count131072.C038414
import PlattCertificates.Count131072.C038415
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000262
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts38384 : List PrefixCut := [⟨64,326137703,326137898⟩]
theorem checked38384 : checkPrefixCuts (2^48) 5034999809 10 Manual.Count131072.C038384.packed 64 cuts38384 = true := by
 decide +kernel
def cuts38385 : List PrefixCut := [⟨4,21242819,21242831⟩,
⟨64,322439700,322439895⟩]
theorem checked38385 : checkPrefixCuts (2^48) 5035130881 10 Manual.Count131072.C038385.packed 64 cuts38385 = true := by
 decide +kernel
def pointBounds38385 : List (Nat × Nat × Nat) := [(5035139072,108347887210065,108348272405802)]
theorem point_links_checked38385 : (cuts38385.take 1).map (fun c => (5035130881-1+2*2^10*c.k,108347865967246+c.lower,108348251162971+c.upper)) = pointBounds38385 := by
 decide +kernel
def cuts38386 : List PrefixCut := [⟨17,89273188,89273241⟩,
⟨64,329195233,329195428⟩]
theorem checked38386 : checkPrefixCuts (2^48) 5035261953 10 Manual.Count131072.C038386.packed 64 cuts38386 = true := by
 decide +kernel
def pointBounds38386 : List (Nat × Nat × Nat) := [(5035296768,108348277680134,108348662876107)]
theorem point_links_checked38386 : (cuts38386.take 1).map (fun c => (5035261953-1+2*2^10*c.k,108348188406946+c.lower,108348573602866+c.upper)) = pointBounds38386 := by
 decide +kernel
def cuts38387 : List PrefixCut := [⟨30,151765645,151765738⟩,
⟨64,326559380,326559577⟩]
theorem checked38387 : checkPrefixCuts (2^48) 5035393025 10 Manual.Count131072.C038387.packed 64 cuts38387 = true := by
 decide +kernel
def pointBounds38387 : List (Nat × Nat × Nat) := [(5035454464,108348669367824,108349054564032)]
theorem point_links_checked38387 : (cuts38387.take 1).map (fun c => (5035393025-1+2*2^10*c.k,108348517602179+c.lower,108348902798294+c.upper)) = pointBounds38387 := by
 decide +kernel
def cuts38388 : List PrefixCut := [⟨43,216658099,216658231⟩,
⟨64,321240668,321240862⟩]
theorem checked38388 : checkPrefixCuts (2^48) 5035524097 10 Manual.Count131072.C038388.packed 64 cuts38388 = true := by
 decide +kernel
def pointBounds38388 : List (Nat × Nat × Nat) := [(5035612160,108349060819658,108349446016102)]
theorem point_links_checked38388 : (cuts38388.take 1).map (fun c => (5035524097-1+2*2^10*c.k,108348844161559+c.lower,108349229357871+c.upper)) = pointBounds38388 := by
 decide +kernel
def cuts38389 : List PrefixCut := [⟨56,293005481,293005655⟩,
⟨64,332579150,332579348⟩]
theorem checked38389 : checkPrefixCuts (2^48) 5035655169 10 Manual.Count131072.C038389.packed 64 cuts38389 = true := by
 decide +kernel
def pointBounds38389 : List (Nat × Nat × Nat) := [(5035769856,108349458407708,108349843604388)]
theorem point_links_checked38389 : (cuts38389.take 1).map (fun c => (5035655169-1+2*2^10*c.k,108349165402227+c.lower,108349550598733+c.upper)) = pointBounds38389 := by
 decide +kernel
def cuts38390 : List PrefixCut := [⟨64,330781861,330782060⟩]
theorem checked38390 : checkPrefixCuts (2^48) 5035786241 10 Manual.Count131072.C038390.packed 64 cuts38390 = true := by
 decide +kernel
def cuts38391 : List PrefixCut := [⟨5,24369528,24369543⟩,
⟨64,324345572,324345768⟩]
theorem checked38391 : checkPrefixCuts (2^48) 5035917313 10 Manual.Count131072.C038391.packed 64 cuts38391 = true := by
 decide +kernel
def pointBounds38391 : List (Nat × Nat × Nat) := [(5035927552,108349853132766,108350238329684)]
theorem point_links_checked38391 : (cuts38391.take 1).map (fun c => (5035917313-1+2*2^10*c.k,108349828763238+c.lower,108350213960141+c.upper)) = pointBounds38391 := by
 decide +kernel
def cuts38392 : List PrefixCut := [⟨18,92668620,92668678⟩,
⟨64,328361285,328361487⟩]
theorem checked38392 : checkPrefixCuts (2^48) 5036048385 10 Manual.Count131072.C038392.packed 64 cuts38392 = true := by
 decide +kernel
def pointBounds38392 : List (Nat × Nat × Nat) := [(5036085248,108350245777430,108350630974587)]
theorem point_links_checked38392 : (cuts38392.take 1).map (fun c => (5036048385-1+2*2^10*c.k,108350153108810+c.lower,108350538305909+c.upper)) = pointBounds38392 := by
 decide +kernel
def cuts38393 : List PrefixCut := [⟨31,156604354,156604449⟩,
⟨64,326340703,326340900⟩]
theorem checked38393 : checkPrefixCuts (2^48) 5036179457 10 Manual.Count131072.C038393.packed 64 cuts38393 = true := by
 decide +kernel
def pointBounds38393 : List (Nat × Nat × Nat) := [(5036242944,108350638074449,108351023271845)]
theorem point_links_checked38393 : (cuts38393.take 1).map (fun c => (5036179457-1+2*2^10*c.k,108350481470095+c.lower,108350866667396+c.upper)) = pointBounds38393 := by
 decide +kernel
def cuts38394 : List PrefixCut := [⟨44,219418666,219418801⟩,
⟨64,322643575,322643772⟩]
theorem checked38394 : checkPrefixCuts (2^48) 5036310529 10 Manual.Count131072.C038394.packed 64 cuts38394 = true := by
 decide +kernel
def pointBounds38394 : List (Nat × Nat × Nat) := [(5036400640,108351027229464,108351412427097)]
theorem point_links_checked38394 : (cuts38394.take 1).map (fun c => (5036310529-1+2*2^10*c.k,108350807810798+c.lower,108351193008296+c.upper)) = pointBounds38394 := by
 decide +kernel
def cuts38395 : List PrefixCut := [⟨57,293518505,293518682⟩,
⟨64,329341608,329341807⟩]
theorem checked38395 : checkPrefixCuts (2^48) 5036441601 10 Manual.Count131072.C038395.packed 64 cuts38395 = true := by
 decide +kernel
def pointBounds38395 : List (Nat × Nat × Nat) := [(5036558336,108351423972878,108351809170750)]
theorem point_links_checked38395 : (cuts38395.take 1).map (fun c => (5036441601-1+2*2^10*c.k,108351130454373+c.lower,108351515652068+c.upper)) = pointBounds38395 := by
 decide +kernel
def cuts38396 : List PrefixCut := [⟨64,323520971,323521170⟩]
theorem checked38396 : checkPrefixCuts (2^48) 5036572673 10 Manual.Count131072.C038396.packed 64 cuts38396 = true := by
 decide +kernel
def cuts38397 : List PrefixCut := [⟨6,30065956,30065973⟩,
⟨64,329100932,329101130⟩]
theorem checked38397 : checkPrefixCuts (2^48) 5036703745 10 Manual.Count131072.C038397.packed 64 cuts38397 = true := by
 decide +kernel
def pointBounds38397 : List (Nat × Nat × Nat) := [(5036716032,108351813382908,108352198581018)]
theorem point_links_checked38397 : (cuts38397.take 1).map (fun c => (5036703745-1+2*2^10*c.k,108351783316952+c.lower,108352168515045+c.upper)) = pointBounds38397 := by
 decide +kernel
def cuts38398 : List PrefixCut := [⟨19,98465981,98466038⟩,
⟨64,328924797,328924996⟩]
theorem checked38398 : checkPrefixCuts (2^48) 5036834817 10 Manual.Count131072.C038398.packed 64 cuts38398 = true := by
 decide +kernel
def pointBounds38398 : List (Nat × Nat × Nat) := [(5036873728,108352210883865,108352596082213)]
theorem point_links_checked38398 : (cuts38398.take 1).map (fun c => (5036834817-1+2*2^10*c.k,108352112417884+c.lower,108352497616175+c.upper)) = pointBounds38398 := by
 decide +kernel
def cuts38399 : List PrefixCut := [⟨32,162335668,162335764⟩,
⟨64,325898602,325898798⟩]
theorem checked38399 : checkPrefixCuts (2^48) 5036965889 10 Manual.Count131072.C038399.packed 64 cuts38399 = true := by
 decide +kernel
def pointBounds38399 : List (Nat × Nat × Nat) := [(5037031424,108352603678349,108352988876935)]
theorem point_links_checked38399 : (cuts38399.take 1).map (fun c => (5036965889-1+2*2^10*c.k,108352441342681+c.lower,108352826541171+c.upper)) = pointBounds38399 := by
 decide +kernel
def cuts38400 : List PrefixCut := [⟨45,231119139,231119276⟩,
⟨64,330975169,330975366⟩]
theorem checked38400 : checkPrefixCuts (2^48) 5037096961 10 Manual.Count131072.C038400.packed 64 cuts38400 = true := by
 decide +kernel
def pointBounds38400 : List (Nat × Nat × Nat) := [(5037189120,108352998360422,108353383559245)]
theorem point_links_checked38400 : (cuts38400.take 1).map (fun c => (5037096961-1+2*2^10*c.k,108352767241283+c.lower,108353152439969+c.upper)) = pointBounds38400 := by
 decide +kernel
def cuts38401 : List PrefixCut := [⟨58,297998775,297998956⟩,
⟨64,328340279,328340478⟩]
theorem checked38401 : checkPrefixCuts (2^48) 5037228033 10 Manual.Count131072.C038401.packed 64 cuts38401 = true := by
 decide +kernel
def pointBounds38401 : List (Nat × Nat × Nat) := [(5037346816,108353396215227,108353781414291)]
theorem point_links_checked38401 : (cuts38401.take 1).map (fun c => (5037228033-1+2*2^10*c.k,108353098216452+c.lower,108353483415335+c.upper)) = pointBounds38401 := by
 decide +kernel
def cuts38402 : List PrefixCut := [⟨64,327996475,327996669⟩]
theorem checked38402 : checkPrefixCuts (2^48) 5037359105 10 Manual.Count131072.C038402.packed 64 cuts38402 = true := by
 decide +kernel
def cuts38403 : List PrefixCut := [⟨7,35537096,35537118⟩,
⟨64,327038067,327038267⟩]
theorem checked38403 : checkPrefixCuts (2^48) 5037490177 10 Manual.Count131072.C038403.packed 64 cuts38403 = true := by
 decide +kernel
def pointBounds38403 : List (Nat × Nat × Nat) := [(5037504512,108353790090302,108354175289600)]
theorem point_links_checked38403 : (cuts38403.take 1).map (fun c => (5037490177-1+2*2^10*c.k,108353754553206+c.lower,108354139752482+c.upper)) = pointBounds38403 := by
 decide +kernel
def cuts38404 : List PrefixCut := [⟨20,103255774,103255835⟩,
⟨64,327253059,327253253⟩]
theorem checked38404 : checkPrefixCuts (2^48) 5037621249 10 Manual.Count131072.C038404.packed 64 cuts38404 = true := by
 decide +kernel
def pointBounds38404 : List (Nat × Nat × Nat) := [(5037662208,108354184847047,108354570046584)]
theorem point_links_checked38404 : (cuts38404.take 1).map (fun c => (5037621249-1+2*2^10*c.k,108354081591273+c.lower,108354466790749+c.upper)) = pointBounds38404 := by
 decide +kernel
def cuts38405 : List PrefixCut := [⟨33,170802948,170803051⟩,
⟨64,329591198,329591394⟩]
theorem checked38405 : checkPrefixCuts (2^48) 5037752321 10 Manual.Count131072.C038405.packed 64 cuts38405 = true := by
 decide +kernel
def pointBounds38405 : List (Nat × Nat × Nat) := [(5037819904,108354579647280,108354964847053)]
theorem point_links_checked38405 : (cuts38405.take 1).map (fun c => (5037752321-1+2*2^10*c.k,108354408844332+c.lower,108354794044002+c.upper)) = pointBounds38405 := by
 decide +kernel
def cuts38406 : List PrefixCut := [⟨46,231529976,231530116⟩,
⟨64,324945299,324945495⟩]
theorem checked38406 : checkPrefixCuts (2^48) 5037883393 10 Manual.Count131072.C038406.packed 64 cuts38406 = true := by
 decide +kernel
def pointBounds38406 : List (Nat × Nat × Nat) := [(5037977600,108354969965506,108355355165512)]
theorem point_links_checked38406 : (cuts38406.take 1).map (fun c => (5037883393-1+2*2^10*c.k,108354738435530+c.lower,108355123635396+c.upper)) = pointBounds38406 := by
 decide +kernel
def cuts38407 : List PrefixCut := [⟨59,299684148,299684329⟩,
⟨64,325327932,325328128⟩]
theorem checked38407 : checkPrefixCuts (2^48) 5038014465 10 Manual.Count131072.C038407.packed 64 cuts38407 = true := by
 decide +kernel
def pointBounds38407 : List (Nat × Nat × Nat) := [(5038135296,108355363064977,108355748265220)]
theorem point_links_checked38407 : (cuts38407.take 1).map (fun c => (5038014465-1+2*2^10*c.k,108355063380829+c.lower,108355448580891+c.upper)) = pointBounds38407 := by
 decide +kernel
def cuts38408 : List PrefixCut := [⟨64,329006848,329007044⟩]
theorem checked38408 : checkPrefixCuts (2^48) 5038145537 10 Manual.Count131072.C038408.packed 64 cuts38408 = true := by
 decide +kernel
def cuts38409 : List PrefixCut := [⟨8,40168521,40168545⟩,
⟨64,331679803,331680006⟩]
theorem checked38409 : checkPrefixCuts (2^48) 5038276609 10 Manual.Count131072.C038409.packed 64 cuts38409 = true := by
 decide +kernel
def pointBounds38409 : List (Nat × Nat × Nat) := [(5038292992,108355757884130,108356143084608)]
theorem point_links_checked38409 : (cuts38409.take 1).map (fun c => (5038276609-1+2*2^10*c.k,108355717715609+c.lower,108356102916063+c.upper)) = pointBounds38409 := by
 decide +kernel
def cuts38410 : List PrefixCut := [⟨21,107820620,107820683⟩,
⟨64,326252299,326252496⟩]
theorem checked38410 : checkPrefixCuts (2^48) 5038407681 10 Manual.Count131072.C038410.packed 64 cuts38410 = true := by
 decide +kernel
def pointBounds38410 : List (Nat × Nat × Nat) := [(5038450688,108356157216032,108356542416752)]
theorem point_links_checked38410 : (cuts38410.take 1).map (fun c => (5038407681-1+2*2^10*c.k,108356049395412+c.lower,108356434596069+c.upper)) = pointBounds38410 := by
 decide +kernel
def cuts38411 : List PrefixCut := [⟨34,176977156,176977261⟩,
⟨64,330936355,330936551⟩]
theorem checked38411 : checkPrefixCuts (2^48) 5038538753 10 Manual.Count131072.C038411.packed 64 cuts38411 = true := by
 decide +kernel
def pointBounds38411 : List (Nat × Nat × Nat) := [(5038608384,108356552624867,108356937825826)]
theorem point_links_checked38411 : (cuts38411.take 1).map (fun c => (5038538753-1+2*2^10*c.k,108356375647711+c.lower,108356760848565+c.upper)) = pointBounds38411 := by
 decide +kernel
def cuts38412 : List PrefixCut := [⟨47,243280753,243280896⟩,
⟨64,327408433,327408627⟩]
theorem checked38412 : checkPrefixCuts (2^48) 5038669825 10 Manual.Count131072.C038412.packed 64 cuts38412 = true := by
 decide +kernel
def pointBounds38412 : List (Nat × Nat × Nat) := [(5038766080,108356949864819,108357335066012)]
theorem point_links_checked38412 : (cuts38412.take 1).map (fun c => (5038669825-1+2*2^10*c.k,108356706584066+c.lower,108357091785116+c.upper)) = pointBounds38412 := by
 decide +kernel
def cuts38413 : List PrefixCut := [⟨60,304217893,304218080⟩,
⟨64,324327519,324327719⟩]
theorem checked38413 : checkPrefixCuts (2^48) 5038800897 10 Manual.Count131072.C038413.packed 64 cuts38413 = true := by
 decide +kernel
def pointBounds38413 : List (Nat × Nat × Nat) := [(5038923776,108357338210392,108357723411823)]
theorem point_links_checked38413 : (cuts38413.take 1).map (fun c => (5038800897-1+2*2^10*c.k,108357033992499+c.lower,108357419193743+c.upper)) = pointBounds38413 := by
 decide +kernel
def cuts38414 : List PrefixCut := [⟨64,328787852,328788048⟩]
theorem checked38414 : checkPrefixCuts (2^48) 5038931969 10 Manual.Count131072.C038414.packed 64 cuts38414 = true := by
 decide +kernel
def cuts38415 : List PrefixCut := [⟨9,46083239,46083268⟩,
⟨64,324757564,324757760⟩]
theorem checked38415 : checkPrefixCuts (2^48) 5039063041 10 Manual.Count131072.C038415.packed 64 cuts38415 = true := by
 decide +kernel
def pointBounds38415 : List (Nat × Nat × Nat) := [(5039081472,108357733191109,108358118392778)]
theorem point_links_checked38415 : (cuts38415.take 1).map (fun c => (5039063041-1+2*2^10*c.k,108357687107870+c.lower,108358072309510+c.upper)) = pointBounds38415 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000262
