import PlattAssemblyKernel
import PlattCertificates.Count131072.C042272
import PlattCertificates.Count131072.C042273
import PlattCertificates.Count131072.C042274
import PlattCertificates.Count131072.C042275
import PlattCertificates.Count131072.C042276
import PlattCertificates.Count131072.C042277
import PlattCertificates.Count131072.C042278
import PlattCertificates.Count131072.C042279
import PlattCertificates.Count131072.C042280
import PlattCertificates.Count131072.C042281
import PlattCertificates.Count131072.C042282
import PlattCertificates.Count131072.C042283
import PlattCertificates.Count131072.C042284
import PlattCertificates.Count131072.C042285
import PlattCertificates.Count131072.C042286
import PlattCertificates.Count131072.C042287
import PlattCertificates.Count131072.C042288
import PlattCertificates.Count131072.C042289
import PlattCertificates.Count131072.C042290
import PlattCertificates.Count131072.C042291
import PlattCertificates.Count131072.C042292
import PlattCertificates.Count131072.C042293
import PlattCertificates.Count131072.C042294
import PlattCertificates.Count131072.C042295
import PlattCertificates.Count131072.C042296
import PlattCertificates.Count131072.C042297
import PlattCertificates.Count131072.C042298
import PlattCertificates.Count131072.C042299
import PlattCertificates.Count131072.C042300
import PlattCertificates.Count131072.C042301
import PlattCertificates.Count131072.C042302
import PlattCertificates.Count131072.C042303
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000071
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42272 : List PrefixCut := [⟨64,294588786,294588959⟩]
theorem checked42272 : checkPrefixCuts (2^48) 5544607745 10 Manual.Count131072.C042272.packed 64 cuts42272 = true := by
 decide +kernel
def cuts42273 : List PrefixCut := [⟨5,23909972,23909986⟩,
⟨64,297018542,297018715⟩]
theorem checked42273 : checkPrefixCuts (2^48) 5544738817 10 Manual.Count131072.C042273.packed 64 cuts42273 = true := by
 decide +kernel
def pointBounds42273 : List (Nat × Nat × Nat) := [(5544749056,109559937295010,109560323209690)]
theorem point_links_checked42273 : (cuts42273.take 1).map (fun c => (5544738817-1+2*2^10*c.k,109559913385038+c.lower,109560299299704+c.upper)) = pointBounds42273 := by
 decide +kernel
def cuts42274 : List PrefixCut := [⟨26,118683603,118683673⟩,
⟨64,299143488,299143664⟩]
theorem checked42274 : checkPrefixCuts (2^48) 5544869889 10 Manual.Count131072.C042274.packed 64 cuts42274 = true := by
 decide +kernel
def pointBounds42274 : List (Nat × Nat × Nat) := [(5544923136,109560329087183,109560715002092)]
theorem point_links_checked42274 : (cuts42274.take 1).map (fun c => (5544869889-1+2*2^10*c.k,109560210403580+c.lower,109560596318419+c.upper)) = pointBounds42274 := by
 decide +kernel
def cuts42275 : List PrefixCut := [⟨47,220761675,220761805⟩,
⟨64,296953751,296953926⟩]
theorem checked42275 : checkPrefixCuts (2^48) 5545000961 10 Manual.Count131072.C042275.packed 64 cuts42275 = true := by
 decide +kernel
def pointBounds42275 : List (Nat × Nat × Nat) := [(5545097216,109560730308743,109561116223888)]
theorem point_links_checked42275 : (cuts42275.take 1).map (fun c => (5545000961-1+2*2^10*c.k,109560509547068+c.lower,109560895462083+c.upper)) = pointBounds42275 := by
 decide +kernel
def cuts42276 : List PrefixCut := [⟨64,293698057,293698226⟩]
theorem checked42276 : checkPrefixCuts (2^48) 5545132033 10 Manual.Count131072.C042276.packed 64 cuts42276 = true := by
 decide +kernel
def cuts42277 : List PrefixCut := [⟨4,19745440,19745451⟩,
⟨64,298157887,298158058⟩]
theorem checked42277 : checkPrefixCuts (2^48) 5545263105 10 Manual.Count131072.C042277.packed 64 cuts42277 = true := by
 decide +kernel
def pointBounds42277 : List (Nat × Nat × Nat) := [(5545271296,109561119944316,109561505859686)]
theorem point_links_checked42277 : (cuts42277.take 1).map (fun c => (5545263105-1+2*2^10*c.k,109561100198876+c.lower,109561486114235+c.upper)) = pointBounds42277 := by
 decide +kernel
def cuts42278 : List PrefixCut := [⟨25,117657244,117657309⟩,
⟨64,297440270,297440439⟩]
theorem checked42278 : checkPrefixCuts (2^48) 5545394177 10 Manual.Count131072.C042278.packed 64 cuts42278 = true := by
 decide +kernel
def pointBounds42278 : List (Nat × Nat × Nat) := [(5545445376,109561516014007,109561901929602)]
theorem point_links_checked42278 : (cuts42278.take 1).map (fun c => (5545394177-1+2*2^10*c.k,109561398356763+c.lower,109561784272293+c.upper)) = pointBounds42278 := by
 decide +kernel
def cuts42279 : List PrefixCut := [⟨46,208660747,208660873⟩,
⟨64,291799225,291799397⟩]
theorem checked42279 : checkPrefixCuts (2^48) 5545525249 10 Manual.Count131072.C042279.packed 64 cuts42279 = true := by
 decide +kernel
def pointBounds42279 : List (Nat × Nat × Nat) := [(5545619456,109561904457780,109562290373605)]
theorem point_links_checked42279 : (cuts42279.take 1).map (fun c => (5545525249-1+2*2^10*c.k,109561695797033+c.lower,109562081712732+c.upper)) = pointBounds42279 := by
 decide +kernel
def cuts42280 : List PrefixCut := [⟨64,297121663,297121838⟩]
theorem checked42280 : checkPrefixCuts (2^48) 5545656321 10 Manual.Count131072.C042280.packed 64 cuts42280 = true := by
 decide +kernel
def cuts42281 : List PrefixCut := [⟨3,13602258,13602266⟩,
⟨64,296708593,296708769⟩]
theorem checked42281 : checkPrefixCuts (2^48) 5545787393 10 Manual.Count131072.C042281.packed 64 cuts42281 = true := by
 decide +kernel
def pointBounds42281 : List (Nat × Nat × Nat) := [(5545793536,109562298320179,109562684236233)]
theorem point_links_checked42281 : (cuts42281.take 1).map (fun c => (5545787393-1+2*2^10*c.k,109562284717921+c.lower,109562670633967+c.upper)) = pointBounds42281 := by
 decide +kernel
def cuts42282 : List PrefixCut := [⟨24,110388413,110388480⟩,
⟨64,294468433,294468608⟩]
theorem checked42282 : checkPrefixCuts (2^48) 5545918465 10 Manual.Count131072.C042282.packed 64 cuts42282 = true := by
 decide +kernel
def pointBounds42282 : List (Nat × Nat × Nat) := [(5545967616,109562691814927,109563077731216)]
theorem point_links_checked42282 : (cuts42282.take 1).map (fun c => (5545918465-1+2*2^10*c.k,109562581426514+c.lower,109562967342736+c.upper)) = pointBounds42282 := by
 decide +kernel
def cuts42283 : List PrefixCut := [⟨45,207930546,207930667⟩,
⟨64,295527288,295527458⟩]
theorem checked42283 : checkPrefixCuts (2^48) 5546049537 10 Manual.Count131072.C042283.packed 64 cuts42283 = true := by
 decide +kernel
def pointBounds42283 : List (Nat × Nat × Nat) := [(5546141696,109563083825493,109563469742011)]
theorem point_links_checked42283 : (cuts42283.take 1).map (fun c => (5546049537-1+2*2^10*c.k,109562875894947+c.lower,109563261811344+c.upper)) = pointBounds42283 := by
 decide +kernel
def cuts42284 : List PrefixCut := [⟨64,297144286,297144454⟩]
theorem checked42284 : checkPrefixCuts (2^48) 5546180609 10 Manual.Count131072.C042284.packed 64 cuts42284 = true := by
 decide +kernel
def cuts42285 : List PrefixCut := [⟨2,10200731,10200737⟩,
⟨64,294346085,294346256⟩]
theorem checked42285 : checkPrefixCuts (2^48) 5546311681 10 Manual.Count131072.C042285.packed 64 cuts42285 = true := by
 decide +kernel
def pointBounds42285 : List (Nat × Nat × Nat) := [(5546315776,109563478767252,109563864683993)]
theorem point_links_checked42285 : (cuts42285.take 1).map (fun c => (5546311681-1+2*2^10*c.k,109563468566521+c.lower,109563854483256+c.upper)) = pointBounds42285 := by
 decide +kernel
def cuts42286 : List PrefixCut := [⟨23,104541923,104541986⟩,
⟨64,293070417,293070591⟩]
theorem checked42286 : checkPrefixCuts (2^48) 5546442753 10 Manual.Count131072.C042286.packed 64 cuts42286 = true := by
 decide +kernel
def pointBounds42286 : List (Nat × Nat × Nat) := [(5546489856,109563867454529,109564253371498)]
theorem point_links_checked42286 : (cuts42286.take 1).map (fun c => (5546442753-1+2*2^10*c.k,109563762912606+c.lower,109564148829512+c.upper)) = pointBounds42286 := by
 decide +kernel
def cuts42287 : List PrefixCut := [⟨44,206134760,206134879⟩,
⟨64,299203865,299204039⟩]
theorem checked42287 : checkPrefixCuts (2^48) 5546573825 10 Manual.Count131072.C042287.packed 64 cuts42287 = true := by
 decide +kernel
def pointBounds42287 : List (Nat × Nat × Nat) := [(5546663936,109564262117783,109564648034982)]
theorem point_links_checked42287 : (cuts42287.take 1).map (fun c => (5546573825-1+2*2^10*c.k,109564055983023+c.lower,109564441900103+c.upper)) = pointBounds42287 := by
 decide +kernel
def cuts42288 : List PrefixCut := [⟨64,293868471,293868644⟩]
theorem checked42288 : checkPrefixCuts (2^48) 5546704897 10 Manual.Count131072.C042288.packed 64 cuts42288 = true := by
 decide +kernel
def cuts42289 : List PrefixCut := [⟨1,4770041,4770044⟩,
⟨64,293963033,293963206⟩]
theorem checked42289 : checkPrefixCuts (2^48) 5546835969 10 Manual.Count131072.C042289.packed 64 cuts42289 = true := by
 decide +kernel
def pointBounds42289 : List (Nat × Nat × Nat) := [(5546838016,109564653825400,109565039742830)]
theorem point_links_checked42289 : (cuts42289.take 1).map (fun c => (5546835969-1+2*2^10*c.k,109564649055359+c.lower,109565034972786+c.upper)) = pointBounds42289 := by
 decide +kernel
def cuts42290 : List PrefixCut := [⟨22,102705294,102705354⟩,
⟨64,298725985,298726155⟩]
theorem checked42290 : checkPrefixCuts (2^48) 5546967041 10 Manual.Count131072.C042290.packed 64 cuts42290 = true := by
 decide +kernel
def pointBounds42290 : List (Nat × Nat × Nat) := [(5547012096,109565045723686,109565431641346)]
theorem point_links_checked42290 : (cuts42290.take 1).map (fun c => (5546967041-1+2*2^10*c.k,109564943018392+c.lower,109565328935992+c.upper)) = pointBounds42290 := by
 decide +kernel
def cuts42291 : List PrefixCut := [⟨43,199569578,199569696⟩,
⟨64,298718917,298719094⟩]
theorem checked42291 : checkPrefixCuts (2^48) 5547098113 10 Manual.Count131072.C042291.packed 64 cuts42291 = true := by
 decide +kernel
def pointBounds42291 : List (Nat × Nat × Nat) := [(5547186176,109565441313955,109565827231843)]
theorem point_links_checked42291 : (cuts42291.take 1).map (fun c => (5547098113-1+2*2^10*c.k,109565241744377+c.lower,109565627662147+c.upper)) = pointBounds42291 := by
 decide +kernel
def cuts42292 : List PrefixCut := [⟨64,297392580,297392747⟩]
theorem checked42292 : checkPrefixCuts (2^48) 5547229185 10 Manual.Count131072.C042292.packed 64 cuts42292 = true := by
 decide +kernel
def pointBounds42292 : List (Nat × Nat × Nat) := [(5547360256,109565837855874,109566223773988)]
theorem point_links_checked42292 : (cuts42292.take 1).map (fun c => (5547229185-1+2*2^10*c.k,109565540463294+c.lower,109565926381241+c.upper)) = pointBounds42292 := by
 decide +kernel
def cuts42293 : List PrefixCut := [⟨64,293580058,293580222⟩]
theorem checked42293 : checkPrefixCuts (2^48) 5547360257 10 Manual.Count131072.C042293.packed 64 cuts42293 = true := by
 decide +kernel
def cuts42294 : List PrefixCut := [⟨21,94729596,94729649⟩,
⟨64,292000247,292000414⟩]
theorem checked42294 : checkPrefixCuts (2^48) 5547491329 10 Manual.Count131072.C042294.packed 64 cuts42294 = true := by
 decide +kernel
def pointBounds42294 : List (Nat × Nat × Nat) := [(5547534336,109566226165528,109566612083859)]
theorem point_links_checked42294 : (cuts42294.take 1).map (fun c => (5547491329-1+2*2^10*c.k,109566131435932+c.lower,109566517354210+c.upper)) = pointBounds42294 := by
 decide +kernel
def cuts42295 : List PrefixCut := [⟨42,195796165,195796277⟩,
⟨64,296458253,296458424⟩]
theorem checked42295 : checkPrefixCuts (2^48) 5547622401 10 Manual.Count131072.C042295.packed 64 cuts42295 = true := by
 decide +kernel
def pointBounds42295 : List (Nat × Nat × Nat) := [(5547708416,109566619232344,109567005150901)]
theorem point_links_checked42295 : (cuts42295.take 1).map (fun c => (5547622401-1+2*2^10*c.k,109566423436179+c.lower,109566809354624+c.upper)) = pointBounds42295 := by
 decide +kernel
def cuts42296 : List PrefixCut := [⟨63,290210762,290210928⟩,
⟨64,294929168,294929336⟩]
theorem checked42296 : checkPrefixCuts (2^48) 5547753473 10 Manual.Count131072.C042296.packed 64 cuts42296 = true := by
 decide +kernel
def pointBounds42296 : List (Nat × Nat × Nat) := [(5547882496,109567010105194,109567396023976)]
theorem point_links_checked42296 : (cuts42296.take 1).map (fun c => (5547753473-1+2*2^10*c.k,109566719894432+c.lower,109567105813048+c.upper)) = pointBounds42296 := by
 decide +kernel
def cuts42297 : List PrefixCut := [⟨64,294871463,294871640⟩]
theorem checked42297 : checkPrefixCuts (2^48) 5547884545 10 Manual.Count131072.C042297.packed 64 cuts42297 = true := by
 decide +kernel
def cuts42298 : List PrefixCut := [⟨20,94974329,94974383⟩,
⟨64,303184816,303184989⟩]
theorem checked42298 : checkPrefixCuts (2^48) 5548015617 10 Manual.Count131072.C042298.packed 64 cuts42298 = true := by
 decide +kernel
def pointBounds42298 : List (Nat × Nat × Nat) := [(5548056576,109567404669392,109567790588407)]
theorem point_links_checked42298 : (cuts42298.take 1).map (fun c => (5548015617-1+2*2^10*c.k,109567309695063+c.lower,109567695614024+c.upper)) = pointBounds42298 := by
 decide +kernel
def cuts42299 : List PrefixCut := [⟨41,189385383,189385493⟩,
⟨64,293842886,293843057⟩]
theorem checked42299 : checkPrefixCuts (2^48) 5548146689 10 Manual.Count131072.C042299.packed 64 cuts42299 = true := by
 decide +kernel
def pointBounds42299 : List (Nat × Nat × Nat) := [(5548230656,109567802265262,109568188184506)]
theorem point_links_checked42299 : (cuts42299.take 1).map (fun c => (5548146689-1+2*2^10*c.k,109567612879879+c.lower,109567998799013+c.upper)) = pointBounds42299 := by
 decide +kernel
def cuts42300 : List PrefixCut := [⟨62,286987286,286987457⟩,
⟨64,296271015,296271192⟩]
theorem checked42300 : checkPrefixCuts (2^48) 5548277761 10 Manual.Count131072.C042300.packed 64 cuts42300 = true := by
 decide +kernel
def pointBounds42300 : List (Nat × Nat × Nat) := [(5548404736,109568193710051,109568579629527)]
theorem point_links_checked42300 : (cuts42300.take 1).map (fun c => (5548277761-1+2*2^10*c.k,109567906722765+c.lower,109568292642070+c.upper)) = pointBounds42300 := by
 decide +kernel
def cuts42301 : List PrefixCut := [⟨64,296314775,296314946⟩]
theorem checked42301 : checkPrefixCuts (2^48) 5548408833 10 Manual.Count131072.C042301.packed 64 cuts42301 = true := by
 decide +kernel
def cuts42302 : List PrefixCut := [⟨19,89334418,89334470⟩,
⟨64,299199331,299199498⟩]
theorem checked42302 : checkPrefixCuts (2^48) 5548539905 10 Manual.Count131072.C042302.packed 64 cuts42302 = true := by
 decide +kernel
def pointBounds42302 : List (Nat × Nat × Nat) := [(5548578816,109568588642973,109568974562678)]
theorem point_links_checked42302 : (cuts42302.take 1).map (fun c => (5548539905-1+2*2^10*c.k,109568499308555+c.lower,109568885228208+c.upper)) = pointBounds42302 := by
 decide +kernel
def cuts42303 : List PrefixCut := [⟨40,187084756,187084865⟩,
⟨64,298228421,298228596⟩]
theorem checked42303 : checkPrefixCuts (2^48) 5548670977 10 Manual.Count131072.C042303.packed 64 cuts42303 = true := by
 decide +kernel
def pointBounds42303 : List (Nat × Nat × Nat) := [(5548752896,109568985592642,109569371512571)]
theorem point_links_checked42303 : (cuts42303.take 1).map (fun c => (5548670977-1+2*2^10*c.k,109568798507886+c.lower,109569184427706+c.upper)) = pointBounds42303 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000071
