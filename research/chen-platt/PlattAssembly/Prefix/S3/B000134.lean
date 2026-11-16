import PlattAssemblyKernel
import PlattCertificates.Count131072.C024288
import PlattCertificates.Count131072.C024289
import PlattCertificates.Count131072.C024290
import PlattCertificates.Count131072.C024291
import PlattCertificates.Count131072.C024292
import PlattCertificates.Count131072.C024293
import PlattCertificates.Count131072.C024294
import PlattCertificates.Count131072.C024295
import PlattCertificates.Count131072.C024296
import PlattCertificates.Count131072.C024297
import PlattCertificates.Count131072.C024298
import PlattCertificates.Count131072.C024299
import PlattCertificates.Count131072.C024300
import PlattCertificates.Count131072.C024301
import PlattCertificates.Count131072.C024302
import PlattCertificates.Count131072.C024303
import PlattCertificates.Count131072.C024304
import PlattCertificates.Count131072.C024305
import PlattCertificates.Count131072.C024306
import PlattCertificates.Count131072.C024307
import PlattCertificates.Count131072.C024308
import PlattCertificates.Count131072.C024309
import PlattCertificates.Count131072.C024310
import PlattCertificates.Count131072.C024311
import PlattCertificates.Count131072.C024312
import PlattCertificates.Count131072.C024313
import PlattCertificates.Count131072.C024314
import PlattCertificates.Count131072.C024315
import PlattCertificates.Count131072.C024316
import PlattCertificates.Count131072.C024317
import PlattCertificates.Count131072.C024318
import PlattCertificates.Count131072.C024319
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000134
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24288 : List PrefixCut := [⟨58,240991291,240991424⟩,
⟨128,530280846,530281139⟩]
theorem checked24288 : checkPrefixCuts (2^48) 3187408897 9 Manual.Count131072.C024288.packed 128 cuts24288 = true := by
 decide +kernel
def pointBounds24288 : List (Nat × Nat × Nat) := [(3187468288,102527336674257,102527718482039)]
theorem point_links_checked24288 : (cuts24288.take 1).map (fun c => (3187408897-1+2*2^9*c.k,102527095682966+c.lower,102527477490615+c.upper)) = pointBounds24288 := by
 decide +kernel
def cuts24289 : List PrefixCut := [⟨28,115855311,115855377⟩,
⟨126,522576903,522577197⟩,
⟨128,528934585,528934883⟩]
theorem checked24289 : checkPrefixCuts (2^48) 3187539969 9 Manual.Count131072.C024289.packed 128 cuts24289 = true := by
 decide +kernel
def pointBounds24289 : List (Nat × Nat × Nat) := [(3187568640,102527741819123,102528123627131),(3187668992,102528148540715,102528530348951)]
theorem point_links_checked24289 : (cuts24289.take 2).map (fun c => (3187539969-1+2*2^9*c.k,102527625963812+c.lower,102528007771754+c.upper)) = pointBounds24289 := by
 decide +kernel
def cuts24290 : List PrefixCut := [⟨96,399379834,399380057⟩,
⟨128,532268228,532268527⟩]
theorem checked24290 : checkPrefixCuts (2^48) 3187671041 9 Manual.Count131072.C024290.packed 128 cuts24290 = true := by
 decide +kernel
def pointBounds24290 : List (Nat × Nat × Nat) := [(3187769344,102528554278231,102528936086694)]
theorem point_links_checked24290 : (cuts24290.take 1).map (fun c => (3187671041-1+2*2^9*c.k,102528154898397+c.lower,102528536706637+c.upper)) = pointBounds24290 := by
 decide +kernel
def cuts24291 : List PrefixCut := [⟨66,270099096,270099246⟩,
⟨128,525535755,525536053⟩]
theorem checked24291 : checkPrefixCuts (2^48) 3187802113 9 Manual.Count131072.C024291.packed 128 cuts24291 = true := by
 decide +kernel
def pointBounds24291 : List (Nat × Nat × Nat) := [(3187869696,102528957265721,102529339074410)]
theorem point_links_checked24291 : (cuts24291.take 1).map (fun c => (3187802113-1+2*2^9*c.k,102528687166625+c.lower,102529068975164+c.upper)) = pointBounds24291 := by
 decide +kernel
def cuts24292 : List PrefixCut := [⟨36,146478652,146478741⟩,
⟨128,525072699,525073002⟩]
theorem checked24292 : checkPrefixCuts (2^48) 3187933185 9 Manual.Count131072.C024292.packed 128 cuts24292 = true := by
 decide +kernel
def pointBounds24292 : List (Nat × Nat × Nat) := [(3187970048,102529359181032,102529740989958)]
theorem point_links_checked24292 : (cuts24292.take 1).map (fun c => (3187933185-1+2*2^9*c.k,102529212702380+c.lower,102529594511217+c.upper)) = pointBounds24292 := by
 decide +kernel
def cuts24293 : List PrefixCut := [⟨6,23132018,23132030⟩,
⟨104,432173421,432173660⟩,
⟨128,531761075,531761372⟩]
theorem checked24293 : checkPrefixCuts (2^48) 3188064257 9 Manual.Count131072.C024293.packed 128 cuts24293 = true := by
 decide +kernel
def pointBounds24293 : List (Nat × Nat × Nat) := [(3188070400,102529760907097,102530142716249),(3188170752,102530169948500,102530551757879)]
theorem point_links_checked24293 : (cuts24293.take 2).map (fun c => (3188064257-1+2*2^9*c.k,102529737775079+c.lower,102530119584219+c.upper)) = pointBounds24293 := by
 decide +kernel
def cuts24294 : List PrefixCut := [⟨74,303702226,303702397⟩,
⟨128,527148327,527148623⟩]
theorem checked24294 : checkPrefixCuts (2^48) 3188195329 9 Manual.Count131072.C024294.packed 128 cuts24294 = true := by
 decide +kernel
def pointBounds24294 : List (Nat × Nat × Nat) := [(3188271104,102530573238380,102530955047988)]
theorem point_links_checked24294 : (cuts24294.take 1).map (fun c => (3188195329-1+2*2^9*c.k,102530269536154+c.lower,102530651345591+c.upper)) = pointBounds24294 := by
 decide +kernel
def cuts24295 : List PrefixCut := [⟨44,186275744,186275849⟩,
⟨128,530128383,530128685⟩]
theorem checked24295 : checkPrefixCuts (2^48) 3188326401 9 Manual.Count131072.C024295.packed 128 cuts24295 = true := by
 decide +kernel
def pointBounds24295 : List (Nat × Nat × Nat) := [(3188371456,102530982960225,102531364770063)]
theorem point_links_checked24295 : (cuts24295.take 1).map (fun c => (3188326401-1+2*2^9*c.k,102530796684481+c.lower,102531178494214+c.upper)) = pointBounds24295 := by
 decide +kernel
def cuts24296 : List PrefixCut := [⟨14,59411855,59411888⟩,
⟨112,461074730,461075002⟩,
⟨128,525692709,525693020⟩]
theorem checked24296 : checkPrefixCuts (2^48) 3188457473 9 Manual.Count131072.C024296.packed 128 cuts24296 = true := by
 decide +kernel
def pointBounds24296 : List (Nat × Nat × Nat) := [(3188471808,102531386224719,102531768034787),(3188572160,102531787887594,102532169697901)]
theorem point_links_checked24296 : (cuts24296.take 2).map (fun c => (3188457473-1+2*2^9*c.k,102531326812864+c.lower,102531708622899+c.upper)) = pointBounds24296 := by
 decide +kernel
def cuts24297 : List PrefixCut := [⟨82,340916288,340916478⟩,
⟨128,535116296,535116603⟩]
theorem checked24297 : checkPrefixCuts (2^48) 3188588545 9 Manual.Count131072.C024297.packed 128 cuts24297 = true := by
 decide +kernel
def pointBounds24297 : List (Nat × Nat × Nat) := [(3188672512,102532193421861,102532575232397)]
theorem point_links_checked24297 : (cuts24297.take 1).map (fun c => (3188588545-1+2*2^9*c.k,102531852505573+c.lower,102532234315919+c.upper)) = pointBounds24297 := by
 decide +kernel
def cuts24298 : List PrefixCut := [⟨52,212645628,212645751⟩,
⟨128,526973411,526973717⟩]
theorem checked24298 : checkPrefixCuts (2^48) 3188719617 9 Manual.Count131072.C024298.packed 128 cuts24298 = true := by
 decide +kernel
def pointBounds24298 : List (Nat × Nat × Nat) := [(3188772864,102532600267497,102532982078273)]
theorem point_links_checked24298 : (cuts24298.take 1).map (fun c => (3188719617-1+2*2^9*c.k,102532387621869+c.lower,102532769432522+c.upper)) = pointBounds24298 := by
 decide +kernel
def cuts24299 : List PrefixCut := [⟨22,93740757,93740808⟩,
⟨120,502767414,502767698⟩,
⟨128,535425438,535425740⟩]
theorem checked24299 : checkPrefixCuts (2^48) 3188850689 9 Manual.Count131072.C024299.packed 128 cuts24299 = true := by
 decide +kernel
def pointBounds24299 : List (Nat × Nat × Nat) := [(3188873216,102533008336037,102533390147047),(3188973568,102533417362694,102533799173937)]
theorem point_links_checked24299 : (cuts24299.take 2).map (fun c => (3188850689-1+2*2^9*c.k,102532914595280+c.lower,102533296406239+c.upper)) = pointBounds24299 := by
 decide +kernel
def cuts24300 : List PrefixCut := [⟨90,378738872,378739081⟩,
⟨128,538139552,538139848⟩]
theorem checked24300 : checkPrefixCuts (2^48) 3188981761 9 Manual.Count131072.C024300.packed 128 cuts24300 = true := by
 decide +kernel
def pointBounds24300 : List (Nat × Nat × Nat) := [(3189073920,102533828759590,102534210571060)]
theorem point_links_checked24300 : (cuts24300.take 1).map (fun c => (3188981761-1+2*2^9*c.k,102533450020718+c.lower,102533831831979+c.upper)) = pointBounds24300 := by
 decide +kernel
def cuts24301 : List PrefixCut := [⟨60,250394576,250394722⟩,
⟨128,531056700,531057007⟩]
theorem checked24301 : checkPrefixCuts (2^48) 3189112833 9 Manual.Count131072.C024301.packed 128 cuts24301 = true := by
 decide +kernel
def pointBounds24301 : List (Nat × Nat × Nat) := [(3189174272,102534238554846,102534620366549)]
theorem point_links_checked24301 : (cuts24301.take 1).map (fun c => (3189112833-1+2*2^9*c.k,102533988160270+c.lower,102534369971827+c.upper)) = pointBounds24301 := by
 decide +kernel
def cuts24302 : List PrefixCut := [⟨30,123383489,123383560⟩,
⟨128,523797921,523798214⟩]
theorem checked24302 : checkPrefixCuts (2^48) 3189243905 9 Manual.Count131072.C024302.packed 128 cuts24302 = true := by
 decide +kernel
def pointBounds24302 : List (Nat × Nat × Nat) := [(3189274624,102534642600459,102535024412394),(3189374976,102535043014891,102535424827048)]
theorem point_links_checked24302 : (cuts24302.take 2).map (fun c => (3189243905-1+2*2^9*c.k,102534519216970+c.lower,102534901028834+c.upper)) = pointBounds24302 := by
 decide +kernel
def cuts24303 : List PrefixCut := [⟨98,402961128,402961355⟩,
⟨128,527041655,527041951⟩]
theorem checked24303 : checkPrefixCuts (2^48) 3189374977 9 Manual.Count131072.C024303.packed 128 cuts24303 = true := by
 decide +kernel
def pointBounds24303 : List (Nat × Nat × Nat) := [(3189475328,102535445976019,102535827788403)]
theorem point_links_checked24303 : (cuts24303.take 1).map (fun c => (3189374977-1+2*2^9*c.k,102535043014891+c.lower,102535424827048+c.upper)) = pointBounds24303 := by
 decide +kernel
def cuts24304 : List PrefixCut := [⟨68,275690957,275691110⟩,
⟨128,526402219,526402515⟩]
theorem checked24304 : checkPrefixCuts (2^48) 3189506049 9 Manual.Count131072.C024304.packed 128 cuts24304 = true := by
 decide +kernel
def pointBounds24304 : List (Nat × Nat × Nat) := [(3189575680,102535845747503,102536227560109)]
theorem point_links_checked24304 : (cuts24304.take 1).map (fun c => (3189506049-1+2*2^9*c.k,102535570056546+c.lower,102535951868999+c.upper)) = pointBounds24304 := by
 decide +kernel
def cuts24305 : List PrefixCut := [⟨38,155666187,155666273⟩,
⟨128,520027070,520027360⟩]
theorem checked24305 : checkPrefixCuts (2^48) 3189637121 9 Manual.Count131072.C024305.packed 128 cuts24305 = true := by
 decide +kernel
def pointBounds24305 : List (Nat × Nat × Nat) := [(3189676032,102536252124952,102536633937787)]
theorem point_links_checked24305 : (cuts24305.take 1).map (fun c => (3189637121-1+2*2^9*c.k,102536096458765+c.lower,102536478271514+c.upper)) = pointBounds24305 := by
 decide +kernel
def cuts24306 : List PrefixCut := [⟨8,29914358,29914377⟩,
⟨106,430001104,430001351⟩,
⟨128,519211479,519211778⟩]
theorem checked24306 : checkPrefixCuts (2^48) 3189768193 9 Manual.Count131072.C024306.packed 128 cuts24306 = true := by
 decide +kernel
def pointBounds24306 : List (Nat × Nat × Nat) := [(3189776384,102536646400193,102537028213251),(3189876736,102537046486939,102537428300225)]
theorem point_links_checked24306 : (cuts24306.take 2).map (fun c => (3189768193-1+2*2^9*c.k,102536616485835+c.lower,102536998298874+c.upper)) = pointBounds24306 := by
 decide +kernel
def cuts24307 : List PrefixCut := [⟨76,318363980,318364163⟩,
⟨128,536749427,536749733⟩]
theorem checked24307 : checkPrefixCuts (2^48) 3189899265 9 Manual.Count131072.C024307.packed 128 cuts24307 = true := by
 decide +kernel
def pointBounds24307 : List (Nat × Nat × Nat) := [(3189977088,102537454061294,102537835874815)]
theorem point_links_checked24307 : (cuts24307.take 1).map (fun c => (3189899265-1+2*2^9*c.k,102537135697314+c.lower,102537517510652+c.upper)) = pointBounds24307 := by
 decide +kernel
def cuts24308 : List PrefixCut := [⟨46,191470308,191470415⟩,
⟨128,536550922,536551223⟩]
theorem checked24308 : checkPrefixCuts (2^48) 3190030337 9 Manual.Count131072.C024308.packed 128 cuts24308 = true := by
 decide +kernel
def pointBounds24308 : List (Nat × Nat × Nat) := [(3190077440,102537863917049,102538245730800)]
theorem point_links_checked24308 : (cuts24308.take 1).map (fun c => (3190030337-1+2*2^9*c.k,102537672446741+c.lower,102538054260385+c.upper)) = pointBounds24308 := by
 decide +kernel
def cuts24309 : List PrefixCut := [⟨16,66262201,66262237⟩,
⟨114,475650987,475651254⟩,
⟨128,533440821,533441119⟩]
theorem checked24309 : checkPrefixCuts (2^48) 3190161409 9 Manual.Count131072.C024309.packed 128 cuts24309 = true := by
 decide +kernel
def pointBounds24309 : List (Nat × Nat × Nat) := [(3190177792,102538275259864,102538657073845),(3190278144,102538684648650,102539066462862)]
theorem point_links_checked24309 : (cuts24309.take 2).map (fun c => (3190161409-1+2*2^9*c.k,102538208997663+c.lower,102538590811608+c.upper)) = pointBounds24309 := by
 decide +kernel
def cuts24310 : List PrefixCut := [⟨84,340822266,340822460⟩,
⟨128,524154966,524155262⟩]
theorem checked24310 : checkPrefixCuts (2^48) 3190292481 9 Manual.Count131072.C024310.packed 128 cuts24310 = true := by
 decide +kernel
def pointBounds24310 : List (Nat × Nat × Nat) := [(3190378496,102539083260750,102539465075187)]
theorem point_links_checked24310 : (cuts24310.take 1).map (fun c => (3190292481-1+2*2^9*c.k,102538742438484+c.lower,102539124252727+c.upper)) = pointBounds24310 := by
 decide +kernel
def cuts24311 : List PrefixCut := [⟨54,220207542,220207664⟩,
⟨128,523339545,523339834⟩]
theorem checked24311 : checkPrefixCuts (2^48) 3190423553 9 Manual.Count131072.C024311.packed 128 cuts24311 = true := by
 decide +kernel
def pointBounds24311 : List (Nat × Nat × Nat) := [(3190478848,102539486800992,102539868615653)]
theorem point_links_checked24311 : (cuts24311.take 1).map (fun c => (3190423553-1+2*2^9*c.k,102539266593450+c.lower,102539648407989+c.upper)) = pointBounds24311 := by
 decide +kernel
def cuts24312 : List PrefixCut := [⟨24,97748836,97748891⟩,
⟨122,497117306,497117590⟩,
⟨128,523759072,523759370⟩]
theorem checked24312 : checkPrefixCuts (2^48) 3190554625 9 Manual.Count131072.C024312.packed 128 cuts24312 = true := by
 decide +kernel
def pointBounds24312 : List (Nat × Nat × Nat) := [(3190579200,102539887681831,102540269496714),(3190679552,102540287050301,102540668865413)]
theorem point_links_checked24312 : (cuts24312.take 2).map (fun c => (3190554625-1+2*2^9*c.k,102539789932995+c.lower,102540171747823+c.upper)) = pointBounds24312 := by
 decide +kernel
def cuts24313 : List PrefixCut := [⟨92,380477233,380477451⟩,
⟨128,529118773,529119074⟩]
theorem checked24313 : checkPrefixCuts (2^48) 3190685697 9 Manual.Count131072.C024313.packed 128 cuts24313 = true := by
 decide +kernel
def pointBounds24313 : List (Nat × Nat × Nat) := [(3190779904,102540694169300,102541075984644)]
theorem point_links_checked24313 : (cuts24313.take 1).map (fun c => (3190685697-1+2*2^9*c.k,102540313692067+c.lower,102540695507193+c.upper)) = pointBounds24313 := by
 decide +kernel
def cuts24314 : List PrefixCut := [⟨62,257317835,257317982⟩,
⟨128,530773071,530773372⟩]
theorem checked24314 : checkPrefixCuts (2^48) 3190816769 9 Manual.Count131072.C024314.packed 128 cuts24314 = true := by
 decide +kernel
def pointBounds24314 : List (Nat × Nat × Nat) := [(3190880256,102541100128675,102541481944249)]
theorem point_links_checked24314 : (cuts24314.take 1).map (fun c => (3190816769-1+2*2^9*c.k,102540842810840+c.lower,102541224626267+c.upper)) = pointBounds24314 := by
 decide +kernel
def cuts24315 : List PrefixCut := [⟨32,131432889,131432963⟩,
⟨128,532780062,532780362⟩]
theorem checked24315 : checkPrefixCuts (2^48) 3190947841 9 Manual.Count131072.C024315.packed 128 cuts24315 = true := by
 decide +kernel
def pointBounds24315 : List (Nat × Nat × Nat) := [(3190980608,102541505016800,102541886832602)]
theorem point_links_checked24315 : (cuts24315.take 1).map (fun c => (3190947841-1+2*2^9*c.k,102541373583911+c.lower,102541755399639+c.upper)) = pointBounds24315 := by
 decide +kernel
def cuts24316 : List PrefixCut := [⟨2,9614540,9614544⟩,
⟨100,413683370,413683606⟩,
⟨128,528612636,528612936⟩]
theorem checked24316 : checkPrefixCuts (2^48) 3191078913 9 Manual.Count131072.C024316.packed 128 cuts24316 = true := by
 decide +kernel
def pointBounds24316 : List (Nat × Nat × Nat) := [(3191080960,102541915978513,102542297794545),(3191181312,102542320047343,102542701863607)]
theorem point_links_checked24316 : (cuts24316.take 2).map (fun c => (3191078913-1+2*2^9*c.k,102541906363973+c.lower,102542288180001+c.upper)) = pointBounds24316 := by
 decide +kernel
def cuts24317 : List PrefixCut := [⟨70,288068331,288068490⟩,
⟨128,527444171,527444465⟩]
theorem checked24317 : checkPrefixCuts (2^48) 3191209985 9 Manual.Count131072.C024317.packed 128 cuts24317 = true := by
 decide +kernel
def pointBounds24317 : List (Nat × Nat × Nat) := [(3191281664,102542723044940,102543104861427)]
theorem point_links_checked24317 : (cuts24317.take 1).map (fun c => (3191209985-1+2*2^9*c.k,102542434976609+c.lower,102542816792937+c.upper)) = pointBounds24317 := by
 decide +kernel
def cuts24318 : List PrefixCut := [⟨40,166255133,166255223⟩,
⟨128,528304641,528304940⟩]
theorem checked24318 : checkPrefixCuts (2^48) 3191341057 9 Manual.Count131072.C024318.packed 128 cuts24318 = true := by
 decide +kernel
def pointBounds24318 : List (Nat × Nat × Nat) := [(3191382016,102543128675913,102543510492625)]
theorem point_links_checked24318 : (cuts24318.take 1).map (fun c => (3191341057-1+2*2^9*c.k,102542962420780+c.lower,102543344237402+c.upper)) = pointBounds24318 := by
 decide +kernel
def cuts24319 : List PrefixCut := [⟨10,40129089,40129112⟩,
⟨108,442735998,442736251⟩,
⟨128,525725243,525725540⟩]
theorem checked24319 : checkPrefixCuts (2^48) 3191472129 9 Manual.Count131072.C024319.packed 128 cuts24319 = true := by
 decide +kernel
def pointBounds24319 : List (Nat × Nat × Nat) := [(3191482368,102543530854510,102543912671454),(3191582720,102543933461419,102544315278593)]
theorem point_links_checked24319 : (cuts24319.take 2).map (fun c => (3191472129-1+2*2^9*c.k,102543490725421+c.lower,102543872542342+c.upper)) = pointBounds24319 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000134
