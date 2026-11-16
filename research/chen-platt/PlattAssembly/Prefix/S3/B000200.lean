import PlattAssemblyKernel
import PlattCertificates.Count131072.C026400
import PlattCertificates.Count131072.C026401
import PlattCertificates.Count131072.C026402
import PlattCertificates.Count131072.C026403
import PlattCertificates.Count131072.C026404
import PlattCertificates.Count131072.C026405
import PlattCertificates.Count131072.C026406
import PlattCertificates.Count131072.C026407
import PlattCertificates.Count131072.C026408
import PlattCertificates.Count131072.C026409
import PlattCertificates.Count131072.C026410
import PlattCertificates.Count131072.C026411
import PlattCertificates.Count131072.C026412
import PlattCertificates.Count131072.C026413
import PlattCertificates.Count131072.C026414
import PlattCertificates.Count131072.C026415
import PlattCertificates.Count131072.C026416
import PlattCertificates.Count131072.C026417
import PlattCertificates.Count131072.C026418
import PlattCertificates.Count131072.C026419
import PlattCertificates.Count131072.C026420
import PlattCertificates.Count131072.C026421
import PlattCertificates.Count131072.C026422
import PlattCertificates.Count131072.C026423
import PlattCertificates.Count131072.C026424
import PlattCertificates.Count131072.C026425
import PlattCertificates.Count131072.C026426
import PlattCertificates.Count131072.C026427
import PlattCertificates.Count131072.C026428
import PlattCertificates.Count131072.C026429
import PlattCertificates.Count131072.C026430
import PlattCertificates.Count131072.C026431
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000200
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26400 : List PrefixCut := [⟨57,216371497,216371618⟩,
⟨128,488557349,488557621⟩]
theorem checked26400 : checkPrefixCuts (2^48) 3464232961 9 Manual.Count131072.C026400.packed 128 cuts26400 = true := by
 decide +kernel
def pointBounds26400 : List (Nat × Nat × Nat) := [(3464291328,103596533824329,103596916232136)]
theorem point_links_checked26400 : (cuts26400.take 1).map (fun c => (3464232961-1+2*2^9*c.k,103596317452832+c.lower,103596699860518+c.upper)) = pointBounds26400 := by
 decide +kernel
def cuts26401 : List PrefixCut := [⟨35,132028363,132028438⟩,
⟨128,493657381,493657651⟩]
theorem checked26401 : checkPrefixCuts (2^48) 3464364033 9 Manual.Count131072.C026401.packed 128 cuts26401 = true := by
 decide +kernel
def pointBounds26401 : List (Nat × Nat × Nat) := [(3464399872,103596938038544,103597320446577)]
theorem point_links_checked26401 : (cuts26401.take 1).map (fun c => (3464364033-1+2*2^9*c.k,103596806010181+c.lower,103597188418139+c.upper)) = pointBounds26401 := by
 decide +kernel
def cuts26402 : List PrefixCut := [⟨13,51509596,51509624⟩,
⟨119,446599121,446599367⟩,
⟨128,480071078,480071342⟩]
theorem checked26402 : checkPrefixCuts (2^48) 3464495105 9 Manual.Count131072.C026402.packed 128 cuts26402 = true := by
 decide +kernel
def pointBounds26402 : List (Nat × Nat × Nat) := [(3464508416,103597351177158,103597733585414),(3464616960,103597746266683,103598128675157)]
theorem point_links_checked26402 : (cuts26402.take 2).map (fun c => (3464495105-1+2*2^9*c.k,103597299667562+c.lower,103597682075790+c.upper)) = pointBounds26402 := by
 decide +kernel
def cuts26403 : List PrefixCut := [⟨97,367860836,367861043⟩,
⟨128,487202089,487202364⟩]
theorem checked26403 : checkPrefixCuts (2^48) 3464626177 9 Manual.Count131072.C026403.packed 128 cuts26403 = true := by
 decide +kernel
def pointBounds26403 : List (Nat × Nat × Nat) := [(3464725504,103598147599476,103598530008175)]
theorem point_links_checked26403 : (cuts26403.take 1).map (fun c => (3464626177-1+2*2^9*c.k,103597779738640+c.lower,103598162147132+c.upper)) = pointBounds26403 := by
 decide +kernel
def cuts26404 : List PrefixCut := [⟨75,285959602,285959763⟩,
⟨128,481172089,481172360⟩]
theorem checked26404 : checkPrefixCuts (2^48) 3464757249 9 Manual.Count131072.C026404.packed 128 cuts26404 = true := by
 decide +kernel
def pointBounds26404 : List (Nat × Nat × Nat) := [(3464834048,103598552900331,103598935309259)]
theorem point_links_checked26404 : (cuts26404.take 1).map (fun c => (3464757249-1+2*2^9*c.k,103598266940729+c.lower,103598649349496+c.upper)) = pointBounds26404 := by
 decide +kernel
def cuts26405 : List PrefixCut := [⟨53,197484036,197484147⟩,
⟨128,481235060,481235327⟩]
theorem checked26405 : checkPrefixCuts (2^48) 3464888321 9 Manual.Count131072.C026405.packed 128 cuts26405 = true := by
 decide +kernel
def pointBounds26405 : List (Nat × Nat × Nat) := [(3464942592,103598945596854,103599328006003)]
theorem point_links_checked26405 : (cuts26405.take 1).map (fun c => (3464888321-1+2*2^9*c.k,103598748112818+c.lower,103599130521856+c.upper)) = pointBounds26405 := by
 decide +kernel
def cuts26406 : List PrefixCut := [⟨31,119980991,119981061⟩,
⟨128,484384967,484385244⟩]
theorem checked26406 : checkPrefixCuts (2^48) 3465019393 9 Manual.Count131072.C026406.packed 128 cuts26406 = true := by
 decide +kernel
def pointBounds26406 : List (Nat × Nat × Nat) := [(3465051136,103599349328869,103599731738244)]
theorem point_links_checked26406 : (cuts26406.take 1).map (fun c => (3465019393-1+2*2^9*c.k,103599229347878+c.lower,103599611757183+c.upper)) = pointBounds26406 := by
 decide +kernel
def cuts26407 : List PrefixCut := [⟨9,34928943,34928962⟩,
⟨115,432705978,432706218⟩,
⟨128,480954991,480955257⟩]
theorem checked26407 : checkPrefixCuts (2^48) 3465150465 9 Manual.Count131072.C026407.packed 128 cuts26407 = true := by
 decide +kernel
def pointBounds26407 : List (Nat × Nat × Nat) := [(3465159680,103599748661788,103600131071389),(3465268224,103600146438823,103600528848645)]
theorem point_links_checked26407 : (cuts26407.take 2).map (fun c => (3465150465-1+2*2^9*c.k,103599713732845+c.lower,103600096142427+c.upper)) = pointBounds26407 := by
 decide +kernel
def cuts26408 : List PrefixCut := [⟨93,354632806,354633004⟩,
⟨128,489384230,489384501⟩]
theorem checked26408 : checkPrefixCuts (2^48) 3465281537 9 Manual.Count131072.C026408.packed 128 cuts26408 = true := by
 decide +kernel
def pointBounds26408 : List (Nat × Nat × Nat) := [(3465376768,103600549320642,103600931730688)]
theorem point_links_checked26408 : (cuts26408.take 1).map (fun c => (3465281537-1+2*2^9*c.k,103600194687836+c.lower,103600577097684+c.upper)) = pointBounds26408 := by
 decide +kernel
def cuts26409 : List PrefixCut := [⟨71,264787629,264787779⟩,
⟨128,480837310,480837583⟩]
theorem checked26409 : checkPrefixCuts (2^48) 3465412609 9 Manual.Count131072.C026409.packed 128 cuts26409 = true := by
 decide +kernel
def pointBounds26409 : List (Nat × Nat × Nat) := [(3465485312,103600948859695,103601331269964)]
theorem point_links_checked26409 : (cuts26409.take 1).map (fun c => (3465412609-1+2*2^9*c.k,103600684072066+c.lower,103601066482185+c.upper)) = pointBounds26409 := by
 decide +kernel
def cuts26410 : List PrefixCut := [⟨49,185344951,185345057⟩,
⟨128,482930900,482931168⟩]
theorem checked26410 : checkPrefixCuts (2^48) 3465543681 9 Manual.Count131072.C026410.packed 128 cuts26410 = true := by
 decide +kernel
def pointBounds26410 : List (Nat × Nat × Nat) := [(3465593856,103601350254327,103601732664825)]
theorem point_links_checked26410 : (cuts26410.take 1).map (fun c => (3465543681-1+2*2^9*c.k,103601164909376+c.lower,103601547319768+c.upper)) = pointBounds26410 := by
 decide +kernel
def cuts26411 : List PrefixCut := [⟨27,103146349,103146408⟩,
⟨128,487135928,487136198⟩]
theorem checked26411 : checkPrefixCuts (2^48) 3465674753 9 Manual.Count131072.C026411.packed 128 cuts26411 = true := by
 decide +kernel
def pointBounds26411 : List (Nat × Nat × Nat) := [(3465702400,103601750986625,103602133397344)]
theorem point_links_checked26411 : (cuts26411.take 1).map (fun c => (3465674753-1+2*2^9*c.k,103601647840276+c.lower,103602030250936+c.upper)) = pointBounds26411 := by
 decide +kernel
def cuts26412 : List PrefixCut := [⟨5,19166690,19166701⟩,
⟨111,424584318,424584551⟩,
⟨128,484112700,484112968⟩]
theorem checked26412 : checkPrefixCuts (2^48) 3465805825 9 Manual.Count131072.C026412.packed 128 cuts26412 = true := by
 decide +kernel
def pointBounds26412 : List (Nat × Nat × Nat) := [(3465810944,103602154142894,103602536553835),(3465919488,103602559560522,103602941971685)]
theorem point_links_checked26412 : (cuts26412.take 2).map (fun c => (3465805825-1+2*2^9*c.k,103602134976204+c.lower,103602517387134+c.upper)) = pointBounds26412 := by
 decide +kernel
def cuts26413 : List PrefixCut := [⟨89,336618385,336618571⟩,
⟨128,483931824,483932091⟩]
theorem checked26413 : checkPrefixCuts (2^48) 3465936897 9 Manual.Count131072.C026413.packed 128 cuts26413 = true := by
 decide +kernel
def pointBounds26413 : List (Nat × Nat × Nat) := [(3466028032,103602955707289,103603338118673)]
theorem point_links_checked26413 : (cuts26413.take 1).map (fun c => (3465936897-1+2*2^9*c.k,103602619088904+c.lower,103603001500102+c.upper)) = pointBounds26413 := by
 decide +kernel
def cuts26414 : List PrefixCut := [⟨67,250688795,250688934⟩,
⟨128,483263850,483264116⟩]
theorem checked26414 : checkPrefixCuts (2^48) 3466067969 9 Manual.Count131072.C026414.packed 128 cuts26414 = true := by
 decide +kernel
def pointBounds26414 : List (Nat × Nat × Nat) := [(3466136576,103603353709523,103603736121127)]
theorem point_links_checked26414 : (cuts26414.take 1).map (fun c => (3466067969-1+2*2^9*c.k,103603103020728+c.lower,103603485432193+c.upper)) = pointBounds26414 := by
 decide +kernel
def cuts26415 : List PrefixCut := [⟨45,173778922,173779015⟩,
⟨128,488686328,488686594⟩]
theorem checked26415 : checkPrefixCuts (2^48) 3466199041 9 Manual.Count131072.C026415.packed 128 cuts26415 = true := by
 decide +kernel
def pointBounds26415 : List (Nat × Nat × Nat) := [(3466245120,103603760063500,103604142475324)]
theorem point_links_checked26415 : (cuts26415.take 1).map (fun c => (3466199041-1+2*2^9*c.k,103603586284578+c.lower,103603968696309+c.upper)) = pointBounds26415 := by
 decide +kernel
def cuts26416 : List PrefixCut := [⟨23,86155626,86155672⟩,
⟨128,481684472,481684740⟩]
theorem checked26416 : checkPrefixCuts (2^48) 3466330113 9 Manual.Count131072.C026416.packed 128 cuts26416 = true := by
 decide +kernel
def pointBounds26416 : List (Nat × Nat × Nat) := [(3466353664,103604161126532,103604543538575)]
theorem point_links_checked26416 : (cuts26416.take 1).map (fun c => (3466330113-1+2*2^9*c.k,103604074970906+c.lower,103604457382903+c.upper)) = pointBounds26416 := by
 decide +kernel
def cuts26417 : List PrefixCut := [⟨1,4709570,4709573⟩,
⟨107,404042341,404042570⟩,
⟨128,481260379,481260652⟩]
theorem checked26417 : checkPrefixCuts (2^48) 3466461185 9 Manual.Count131072.C026417.packed 128 cuts26417 = true := by
 decide +kernel
def pointBounds26417 : List (Nat × Nat × Nat) := [(3466462208,103604561364948,103604943777216),(3466570752,103604960697719,103605343110213)]
theorem point_links_checked26417 : (cuts26417.take 2).map (fun c => (3466461185-1+2*2^9*c.k,103604556655378+c.lower,103604939067643+c.upper)) = pointBounds26417 := by
 decide +kernel
def cuts26418 : List PrefixCut := [⟨85,318773126,318773303⟩,
⟨128,482135219,482135488⟩]
theorem checked26418 : checkPrefixCuts (2^48) 3466592257 9 Manual.Count131072.C026418.packed 128 cuts26418 = true := by
 decide +kernel
def pointBounds26418 : List (Nat × Nat × Nat) := [(3466679296,103605356688883,103605739101598)]
theorem point_links_checked26418 : (cuts26418.take 1).map (fun c => (3466592257-1+2*2^9*c.k,103605037915757+c.lower,103605420328295+c.upper)) = pointBounds26418 := by
 decide +kernel
def cuts26419 : List PrefixCut := [⟨63,239518179,239518313⟩,
⟨128,484958769,484959039⟩]
theorem checked26419 : checkPrefixCuts (2^48) 3466723329 9 Manual.Count131072.C026419.packed 128 cuts26419 = true := by
 decide +kernel
def pointBounds26419 : List (Nat × Nat × Nat) := [(3466787840,103605759569155,103606141982096)]
theorem point_links_checked26419 : (cuts26419.take 1).map (fun c => (3466723329-1+2*2^9*c.k,103605520050976+c.lower,103605902463783+c.upper)) = pointBounds26419 := by
 decide +kernel
def cuts26420 : List PrefixCut := [⟨41,152393244,152393328⟩,
⟨128,485752263,485752540⟩]
theorem checked26420 : checkPrefixCuts (2^48) 3466854401 9 Manual.Count131072.C026420.packed 128 cuts26420 = true := by
 decide +kernel
def pointBounds26420 : List (Nat × Nat × Nat) := [(3466896384,103606157402989,103606539816150)]
theorem point_links_checked26420 : (cuts26420.take 1).map (fun c => (3466854401-1+2*2^9*c.k,103606005009745+c.lower,103606387422822+c.upper)) = pointBounds26420 := by
 decide +kernel
def cuts26421 : List PrefixCut := [⟨19,70795055,70795096⟩,
⟨125,470065240,470065501⟩,
⟨128,481755762,481756029⟩]
theorem checked26421 : checkPrefixCuts (2^48) 3466985473 9 Manual.Count131072.C026421.packed 128 cuts26421 = true := by
 decide +kernel
def pointBounds26421 : List (Nat × Nat × Nat) := [(3467004928,103606561557063,103606943970458),(3467113472,103606960827248,103607343240863)]
theorem point_links_checked26421 : (cuts26421.take 2).map (fun c => (3466985473-1+2*2^9*c.k,103606490762008+c.lower,103606873175362+c.upper)) = pointBounds26421 := by
 decide +kernel
def cuts26422 : List PrefixCut := [⟨103,389028466,389028682⟩,
⟨128,483036495,483036763⟩]
theorem checked26422 : checkPrefixCuts (2^48) 3467116545 9 Manual.Count131072.C026422.packed 128 cuts26422 = true := by
 decide +kernel
def pointBounds26422 : List (Nat × Nat × Nat) := [(3467222016,103607361546236,103607743960073)]
theorem point_links_checked26422 : (cuts26422.take 1).map (fun c => (3467116545-1+2*2^9*c.k,103606972517770+c.lower,103607354931391+c.upper)) = pointBounds26422 := by
 decide +kernel
def cuts26423 : List PrefixCut := [⟨81,307916143,307916316⟩,
⟨128,487158440,487158711⟩]
theorem checked26423 : checkPrefixCuts (2^48) 3467247617 9 Manual.Count131072.C026423.packed 128 cuts26423 = true := by
 decide +kernel
def pointBounds26423 : List (Nat × Nat × Nat) := [(3467330560,103607763470408,103608145884470)]
theorem point_links_checked26423 : (cuts26423.take 1).map (fun c => (3467247617-1+2*2^9*c.k,103607455554265+c.lower,103607837968154+c.upper)) = pointBounds26423 := by
 decide +kernel
def cuts26424 : List PrefixCut := [⟨59,227783508,227783636⟩,
⟨128,491036521,491036792⟩]
theorem checked26424 : checkPrefixCuts (2^48) 3467378689 9 Manual.Count131072.C026424.packed 128 cuts26424 = true := by
 decide +kernel
def pointBounds26424 : List (Nat × Nat × Nat) := [(3467439104,103608170496213,103608552910501)]
theorem point_links_checked26424 : (cuts26424.take 1).map (fun c => (3467378689-1+2*2^9*c.k,103607942712705+c.lower,103608325126865+c.upper)) = pointBounds26424 := by
 decide +kernel
def cuts26425 : List PrefixCut := [⟨37,138402535,138402610⟩,
⟨128,484037003,484037274⟩]
theorem checked26425 : checkPrefixCuts (2^48) 3467509761 9 Manual.Count131072.C026425.packed 128 cuts26425 = true := by
 decide +kernel
def pointBounds26425 : List (Nat × Nat × Nat) := [(3467547648,103608572151761,103608954566267)]
theorem point_links_checked26425 : (cuts26425.take 1).map (fun c => (3467509761-1+2*2^9*c.k,103608433749226+c.lower,103608816163657+c.upper)) = pointBounds26425 := by
 decide +kernel
def cuts26426 : List PrefixCut := [⟨15,57631900,57631930⟩,
⟨121,458450550,458450804⟩,
⟨128,485236282,485236551⟩]
theorem checked26426 : checkPrefixCuts (2^48) 3467640833 9 Manual.Count131072.C026426.packed 128 cuts26426 = true := by
 decide +kernel
def pointBounds26426 : List (Nat × Nat × Nat) := [(3467656192,103608975418129,103609357832861),(3467764736,103609376236779,103609758651735)]
theorem point_links_checked26426 : (cuts26426.take 2).map (fun c => (3467640833-1+2*2^9*c.k,103608917786229+c.lower,103609300200931+c.upper)) = pointBounds26426 := by
 decide +kernel
def cuts26427 : List PrefixCut := [⟨99,372721713,372721926⟩,
⟨128,480997265,480997540⟩]
theorem checked26427 : checkPrefixCuts (2^48) 3467771905 9 Manual.Count131072.C026427.packed 128 cuts26427 = true := by
 decide +kernel
def pointBounds26427 : List (Nat × Nat × Nat) := [(3467873280,103609775744224,103610158159408)]
theorem point_links_checked26427 : (cuts26427.take 1).map (fun c => (3467771905-1+2*2^9*c.k,103609403022511+c.lower,103609785437482+c.upper)) = pointBounds26427 := by
 decide +kernel
def cuts26428 : List PrefixCut := [⟨77,293248430,293248596⟩,
⟨128,487228665,487228935⟩]
theorem checked26428 : checkPrefixCuts (2^48) 3467902977 9 Manual.Count131072.C026428.packed 128 cuts26428 = true := by
 decide +kernel
def pointBounds26428 : List (Nat × Nat × Nat) := [(3467981824,103610177268206,103610559683618)]
theorem point_links_checked26428 : (cuts26428.take 1).map (fun c => (3467902977-1+2*2^9*c.k,103609884019776+c.lower,103610266435022+c.upper)) = pointBounds26428 := by
 decide +kernel
def cuts26429 : List PrefixCut := [⟨55,206476142,206476260⟩,
⟨128,486073999,486074269⟩]
theorem checked26429 : checkPrefixCuts (2^48) 3468034049 9 Manual.Count131072.C026429.packed 128 cuts26429 = true := by
 decide +kernel
def pointBounds26429 : List (Nat × Nat × Nat) := [(3468090368,103610577724583,103610960140217)]
theorem point_links_checked26429 : (cuts26429.take 1).map (fun c => (3468034049-1+2*2^9*c.k,103610371248441+c.lower,103610753663957+c.upper)) = pointBounds26429 := by
 decide +kernel
def cuts26430 : List PrefixCut := [⟨33,123605470,123605540⟩,
⟨128,478832589,478832868⟩]
theorem checked26430 : checkPrefixCuts (2^48) 3468165121 9 Manual.Count131072.C026430.packed 128 cuts26430 = true := by
 decide +kernel
def pointBounds26430 : List (Nat × Nat × Nat) := [(3468198912,103610980927910,103611363343766)]
theorem point_links_checked26430 : (cuts26430.take 1).map (fun c => (3468165121-1+2*2^9*c.k,103610857322440+c.lower,103611239738226+c.upper)) = pointBounds26430 := by
 decide +kernel
def cuts26431 : List PrefixCut := [⟨11,39036230,39036254⟩,
⟨117,440753489,440753743⟩,
⟨128,480437603,480437878⟩]
theorem checked26431 : checkPrefixCuts (2^48) 3468296193 9 Manual.Count131072.C026431.packed 128 cuts26431 = true := by
 decide +kernel
def pointBounds26431 : List (Nat × Nat × Nat) := [(3468307456,103611375191259,103611757607348),(3468416000,103611776908518,103612159324837)]
theorem point_links_checked26431 : (cuts26431.take 2).map (fun c => (3468296193-1+2*2^9*c.k,103611336155029+c.lower,103611718571094+c.upper)) = pointBounds26431 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000200
