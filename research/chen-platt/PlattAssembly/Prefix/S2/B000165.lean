import PlattAssemblyKernel
import PlattCertificates.Count131072.C015280
import PlattCertificates.Count131072.C015281
import PlattCertificates.Count131072.C015282
import PlattCertificates.Count131072.C015283
import PlattCertificates.Count131072.C015284
import PlattCertificates.Count131072.C015285
import PlattCertificates.Count131072.C015286
import PlattCertificates.Count131072.C015287
import PlattCertificates.Count131072.C015288
import PlattCertificates.Count131072.C015289
import PlattCertificates.Count131072.C015290
import PlattCertificates.Count131072.C015291
import PlattCertificates.Count131072.C015292
import PlattCertificates.Count131072.C015293
import PlattCertificates.Count131072.C015294
import PlattCertificates.Count131072.C015295
import PlattCertificates.Count131072.C015296
import PlattCertificates.Count131072.C015297
import PlattCertificates.Count131072.C015298
import PlattCertificates.Count131072.C015299
import PlattCertificates.Count131072.C015300
import PlattCertificates.Count131072.C015301
import PlattCertificates.Count131072.C015302
import PlattCertificates.Count131072.C015303
import PlattCertificates.Count131072.C015304
import PlattCertificates.Count131072.C015305
import PlattCertificates.Count131072.C015306
import PlattCertificates.Count131072.C015307
import PlattCertificates.Count131072.C015308
import PlattCertificates.Count131072.C015309
import PlattCertificates.Count131072.C015310
import PlattCertificates.Count131072.C015311
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000165
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15280 : List PrefixCut := [⟨50,335233073,335233297⟩,
⟨112,753771620,753772117⟩,
⟨128,860508021,860508592⟩]
theorem checked15280 : checkPrefixCuts (2^48) 2006712321 9 Manual.Count131072.C015280.packed 128 cuts15280 = true := by
 decide +kernel
def pointBounds15280 : List (Nat × Nat × Nat) := [(2006763520,96511855258111,96512233453143),(2006827008,96512273796658,96512651991963)]
theorem point_links_checked15280 : (cuts15280.take 2).map (fun c => (2006712321-1+2*2^9*c.k,96511520025038+c.lower,96511898219846+c.upper)) = pointBounds15280 := by
 decide +kernel
def cuts15281 : List PrefixCut := [⟨46,307160396,307160601⟩,
⟨108,722025797,722026273⟩,
⟨128,855402651,855403216⟩]
theorem checked15281 : checkPrefixCuts (2^48) 2006843393 9 Manual.Count131072.C015281.packed 128 cuts15281 = true := by
 decide +kernel
def pointBounds15281 : List (Nat × Nat × Nat) := [(2006890496,96512687693455,96513065889039),(2006953984,96513102558856,96513480754711)]
theorem point_links_checked15281 : (cuts15281.take 2).map (fun c => (2006843393-1+2*2^9*c.k,96512380533059+c.lower,96512758728438+c.upper)) = pointBounds15281 := by
 decide +kernel
def cuts15282 : List PrefixCut := [⟨42,284981634,284981821⟩,
⟨104,709637852,709638313⟩,
⟨128,868950572,868951138⟩]
theorem checked15282 : checkPrefixCuts (2^48) 2006974465 9 Manual.Count131072.C015282.packed 128 cuts15282 = true := by
 decide +kernel
def pointBounds15282 : List (Nat × Nat × Nat) := [(2007017472,96513520917344,96513899113475),(2007080960,96513945573562,96514323769967)]
theorem point_links_checked15282 : (cuts15282.take 2).map (fun c => (2006974465-1+2*2^9*c.k,96513235935710+c.lower,96513614131654+c.upper)) = pointBounds15282 := by
 decide +kernel
def cuts15283 : List PrefixCut := [⟨38,260141234,260141405⟩,
⟨100,671588562,671589000⟩,
⟨128,861040694,861041256⟩]
theorem checked15283 : checkPrefixCuts (2^48) 2007105537 9 Manual.Count131072.C015283.packed 128 cuts15283 = true := by
 decide +kernel
def pointBounds15283 : List (Nat × Nat × Nat) := [(2007144448,96514365027516,96514743224197),(2007207936,96514776474844,96515154671792)]
theorem point_links_checked15283 : (cuts15283.take 2).map (fun c => (2007105537-1+2*2^9*c.k,96514104886282+c.lower,96514483082792+c.upper)) = pointBounds15283 := by
 decide +kernel
def cuts15284 : List PrefixCut := [⟨34,224786806,224786951⟩,
⟨96,644761835,644762257⟩,
⟨128,855936204,855936766⟩]
theorem checked15284 : checkPrefixCuts (2^48) 2007236609 9 Manual.Count131072.C015284.packed 128 cuts15284 = true := by
 decide +kernel
def pointBounds15284 : List (Nat × Nat × Nat) := [(2007271424,96515190713782,96515568910999),(2007334912,96515610688811,96515988886305)]
theorem point_links_checked15284 : (cuts15284.take 2).map (fun c => (2007236609-1+2*2^9*c.k,96514965926976+c.lower,96515344124048+c.upper)) = pointBounds15284 := by
 decide +kernel
def cuts15285 : List PrefixCut := [⟨30,196027279,196027411⟩,
⟨92,606160607,606161006⟩,
⟨128,841578299,841578853⟩]
theorem checked15285 : checkPrefixCuts (2^48) 2007367681 9 Manual.Count131072.C015285.packed 128 cuts15285 = true := by
 decide +kernel
def pointBounds15285 : List (Nat × Nat × Nat) := [(2007398400,96516017890459,96516396088225),(2007461888,96516428023787,96516806221820)]
theorem point_links_checked15285 : (cuts15285.take 2).map (fun c => (2007367681-1+2*2^9*c.k,96515821863180+c.lower,96516200060814+c.upper)) = pointBounds15285 := by
 decide +kernel
def cuts15286 : List PrefixCut := [⟨26,171898463,171898573⟩,
⟨88,594204009,594204398⟩,
⟨128,861292659,861293225⟩]
theorem checked15286 : checkPrefixCuts (2^48) 2007498753 9 Manual.Count131072.C015286.packed 128 cuts15286 = true := by
 decide +kernel
def pointBounds15286 : List (Nat × Nat × Nat) := [(2007525376,96516835339942,96517213538240),(2007588864,96517257645488,96517635844065)]
theorem point_links_checked15286 : (cuts15286.take 2).map (fun c => (2007498753-1+2*2^9*c.k,96516663441479+c.lower,96517041639667+c.upper)) = pointBounds15286 := by
 decide +kernel
def cuts15287 : List PrefixCut := [⟨22,148333488,148333585⟩,
⟨84,563462096,563462465⟩,
⟨128,862638217,862638789⟩]
theorem checked15287 : checkPrefixCuts (2^48) 2007629825 9 Manual.Count131072.C015287.packed 128 cuts15287 = true := by
 decide +kernel
def pointBounds15287 : List (Nat × Nat × Nat) := [(2007652352,96517673067626,96518051266477),(2007715840,96518088196234,96518466395357)]
theorem point_links_checked15287 : (cuts15287.take 2).map (fun c => (2007629825-1+2*2^9*c.k,96517524734138+c.lower,96517902932892+c.upper)) = pointBounds15287 := by
 decide +kernel
def cuts15288 : List PrefixCut := [⟨18,115659034,115659110⟩,
⟨80,537630673,537631034⟩,
⟨128,856273419,856273992⟩]
theorem checked15288 : checkPrefixCuts (2^48) 2007760897 9 Manual.Count131072.C015288.packed 128 cuts15288 = true := by
 decide +kernel
def pointBounds15288 : List (Nat × Nat × Nat) := [(2007779328,96518503031389,96518881230791),(2007842816,96518925003028,96519303202715)]
theorem point_links_checked15288 : (cuts15288.take 2).map (fun c => (2007760897-1+2*2^9*c.k,96518387372355+c.lower,96518765571681+c.upper)) = pointBounds15288 := by
 decide +kernel
def cuts15289 : List PrefixCut := [⟨14,92240931,92240991⟩,
⟨76,500308034,500308366⟩,
⟨128,848367497,848368057⟩]
theorem checked15289 : checkPrefixCuts (2^48) 2007891969 9 Manual.Count131072.C015289.packed 128 cuts15289 = true := by
 decide +kernel
def pointBounds15289 : List (Nat × Nat × Nat) := [(2007906304,96519335886705,96519714086664),(2007969792,96519743953808,96520122154039)]
theorem point_links_checked15289 : (cuts15289.take 2).map (fun c => (2007891969-1+2*2^9*c.k,96519243645774+c.lower,96519621845673+c.upper)) = pointBounds15289 := by
 decide +kernel
def cuts15290 : List PrefixCut := [⟨10,66442840,66442886⟩,
⟨72,483735430,483735754⟩,
⟨128,863730819,863731392⟩]
theorem checked15290 : checkPrefixCuts (2^48) 2008023041 9 Manual.Count131072.C015290.packed 128 cuts15290 = true := by
 decide +kernel
def pointBounds15290 : List (Nat × Nat × Nat) := [(2008033280,96520158456111,96520536656616),(2008096768,96520575748701,96520953949484)]
theorem point_links_checked15290 : (cuts15290.take 2).map (fun c => (2008023041-1+2*2^9*c.k,96520092013271+c.lower,96520470213730+c.upper)) = pointBounds15290 := by
 decide +kernel
def cuts15291 : List PrefixCut := [⟨6,40507905,40507933⟩,
⟨68,457633923,457634221⟩,
⟨128,849238007,849238565⟩]
theorem checked15291 : checkPrefixCuts (2^48) 2008154113 9 Manual.Count131072.C015291.packed 128 cuts15291 = true := by
 decide +kernel
def pointBounds15291 : List (Nat × Nat × Nat) := [(2008160256,96520996251995,96521374453055),(2008223744,96521413378013,96521791579343)]
theorem point_links_checked15291 : (cuts15291.take 2).map (fun c => (2008154113-1+2*2^9*c.k,96520955744090+c.lower,96521333945122+c.upper)) = pointBounds15291 := by
 decide +kernel
def cuts15292 : List PrefixCut := [⟨2,12754264,12754273⟩,
⟨64,425509194,425509474⟩,
⟨126,850304002,850304557⟩,
⟨128,863057448,863058011⟩]
theorem checked15292 : checkPrefixCuts (2^48) 2008285185 9 Manual.Count131072.C015292.packed 128 cuts15292 = true := by
 decide +kernel
def pointBounds15292 : List (Nat × Nat × Nat) := [(2008287232,96521817736361,96522195937960),(2008350720,96522230491291,96522608693161),(2008414208,96522655286099,96523033488244)]
theorem point_links_checked15292 : (cuts15292.take 3).map (fun c => (2008285185-1+2*2^9*c.k,96521804982097+c.lower,96522183183687+c.upper)) = pointBounds15292 := by
 decide +kernel
def cuts15293 : List PrefixCut := [⟨60,396471669,396471931⟩,
⟨122,808767017,808767551⟩,
⟨128,850388224,850388785⟩]
theorem checked15293 : checkPrefixCuts (2^48) 2008416257 9 Manual.Count131072.C015293.packed 128 cuts15293 = true := by
 decide +kernel
def pointBounds15293 : List (Nat × Nat × Nat) := [(2008477696,96523064511214,96523442713629),(2008541184,96523476806562,96523855009249)]
theorem point_links_checked15293 : (cuts15293.take 2).map (fun c => (2008416257-1+2*2^9*c.k,96522668039545+c.lower,96523046241698+c.upper)) = pointBounds15293 := by
 decide +kernel
def cuts15294 : List PrefixCut := [⟨56,370801303,370801545⟩,
⟨118,783070587,783071104⟩,
⟨128,851033518,851034079⟩]
theorem checked15294 : checkPrefixCuts (2^48) 2008547329 9 Manual.Count131072.C015294.packed 128 cuts15294 = true := by
 decide +kernel
def pointBounds15294 : List (Nat × Nat × Nat) := [(2008604672,96523889229072,96524267432028),(2008668160,96524301498356,96524679701587)]
theorem point_links_checked15294 : (cuts15294.take 2).map (fun c => (2008547329-1+2*2^9*c.k,96523518427769+c.lower,96523896630483+c.upper)) = pointBounds15294 := by
 decide +kernel
def cuts15295 : List PrefixCut := [⟨52,355223342,355223569⟩,
⟨114,780638251,780638758⟩,
⟨128,875920357,875920926⟩]
theorem checked15295 : checkPrefixCuts (2^48) 2008678401 9 Manual.Count131072.C015295.packed 128 cuts15295 = true := by
 decide +kernel
def pointBounds15295 : List (Nat × Nat × Nat) := [(2008731648,96524724684629,96525102888131),(2008795136,96525150099538,96525528303320)]
theorem point_links_checked15295 : (cuts15295.take 2).map (fun c => (2008678401-1+2*2^9*c.k,96524369461287+c.lower,96524747664562+c.upper)) = pointBounds15295 := by
 decide +kernel
def cuts15296 : List PrefixCut := [⟨48,313865509,313865720⟩,
⟨110,723140354,723140838⟩,
⟨128,844196906,844197469⟩]
theorem checked15296 : checkPrefixCuts (2^48) 2008809473 9 Manual.Count131072.C015296.packed 128 cuts15296 = true := by
 decide +kernel
def pointBounds15296 : List (Nat × Nat × Nat) := [(2008858624,96525559247153,96525937451208),(2008922112,96525968521998,96526346726326)]
theorem point_links_checked15296 : (cuts15296.take 2).map (fun c => (2008809473-1+2*2^9*c.k,96525245381644+c.lower,96525623585488+c.upper)) = pointBounds15296 := by
 decide +kernel
def cuts15297 : List PrefixCut := [⟨44,294650311,294650502⟩,
⟨106,709083117,709083584⟩,
⟨128,849185853,849186414⟩]
theorem checked15297 : checkPrefixCuts (2^48) 2008940545 9 Manual.Count131072.C015297.packed 128 cuts15297 = true := by
 decide +kernel
def pointBounds15297 : List (Nat × Nat × Nat) := [(2008985600,96526384228861,96526762433459),(2009049088,96526798661667,96527176866541)]
theorem point_links_checked15297 : (cuts15297.take 2).map (fun c => (2008940545-1+2*2^9*c.k,96526089578550+c.lower,96526467782957+c.upper)) = pointBounds15297 := by
 decide +kernel
def cuts15298 : List PrefixCut := [⟨40,269693546,269693725⟩,
⟨102,686762054,686762506⟩,
⟨128,862579714,862580284⟩]
theorem checked15298 : checkPrefixCuts (2^48) 2009071617 9 Manual.Count131072.C015298.packed 128 cuts15298 = true := by
 decide +kernel
def pointBounds15298 : List (Nat × Nat × Nat) := [(2009112576,96527208457949,96527586663096),(2009176064,96527625526457,96528003731877)]
theorem point_links_checked15298 : (cuts15298.take 2).map (fun c => (2009071617-1+2*2^9*c.k,96526938764403+c.lower,96527316969371+c.upper)) = pointBounds15298 := by
 decide +kernel
def cuts15299 : List PrefixCut := [⟨36,243058794,243058954⟩,
⟨98,667385510,667385942⟩,
⟨128,863924440,863925007⟩]
theorem checked15299 : checkPrefixCuts (2^48) 2009202689 9 Manual.Count131072.C015299.packed 128 cuts15299 = true := by
 decide +kernel
def pointBounds15299 : List (Nat × Nat × Nat) := [(2009239552,96528044402911,96528422608609),(2009303040,96528468729627,96528846935597)]
theorem point_links_checked15299 : (cuts15299.take 2).map (fun c => (2009202689-1+2*2^9*c.k,96527801344117+c.lower,96528179549655+c.upper)) = pointBounds15299 := by
 decide +kernel
def cuts15300 : List PrefixCut := [⟨32,213345711,213345853⟩,
⟨94,628960694,628961107⟩,
⟨128,857144098,857144661⟩]
theorem checked15300 : checkPrefixCuts (2^48) 2009333761 9 Manual.Count131072.C015300.packed 128 cuts15300 = true := by
 decide +kernel
def pointBounds15300 : List (Nat × Nat × Nat) := [(2009366528,96528878614268,96529256820515),(2009430016,96529294229251,96529672435769)]
theorem point_links_checked15300 : (cuts15300.take 2).map (fun c => (2009333761-1+2*2^9*c.k,96528665268557+c.lower,96529043474662+c.upper)) = pointBounds15300 := by
 decide +kernel
def cuts15301 : List PrefixCut := [⟨28,191060324,191060451⟩,
⟨90,604267756,604268145⟩,
⟨128,854286901,854287453⟩]
theorem checked15301 : checkPrefixCuts (2^48) 2009464833 9 Manual.Count131072.C015301.packed 128 cuts15301 = true := by
 decide +kernel
def pointBounds15301 : List (Nat × Nat × Nat) := [(2009493504,96529713472979,96530091679774),(2009556992,96530126680411,96530504887468)]
theorem point_links_checked15301 : (cuts15301.take 2).map (fun c => (2009464833-1+2*2^9*c.k,96529522412655+c.lower,96529900619323+c.upper)) = pointBounds15301 := by
 decide +kernel
def cuts15302 : List PrefixCut := [⟨24,159953726,159953833⟩,
⟨86,574955908,574956286⟩,
⟨128,854371185,854371748⟩]
theorem checked15302 : checkPrefixCuts (2^48) 2009595905 9 Manual.Count131072.C015302.packed 128 cuts15302 = true := by
 decide +kernel
def pointBounds15302 : List (Nat × Nat × Nat) := [(2009620480,96530536653282,96530914860609),(2009683968,96530951655464,96531329863062)]
theorem point_links_checked15302 : (cuts15302.take 2).map (fun c => (2009595905-1+2*2^9*c.k,96530376699556+c.lower,96530754906776+c.upper)) = pointBounds15302 := by
 decide +kernel
def cuts15303 : List PrefixCut := [⟨20,132492574,132492661⟩,
⟨82,544667591,544667948⟩,
⟨128,860757688,860758251⟩]
theorem checked15303 : checkPrefixCuts (2^48) 2009726977 9 Manual.Count131072.C015303.packed 128 cuts15303 = true := by
 decide +kernel
def pointBounds15303 : List (Nat × Nat × Nat) := [(2009747456,96531363563315,96531741771185),(2009810944,96531775738332,96532153946472)]
theorem point_links_checked15303 : (cuts15303.take 2).map (fun c => (2009726977-1+2*2^9*c.k,96531231070741+c.lower,96531609278524+c.upper)) = pointBounds15303 := by
 decide +kernel
def cuts15304 : List PrefixCut := [⟨16,105735171,105735242⟩,
⟨78,528527375,528527725⟩,
⟨128,864622885,864623457⟩]
theorem checked15304 : checkPrefixCuts (2^48) 2009858049 9 Manual.Count131072.C015304.packed 128 cuts15304 = true := by
 decide +kernel
def pointBounds15304 : List (Nat × Nat × Nat) := [(2009874432,96532197563600,96532575772017),(2009937920,96532620355804,96532998564500)]
theorem point_links_checked15304 : (cuts15304.take 2).map (fun c => (2009858049-1+2*2^9*c.k,96532091828429+c.lower,96532470036775+c.upper)) = pointBounds15304 := by
 decide +kernel
def cuts15305 : List PrefixCut := [⟨12,76460523,76460573⟩,
⟨74,482281791,482282108⟩,
⟨128,841460792,841461350⟩]
theorem checked15305 : checkPrefixCuts (2^48) 2009989121 9 Manual.Count131072.C015305.packed 128 cuts15305 = true := by
 decide +kernel
def pointBounds15305 : List (Nat × Nat × Nat) := [(2010001408,96533032911837,96533411120805),(2010064896,96533438733105,96533816942340)]
theorem point_links_checked15305 : (cuts15305.take 2).map (fun c => (2009989121-1+2*2^9*c.k,96532956451314+c.lower,96533334660232+c.upper)) = pointBounds15305 := by
 decide +kernel
def cuts15306 : List PrefixCut := [⟨8,49290065,49290098⟩,
⟨70,455505845,455506145⟩,
⟨128,844906539,844907100⟩]
theorem checked15306 : checkPrefixCuts (2^48) 2010120193 9 Manual.Count131072.C015306.packed 128 cuts15306 = true := by
 decide +kernel
def pointBounds15306 : List (Nat × Nat × Nat) := [(2010128384,96533847202171,96534225411680),(2010191872,96534253417951,96534631627727)]
theorem point_links_checked15306 : (cuts15306.take 2).map (fun c => (2010120193-1+2*2^9*c.k,96533797912106+c.lower,96534176121582+c.upper)) = pointBounds15306 := by
 decide +kernel
def cuts15307 : List PrefixCut := [⟨4,28423981,28424000⟩,
⟨66,450156000,450156296⟩,
⟨128,865994108,865994680⟩]
theorem checked15307 : checkPrefixCuts (2^48) 2010251265 9 Manual.Count131072.C015307.packed 128 cuts15307 = true := by
 decide +kernel
def pointBounds15307 : List (Nat × Nat × Nat) := [(2010255360,96534671242626,96535049452682),(2010318848,96535092974645,96535471184978),(2010382336,96535508812753,96535887023362)]
theorem point_links_checked15307 : (cuts15307.take 3).map (fun c => (2010251265-1+2*2^9*c.k,96534642818645+c.lower,96535021028682+c.upper)) = pointBounds15307 := by
 decide +kernel
def cuts15308 : List PrefixCut := [⟨62,416244996,416245271⟩,
⟨124,822956572,822957114⟩,
⟨128,849276880,849277439⟩]
theorem checked15308 : checkPrefixCuts (2^48) 2010382337 9 Manual.Count131072.C015308.packed 128 cuts15308 = true := by
 decide +kernel
def pointBounds15308 : List (Nat × Nat × Nat) := [(2010445824,96535925057749,96536303268633),(2010509312,96536331769325,96536709980476)]
theorem point_links_checked15308 : (cuts15308.take 2).map (fun c => (2010382337-1+2*2^9*c.k,96535508812753+c.lower,96535887023362+c.upper)) = pointBounds15308 := by
 decide +kernel
def cuts15309 : List PrefixCut := [⟨58,390598461,390598720⟩,
⟨120,810583947,810584482⟩,
⟨128,861401280,861401849⟩]
theorem checked15309 : checkPrefixCuts (2^48) 2010513409 9 Manual.Count131072.C015309.packed 128 cuts15309 = true := by
 decide +kernel
def pointBounds15309 : List (Nat × Nat × Nat) := [(2010572800,96536748688094,96537126899521),(2010636288,96537168673580,96537546885283)]
theorem point_links_checked15309 : (cuts15309.take 2).map (fun c => (2010513409-1+2*2^9*c.k,96536358089633+c.lower,96536736300801+c.upper)) = pointBounds15309 := by
 decide +kernel
def cuts15310 : List PrefixCut := [⟨54,354035811,354036046⟩,
⟨116,761955929,761956439⟩,
⟨128,838387020,838387579⟩]
theorem checked15310 : checkPrefixCuts (2^48) 2010644481 9 Manual.Count131072.C015310.packed 128 cuts15310 = true := by
 decide +kernel
def pointBounds15310 : List (Nat × Nat × Nat) := [(2010699776,96537573526724,96537951738696),(2010763264,96537981446842,96538359659089)]
theorem point_links_checked15310 : (cuts15310.take 2).map (fun c => (2010644481-1+2*2^9*c.k,96537219490913+c.lower,96537597702650+c.upper)) = pointBounds15310 := by
 decide +kernel
def cuts15311 : List PrefixCut := [⟨50,341274809,341275032⟩,
⟨112,764846646,764847150⟩,
⟨128,872207236,872207811⟩]
theorem checked15311 : checkPrefixCuts (2^48) 2010775553 9 Manual.Count131072.C015311.packed 128 cuts15311 = true := by
 decide +kernel
def pointBounds15311 : List (Nat × Nat × Nat) := [(2010826752,96538399152742,96538777365261),(2010890240,96538822724579,96539200937379)]
theorem point_links_checked15311 : (cuts15311.take 2).map (fun c => (2010775553-1+2*2^9*c.k,96538057877933+c.lower,96538436090229+c.upper)) = pointBounds15311 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000165
