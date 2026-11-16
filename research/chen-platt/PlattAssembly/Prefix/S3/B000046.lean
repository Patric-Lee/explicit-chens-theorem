import PlattAssemblyKernel
import PlattCertificates.Count131072.C021472
import PlattCertificates.Count131072.C021473
import PlattCertificates.Count131072.C021474
import PlattCertificates.Count131072.C021475
import PlattCertificates.Count131072.C021476
import PlattCertificates.Count131072.C021477
import PlattCertificates.Count131072.C021478
import PlattCertificates.Count131072.C021479
import PlattCertificates.Count131072.C021480
import PlattCertificates.Count131072.C021481
import PlattCertificates.Count131072.C021482
import PlattCertificates.Count131072.C021483
import PlattCertificates.Count131072.C021484
import PlattCertificates.Count131072.C021485
import PlattCertificates.Count131072.C021486
import PlattCertificates.Count131072.C021487
import PlattCertificates.Count131072.C021488
import PlattCertificates.Count131072.C021489
import PlattCertificates.Count131072.C021490
import PlattCertificates.Count131072.C021491
import PlattCertificates.Count131072.C021492
import PlattCertificates.Count131072.C021493
import PlattCertificates.Count131072.C021494
import PlattCertificates.Count131072.C021495
import PlattCertificates.Count131072.C021496
import PlattCertificates.Count131072.C021497
import PlattCertificates.Count131072.C021498
import PlattCertificates.Count131072.C021499
import PlattCertificates.Count131072.C021500
import PlattCertificates.Count131072.C021501
import PlattCertificates.Count131072.C021502
import PlattCertificates.Count131072.C021503
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000046
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21472 : List PrefixCut := [⟨16,75803872,75803915⟩,
⟨103,490270416,490270701⟩,
⟨128,610413375,610413727⟩]
theorem checked21472 : checkPrefixCuts (2^48) 2818310145 9 Manual.Count131072.C021472.packed 128 cuts21472 = true := by
 decide +kernel
def pointBounds21472 : List (Nat × Nat × Nat) := [(2818326528,100939679843334,100940060747466),(2818415616,100940094309878,100940475214252)]
theorem point_links_checked21472 : (cuts21472.take 2).map (fun c => (2818310145-1+2*2^9*c.k,100939604039462+c.lower,100939984943551+c.upper)) = pointBounds21472 := by
 decide +kernel
def cuts21473 : List PrefixCut := [⟨62,287619491,287619657⟩,
⟨128,603094765,603095109⟩]
theorem checked21473 : checkPrefixCuts (2^48) 2818441217 9 Manual.Count131072.C021473.packed 128 cuts21473 = true := by
 decide +kernel
def pointBounds21473 : List (Nat × Nat × Nat) := [(2818504704,100940502072328,100940882976935)]
theorem point_links_checked21473 : (cuts21473.take 1).map (fun c => (2818441217-1+2*2^9*c.k,100940214452837+c.lower,100940595357278+c.upper)) = pointBounds21473 := by
 decide +kernel
def cuts21474 : List PrefixCut := [⟨21,98166292,98166346⟩,
⟨108,506102661,506102945⟩,
⟨128,598772812,598773150⟩]
theorem checked21474 : checkPrefixCuts (2^48) 2818572289 9 Manual.Count131072.C021474.packed 128 cuts21474 = true := by
 decide +kernel
def pointBounds21474 : List (Nat × Nat × Nat) := [(2818593792,100940915713894,100941296618733),(2818682880,100941323650263,100941704555332)]
theorem point_links_checked21474 : (cuts21474.take 2).map (fun c => (2818572289-1+2*2^9*c.k,100940817547602+c.lower,100941198452387+c.upper)) = pointBounds21474 := by
 decide +kernel
def cuts21475 : List PrefixCut := [⟨67,323940956,323941142⟩,
⟨128,608231486,608231832⟩]
theorem checked21475 : checkPrefixCuts (2^48) 2818703361 9 Manual.Count131072.C021475.packed 128 cuts21475 = true := by
 decide +kernel
def pointBounds21475 : List (Nat × Nat × Nat) := [(2818771968,100941740261370,100942121166679)]
theorem point_links_checked21475 : (cuts21475.take 1).map (fun c => (2818703361-1+2*2^9*c.k,100941416320414+c.lower,100941797225537+c.upper)) = pointBounds21475 := by
 decide +kernel
def cuts21476 : List PrefixCut := [⟨26,125517232,125517302⟩,
⟨113,533315012,533315329⟩,
⟨128,607304375,607304732⟩]
theorem checked21476 : checkPrefixCuts (2^48) 2818834433 9 Manual.Count131072.C021476.packed 128 cuts21476 = true := by
 decide +kernel
def pointBounds21476 : List (Nat × Nat × Nat) := [(2818861056,100942150069132,100942530974671),(2818950144,100942557866912,100942938772698)]
theorem point_links_checked21476 : (cuts21476.take 2).map (fun c => (2818834433-1+2*2^9*c.k,100942024551900+c.lower,100942405457369+c.upper)) = pointBounds21476 := by
 decide +kernel
def cuts21477 : List PrefixCut := [⟨72,339986269,339986461⟩,
⟨128,599787627,599787965⟩]
theorem checked21477 : checkPrefixCuts (2^48) 2818965505 9 Manual.Count131072.C021477.packed 128 cuts21477 = true := by
 decide +kernel
def pointBounds21477 : List (Nat × Nat × Nat) := [(2819039232,100942971842544,100943352748562)]
theorem point_links_checked21477 : (cuts21477.take 1).map (fun c => (2818965505-1+2*2^9*c.k,100942631856275+c.lower,100943012762101+c.upper)) = pointBounds21477 := by
 decide +kernel
def cuts21478 : List PrefixCut := [⟨31,145773998,145774084⟩,
⟨118,554431669,554431987⟩,
⟨128,600758042,600758387⟩]
theorem checked21478 : checkPrefixCuts (2^48) 2819096577 9 Manual.Count131072.C021478.packed 128 cuts21478 = true := by
 decide +kernel
def pointBounds21478 : List (Nat × Nat × Nat) := [(2819128320,100943377417900,100943758324150),(2819217408,100943786075571,100944166982053)]
theorem point_links_checked21478 : (cuts21478.take 2).map (fun c => (2819096577-1+2*2^9*c.k,100943231643902+c.lower,100943612550066+c.upper)) = pointBounds21478 := by
 decide +kernel
def cuts21479 : List PrefixCut := [⟨77,361919110,361919320⟩,
⟨128,603525676,603526025⟩]
theorem checked21479 : checkPrefixCuts (2^48) 2819227649 9 Manual.Count131072.C021479.packed 128 cuts21479 = true := by
 decide +kernel
def pointBounds21479 : List (Nat × Nat × Nat) := [(2819306496,100944194321054,100944575227773)]
theorem point_links_checked21479 : (cuts21479.take 1).map (fun c => (2819227649-1+2*2^9*c.k,100943832401944+c.lower,100944213308453+c.upper)) = pointBounds21479 := by
 decide +kernel
def cuts21480 : List PrefixCut := [⟨36,170719289,170719387⟩,
⟨123,581534638,581534971⟩,
⟨128,604995145,604995491⟩]
theorem checked21480 : checkPrefixCuts (2^48) 2819358721 9 Manual.Count131072.C021480.packed 128 cuts21480 = true := by
 decide +kernel
def pointBounds21480 : List (Nat × Nat × Nat) := [(2819395584,100944606646909,100944987553865),(2819484672,100945017462258,100945398369449)]
theorem point_links_checked21480 : (cuts21480.take 2).map (fun c => (2819358721-1+2*2^9*c.k,100944435927620+c.lower,100944816834478+c.upper)) = pointBounds21480 := by
 decide +kernel
def cuts21481 : List PrefixCut := [⟨82,384247118,384247336⟩,
⟨128,599077067,599077408⟩]
theorem checked21481 : checkPrefixCuts (2^48) 2819489793 9 Manual.Count131072.C021481.packed 128 cuts21481 = true := by
 decide +kernel
def pointBounds21481 : List (Nat × Nat × Nat) := [(2819573760,100945425169883,100945806077305)]
theorem point_links_checked21481 : (cuts21481.take 1).map (fun c => (2819489793-1+2*2^9*c.k,100945040922765+c.lower,100945421829969+c.upper)) = pointBounds21481 := by
 decide +kernel
def cuts21482 : List PrefixCut := [⟨41,189670276,189670385⟩,
⟨128,598050893,598051239⟩]
theorem checked21482 : checkPrefixCuts (2^48) 2819620865 9 Manual.Count131072.C021482.packed 128 cuts21482 = true := by
 decide +kernel
def pointBounds21482 : List (Nat × Nat × Nat) := [(2819662848,100945829670108,100946210577762),(2819751936,100946238050725,100946618958616)]
theorem point_links_checked21482 : (cuts21482.take 2).map (fun c => (2819620865-1+2*2^9*c.k,100945639999832+c.lower,100946020907377+c.upper)) = pointBounds21482 := by
 decide +kernel
def cuts21483 : List PrefixCut := [⟨87,404674267,404674503⟩,
⟨128,597424117,597424461⟩]
theorem checked21483 : checkPrefixCuts (2^48) 2819751937 9 Manual.Count131072.C021483.packed 128 cuts21483 = true := by
 decide +kernel
def pointBounds21483 : List (Nat × Nat × Nat) := [(2819841024,100946642724992,100947023633119)]
theorem point_links_checked21483 : (cuts21483.take 1).map (fun c => (2819751937-1+2*2^9*c.k,100946238050725+c.lower,100946618958616+c.upper)) = pointBounds21483 := by
 decide +kernel
def cuts21484 : List PrefixCut := [⟨46,217701071,217701197⟩,
⟨128,602187651,602187999⟩]
theorem checked21484 : checkPrefixCuts (2^48) 2819883009 9 Manual.Count131072.C021484.packed 128 cuts21484 = true := by
 decide +kernel
def pointBounds21484 : List (Nat × Nat × Nat) := [(2819930112,100947053175913,100947434084274)]
theorem point_links_checked21484 : (cuts21484.take 1).map (fun c => (2819883009-1+2*2^9*c.k,100946835474842+c.lower,100947216383077+c.upper)) = pointBounds21484 := by
 decide +kernel
def cuts21485 : List PrefixCut := [⟨5,24853487,24853501⟩,
⟨92,435877447,435877701⟩,
⟨128,606052308,606052656⟩]
theorem checked21485 : checkPrefixCuts (2^48) 2820014081 9 Manual.Count131072.C021485.packed 128 cuts21485 = true := by
 decide +kernel
def pointBounds21485 : List (Nat × Nat × Nat) := [(2820019200,100947462515980,100947843424577),(2820108288,100947873539940,100948254448777)]
theorem point_links_checked21485 : (cuts21485.take 2).map (fun c => (2820014081-1+2*2^9*c.k,100947437662493+c.lower,100947818571076+c.upper)) = pointBounds21485 := by
 decide +kernel
def cuts21486 : List PrefixCut := [⟨51,237342791,237342930⟩,
⟨128,604027874,604028222⟩]
theorem checked21486 : checkPrefixCuts (2^48) 2820145153 9 Manual.Count131072.C021486.packed 128 cuts21486 = true := by
 decide +kernel
def pointBounds21486 : List (Nat × Nat × Nat) := [(2820197376,100948281057592,100948661966662)]
theorem point_links_checked21486 : (cuts21486.take 1).map (fun c => (2820145153-1+2*2^9*c.k,100948043714801+c.lower,100948424623732+c.upper)) = pointBounds21486 := by
 decide +kernel
def cuts21487 : List PrefixCut := [⟨10,47406823,47406849⟩,
⟨97,460088432,460088695⟩,
⟨128,606594738,606595084⟩]
theorem checked21487 : checkPrefixCuts (2^48) 2820276225 9 Manual.Count131072.C021487.packed 128 cuts21487 = true := by
 decide +kernel
def pointBounds21487 : List (Nat × Nat × Nat) := [(2820286464,100948695149498,100949076058803),(2820375552,100949107831107,100949488740649)]
theorem point_links_checked21487 : (cuts21487.take 2).map (fun c => (2820276225-1+2*2^9*c.k,100948647742675+c.lower,100949028651954+c.upper)) = pointBounds21487 := by
 decide +kernel
def cuts21488 : List PrefixCut := [⟨56,258477750,258477905⟩,
⟨128,598682400,598682751⟩]
theorem checked21488 : checkPrefixCuts (2^48) 2820407297 9 Manual.Count131072.C021488.packed 128 cuts21488 = true := by
 decide +kernel
def pointBounds21488 : List (Nat × Nat × Nat) := [(2820464640,100949512815163,100949893724943)]
theorem point_links_checked21488 : (cuts21488.take 1).map (fun c => (2820407297-1+2*2^9*c.k,100949254337413+c.lower,100949635247038+c.upper)) = pointBounds21488 := by
 decide +kernel
def cuts21489 : List PrefixCut := [⟨15,71053657,71053698⟩,
⟨102,478307398,478307677⟩,
⟨128,601448969,601449321⟩]
theorem checked21489 : checkPrefixCuts (2^48) 2820538369 9 Manual.Count131072.C021489.packed 128 cuts21489 = true := by
 decide +kernel
def pointBounds21489 : List (Nat × Nat × Nat) := [(2820553728,100949924073470,100950304983487),(2820642816,100950331327211,100950712237466)]
theorem point_links_checked21489 : (cuts21489.take 2).map (fun c => (2820538369-1+2*2^9*c.k,100949853019813+c.lower,100950233929789+c.upper)) = pointBounds21489 := by
 decide +kernel
def cuts21490 : List PrefixCut := [⟨61,284199036,284199198⟩,
⟨128,598527103,598527449⟩]
theorem checked21490 : checkPrefixCuts (2^48) 2820669441 9 Manual.Count131072.C021490.packed 128 cuts21490 = true := by
 decide +kernel
def pointBounds21490 : List (Nat × Nat × Nat) := [(2820731904,100950738667818,100951119578308)]
theorem point_links_checked21490 : (cuts21490.take 1).map (fun c => (2820669441-1+2*2^9*c.k,100950454468782+c.lower,100950835379110+c.upper)) = pointBounds21490 := by
 decide +kernel
def cuts21491 : List PrefixCut := [⟨20,94696064,94696116⟩,
⟨107,502410097,502410384⟩,
⟨128,598898530,598898871⟩]
theorem checked21491 : checkPrefixCuts (2^48) 2820800513 9 Manual.Count131072.C021491.packed 128 cuts21491 = true := by
 decide +kernel
def pointBounds21491 : List (Nat × Nat × Nat) := [(2820820992,100951147691949,100951528602675),(2820910080,100951555405982,100951936316943)]
theorem point_links_checked21491 : (cuts21491.take 2).map (fun c => (2820800513-1+2*2^9*c.k,100951052995885+c.lower,100951433906559+c.upper)) = pointBounds21491 := by
 decide +kernel
def cuts21492 : List PrefixCut := [⟨66,311212642,311212827⟩,
⟨128,602163292,602163641⟩]
theorem checked21492 : checkPrefixCuts (2^48) 2820931585 9 Manual.Count131072.C021492.packed 128 cuts21492 = true := by
 decide +kernel
def pointBounds21492 : List (Nat × Nat × Nat) := [(2820999168,100951963107057,100952344018257)]
theorem point_links_checked21492 : (cuts21492.take 1).map (fun c => (2820931585-1+2*2^9*c.k,100951651894415+c.lower,100952032805430+c.upper)) = pointBounds21492 := by
 decide +kernel
def cuts21493 : List PrefixCut := [⟨25,117934932,117935003⟩,
⟨112,528403992,528404303⟩,
⟨128,602734018,602734373⟩]
theorem checked21493 : checkPrefixCuts (2^48) 2821062657 9 Manual.Count131072.C021493.packed 128 cuts21493 = true := by
 decide +kernel
def pointBounds21493 : List (Nat × Nat × Nat) := [(2821088256,100952371992639,100952752904074),(2821177344,100952782461699,100953163373374)]
theorem point_links_checked21493 : (cuts21493.take 2).map (fun c => (2821062657-1+2*2^9*c.k,100952254057707+c.lower,100952634969071+c.upper)) = pointBounds21493 := by
 decide +kernel
def cuts21494 : List PrefixCut := [⟨71,334030909,334031101⟩,
⟨128,603304590,603304932⟩]
theorem checked21494 : checkPrefixCuts (2^48) 2821193729 9 Manual.Count131072.C021494.packed 128 cuts21494 = true := by
 decide +kernel
def pointBounds21494 : List (Nat × Nat × Nat) := [(2821266432,100953190822634,100953571734545)]
theorem point_links_checked21494 : (cuts21494.take 1).map (fun c => (2821193729-1+2*2^9*c.k,100952856791725+c.lower,100953237703444+c.upper)) = pointBounds21494 := by
 decide +kernel
def cuts21495 : List PrefixCut := [⟨30,142167093,142167175⟩,
⟨117,554692397,554692713⟩,
⟨128,606269606,606269953⟩]
theorem checked21495 : checkPrefixCuts (2^48) 2821324801 9 Manual.Count131072.C021495.packed 128 cuts21495 = true := by
 decide +kernel
def pointBounds21495 : List (Nat × Nat × Nat) := [(2821355520,100953602263408,100953983175551),(2821444608,100954014788712,100954395701089)]
theorem point_links_checked21495 : (cuts21495.take 2).map (fun c => (2821324801-1+2*2^9*c.k,100953460096315+c.lower,100953841008376+c.upper)) = pointBounds21495 := by
 decide +kernel
def cuts21496 : List PrefixCut := [⟨76,354151272,354151483⟩,
⟨128,592474573,592474923⟩]
theorem checked21496 : checkPrefixCuts (2^48) 2821455873 9 Manual.Count131072.C021496.packed 128 cuts21496 = true := by
 decide +kernel
def pointBounds21496 : List (Nat × Nat × Nat) := [(2821533696,100954420517193,100954801429812)]
theorem point_links_checked21496 : (cuts21496.take 1).map (fun c => (2821455873-1+2*2^9*c.k,100954066365921+c.lower,100954447278329+c.upper)) = pointBounds21496 := by
 decide +kernel
def cuts21497 : List PrefixCut := [⟨35,163701258,163701353⟩,
⟨122,567508699,567509031⟩,
⟨128,596836119,596836467⟩]
theorem checked21497 : checkPrefixCuts (2^48) 2821586945 9 Manual.Count131072.C021497.packed 128 cuts21497 = true := by
 decide +kernel
def pointBounds21497 : List (Nat × Nat × Nat) := [(2821622784,100954822541752,100955203454605),(2821711872,100955226349193,100955607262283)]
theorem point_links_checked21497 : (cuts21497.take 2).map (fun c => (2821586945-1+2*2^9*c.k,100954658840494+c.lower,100955039753252+c.upper)) = pointBounds21497 := by
 decide +kernel
def cuts21498 : List PrefixCut := [⟨81,383345266,383345486⟩,
⟨128,606883296,606883650⟩]
theorem checked21498 : checkPrefixCuts (2^48) 2821718017 9 Manual.Count131072.C021498.packed 128 cuts21498 = true := by
 decide +kernel
def pointBounds21498 : List (Nat × Nat × Nat) := [(2821800960,100955639021879,100956019935205)]
theorem point_links_checked21498 : (cuts21498.take 1).map (fun c => (2821718017-1+2*2^9*c.k,100955255676613+c.lower,100955636589719+c.upper)) = pointBounds21498 := by
 decide +kernel
def cuts21499 : List PrefixCut := [⟨40,190917026,190917137⟩,
⟨127,596880652,596881006⟩,
⟨128,601468866,601469222⟩]
theorem checked21499 : checkPrefixCuts (2^48) 2821849089 9 Manual.Count131072.C021499.packed 128 cuts21499 = true := by
 decide +kernel
def pointBounds21499 : List (Nat × Nat × Nat) := [(2821890048,100956053476935,100956434390506),(2821979136,100956459440561,100956840354375)]
theorem point_links_checked21499 : (cuts21499.take 2).map (fun c => (2821849089-1+2*2^9*c.k,100955862559909+c.lower,100956243473369+c.upper)) = pointBounds21499 := by
 decide +kernel
def cuts21500 : List PrefixCut := [⟨86,406150222,406150452⟩,
⟨128,603734917,603735265⟩]
theorem checked21500 : checkPrefixCuts (2^48) 2821980161 9 Manual.Count131072.C021500.packed 128 cuts21500 = true := by
 decide +kernel
def pointBounds21500 : List (Nat × Nat × Nat) := [(2822068224,100956870178997,100957251093043)]
theorem point_links_checked21500 : (cuts21500.take 1).map (fun c => (2821980161-1+2*2^9*c.k,100956464028775+c.lower,100956844942591+c.upper)) = pointBounds21500 := by
 decide +kernel
def cuts21501 : List PrefixCut := [⟨45,211245739,211245865⟩,
⟨128,593733291,593733642⟩]
theorem checked21501 : checkPrefixCuts (2^48) 2822111233 9 Manual.Count131072.C021501.packed 128 cuts21501 = true := by
 decide +kernel
def pointBounds21501 : List (Nat × Nat × Nat) := [(2822157312,100957279009431,100957659923721)]
theorem point_links_checked21501 : (cuts21501.take 1).map (fun c => (2822111233-1+2*2^9*c.k,100957067763692+c.lower,100957448677856+c.upper)) = pointBounds21501 := by
 decide +kernel
def cuts21502 : List PrefixCut := [⟨4,20046618,20046629⟩,
⟨91,428452355,428452600⟩,
⟨128,604875670,604876014⟩]
theorem checked21502 : checkPrefixCuts (2^48) 2822242305 9 Manual.Count131072.C021502.packed 128 cuts21502 = true := by
 decide +kernel
def pointBounds21502 : List (Nat × Nat × Nat) := [(2822246400,100957681543601,100958062458127),(2822335488,100958089949338,100958470864098)]
theorem point_links_checked21502 : (cuts21502.take 2).map (fun c => (2822242305-1+2*2^9*c.k,100957661496983+c.lower,100958042411498+c.upper)) = pointBounds21502 := by
 decide +kernel
def cuts21503 : List PrefixCut := [⟨50,236955995,236956135⟩,
⟨128,606343433,606343783⟩]
theorem checked21503 : checkPrefixCuts (2^48) 2822373377 9 Manual.Count131072.C021503.packed 128 cuts21503 = true := by
 decide +kernel
def pointBounds21503 : List (Nat × Nat × Nat) := [(2822424576,100958503328648,100958884243647)]
theorem point_links_checked21503 : (cuts21503.take 1).map (fun c => (2822373377-1+2*2^9*c.k,100958266372653+c.lower,100958647287512+c.upper)) = pointBounds21503 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000046
