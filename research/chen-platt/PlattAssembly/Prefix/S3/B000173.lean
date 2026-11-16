import PlattAssemblyKernel
import PlattCertificates.Count131072.C025536
import PlattCertificates.Count131072.C025537
import PlattCertificates.Count131072.C025538
import PlattCertificates.Count131072.C025539
import PlattCertificates.Count131072.C025540
import PlattCertificates.Count131072.C025541
import PlattCertificates.Count131072.C025542
import PlattCertificates.Count131072.C025543
import PlattCertificates.Count131072.C025544
import PlattCertificates.Count131072.C025545
import PlattCertificates.Count131072.C025546
import PlattCertificates.Count131072.C025547
import PlattCertificates.Count131072.C025548
import PlattCertificates.Count131072.C025549
import PlattCertificates.Count131072.C025550
import PlattCertificates.Count131072.C025551
import PlattCertificates.Count131072.C025552
import PlattCertificates.Count131072.C025553
import PlattCertificates.Count131072.C025554
import PlattCertificates.Count131072.C025555
import PlattCertificates.Count131072.C025556
import PlattCertificates.Count131072.C025557
import PlattCertificates.Count131072.C025558
import PlattCertificates.Count131072.C025559
import PlattCertificates.Count131072.C025560
import PlattCertificates.Count131072.C025561
import PlattCertificates.Count131072.C025562
import PlattCertificates.Count131072.C025563
import PlattCertificates.Count131072.C025564
import PlattCertificates.Count131072.C025565
import PlattCertificates.Count131072.C025566
import PlattCertificates.Count131072.C025567
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000173
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25536 : List PrefixCut := [⟨3,10583694,10583700⟩,
⟨106,416705337,416705565⟩,
⟨128,501791879,501792157⟩]
theorem checked25536 : checkPrefixCuts (2^48) 3350986753 9 Manual.Count131072.C025536.packed 128 cuts25536 = true := by
 decide +kernel
def pointBounds25536 : List (Nat × Nat × Nat) := [(3350989824,103170081864539,103170464033588),(3351095296,103170487986182,103170870155453)]
theorem point_links_checked25536 : (cuts25536.take 2).map (fun c => (3350986753-1+2*2^9*c.k,103170071280845+c.lower,103170453449888+c.upper)) = pointBounds25536 := by
 decide +kernel
def cuts25537 : List PrefixCut := [⟨81,327321846,327322023⟩,
⟨128,506224068,506224345⟩]
theorem checked25537 : checkPrefixCuts (2^48) 3351117825 9 Manual.Count131072.C025537.packed 128 cuts25537 = true := by
 decide +kernel
def pointBounds25537 : List (Nat × Nat × Nat) := [(3351200768,103170900394570,103171282564068)]
theorem point_links_checked25537 : (cuts25537.take 1).map (fun c => (3351117825-1+2*2^9*c.k,103170573072724+c.lower,103170955242045+c.upper)) = pointBounds25537 := by
 decide +kernel
def cuts25538 : List PrefixCut := [⟨56,222826337,222826459⟩,
⟨128,506624069,506624353⟩]
theorem checked25538 : checkPrefixCuts (2^48) 3351248897 9 Manual.Count131072.C025538.packed 128 cuts25538 = true := by
 decide +kernel
def pointBounds25538 : List (Nat × Nat × Nat) := [(3351306240,103171302123129,103171684292849)]
theorem point_links_checked25538 : (cuts25538.take 1).map (fun c => (3351248897-1+2*2^9*c.k,103171079296792+c.lower,103171461466390+c.upper)) = pointBounds25538 := by
 decide +kernel
def cuts25539 : List PrefixCut := [⟨31,120353890,120353957⟩,
⟨128,500725206,500725486⟩]
theorem checked25539 : checkPrefixCuts (2^48) 3351379969 9 Manual.Count131072.C025539.packed 128 cuts25539 = true := by
 decide +kernel
def pointBounds25539 : List (Nat × Nat × Nat) := [(3351411712,103171706274751,103172088444700)]
theorem point_links_checked25539 : (cuts25539.take 1).map (fun c => (3351379969-1+2*2^9*c.k,103171585920861+c.lower,103171968090743+c.upper)) = pointBounds25539 := by
 decide +kernel
def cuts25540 : List PrefixCut := [⟨6,24439461,24439473⟩,
⟨109,430665253,430665494⟩,
⟨128,506164567,506164850⟩]
theorem checked25540 : checkPrefixCuts (2^48) 3351511041 9 Manual.Count131072.C025540.packed 128 cuts25540 = true := by
 decide +kernel
def pointBounds25540 : List (Nat × Nat × Nat) := [(3351517184,103172111085528,103172493255702),(3351622656,103172517311320,103172899481723)]
theorem point_links_checked25540 : (cuts25540.take 2).map (fun c => (3351511041-1+2*2^9*c.k,103172086646067+c.lower,103172468816229+c.upper)) = pointBounds25540 := by
 decide +kernel
def cuts25541 : List PrefixCut := [⟨84,329705968,329706158⟩,
⟨128,499762369,499762654⟩]
theorem checked25541 : checkPrefixCuts (2^48) 3351642113 9 Manual.Count131072.C025541.packed 128 cuts25541 = true := by
 decide +kernel
def pointBounds25541 : List (Nat × Nat × Nat) := [(3351728128,103172922516602,103173304687237)]
theorem point_links_checked25541 : (cuts25541.take 1).map (fun c => (3351642113-1+2*2^9*c.k,103172592810634+c.lower,103172974981079+c.upper)) = pointBounds25541 := by
 decide +kernel
def cuts25542 : List PrefixCut := [⟨59,226402389,226402515⟩,
⟨128,497895173,497895446⟩]
theorem checked25542 : checkPrefixCuts (2^48) 3351773185 9 Manual.Count131072.C025542.packed 128 cuts25542 = true := by
 decide +kernel
def pointBounds25542 : List (Nat × Nat × Nat) := [(3351833600,103173318975392,103173701146248)]
theorem point_links_checked25542 : (cuts25542.take 1).map (fun c => (3351773185-1+2*2^9*c.k,103173092573003+c.lower,103173474743733+c.upper)) = pointBounds25542 := by
 decide +kernel
def cuts25543 : List PrefixCut := [⟨34,133183068,133183144⟩,
⟨128,494936736,494937014⟩]
theorem checked25543 : checkPrefixCuts (2^48) 3351904257 9 Manual.Count131072.C025543.packed 128 cuts25543 = true := by
 decide +kernel
def pointBounds25543 : List (Nat × Nat × Nat) := [(3351939072,103173723651244,103174105822323)]
theorem point_links_checked25543 : (cuts25543.take 1).map (fun c => (3351904257-1+2*2^9*c.k,103173590468176+c.lower,103173972639179+c.upper)) = pointBounds25543 := by
 decide +kernel
def cuts25544 : List PrefixCut := [⟨9,33924374,33924394⟩,
⟨112,436055709,436055951⟩,
⟨128,496428893,496429168⟩]
theorem checked25544 : checkPrefixCuts (2^48) 3352035329 9 Manual.Count131072.C025544.packed 128 cuts25544 = true := by
 decide +kernel
def pointBounds25544 : List (Nat × Nat × Nat) := [(3352044544,103174119329286,103174501500587),(3352150016,103174521460621,103174903632144)]
theorem point_links_checked25544 : (cuts25544.take 2).map (fun c => (3352035329-1+2*2^9*c.k,103174085404912+c.lower,103174467576193+c.upper)) = pointBounds25544 := by
 decide +kernel
def cuts25545 : List PrefixCut := [⟨87,340233979,340234172⟩,
⟨128,500271829,500272113⟩]
theorem checked25545 : checkPrefixCuts (2^48) 3352166401 9 Manual.Count131072.C025545.packed 128 cuts25545 = true := by
 decide +kernel
def pointBounds25545 : List (Nat × Nat × Nat) := [(3352255488,103174922067784,103175304239533)]
theorem point_links_checked25545 : (cuts25545.take 1).map (fun c => (3352166401-1+2*2^9*c.k,103174581833805+c.lower,103174964005361+c.upper)) = pointBounds25545 := by
 decide +kernel
def cuts25546 : List PrefixCut := [⟨62,241564376,241564514⟩,
⟨128,500000411,500000693⟩]
theorem checked25546 : checkPrefixCuts (2^48) 3352297473 9 Manual.Count131072.C025546.packed 128 cuts25546 = true := by
 decide +kernel
def pointBounds25546 : List (Nat × Nat × Nat) := [(3352360960,103175323670010,103175705841988)]
theorem point_links_checked25546 : (cuts25546.take 1).map (fun c => (3352297473-1+2*2^9*c.k,103175082105634+c.lower,103175464277474+c.upper)) = pointBounds25546 := by
 decide +kernel
def cuts25547 : List PrefixCut := [⟨37,143909190,143909269⟩,
⟨128,499813025,499813307⟩]
theorem checked25547 : checkPrefixCuts (2^48) 3352428545 9 Manual.Count131072.C025547.packed 128 cuts25547 = true := by
 decide +kernel
def pointBounds25547 : List (Nat × Nat × Nat) := [(3352466432,103175726015235,103176108187436)]
theorem point_links_checked25547 : (cuts25547.take 1).map (fun c => (3352428545-1+2*2^9*c.k,103175582106045+c.lower,103175964278167+c.upper)) = pointBounds25547 := by
 decide +kernel
def cuts25548 : List PrefixCut := [⟨12,47940050,47940079⟩,
⟨115,458823561,458823818⟩,
⟨128,507265652,507265938⟩]
theorem checked25548 : checkPrefixCuts (2^48) 3352559617 9 Manual.Count131072.C025548.packed 128 cuts25548 = true := by
 decide +kernel
def pointBounds25548 : List (Nat × Nat × Nat) := [(3352571904,103176129859120,103176512031553),(3352677376,103176540742631,103176922915292)]
theorem point_links_checked25548 : (cuts25548.take 2).map (fun c => (3352559617-1+2*2^9*c.k,103176081919070+c.lower,103176464091474+c.upper)) = pointBounds25548 := by
 decide +kernel
def cuts25549 : List PrefixCut := [⟨90,355544209,355544410⟩,
⟨128,506574101,506574383⟩]
theorem checked25549 : checkPrefixCuts (2^48) 3352690689 9 Manual.Count131072.C025549.packed 128 cuts25549 = true := by
 decide +kernel
def pointBounds25549 : List (Nat × Nat × Nat) := [(3352782848,103176944728931,103177326901822)]
theorem point_links_checked25549 : (cuts25549.take 1).map (fun c => (3352690689-1+2*2^9*c.k,103176589184722+c.lower,103176971357412+c.upper)) = pointBounds25549 := by
 decide +kernel
def cuts25550 : List PrefixCut := [⟨65,252356163,252356312⟩,
⟨128,496228503,496228792⟩]
theorem checked25550 : checkPrefixCuts (2^48) 3352821761 9 Manual.Count131072.C025550.packed 128 cuts25550 = true := by
 decide +kernel
def pointBounds25550 : List (Nat × Nat × Nat) := [(3352888320,103177348114986,103177730288107)]
theorem point_links_checked25550 : (cuts25550.take 1).map (fun c => (3352821761-1+2*2^9*c.k,103177095758823+c.lower,103177477931795+c.upper)) = pointBounds25550 := by
 decide +kernel
def cuts25551 : List PrefixCut := [⟨40,160004613,160004703⟩,
⟨128,508297448,508297734⟩]
theorem checked25551 : checkPrefixCuts (2^48) 3352952833 9 Manual.Count131072.C025551.packed 128 cuts25551 = true := by
 decide +kernel
def pointBounds25551 : List (Nat × Nat × Nat) := [(3352993792,103177751991939,103178134165290)]
theorem point_links_checked25551 : (cuts25551.take 1).map (fun c => (3352952833-1+2*2^9*c.k,103177591987326+c.lower,103177974160587+c.upper)) = pointBounds25551 := by
 decide +kernel
def cuts25552 : List PrefixCut := [⟨15,57502250,57502283⟩,
⟨118,458499767,458500027⟩,
⟨128,495182389,495182668⟩]
theorem checked25552 : checkPrefixCuts (2^48) 3353083905 9 Manual.Count131072.C025552.packed 128 cuts25552 = true := by
 decide +kernel
def pointBounds25552 : List (Nat × Nat × Nat) := [(3353099264,103178157787024,103178539960604),(3353204736,103178558784541,103178940958348)]
theorem point_links_checked25552 : (cuts25552.take 2).map (fun c => (3353083905-1+2*2^9*c.k,103178100284774+c.lower,103178482458321+c.upper)) = pointBounds25552 := by
 decide +kernel
def cuts25553 : List PrefixCut := [⟨93,369422591,369422799⟩,
⟨128,511615204,511615492⟩]
theorem checked25553 : checkPrefixCuts (2^48) 3353214977 9 Manual.Count131072.C025553.packed 128 cuts25553 = true := by
 decide +kernel
def pointBounds25553 : List (Nat × Nat × Nat) := [(3353310208,103178964889754,103179347063788)]
theorem point_links_checked25553 : (cuts25553.take 1).map (fun c => (3353214977-1+2*2^9*c.k,103178595467163+c.lower,103178977640989+c.upper)) = pointBounds25553 := by
 decide +kernel
def cuts25554 : List PrefixCut := [⟨68,263396313,263396460⟩,
⟨128,499340433,499340714⟩]
theorem checked25554 : checkPrefixCuts (2^48) 3353346049 9 Manual.Count131072.C025554.packed 128 cuts25554 = true := by
 decide +kernel
def pointBounds25554 : List (Nat × Nat × Nat) := [(3353415680,103179370478680,103179752652941)]
theorem point_links_checked25554 : (cuts25554.take 1).map (fun c => (3353346049-1+2*2^9*c.k,103179107082367+c.lower,103179489256481+c.upper)) = pointBounds25554 := by
 decide +kernel
def cuts25555 : List PrefixCut := [⟨43,168876593,168876688⟩,
⟨128,504021243,504021528⟩]
theorem checked25555 : checkPrefixCuts (2^48) 3353477121 9 Manual.Count131072.C025555.packed 128 cuts25555 = true := by
 decide +kernel
def pointBounds25555 : List (Nat × Nat × Nat) := [(3353521152,103179775299393,103180157473883)]
theorem point_links_checked25555 : (cuts25555.take 1).map (fun c => (3353477121-1+2*2^9*c.k,103179606422800+c.lower,103179988597195+c.upper)) = pointBounds25555 := by
 decide +kernel
def cuts25556 : List PrefixCut := [⟨18,70418723,70418763⟩,
⟨121,475046153,475046415⟩,
⟨128,502574789,502575066⟩]
theorem checked25556 : checkPrefixCuts (2^48) 3353608193 9 Manual.Count131072.C025556.packed 128 cuts25556 = true := by
 decide +kernel
def pointBounds25556 : List (Nat × Nat × Nat) := [(3353626624,103180180862766,103180563037486),(3353732096,103180585490196,103180967665138)]
theorem point_links_checked25556 : (cuts25556.take 2).map (fun c => (3353608193-1+2*2^9*c.k,103180110444043+c.lower,103180492618723+c.upper)) = pointBounds25556 := by
 decide +kernel
def cuts25557 : List PrefixCut := [⟨96,377505597,377505802⟩,
⟨128,503310381,503310656⟩]
theorem checked25557 : checkPrefixCuts (2^48) 3353739265 9 Manual.Count131072.C025557.packed 128 cuts25557 = true := by
 decide +kernel
def pointBounds25557 : List (Nat × Nat × Nat) := [(3353837568,103180990524429,103181372699591)]
theorem point_links_checked25557 : (cuts25557.take 1).map (fun c => (3353739265-1+2*2^9*c.k,103180613018832+c.lower,103180995193789+c.upper)) = pointBounds25557 := by
 decide +kernel
def cuts25558 : List PrefixCut := [⟨71,281482734,281482899⟩,
⟨128,500857073,500857363⟩]
theorem checked25558 : checkPrefixCuts (2^48) 3353870337 9 Manual.Count131072.C025558.packed 128 cuts25558 = true := by
 decide +kernel
def pointBounds25558 : List (Nat × Nat × Nat) := [(3353943040,103181397811947,103181779987344)]
theorem point_links_checked25558 : (cuts25558.take 1).map (fun c => (3353870337-1+2*2^9*c.k,103181116329213+c.lower,103181498504445+c.upper)) = pointBounds25558 := by
 decide +kernel
def cuts25559 : List PrefixCut := [⟨46,178585014,178585113⟩,
⟨128,500166003,500166276⟩]
theorem checked25559 : checkPrefixCuts (2^48) 3354001409 9 Manual.Count131072.C025559.packed 128 cuts25559 = true := by
 decide +kernel
def pointBounds25559 : List (Nat × Nat × Nat) := [(3354048512,103181795771300,103182177946921)]
theorem point_links_checked25559 : (cuts25559.take 1).map (fun c => (3354001409-1+2*2^9*c.k,103181617186286+c.lower,103181999361808+c.upper)) = pointBounds25559 := by
 decide +kernel
def cuts25560 : List PrefixCut := [⟨21,78379938,78379982⟩,
⟨124,485041593,485041863⟩,
⟨128,500733812,500734091⟩]
theorem checked25560 : checkPrefixCuts (2^48) 3354132481 9 Manual.Count131072.C025560.packed 128 cuts25560 = true := by
 decide +kernel
def pointBounds25560 : List (Nat × Nat × Nat) := [(3354153984,103182195732227,103182577908066),(3354259456,103182602393882,103182984569947)]
theorem point_links_checked25560 : (cuts25560.take 2).map (fun c => (3354132481-1+2*2^9*c.k,103182117352289+c.lower,103182499528084+c.upper)) = pointBounds25560 := by
 decide +kernel
def cuts25561 : List PrefixCut := [⟨99,384830911,384831124⟩,
⟨128,499875162,499875439⟩]
theorem checked25561 : checkPrefixCuts (2^48) 3354263553 9 Manual.Count131072.C025561.packed 128 cuts25561 = true := by
 decide +kernel
def pointBounds25561 : List (Nat × Nat × Nat) := [(3354364928,103183002917012,103183385093299)]
theorem point_links_checked25561 : (cuts25561.take 1).map (fun c => (3354263553-1+2*2^9*c.k,103182618086101+c.lower,103183000262175+c.upper)) = pointBounds25561 := by
 decide +kernel
def cuts25562 : List PrefixCut := [⟨74,292095322,292095483⟩,
⟨128,505142049,505142328⟩]
theorem checked25562 : checkPrefixCuts (2^48) 3354394625 9 Manual.Count131072.C025562.packed 128 cuts25562 = true := by
 decide +kernel
def pointBounds25562 : List (Nat × Nat × Nat) := [(3354470400,103183410056585,103183792233097)]
theorem point_links_checked25562 : (cuts25562.take 1).map (fun c => (3354394625-1+2*2^9*c.k,103183117961263+c.lower,103183500137614+c.upper)) = pointBounds25562 := by
 decide +kernel
def cuts25563 : List PrefixCut := [⟨49,188290402,188290509⟩,
⟨128,506213026,506213307⟩]
theorem checked25563 : checkPrefixCuts (2^48) 3354525697 9 Manual.Count131072.C025563.packed 128 cuts25563 = true := by
 decide +kernel
def pointBounds25563 : List (Nat × Nat × Nat) := [(3354575872,103183811393714,103184193570451)]
theorem point_links_checked25563 : (cuts25563.take 1).map (fun c => (3354525697-1+2*2^9*c.k,103183623103312+c.lower,103184005279942+c.upper)) = pointBounds25563 := by
 decide +kernel
def cuts25564 : List PrefixCut := [⟨24,90198316,90198368⟩,
⟨127,501494694,501494976⟩,
⟨128,505438109,505438394⟩]
theorem checked25564 : checkPrefixCuts (2^48) 3354656769 9 Manual.Count131072.C025564.packed 128 cuts25564 = true := by
 decide +kernel
def pointBounds25564 : List (Nat × Nat × Nat) := [(3354681344,103184219514654,103184601691617),(3354786816,103184630811032,103185012988225)]
theorem point_links_checked25564 : (cuts25564.take 2).map (fun c => (3354656769-1+2*2^9*c.k,103184129316338+c.lower,103184511493249+c.upper)) = pointBounds25564 := by
 decide +kernel
def cuts25565 : List PrefixCut := [⟨102,394503163,394503380⟩,
⟨128,496524948,496525221⟩]
theorem checked25565 : checkPrefixCuts (2^48) 3354787841 9 Manual.Count131072.C025565.packed 128 cuts25565 = true := by
 decide +kernel
def pointBounds25565 : List (Nat × Nat × Nat) := [(3354892288,103185029257610,103185411435023)]
theorem point_links_checked25565 : (cuts25565.take 1).map (fun c => (3354787841-1+2*2^9*c.k,103184634754447+c.lower,103185016931643+c.upper)) = pointBounds25565 := by
 decide +kernel
def cuts25566 : List PrefixCut := [⟨77,298845359,298845526⟩,
⟨128,494911579,494911855⟩]
theorem checked25566 : checkPrefixCuts (2^48) 3354918913 9 Manual.Count131072.C025566.packed 128 cuts25566 = true := by
 decide +kernel
def pointBounds25566 : List (Nat × Nat × Nat) := [(3354997760,103185430124754,103185812302390)]
theorem point_links_checked25566 : (cuts25566.take 1).map (fun c => (3354918913-1+2*2^9*c.k,103185131279395+c.lower,103185513456864+c.upper)) = pointBounds25566 := by
 decide +kernel
def cuts25567 : List PrefixCut := [⟨52,208311825,208311945⟩,
⟨128,495311797,495312080⟩]
theorem checked25567 : checkPrefixCuts (2^48) 3355049985 9 Manual.Count131072.C025567.packed 128 cuts25567 = true := by
 decide +kernel
def pointBounds25567 : List (Nat × Nat × Nat) := [(3355103232,103185834502799,103186216680664)]
theorem point_links_checked25567 : (cuts25567.take 1).map (fun c => (3355049985-1+2*2^9*c.k,103185626190974+c.lower,103186008368719+c.upper)) = pointBounds25567 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000173
