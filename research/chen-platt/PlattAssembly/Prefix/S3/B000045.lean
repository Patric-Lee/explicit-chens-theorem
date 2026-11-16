import PlattAssemblyKernel
import PlattCertificates.Count131072.C021440
import PlattCertificates.Count131072.C021441
import PlattCertificates.Count131072.C021442
import PlattCertificates.Count131072.C021443
import PlattCertificates.Count131072.C021444
import PlattCertificates.Count131072.C021445
import PlattCertificates.Count131072.C021446
import PlattCertificates.Count131072.C021447
import PlattCertificates.Count131072.C021448
import PlattCertificates.Count131072.C021449
import PlattCertificates.Count131072.C021450
import PlattCertificates.Count131072.C021451
import PlattCertificates.Count131072.C021452
import PlattCertificates.Count131072.C021453
import PlattCertificates.Count131072.C021454
import PlattCertificates.Count131072.C021455
import PlattCertificates.Count131072.C021456
import PlattCertificates.Count131072.C021457
import PlattCertificates.Count131072.C021458
import PlattCertificates.Count131072.C021459
import PlattCertificates.Count131072.C021460
import PlattCertificates.Count131072.C021461
import PlattCertificates.Count131072.C021462
import PlattCertificates.Count131072.C021463
import PlattCertificates.Count131072.C021464
import PlattCertificates.Count131072.C021465
import PlattCertificates.Count131072.C021466
import PlattCertificates.Count131072.C021467
import PlattCertificates.Count131072.C021468
import PlattCertificates.Count131072.C021469
import PlattCertificates.Count131072.C021470
import PlattCertificates.Count131072.C021471
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000045
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21440 : List PrefixCut := [⟨68,321368348,321368536⟩,
⟨128,603721822,603722181⟩]
theorem checked21440 : checkPrefixCuts (2^48) 2814115841 9 Manual.Count131072.C021440.packed 128 cuts21440 = true := by
 decide +kernel
def pointBounds21440 : List (Nat × Nat × Nat) := [(2814185472,100920645723131,100921026616310)]
theorem point_links_checked21440 : (cuts21440.take 1).map (fun c => (2814115841-1+2*2^9*c.k,100920324354783+c.lower,100920705247774+c.upper)) = pointBounds21440 := by
 decide +kernel
def cuts21441 : List PrefixCut := [⟨26,122221226,122221299⟩,
⟨112,525383032,525383338⟩,
⟨128,600893206,600893556⟩]
theorem checked21441 : checkPrefixCuts (2^48) 2814246913 9 Manual.Count131072.C021441.packed 128 cuts21441 = true := by
 decide +kernel
def pointBounds21441 : List (Nat × Nat × Nat) := [(2814273536,100921050297831,100921431191254),(2814361600,100921453459637,100921834353293)]
theorem point_links_checked21441 : (cuts21441.take 2).map (fun c => (2814246913-1+2*2^9*c.k,100920928076605+c.lower,100921308969955+c.upper)) = pointBounds21441 := by
 decide +kernel
def cuts21442 : List PrefixCut := [⟨70,331539466,331539650⟩,
⟨128,609866128,609866477⟩]
theorem checked21442 : checkPrefixCuts (2^48) 2814377985 9 Manual.Count131072.C021442.packed 128 cuts21442 = true := by
 decide +kernel
def pointBounds21442 : List (Nat × Nat × Nat) := [(2814449664,100921860509277,100922241403161)]
theorem point_links_checked21442 : (cuts21442.take 1).map (fun c => (2814377985-1+2*2^9*c.k,100921528969811+c.lower,100921909863511+c.upper)) = pointBounds21442 := by
 decide +kernel
def cuts21443 : List PrefixCut := [⟨28,132010570,132010647⟩,
⟨114,541934940,541935253⟩,
⟨128,606937616,606937966⟩]
theorem checked21443 : checkPrefixCuts (2^48) 2814509057 9 Manual.Count131072.C021443.packed 128 cuts21443 = true := by
 decide +kernel
def pointBounds21443 : List (Nat × Nat × Nat) := [(2814537728,100922270846509,100922651740635),(2814625792,100922680770879,100923061665241)]
theorem point_links_checked21443 : (cuts21443.take 2).map (fun c => (2814509057-1+2*2^9*c.k,100922138835939+c.lower,100922519729988+c.upper)) = pointBounds21443 := by
 decide +kernel
def cuts21444 : List PrefixCut := [⟨72,336308594,336308790⟩,
⟨128,605409187,605409539⟩]
theorem checked21444 : checkPrefixCuts (2^48) 2814640129 9 Manual.Count131072.C021444.packed 128 cuts21444 = true := by
 decide +kernel
def pointBounds21444 : List (Nat × Nat × Nat) := [(2814713856,100923082082149,100923462976744)]
theorem point_links_checked21444 : (cuts21444.take 1).map (fun c => (2814640129-1+2*2^9*c.k,100922745773555+c.lower,100923126667954+c.upper)) = pointBounds21444 := by
 decide +kernel
def cuts21445 : List PrefixCut := [⟨30,138298138,138298219⟩,
⟨116,549584037,549584362⟩,
⟨128,607381013,607381371⟩]
theorem checked21445 : checkPrefixCuts (2^48) 2814771201 9 Manual.Count131072.C021445.packed 128 cuts21445 = true := by
 decide +kernel
def pointBounds21445 : List (Nat × Nat × Nat) := [(2814801920,100923489480880,100923870375712),(2814889984,100923900766779,100924281661855)]
theorem point_links_checked21445 : (cuts21445.take 2).map (fun c => (2814771201-1+2*2^9*c.k,100923351182742+c.lower,100923732077493+c.upper)) = pointBounds21445 := by
 decide +kernel
def cuts21446 : List PrefixCut := [⟨74,351576112,351576318⟩,
⟨128,601953278,601953636⟩]
theorem checked21446 : checkPrefixCuts (2^48) 2814902273 9 Manual.Count131072.C021446.packed 128 cuts21446 = true := by
 decide +kernel
def pointBounds21446 : List (Nat × Nat × Nat) := [(2814978048,100924310139867,100924691035182)]
theorem point_links_checked21446 : (cuts21446.take 1).map (fun c => (2814902273-1+2*2^9*c.k,100923958563755+c.lower,100924339458864+c.upper)) = pointBounds21446 := by
 decide +kernel
def cuts21447 : List PrefixCut := [⟨32,145384455,145384540⟩,
⟨118,547332886,547333197⟩,
⟨128,594226049,594226387⟩]
theorem checked21447 : checkPrefixCuts (2^48) 2815033345 9 Manual.Count131072.C021447.packed 128 cuts21447 = true := by
 decide +kernel
def pointBounds21447 : List (Nat × Nat × Nat) := [(2815066112,100924705901488,100925086797040),(2815154176,100925107849919,100925488745697)]
theorem point_links_checked21447 : (cuts21447.take 2).map (fun c => (2815033345-1+2*2^9*c.k,100924560517033+c.lower,100924941412500+c.upper)) = pointBounds21447 := by
 decide +kernel
def cuts21448 : List PrefixCut := [⟨76,361641664,361641874⟩,
⟨128,603097075,603097422⟩]
theorem checked21448 : checkPrefixCuts (2^48) 2815164417 9 Manual.Count131072.C021448.packed 128 cuts21448 = true := by
 decide +kernel
def pointBounds21448 : List (Nat × Nat × Nat) := [(2815242240,100925516384746,100925897280761)]
theorem point_links_checked21448 : (cuts21448.take 1).map (fun c => (2815164417-1+2*2^9*c.k,100925154743082+c.lower,100925535638887+c.upper)) = pointBounds21448 := by
 decide +kernel
def cuts21449 : List PrefixCut := [⟨34,163267296,163267391⟩,
⟨120,567877461,567877788⟩,
⟨128,606568202,606568551⟩]
theorem checked21449 : checkPrefixCuts (2^48) 2815295489 9 Manual.Count131072.C021449.packed 128 cuts21449 = true := by
 decide +kernel
def pointBounds21449 : List (Nat × Nat × Nat) := [(2815330304,100925921107453,100926302003700),(2815418368,100926325717618,100926706614097)]
theorem point_links_checked21449 : (cuts21449.take 2).map (fun c => (2815295489-1+2*2^9*c.k,100925757840157+c.lower,100926138736309+c.upper)) = pointBounds21449 := by
 decide +kernel
def cuts21450 : List PrefixCut := [⟨78,368006173,368006388⟩,
⟨128,608839185,608839529⟩]
theorem checked21450 : checkPrefixCuts (2^48) 2815426561 9 Manual.Count131072.C021450.packed 128 cuts21450 = true := by
 decide +kernel
def pointBounds21450 : List (Nat × Nat × Nat) := [(2815506432,100926732414532,100927113311248)]
theorem point_links_checked21450 : (cuts21450.take 1).map (fun c => (2815426561-1+2*2^9*c.k,100926364408359+c.lower,100926745304860+c.upper)) = pointBounds21450 := by
 decide +kernel
def cuts21451 : List PrefixCut := [⟨36,172749248,172749345⟩,
⟨122,576321704,576322036⟩,
⟨128,603912524,603912872⟩]
theorem checked21451 : checkPrefixCuts (2^48) 2815557633 9 Manual.Count131072.C021451.packed 128 cuts21451 = true := by
 decide +kernel
def pointBounds21451 : List (Nat × Nat × Nat) := [(2815594496,100927145996792,100927526893734),(2815682560,100927549569248,100927930466425)]
theorem point_links_checked21451 : (cuts21451.take 2).map (fun c => (2815557633-1+2*2^9*c.k,100926973247544+c.lower,100927354144389+c.upper)) = pointBounds21451 := by
 decide +kernel
def cuts21452 : List PrefixCut := [⟨80,376068996,376069209⟩,
⟨128,602884715,602885060⟩]
theorem checked21452 : checkPrefixCuts (2^48) 2815688705 9 Manual.Count131072.C021452.packed 128 cuts21452 = true := by
 decide +kernel
def pointBounds21452 : List (Nat × Nat × Nat) := [(2815770624,100927953229064,100928334126470)]
theorem point_links_checked21452 : (cuts21452.take 1).map (fun c => (2815688705-1+2*2^9*c.k,100927577160068+c.lower,100927958057261+c.upper)) = pointBounds21452 := by
 decide +kernel
def cuts21453 : List PrefixCut := [⟨38,180030242,180030344⟩,
⟨124,578766758,578767096⟩,
⟨128,597258876,597259222⟩]
theorem checked21453 : checkPrefixCuts (2^48) 2815819777 9 Manual.Count131072.C021453.packed 128 cuts21453 = true := by
 decide +kernel
def pointBounds21453 : List (Nat × Nat × Nat) := [(2815858688,100928360075025,100928740972665),(2815946752,100928758811541,100929139709417)]
theorem point_links_checked21453 : (cuts21453.take 2).map (fun c => (2815819777-1+2*2^9*c.k,100928180044783+c.lower,100928560942321+c.upper)) = pointBounds21453 := by
 decide +kernel
def cuts21454 : List PrefixCut := [⟨82,387928591,387928812⟩,
⟨128,605327456,605327800⟩]
theorem checked21454 : checkPrefixCuts (2^48) 2815950849 9 Manual.Count131072.C021454.packed 128 cuts21454 = true := by
 decide +kernel
def pointBounds21454 : List (Nat × Nat × Nat) := [(2816034816,100929165232250,100929546130355)]
theorem point_links_checked21454 : (cuts21454.take 1).map (fun c => (2815950849-1+2*2^9*c.k,100928777303659+c.lower,100929158201543+c.upper)) = pointBounds21454 := by
 decide +kernel
def cuts21455 : List PrefixCut := [⟨40,183111941,183112047⟩,
⟨126,586908479,586908816⟩,
⟨128,596103699,596104042⟩]
theorem checked21455 : checkPrefixCuts (2^48) 2816081921 9 Manual.Count131072.C021455.packed 128 cuts21455 = true := by
 decide +kernel
def pointBounds21455 : List (Nat × Nat × Nat) := [(2816122880,100929565743056,100929946641390),(2816210944,100929969539594,100930350438159)]
theorem point_links_checked21455 : (cuts21455.take 2).map (fun c => (2816081921-1+2*2^9*c.k,100929382631115+c.lower,100929763529343+c.upper)) = pointBounds21455 := by
 decide +kernel
def cuts21456 : List PrefixCut := [⟨84,390490926,390491153⟩,
⟨128,598174880,598175226⟩]
theorem checked21456 : checkPrefixCuts (2^48) 2816212993 9 Manual.Count131072.C021456.packed 128 cuts21456 = true := by
 decide +kernel
def pointBounds21456 : List (Nat × Nat × Nat) := [(2816299008,100930369225740,100930750124538)]
theorem point_links_checked21456 : (cuts21456.take 1).map (fun c => (2816212993-1+2*2^9*c.k,100929978734814+c.lower,100930359633385+c.upper)) = pointBounds21456 := by
 decide +kernel
def cuts21457 : List PrefixCut := [⟨42,196187335,196187448⟩,
⟨128,601045455,601045794⟩]
theorem checked21457 : checkPrefixCuts (2^48) 2816344065 9 Manual.Count131072.C021457.packed 128 cuts21457 = true := by
 decide +kernel
def pointBounds21457 : List (Nat × Nat × Nat) := [(2816387072,100930773097029,100931153996059),(2816475136,100931177955149,100931558854405)]
theorem point_links_checked21457 : (cuts21457.take 2).map (fun c => (2816344065-1+2*2^9*c.k,100930576909694+c.lower,100930957808611+c.upper)) = pointBounds21457 := by
 decide +kernel
def cuts21458 : List PrefixCut := [⟨86,408643029,408643262⟩,
⟨128,603815738,603816082⟩]
theorem checked21458 : checkPrefixCuts (2^48) 2816475137 9 Manual.Count131072.C021458.packed 128 cuts21458 = true := by
 decide +kernel
def pointBounds21458 : List (Nat × Nat × Nat) := [(2816563200,100931586598178,100931967497667)]
theorem point_links_checked21458 : (cuts21458.take 1).map (fun c => (2816475137-1+2*2^9*c.k,100931177955149+c.lower,100931558854405+c.upper)) = pointBounds21458 := by
 decide +kernel
def cuts21459 : List PrefixCut := [⟨44,206062398,206062518⟩,
⟨128,595493265,595493609⟩]
theorem checked21459 : checkPrefixCuts (2^48) 2816606209 9 Manual.Count131072.C021459.packed 128 cuts21459 = true := by
 decide +kernel
def pointBounds21459 : List (Nat × Nat × Nat) := [(2816651264,100931987833285,100932368733005)]
theorem point_links_checked21459 : (cuts21459.take 1).map (fun c => (2816606209-1+2*2^9*c.k,100931781770887+c.lower,100932162670487+c.upper)) = pointBounds21459 := by
 decide +kernel
def cuts21460 : List PrefixCut := [⟨2,8693856,8693860⟩,
⟨88,410203723,410203952⟩,
⟨128,601261231,601261568⟩]
theorem checked21460 : checkPrefixCuts (2^48) 2816737281 9 Manual.Count131072.C021460.packed 128 cuts21460 = true := by
 decide +kernel
def pointBounds21460 : List (Nat × Nat × Nat) := [(2816739328,100932385958008,100932766857956),(2816827392,100932787467875,100933168368048)]
theorem point_links_checked21460 : (cuts21460.take 2).map (fun c => (2816737281-1+2*2^9*c.k,100932377264152+c.lower,100932758164096+c.upper)) = pointBounds21460 := by
 decide +kernel
def cuts21461 : List PrefixCut := [⟨46,215236139,215236264⟩,
⟨128,598635300,598635644⟩]
theorem checked21461 : checkPrefixCuts (2^48) 2816868353 9 Manual.Count131072.C021461.packed 128 cuts21461 = true := by
 decide +kernel
def pointBounds21461 : List (Nat × Nat × Nat) := [(2816915456,100933193761522,100933574661928)]
theorem point_links_checked21461 : (cuts21461.take 1).map (fun c => (2816868353-1+2*2^9*c.k,100932978525383+c.lower,100933359425664+c.upper)) = pointBounds21461 := by
 decide +kernel
def cuts21462 : List PrefixCut := [⟨4,19684247,19684257⟩,
⟨90,426851795,426852038⟩,
⟨128,607100514,607100863⟩]
theorem checked21462 : checkPrefixCuts (2^48) 2816999425 9 Manual.Count131072.C021462.packed 128 cuts21462 = true := by
 decide +kernel
def pointBounds21462 : List (Nat × Nat × Nat) := [(2817003520,100933596844930,100933977745565),(2817091584,100934004012478,100934384913346)]
theorem point_links_checked21462 : (cuts21462.take 2).map (fun c => (2816999425-1+2*2^9*c.k,100933577160683+c.lower,100933958061308+c.upper)) = pointBounds21462 := by
 decide +kernel
def cuts21463 : List PrefixCut := [⟨48,227905180,227905317⟩,
⟨128,598579683,598580037⟩]
theorem checked21463 : checkPrefixCuts (2^48) 2817130497 9 Manual.Count131072.C021463.packed 128 cuts21463 = true := by
 decide +kernel
def pointBounds21463 : List (Nat × Nat × Nat) := [(2817179648,100934412166377,100934793067488)]
theorem point_links_checked21463 : (cuts21463.take 1).map (fun c => (2817130497-1+2*2^9*c.k,100934184261197+c.lower,100934565162171+c.upper)) = pointBounds21463 := by
 decide +kernel
def cuts21464 : List PrefixCut := [⟨6,27575354,27575370⟩,
⟨92,428110669,428110914⟩,
⟨128,593356555,593356897⟩]
theorem checked21464 : checkPrefixCuts (2^48) 2817261569 9 Manual.Count131072.C021464.packed 128 cuts21464 = true := by
 decide +kernel
def pointBounds21464 : List (Nat × Nat × Nat) := [(2817267712,100934810416234,100935191317578),(2817355776,100935210951549,100935591853122)]
theorem point_links_checked21464 : (cuts21464.take 2).map (fun c => (2817261569-1+2*2^9*c.k,100934782840880+c.lower,100935163742208+c.upper)) = pointBounds21464 := by
 decide +kernel
def cuts21465 : List PrefixCut := [⟨50,237774519,237774653⟩,
⟨128,608614206,608614549⟩]
theorem checked21465 : checkPrefixCuts (2^48) 2817392641 9 Manual.Count131072.C021465.packed 128 cuts21465 = true := by
 decide +kernel
def pointBounds21465 : List (Nat × Nat × Nat) := [(2817443840,100935613971954,100935994873758)]
theorem point_links_checked21465 : (cuts21465.take 1).map (fun c => (2817392641-1+2*2^9*c.k,100935376197435+c.lower,100935757099105+c.upper)) = pointBounds21465 := by
 decide +kernel
def cuts21466 : List PrefixCut := [⟨8,37662817,37662837⟩,
⟨94,442556150,442556404⟩,
⟨128,599495116,599495464⟩]
theorem checked21466 : checkPrefixCuts (2^48) 2817523713 9 Manual.Count131072.C021466.packed 128 cuts21466 = true := by
 decide +kernel
def pointBounds21466 : List (Nat × Nat × Nat) := [(2817531904,100936022474458,100936403376491),(2817619968,100936427367791,100936808270058)]
theorem point_links_checked21466 : (cuts21466.take 2).map (fun c => (2817523713-1+2*2^9*c.k,100935984811641+c.lower,100936365713654+c.upper)) = pointBounds21466 := by
 decide +kernel
def cuts21467 : List PrefixCut := [⟨52,248640964,248641106⟩,
⟨128,612353590,612353936⟩]
theorem checked21467 : checkPrefixCuts (2^48) 2817654785 9 Manual.Count131072.C021467.packed 128 cuts21467 = true := by
 decide +kernel
def pointBounds21467 : List (Nat × Nat × Nat) := [(2817708032,100936832947721,100937213850224)]
theorem point_links_checked21467 : (cuts21467.take 1).map (fun c => (2817654785-1+2*2^9*c.k,100936584306757+c.lower,100936965209118+c.upper)) = pointBounds21467 := by
 decide +kernel
def cuts21468 : List PrefixCut := [⟨10,46050233,46050259⟩,
⟨96,454401737,454401999⟩,
⟨128,605732289,605732640⟩]
theorem checked21468 : checkPrefixCuts (2^48) 2817785857 9 Manual.Count131072.C021468.packed 128 cuts21468 = true := by
 decide +kernel
def pointBounds21468 : List (Nat × Nat × Nat) := [(2817796096,100937242710580,100937623613313),(2817884160,100937651062084,100938031965053)]
theorem point_links_checked21468 : (cuts21468.take 2).map (fun c => (2817785857-1+2*2^9*c.k,100937196660347+c.lower,100937577563054+c.upper)) = pointBounds21468 := by
 decide +kernel
def cuts21469 : List PrefixCut := [⟨54,255809564,255809708⟩,
⟨128,605504371,605504715⟩]
theorem checked21469 : checkPrefixCuts (2^48) 2817916929 9 Manual.Count131072.C021469.packed 128 cuts21469 = true := by
 decide +kernel
def pointBounds21469 : List (Nat × Nat × Nat) := [(2817972224,100938058202200,100938439105402)]
theorem point_links_checked21469 : (cuts21469.take 1).map (fun c => (2817916929-1+2*2^9*c.k,100937802392636+c.lower,100938183295694+c.upper)) = pointBounds21469 := by
 decide +kernel
def cuts21470 : List PrefixCut := [⟨12,54635843,54635877⟩,
⟨98,459752918,459753185⟩,
⟨128,598384743,598385092⟩]
theorem checked21470 : checkPrefixCuts (2^48) 2818048001 9 Manual.Count131072.C021470.packed 128 cuts21470 = true := by
 decide +kernel
def pointBounds21470 : List (Nat × Nat × Nat) := [(2818060288,100938462532850,100938843436286),(2818148352,100938867649925,100939248553594)]
theorem point_links_checked21470 : (cuts21470.take 2).map (fun c => (2818048001-1+2*2^9*c.k,100938407897007+c.lower,100938788800409+c.upper)) = pointBounds21470 := by
 decide +kernel
def cuts21471 : List PrefixCut := [⟨57,268470053,268470205⟩,
⟨128,597757712,597758050⟩]
theorem checked21471 : checkPrefixCuts (2^48) 2818179073 9 Manual.Count131072.C021471.packed 128 cuts21471 = true := by
 decide +kernel
def pointBounds21471 : List (Nat × Nat × Nat) := [(2818237440,100939274751803,100939655655706)]
theorem point_links_checked21471 : (cuts21471.take 1).map (fun c => (2818179073-1+2*2^9*c.k,100939006281750+c.lower,100939387185501+c.upper)) = pointBounds21471 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000045
