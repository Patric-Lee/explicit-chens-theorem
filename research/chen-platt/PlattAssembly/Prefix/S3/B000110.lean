import PlattAssemblyKernel
import PlattCertificates.Count131072.C023520
import PlattCertificates.Count131072.C023521
import PlattCertificates.Count131072.C023522
import PlattCertificates.Count131072.C023523
import PlattCertificates.Count131072.C023524
import PlattCertificates.Count131072.C023525
import PlattCertificates.Count131072.C023526
import PlattCertificates.Count131072.C023527
import PlattCertificates.Count131072.C023528
import PlattCertificates.Count131072.C023529
import PlattCertificates.Count131072.C023530
import PlattCertificates.Count131072.C023531
import PlattCertificates.Count131072.C023532
import PlattCertificates.Count131072.C023533
import PlattCertificates.Count131072.C023534
import PlattCertificates.Count131072.C023535
import PlattCertificates.Count131072.C023536
import PlattCertificates.Count131072.C023537
import PlattCertificates.Count131072.C023538
import PlattCertificates.Count131072.C023539
import PlattCertificates.Count131072.C023540
import PlattCertificates.Count131072.C023541
import PlattCertificates.Count131072.C023542
import PlattCertificates.Count131072.C023543
import PlattCertificates.Count131072.C023544
import PlattCertificates.Count131072.C023545
import PlattCertificates.Count131072.C023546
import PlattCertificates.Count131072.C023547
import PlattCertificates.Count131072.C023548
import PlattCertificates.Count131072.C023549
import PlattCertificates.Count131072.C023550
import PlattCertificates.Count131072.C023551
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000110
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23520 : List PrefixCut := [⟨13,54165696,54165726⟩,
⟨108,458851004,458851261⟩,
⟨128,547300127,547300435⟩]
theorem checked23520 : checkPrefixCuts (2^48) 3086745601 9 Manual.Count131072.C023520.packed 128 cuts23520 = true := by
 decide +kernel
def pointBounds23520 : List (Nat × Nat × Nat) := [(3086758912,102114107580254,102114489154728),(3086856192,102114512265562,102114893840263)]
theorem point_links_checked23520 : (cuts23520.take 2).map (fun c => (3086745601-1+2*2^9*c.k,102114053414558+c.lower,102114434989002+c.upper)) = pointBounds23520 := by
 decide +kernel
def cuts23521 : List PrefixCut := [⟨75,320782630,320782813⟩,
⟨128,551562477,551562788⟩]
theorem checked23521 : checkPrefixCuts (2^48) 3086876673 9 Manual.Count131072.C023521.packed 128 cuts23521 = true := by
 decide +kernel
def pointBounds23521 : List (Nat × Nat × Nat) := [(3086953472,102114921497315,102115303072250)]
theorem point_links_checked23521 : (cuts23521.take 1).map (fun c => (3086876673-1+2*2^9*c.k,102114600714685+c.lower,102114982289437+c.upper)) = pointBounds23521 := by
 decide +kernel
def cuts23522 : List PrefixCut := [⟨42,183453876,183453982⟩,
⟨128,548986178,548986505⟩]
theorem checked23522 : checkPrefixCuts (2^48) 3087007745 9 Manual.Count131072.C023522.packed 128 cuts23522 = true := by
 decide +kernel
def pointBounds23522 : List (Nat × Nat × Nat) := [(3087050752,102115335731038,102115717306207)]
theorem point_links_checked23522 : (cuts23522.take 1).map (fun c => (3087007745-1+2*2^9*c.k,102115152277162+c.lower,102115533852225+c.upper)) = pointBounds23522 := by
 decide +kernel
def cuts23523 : List PrefixCut := [⟨9,38658832,38658852⟩,
⟨104,444296026,444296273⟩,
⟨128,547777512,547777815⟩]
theorem checked23523 : checkPrefixCuts (2^48) 3087138817 9 Manual.Count131072.C023523.packed 128 cuts23523 = true := by
 decide +kernel
def pointBounds23523 : List (Nat × Nat × Nat) := [(3087148032,102115739922172,102116121497582),(3087245312,102116145559366,102116527135003)]
theorem point_links_checked23523 : (cuts23523.take 2).map (fun c => (3087138817-1+2*2^9*c.k,102115701263340+c.lower,102116082838730+c.upper)) = pointBounds23523 := by
 decide +kernel
def cuts23524 : List PrefixCut := [⟨71,300684190,300684359⟩,
⟨128,549121733,549122044⟩]
theorem checked23524 : checkPrefixCuts (2^48) 3087269889 9 Manual.Count131072.C023524.packed 128 cuts23524 = true := by
 decide +kernel
def pointBounds23524 : List (Nat × Nat × Nat) := [(3087342592,102116549725042,102116931300904)]
theorem point_links_checked23524 : (cuts23524.take 1).map (fun c => (3087269889-1+2*2^9*c.k,102116249040852+c.lower,102116630616545+c.upper)) = pointBounds23524 := by
 decide +kernel
def cuts23525 : List PrefixCut := [⟨38,160456233,160456326⟩,
⟨128,546636977,546637287⟩]
theorem checked23525 : checkPrefixCuts (2^48) 3087400961 9 Manual.Count131072.C023525.packed 128 cuts23525 = true := by
 decide +kernel
def pointBounds23525 : List (Nat × Nat × Nat) := [(3087439872,102116958618818,102117340194915)]
theorem point_links_checked23525 : (cuts23525.take 1).map (fun c => (3087400961-1+2*2^9*c.k,102116798162585+c.lower,102117179738589+c.upper)) = pointBounds23525 := by
 decide +kernel
def cuts23526 : List PrefixCut := [⟨5,20512111,20512122⟩,
⟨100,424183789,424184027⟩,
⟨128,541599879,541600184⟩]
theorem checked23526 : checkPrefixCuts (2^48) 3087532033 9 Manual.Count131072.C023526.packed 128 cuts23526 = true := by
 decide +kernel
def pointBounds23526 : List (Nat × Nat × Nat) := [(3087537152,102117365311673,102117746887998),(3087634432,102117768983351,102118150559903)]
theorem point_links_checked23526 : (cuts23526.take 2).map (fun c => (3087532033-1+2*2^9*c.k,102117344799562+c.lower,102117726375876+c.upper)) = pointBounds23526 := by
 decide +kernel
def cuts23527 : List PrefixCut := [⟨67,282869899,282870062⟩,
⟨128,540574129,540574433⟩]
theorem checked23527 : checkPrefixCuts (2^48) 3087663105 9 Manual.Count131072.C023527.packed 128 cuts23527 = true := by
 decide +kernel
def pointBounds23527 : List (Nat × Nat × Nat) := [(3087731712,102118169269340,102118550846122)]
theorem point_links_checked23527 : (cuts23527.take 1).map (fun c => (3087663105-1+2*2^9*c.k,102117886399441+c.lower,102118267976060+c.upper)) = pointBounds23527 := by
 decide +kernel
def cuts23528 : List PrefixCut := [⟨34,145395040,145395125⟩,
⟨128,545473592,545473904⟩]
theorem checked23528 : checkPrefixCuts (2^48) 3087794177 9 Manual.Count131072.C023528.packed 128 cuts23528 = true := by
 decide +kernel
def pointBounds23528 : List (Nat × Nat × Nat) := [(3087828992,102118572368610,102118953945618)]
theorem point_links_checked23528 : (cuts23528.take 1).map (fun c => (3087794177-1+2*2^9*c.k,102118426973570+c.lower,102118808550493+c.upper)) = pointBounds23528 := by
 decide +kernel
def cuts23529 : List PrefixCut := [⟨1,4010749,4010751⟩,
⟨96,409910304,409910538⟩,
⟨128,547364512,547364823⟩]
theorem checked23529 : checkPrefixCuts (2^48) 3087925249 9 Manual.Count131072.C023529.packed 128 cuts23529 = true := by
 decide +kernel
def pointBounds23529 : List (Nat × Nat × Nat) := [(3087926272,102118976457911,102119358035148),(3088023552,102119382357466,102119763934935)]
theorem point_links_checked23529 : (cuts23529.take 2).map (fun c => (3087925249-1+2*2^9*c.k,102118972447162+c.lower,102119354024397+c.upper)) = pointBounds23529 := by
 decide +kernel
def cuts23530 : List PrefixCut := [⟨63,274812985,274813138⟩,
⟨128,556364984,556365301⟩]
theorem checked23530 : checkPrefixCuts (2^48) 3088056321 9 Manual.Count131072.C023530.packed 128 cuts23530 = true := by
 decide +kernel
def pointBounds23530 : List (Nat × Nat × Nat) := [(3088120832,102119794624659,102120176202358)]
theorem point_links_checked23530 : (cuts23530.take 1).map (fun c => (3088056321-1+2*2^9*c.k,102119519811674+c.lower,102119901389220+c.upper)) = pointBounds23530 := by
 decide +kernel
def cuts23531 : List PrefixCut := [⟨30,123046045,123046115⟩,
⟨125,526264172,526264467⟩,
⟨128,538021469,538021772⟩]
theorem checked23531 : checkPrefixCuts (2^48) 3088187393 9 Manual.Count131072.C023531.packed 128 cuts23531 = true := by
 decide +kernel
def pointBounds23531 : List (Nat × Nat × Nat) := [(3088218112,102120199222703,102120580800636),(3088315392,102120602440830,102120984018988)]
theorem point_links_checked23531 : (cuts23531.take 2).map (fun c => (3088187393-1+2*2^9*c.k,102120076176658+c.lower,102120457754521+c.upper)) = pointBounds23531 := by
 decide +kernel
def cuts23532 : List PrefixCut := [⟨92,383792236,383792464⟩,
⟨128,537725109,537725420⟩]
theorem checked23532 : checkPrefixCuts (2^48) 3088318465 9 Manual.Count131072.C023532.packed 128 cuts23532 = true := by
 decide +kernel
def pointBounds23532 : List (Nat × Nat × Nat) := [(3088412672,102120997990363,102121379568757)]
theorem point_links_checked23532 : (cuts23532.take 1).map (fun c => (3088318465-1+2*2^9*c.k,102120614198127+c.lower,102120995776293+c.upper)) = pointBounds23532 := by
 decide +kernel
def cuts23533 : List PrefixCut := [⟨59,251993902,251994041⟩,
⟨128,542623788,542624096⟩]
theorem checked23533 : checkPrefixCuts (2^48) 3088449537 9 Manual.Count131072.C023533.packed 128 cuts23533 = true := by
 decide +kernel
def pointBounds23533 : List (Nat × Nat × Nat) := [(3088509952,102121403917138,102121785495754)]
theorem point_links_checked23533 : (cuts23533.take 1).map (fun c => (3088449537-1+2*2^9*c.k,102121151923236+c.lower,102121533501713+c.upper)) = pointBounds23533 := by
 decide +kernel
def cuts23534 : List PrefixCut := [⟨26,112823487,112823553⟩,
⟨121,518177879,518178181⟩,
⟨128,546610533,546610850⟩]
theorem checked23534 : checkPrefixCuts (2^48) 3088580609 9 Manual.Count131072.C023534.packed 128 cuts23534 = true := by
 decide +kernel
def pointBounds23534 : List (Nat × Nat × Nat) := [(3088607232,102121807370511,102122188949362),(3088704512,102122212724903,102122594303990)]
theorem point_links_checked23534 : (cuts23534.take 2).map (fun c => (3088580609-1+2*2^9*c.k,102121694547024+c.lower,102122076125809+c.upper)) = pointBounds23534 := by
 decide +kernel
def cuts23535 : List PrefixCut := [⟨88,372990435,372990646⟩,
⟨128,544309061,544309371⟩]
theorem checked23535 : checkPrefixCuts (2^48) 3088711681 9 Manual.Count131072.C023535.packed 128 cuts23535 = true := by
 decide +kernel
def pointBounds23535 : List (Nat × Nat × Nat) := [(3088801792,102122614147992,102122995727305)]
theorem point_links_checked23535 : (cuts23535.take 1).map (fun c => (3088711681-1+2*2^9*c.k,102122241157557+c.lower,102122622736659+c.upper)) = pointBounds23535 := by
 decide +kernel
def cuts23536 : List PrefixCut := [⟨55,237199698,237199826⟩,
⟨128,545926337,545926635⟩]
theorem checked23536 : checkPrefixCuts (2^48) 3088842753 9 Manual.Count131072.C023536.packed 128 cuts23536 = true := by
 decide +kernel
def pointBounds23536 : List (Nat × Nat × Nat) := [(3088899072,102123022666316,102123404245856)]
theorem point_links_checked23536 : (cuts23536.take 1).map (fun c => (3088842753-1+2*2^9*c.k,102122785466618+c.lower,102123167046030+c.upper)) = pointBounds23536 := by
 decide +kernel
def cuts23537 : List PrefixCut := [⟨22,93582433,93582484⟩,
⟨117,505628717,505628997⟩,
⟨128,551552572,551552878⟩]
theorem checked23537 : checkPrefixCuts (2^48) 3088973825 9 Manual.Count131072.C023537.packed 128 cuts23537 = true := by
 decide +kernel
def pointBounds23537 : List (Nat × Nat × Nat) := [(3088996352,102123424975388,102123806555149),(3089093632,102123837021672,102124218601662)]
theorem point_links_checked23537 : (cuts23537.take 2).map (fun c => (3088973825-1+2*2^9*c.k,102123331392955+c.lower,102123712972665+c.upper)) = pointBounds23537 := by
 decide +kernel
def cuts23538 : List PrefixCut := [⟨84,355539831,355540030⟩,
⟨128,542508619,542508925⟩]
theorem checked23538 : checkPrefixCuts (2^48) 3089104897 9 Manual.Count131072.C023538.packed 128 cuts23538 = true := by
 decide +kernel
def pointBounds23538 : List (Nat × Nat × Nat) := [(3089190912,102124238485358,102124620065573)]
theorem point_links_checked23538 : (cuts23538.take 1).map (fun c => (3089104897-1+2*2^9*c.k,102123882945527+c.lower,102124264525543+c.upper)) = pointBounds23538 := by
 decide +kernel
def cuts23539 : List PrefixCut := [⟨51,219584620,219584741⟩,
⟨128,547132332,547132637⟩]
theorem checked23539 : checkPrefixCuts (2^48) 3089235969 9 Manual.Count131072.C023539.packed 128 cuts23539 = true := by
 decide +kernel
def pointBounds23539 : List (Nat × Nat × Nat) := [(3089288192,102124645038766,102125026619209)]
theorem point_links_checked23539 : (cuts23539.take 1).map (fun c => (3089235969-1+2*2^9*c.k,102124425454146+c.lower,102124807034468+c.upper)) = pointBounds23539 := by
 decide +kernel
def cuts23540 : List PrefixCut := [⟨18,77535118,77535160⟩,
⟨113,487616151,487616432⟩,
⟨128,552757816,552758135⟩]
theorem checked23540 : checkPrefixCuts (2^48) 3089367041 9 Manual.Count131072.C023540.packed 128 cuts23540 = true := by
 decide +kernel
def pointBounds23540 : List (Nat × Nat × Nat) := [(3089385472,102125050121596,102125431702265),(3089482752,102125460202629,102125841783537)]
theorem point_links_checked23540 : (cuts23540.take 2).map (fun c => (3089367041-1+2*2^9*c.k,102124972586478+c.lower,102125354167105+c.upper)) = pointBounds23540 := by
 decide +kernel
def cuts23541 : List PrefixCut := [⟨80,338184740,338184928⟩,
⟨128,543077328,543077635⟩]
theorem checked23541 : checkPrefixCuts (2^48) 3089498113 9 Manual.Count131072.C023541.packed 128 cuts23541 = true := by
 decide +kernel
def pointBounds23541 : List (Nat × Nat × Nat) := [(3089580032,102125863529034,102126245110168)]
theorem point_links_checked23541 : (cuts23541.take 1).map (fun c => (3089498113-1+2*2^9*c.k,102125525344294+c.lower,102125906925240+c.upper)) = pointBounds23541 := by
 decide +kernel
def cuts23542 : List PrefixCut := [⟨47,203249509,203249628⟩,
⟨128,543327637,543327955⟩]
theorem checked23542 : checkPrefixCuts (2^48) 3089629185 9 Manual.Count131072.C023542.packed 128 cuts23542 = true := by
 decide +kernel
def pointBounds23542 : List (Nat × Nat × Nat) := [(3089677312,102126271671131,102126653252503)]
theorem point_links_checked23542 : (cuts23542.take 1).map (fun c => (3089629185-1+2*2^9*c.k,102126068421622+c.lower,102126450002875+c.upper)) = pointBounds23542 := by
 decide +kernel
def cuts23543 : List PrefixCut := [⟨14,61036367,61036400⟩,
⟨109,478900165,478900427⟩,
⟨128,560248613,560248917⟩]
theorem checked23543 : checkPrefixCuts (2^48) 3089760257 9 Manual.Count131072.C023543.packed 128 cuts23543 = true := by
 decide +kernel
def pointBounds23543 : List (Nat × Nat × Nat) := [(3089774592,102126672785626,102127054367230),(3089871872,102127090649424,102127472231257)]
theorem point_links_checked23543 : (cuts23543.take 2).map (fun c => (3089760257-1+2*2^9*c.k,102126611749259+c.lower,102126993330830+c.upper)) = pointBounds23543 := by
 decide +kernel
def cuts23544 : List PrefixCut := [⟨76,325753088,325753266⟩,
⟨128,539911156,539911459⟩]
theorem checked23544 : checkPrefixCuts (2^48) 3089891329 9 Manual.Count131072.C023544.packed 128 cuts23544 = true := by
 decide +kernel
def pointBounds23544 : List (Nat × Nat × Nat) := [(3089969152,102127497750960,102127879333013)]
theorem point_links_checked23544 : (cuts23544.take 1).map (fun c => (3089891329-1+2*2^9*c.k,102127171997872+c.lower,102127553579747+c.upper)) = pointBounds23544 := by
 decide +kernel
def cuts23545 : List PrefixCut := [⟨43,186645230,186645334⟩,
⟨128,550727766,550728073⟩]
theorem checked23545 : checkPrefixCuts (2^48) 3090022401 9 Manual.Count131072.C023545.packed 128 cuts23545 = true := by
 decide +kernel
def pointBounds23545 : List (Nat × Nat × Nat) := [(3090066432,102127898554258,102128280136540)]
theorem point_links_checked23545 : (cuts23545.take 1).map (fun c => (3090022401-1+2*2^9*c.k,102127711909028+c.lower,102128093491206+c.upper)) = pointBounds23545 := by
 decide +kernel
def cuts23546 : List PrefixCut := [⟨10,44906152,44906174⟩,
⟨105,448234688,448234936⟩,
⟨128,548336188,548336493⟩]
theorem checked23546 : checkPrefixCuts (2^48) 3090153473 9 Manual.Count131072.C023546.packed 128 cuts23546 = true := by
 decide +kernel
def pointBounds23546 : List (Nat × Nat × Nat) := [(3090163712,102128307542946,102128689125453),(3090260992,102128710871482,102129092454215)]
theorem point_links_checked23546 : (cuts23546.take 2).map (fun c => (3090153473-1+2*2^9*c.k,102128262636794+c.lower,102128644219279+c.upper)) = pointBounds23546 := by
 decide +kernel
def cuts23547 : List PrefixCut := [⟨72,307313136,307313316⟩,
⟨128,542665909,542666224⟩]
theorem checked23547 : checkPrefixCuts (2^48) 3090284545 9 Manual.Count131072.C023547.packed 128 cuts23547 = true := by
 decide +kernel
def pointBounds23547 : List (Nat × Nat × Nat) := [(3090358272,102129118286118,102129499869088)]
theorem point_links_checked23547 : (cuts23547.take 1).map (fun c => (3090284545-1+2*2^9*c.k,102128810972982+c.lower,102129192555772+c.upper)) = pointBounds23547 := by
 decide +kernel
def cuts23548 : List PrefixCut := [⟨39,166219839,166219937⟩,
⟨128,542642845,542643161⟩]
theorem checked23548 : checkPrefixCuts (2^48) 3090415617 9 Manual.Count131072.C023548.packed 128 cuts23548 = true := by
 decide +kernel
def pointBounds23548 : List (Nat × Nat × Nat) := [(3090455552,102129519858730,102129901441933)]
theorem point_links_checked23548 : (cuts23548.take 1).map (fun c => (3090415617-1+2*2^9*c.k,102129353638891+c.lower,102129735221996+c.upper)) = pointBounds23548 := by
 decide +kernel
def cuts23549 : List PrefixCut := [⟨6,24954822,24954837⟩,
⟨101,435063158,435063406⟩,
⟨128,545807465,545807782⟩]
theorem checked23549 : checkPrefixCuts (2^48) 3090546689 9 Manual.Count131072.C023549.packed 128 cuts23549 = true := by
 decide +kernel
def pointBounds23549 : List (Nat × Nat × Nat) := [(3090552832,102129921236558,102130302819994),(3090650112,102130331344894,102130712928563)]
theorem point_links_checked23549 : (cuts23549.take 2).map (fun c => (3090546689-1+2*2^9*c.k,102129896281736+c.lower,102130277865157+c.upper)) = pointBounds23549 := by
 decide +kernel
def cuts23550 : List PrefixCut := [⟨68,292429590,292429756⟩,
⟨128,551339512,551339826⟩]
theorem checked23550 : checkPrefixCuts (2^48) 3090677761 9 Manual.Count131072.C023550.packed 128 cuts23550 = true := by
 decide +kernel
def pointBounds23550 : List (Nat × Nat × Nat) := [(3090747392,102130734518791,102131116102695)]
theorem point_links_checked23550 : (cuts23550.take 1).map (fun c => (3090677761-1+2*2^9*c.k,102130442089201+c.lower,102130823672939+c.upper)) = pointBounds23550 := by
 decide +kernel
def cuts23551 : List PrefixCut := [⟨35,150899403,150899489⟩,
⟨128,547946790,547947103⟩]
theorem checked23551 : checkPrefixCuts (2^48) 3090808833 9 Manual.Count131072.C023551.packed 128 cuts23551 = true := by
 decide +kernel
def pointBounds23551 : List (Nat × Nat × Nat) := [(3090844672,102131144328116,102131525912254)]
theorem point_links_checked23551 : (cuts23551.take 1).map (fun c => (3090808833-1+2*2^9*c.k,102130993428713+c.lower,102131375012765+c.upper)) = pointBounds23551 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000110
