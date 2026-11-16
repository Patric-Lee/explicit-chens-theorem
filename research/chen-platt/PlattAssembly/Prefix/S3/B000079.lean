import PlattAssemblyKernel
import PlattCertificates.Count131072.C022528
import PlattCertificates.Count131072.C022529
import PlattCertificates.Count131072.C022530
import PlattCertificates.Count131072.C022531
import PlattCertificates.Count131072.C022532
import PlattCertificates.Count131072.C022533
import PlattCertificates.Count131072.C022534
import PlattCertificates.Count131072.C022535
import PlattCertificates.Count131072.C022536
import PlattCertificates.Count131072.C022537
import PlattCertificates.Count131072.C022538
import PlattCertificates.Count131072.C022539
import PlattCertificates.Count131072.C022540
import PlattCertificates.Count131072.C022541
import PlattCertificates.Count131072.C022542
import PlattCertificates.Count131072.C022543
import PlattCertificates.Count131072.C022544
import PlattCertificates.Count131072.C022545
import PlattCertificates.Count131072.C022546
import PlattCertificates.Count131072.C022547
import PlattCertificates.Count131072.C022548
import PlattCertificates.Count131072.C022549
import PlattCertificates.Count131072.C022550
import PlattCertificates.Count131072.C022551
import PlattCertificates.Count131072.C022552
import PlattCertificates.Count131072.C022553
import PlattCertificates.Count131072.C022554
import PlattCertificates.Count131072.C022555
import PlattCertificates.Count131072.C022556
import PlattCertificates.Count131072.C022557
import PlattCertificates.Count131072.C022558
import PlattCertificates.Count131072.C022559
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000079
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22528 : List PrefixCut := [⟨86,384690498,384690718⟩,
⟨128,571462609,571462932⟩]
theorem checked22528 : checkPrefixCuts (2^48) 2956722177 9 Manual.Count131072.C022528.packed 128 cuts22528 = true := by
 decide +kernel
def pointBounds22528 : List (Nat × Nat × Nat) := [(2956810240,101559508779100,101559890038582)]
theorem point_links_checked22528 : (cuts22528.take 1).map (fun c => (2956722177-1+2*2^9*c.k,101559124088602+c.lower,101559505347864+c.upper)) = pointBounds22528 := by
 decide +kernel
def cuts22529 : List PrefixCut := [⟨49,213232897,213233023⟩,
⟨128,565059369,565059689⟩]
theorem checked22529 : checkPrefixCuts (2^48) 2956853249 9 Manual.Count131072.C022529.packed 128 cuts22529 = true := by
 decide +kernel
def pointBounds22529 : List (Nat × Nat × Nat) := [(2956903424,101559908784108,101560290043819)]
theorem point_links_checked22529 : (cuts22529.take 1).map (fun c => (2956853249-1+2*2^9*c.k,101559695551211+c.lower,101560076810796+c.upper)) = pointBounds22529 := by
 decide +kernel
def cuts22530 : List PrefixCut := [⟨12,53020635,53020667⟩,
⟨103,462995134,462995404⟩,
⟨128,574077247,574077580⟩]
theorem checked22530 : checkPrefixCuts (2^48) 2956984321 9 Manual.Count131072.C022530.packed 128 cuts22530 = true := by
 decide +kernel
def pointBounds22530 : List (Nat × Nat × Nat) := [(2956996608,101560313631215,101560694891152),(2957089792,101560723605714,101561104865889)]
theorem point_links_checked22530 : (cuts22530.take 2).map (fun c => (2956984321-1+2*2^9*c.k,101560260610580+c.lower,101560641870485+c.upper)) = pointBounds22530 := by
 decide +kernel
def cuts22531 : List PrefixCut := [⟨66,290598386,290598546⟩,
⟨128,570149192,570149512⟩]
theorem checked22531 : checkPrefixCuts (2^48) 2957115393 9 Manual.Count131072.C022531.packed 128 cuts22531 = true := by
 decide +kernel
def pointBounds22531 : List (Nat × Nat × Nat) := [(2957182976,101561125286213,101561506546611)]
theorem point_links_checked22531 : (cuts22531.take 1).map (fun c => (2957115393-1+2*2^9*c.k,101560834687827+c.lower,101561215948065+c.upper)) = pointBounds22531 := by
 decide +kernel
def cuts22532 : List PrefixCut := [⟨29,128874991,128875069⟩,
⟨120,539952932,539953239⟩,
⟨128,576501026,576501355⟩]
theorem checked22532 : checkPrefixCuts (2^48) 2957246465 9 Manual.Count131072.C022532.packed 128 cuts22532 = true := by
 decide +kernel
def pointBounds22532 : List (Nat × Nat × Nat) := [(2957276160,101561533712010,101561914972646),(2957369344,101561944789951,101562326050816)]
theorem point_links_checked22532 : (cuts22532.take 2).map (fun c => (2957246465-1+2*2^9*c.k,101561404837019+c.lower,101561786097577+c.upper)) = pointBounds22532 := by
 decide +kernel
def cuts22533 : List PrefixCut := [⟨83,369282214,369282431⟩,
⟨128,569622874,569623207⟩]
theorem checked22533 : checkPrefixCuts (2^48) 2957377537 9 Manual.Count131072.C022533.packed 128 cuts22533 = true := by
 decide +kernel
def pointBounds22533 : List (Nat × Nat × Nat) := [(2957462528,101562350620259,101562731881363)]
theorem point_links_checked22533 : (cuts22533.take 1).map (fun c => (2957377537-1+2*2^9*c.k,101561981338045+c.lower,101562362598932+c.upper)) = pointBounds22533 := by
 decide +kernel
def cuts22534 : List PrefixCut := [⟨46,203383024,203383137⟩,
⟨128,571501021,571501344⟩]
theorem checked22534 : checkPrefixCuts (2^48) 2957508609 9 Manual.Count131072.C022534.packed 128 cuts22534 = true := by
 decide +kernel
def pointBounds22534 : List (Nat × Nat × Nat) := [(2957555712,101562754343943,101563135605276)]
theorem point_links_checked22534 : (cuts22534.take 1).map (fun c => (2957508609-1+2*2^9*c.k,101562550960919+c.lower,101562932222139+c.upper)) = pointBounds22534 := by
 decide +kernel
def cuts22535 : List PrefixCut := [⟨9,40161154,40161179⟩,
⟨100,449093625,449093879⟩,
⟨128,575282408,575282733⟩]
theorem checked22535 : checkPrefixCuts (2^48) 2957639681 9 Manual.Count131072.C022535.packed 128 cuts22535 = true := by
 decide +kernel
def pointBounds22535 : List (Nat × Nat × Nat) := [(2957648896,101563162623094,101563543884662),(2957742080,101563571555565,101563952817362)]
theorem point_links_checked22535 : (cuts22535.take 2).map (fun c => (2957639681-1+2*2^9*c.k,101563122461940+c.lower,101563503723483+c.upper)) = pointBounds22535 := by
 decide +kernel
def cuts22536 : List PrefixCut := [⟨63,277687073,277687234⟩,
⟨128,564789006,564789326⟩]
theorem checked22536 : checkPrefixCuts (2^48) 2957770753 9 Manual.Count131072.C022536.packed 128 cuts22536 = true := by
 decide +kernel
def pointBounds22536 : List (Nat × Nat × Nat) := [(2957835264,101563975431421,101564356693450)]
theorem point_links_checked22536 : (cuts22536.take 1).map (fun c => (2957770753-1+2*2^9*c.k,101563697744348+c.lower,101564079006216+c.upper)) = pointBounds22536 := by
 decide +kernel
def cuts22537 : List PrefixCut := [⟨26,115904762,115904824⟩,
⟨117,523942061,523942360⟩,
⟨128,569807394,569807719⟩]
theorem checked22537 : checkPrefixCuts (2^48) 2957901825 9 Manual.Count131072.C022537.packed 128 cuts22537 = true := by
 decide +kernel
def pointBounds22537 : List (Nat × Nat × Nat) := [(2957928448,101564378438116,101564759700366),(2958021632,101564786475415,101565167737902)]
theorem point_links_checked22537 : (cuts22537.take 2).map (fun c => (2957901825-1+2*2^9*c.k,101564262533354+c.lower,101564643795542+c.upper)) = pointBounds22537 := by
 decide +kernel
def cuts22538 : List PrefixCut := [⟨80,358733567,358733770⟩,
⟨128,575205915,575206236⟩]
theorem checked22538 : checkPrefixCuts (2^48) 2958032897 9 Manual.Count131072.C022538.packed 128 cuts22538 = true := by
 decide +kernel
def pointBounds22538 : List (Nat × Nat × Nat) := [(2958114816,101565191074315,101565572337031)]
theorem point_links_checked22538 : (cuts22538.take 1).map (fun c => (2958032897-1+2*2^9*c.k,101564832340748+c.lower,101565213603261+c.upper)) = pointBounds22538 := by
 decide +kernel
def cuts22539 : List PrefixCut := [⟨43,196296898,196297008⟩,
⟨128,570042428,570042757⟩]
theorem checked22539 : checkPrefixCuts (2^48) 2958163969 9 Manual.Count131072.C022539.packed 128 cuts22539 = true := by
 decide +kernel
def pointBounds22539 : List (Nat × Nat × Nat) := [(2958208000,101565603843561,101565985106505)]
theorem point_links_checked22539 : (cuts22539.take 1).map (fun c => (2958163969-1+2*2^9*c.k,101565407546663+c.lower,101565788809497+c.upper)) = pointBounds22539 := by
 decide +kernel
def cuts22540 : List PrefixCut := [⟨6,27117062,27117076⟩,
⟨97,436910763,436911007⟩,
⟨128,578580137,578580459⟩]
theorem checked22540 : checkPrefixCuts (2^48) 2958295041 9 Manual.Count131072.C022540.packed 128 cuts22540 = true := by
 decide +kernel
def pointBounds22540 : List (Nat × Nat × Nat) := [(2958301184,101566004706153,101566385969330),(2958394368,101566414499854,101566795763261)]
theorem point_links_checked22540 : (cuts22540.take 2).map (fun c => (2958295041-1+2*2^9*c.k,101565977589091+c.lower,101566358852254+c.upper)) = pointBounds22540 := by
 decide +kernel
def cuts22541 : List PrefixCut := [⟨60,263734943,263735090⟩,
⟨128,575034196,575034518⟩]
theorem checked22541 : checkPrefixCuts (2^48) 2958426113 9 Manual.Count131072.C022541.packed 128 cuts22541 = true := by
 decide +kernel
def pointBounds22541 : List (Nat × Nat × Nat) := [(2958487552,101566819904171,101567201167803)]
theorem point_links_checked22541 : (cuts22541.take 1).map (fun c => (2958426113-1+2*2^9*c.k,101566556169228+c.lower,101566937432713+c.upper)) = pointBounds22541 := by
 decide +kernel
def cuts22542 : List PrefixCut := [⟨23,99895809,99895863⟩,
⟨114,506225858,506226147⟩,
⟨128,571678917,571679242⟩]
theorem checked22542 : checkPrefixCuts (2^48) 2958557185 9 Manual.Count131072.C022542.packed 128 cuts22542 = true := by
 decide +kernel
def pointBounds22542 : List (Nat × Nat × Nat) := [(2958580736,101567231099233,101567612363094),(2958673920,101567637429282,101568018693378)]
theorem point_links_checked22542 : (cuts22542.take 2).map (fun c => (2958557185-1+2*2^9*c.k,101567131203424+c.lower,101567512467231+c.upper)) = pointBounds22542 := by
 decide +kernel
def cuts22543 : List PrefixCut := [⟨77,343813417,343813608⟩,
⟨128,571748884,571749206⟩]
theorem checked22543 : checkPrefixCuts (2^48) 2958688257 9 Manual.Count131072.C022543.packed 128 cuts22543 = true := by
 decide +kernel
def pointBounds22543 : List (Nat × Nat × Nat) := [(2958767104,101568046695758,101568427960081)]
theorem point_links_checked22543 : (cuts22543.take 1).map (fun c => (2958688257-1+2*2^9*c.k,101567702882341+c.lower,101568084146473+c.upper)) = pointBounds22543 := by
 decide +kernel
def cuts22544 : List PrefixCut := [⟨40,180461870,180461974⟩,
⟨128,575718911,575719240⟩]
theorem checked22544 : checkPrefixCuts (2^48) 2958819329 9 Manual.Count131072.C022544.packed 128 cuts22544 = true := by
 decide +kernel
def pointBounds22544 : List (Nat × Nat × Nat) := [(2958860288,101568455093095,101568836357653)]
theorem point_links_checked22544 : (cuts22544.take 1).map (fun c => (2958819329-1+2*2^9*c.k,101568274631225+c.lower,101568655895679+c.upper)) = pointBounds22544 := by
 decide +kernel
def cuts22545 : List PrefixCut := [⟨3,13603097,13603105⟩,
⟨94,417884374,417884615⟩,
⟨128,571032323,571032648⟩]
theorem checked22545 : checkPrefixCuts (2^48) 2958950401 9 Manual.Count131072.C022545.packed 128 cuts22545 = true := by
 decide +kernel
def pointBounds22545 : List (Nat × Nat × Nat) := [(2958953472,101568863953233,101569245218024),(2959046656,101569268234510,101569649499534)]
theorem point_links_checked22545 : (cuts22545.take 2).map (fun c => (2958950401-1+2*2^9*c.k,101568850350136+c.lower,101569231614919+c.upper)) = pointBounds22545 := by
 decide +kernel
def cuts22546 : List PrefixCut := [⟨57,255305995,255306139⟩,
⟨128,571292427,571292748⟩]
theorem checked22546 : checkPrefixCuts (2^48) 2959081473 9 Manual.Count131072.C022546.packed 128 cuts22546 = true := by
 decide +kernel
def pointBounds22546 : List (Nat × Nat × Nat) := [(2959139840,101569676688454,101570057953706)]
theorem point_links_checked22546 : (cuts22546.take 1).map (fun c => (2959081473-1+2*2^9*c.k,101569421382459+c.lower,101569802647567+c.upper)) = pointBounds22546 := by
 decide +kernel
def cuts22547 : List PrefixCut := [⟨20,90932652,90932705⟩,
⟨111,497458508,497458794⟩,
⟨128,573454786,573455116⟩]
theorem checked22547 : checkPrefixCuts (2^48) 2959212545 9 Manual.Count131072.C022547.packed 128 cuts22547 = true := by
 decide +kernel
def pointBounds22547 : List (Nat × Nat × Nat) := [(2959233024,101570083607538,101570464873020),(2959326208,101570490133394,101570871399109)]
theorem point_links_checked22547 : (cuts22547.take 2).map (fun c => (2959212545-1+2*2^9*c.k,101569992674886+c.lower,101570373940315+c.upper)) = pointBounds22547 := by
 decide +kernel
def cuts22548 : List PrefixCut := [⟨74,333465271,333465460⟩,
⟨128,574285446,574285775⟩]
theorem checked22548 : checkPrefixCuts (2^48) 2959343617 9 Manual.Count131072.C022548.packed 128 cuts22548 = true := by
 decide +kernel
def pointBounds22548 : List (Nat × Nat × Nat) := [(2959419392,101570899594943,101571280860891)]
theorem point_links_checked22548 : (cuts22548.take 1).map (fun c => (2959343617-1+2*2^9*c.k,101570566129672+c.lower,101570947395431+c.upper)) = pointBounds22548 := by
 decide +kernel
def cuts22549 : List PrefixCut := [⟨37,159307800,159307893⟩,
⟨128,570455488,570455818⟩]
theorem checked22549 : checkPrefixCuts (2^48) 2959474689 9 Manual.Count131072.C022549.packed 128 cuts22549 = true := by
 decide +kernel
def pointBounds22549 : List (Nat × Nat × Nat) := [(2959512576,101571299722918,101571680989099),(2959605760,101571710870606,101572092137024)]
theorem point_links_checked22549 : (cuts22549.take 2).map (fun c => (2959474689-1+2*2^9*c.k,101571140415118+c.lower,101571521681206+c.upper)) = pointBounds22549 := by
 decide +kernel
def cuts22550 : List PrefixCut := [⟨91,402480267,402480497⟩,
⟨128,565009470,565009799⟩]
theorem checked22550 : checkPrefixCuts (2^48) 2959605761 9 Manual.Count131072.C022550.packed 128 cuts22550 = true := by
 decide +kernel
def pointBounds22550 : List (Nat × Nat × Nat) := [(2959698944,101572113350873,101572494617521)]
theorem point_links_checked22550 : (cuts22550.take 1).map (fun c => (2959605761-1+2*2^9*c.k,101571710870606+c.lower,101572092137024+c.upper)) = pointBounds22550 := by
 decide +kernel
def cuts22551 : List PrefixCut := [⟨54,243742468,243742609⟩,
⟨128,576967053,576967386⟩]
theorem checked22551 : checkPrefixCuts (2^48) 2959736833 9 Manual.Count131072.C022551.packed 128 cuts22551 = true := by
 decide +kernel
def pointBounds22551 : List (Nat × Nat × Nat) := [(2959792128,101572519622544,101572900889432)]
theorem point_links_checked22551 : (cuts22551.take 1).map (fun c => (2959736833-1+2*2^9*c.k,101572275880076+c.lower,101572657146823+c.upper)) = pointBounds22551 := by
 decide +kernel
def cuts22552 : List PrefixCut := [⟨17,73129461,73129501⟩,
⟨108,480231455,480231728⟩,
⟨128,567241757,567242082⟩]
theorem checked22552 : checkPrefixCuts (2^48) 2959867905 9 Manual.Count131072.C022552.packed 128 cuts22552 = true := by
 decide +kernel
def pointBounds22552 : List (Nat × Nat × Nat) := [(2959885312,101572925976590,101573307243710),(2959978496,101573333078584,101573714345937)]
theorem point_links_checked22552 : (cuts22552.take 2).map (fun c => (2959867905-1+2*2^9*c.k,101572852847129+c.lower,101573234114209+c.upper)) = pointBounds22552 := by
 decide +kernel
def cuts22553 : List PrefixCut := [⟨71,313612565,313612740⟩,
⟨128,571115285,571115604⟩]
theorem checked22553 : checkPrefixCuts (2^48) 2959998977 9 Manual.Count131072.C022553.packed 128 cuts22553 = true := by
 decide +kernel
def pointBounds22553 : List (Nat × Nat × Nat) := [(2960071680,101573733701451,101574114969031)]
theorem point_links_checked22553 : (cuts22553.take 1).map (fun c => (2959998977-1+2*2^9*c.k,101573420088886+c.lower,101573801356291+c.upper)) = pointBounds22553 := by
 decide +kernel
def cuts22554 : List PrefixCut := [⟨34,149668715,149668801⟩,
⟨125,551597567,551597890⟩,
⟨128,564243810,564244139⟩]
theorem checked22554 : checkPrefixCuts (2^48) 2960130049 9 Manual.Count131072.C022554.packed 128 cuts22554 = true := by
 decide +kernel
def pointBounds22554 : List (Nat × Nat × Nat) := [(2960164864,101574140872886,101574522140696),(2960258048,101574542801738,101574924069785)]
theorem point_links_checked22554 : (cuts22554.take 2).map (fun c => (2960130049-1+2*2^9*c.k,101573991204171+c.lower,101574372471895+c.upper)) = pointBounds22554 := by
 decide +kernel
def cuts22555 : List PrefixCut := [⟨88,393358498,393358731⟩,
⟨128,576674552,576674887⟩]
theorem checked22555 : checkPrefixCuts (2^48) 2960261121 9 Manual.Count131072.C022555.packed 128 cuts22555 = true := by
 decide +kernel
def pointBounds22555 : List (Nat × Nat × Nat) := [(2960351232,101574948806479,101575330074765)]
theorem point_links_checked22555 : (cuts22555.take 1).map (fun c => (2960261121-1+2*2^9*c.k,101574555447981+c.lower,101574936716034+c.upper)) = pointBounds22555 := by
 decide +kernel
def cuts22556 : List PrefixCut := [⟨51,228000485,228000617⟩,
⟨128,577694918,577695248⟩]
theorem checked22556 : checkPrefixCuts (2^48) 2960392193 9 Manual.Count131072.C022556.packed 128 cuts22556 = true := by
 decide +kernel
def pointBounds22556 : List (Nat × Nat × Nat) := [(2960444416,101575360123018,101575741391538)]
theorem point_links_checked22556 : (cuts22556.take 1).map (fun c => (2960392193-1+2*2^9*c.k,101575132122533+c.lower,101575513390921+c.upper)) = pointBounds22556 := by
 decide +kernel
def cuts22557 : List PrefixCut := [⟨14,61704217,61704251⟩,
⟨105,463582422,463582686⟩,
⟨128,565404789,565405112⟩]
theorem checked22557 : checkPrefixCuts (2^48) 2960523265 9 Manual.Count131072.C022557.packed 128 cuts22557 = true := by
 decide +kernel
def pointBounds22557 : List (Nat × Nat × Nat) := [(2960537600,101575771521668,101576152790420),(2960630784,101576173399873,101576554668855)]
theorem point_links_checked22557 : (cuts22557.take 2).map (fun c => (2960523265-1+2*2^9*c.k,101575709817451+c.lower,101576091086169+c.upper)) = pointBounds22557 := by
 decide +kernel
def cuts22558 : List PrefixCut := [⟨68,301564371,301564543⟩,
⟨128,569372687,569373016⟩]
theorem checked22558 : checkPrefixCuts (2^48) 2960654337 9 Manual.Count131072.C022558.packed 128 cuts22558 = true := by
 decide +kernel
def pointBounds22558 : List (Nat × Nat × Nat) := [(2960723968,101576576786611,101576958055824)]
theorem point_links_checked22558 : (cuts22558.take 1).map (fun c => (2960654337-1+2*2^9*c.k,101576275222240+c.lower,101576656491281+c.upper)) = pointBounds22558 := by
 decide +kernel
def cuts22559 : List PrefixCut := [⟨31,140319103,140319180⟩,
⟨122,546437325,546437632⟩,
⟨128,571914352,571914674⟩]
theorem checked22559 : checkPrefixCuts (2^48) 2960785409 9 Manual.Count131072.C022559.packed 128 cuts22559 = true := by
 decide +kernel
def pointBounds22559 : List (Nat × Nat × Nat) := [(2960817152,101576984914030,101577366183477),(2960910336,101577391032252,101577772301929)]
theorem point_links_checked22559 : (cuts22559.take 2).map (fun c => (2960785409-1+2*2^9*c.k,101576844594927+c.lower,101577225864297+c.upper)) = pointBounds22559 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000079
