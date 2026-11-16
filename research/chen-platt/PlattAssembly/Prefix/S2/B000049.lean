import PlattAssemblyKernel
import PlattCertificates.Count131072.C011568
import PlattCertificates.Count131072.C011569
import PlattCertificates.Count131072.C011570
import PlattCertificates.Count131072.C011571
import PlattCertificates.Count131072.C011572
import PlattCertificates.Count131072.C011573
import PlattCertificates.Count131072.C011574
import PlattCertificates.Count131072.C011575
import PlattCertificates.Count131072.C011576
import PlattCertificates.Count131072.C011577
import PlattCertificates.Count131072.C011578
import PlattCertificates.Count131072.C011579
import PlattCertificates.Count131072.C011580
import PlattCertificates.Count131072.C011581
import PlattCertificates.Count131072.C011582
import PlattCertificates.Count131072.C011583
import PlattCertificates.Count131072.C011584
import PlattCertificates.Count131072.C011585
import PlattCertificates.Count131072.C011586
import PlattCertificates.Count131072.C011587
import PlattCertificates.Count131072.C011588
import PlattCertificates.Count131072.C011589
import PlattCertificates.Count131072.C011590
import PlattCertificates.Count131072.C011591
import PlattCertificates.Count131072.C011592
import PlattCertificates.Count131072.C011593
import PlattCertificates.Count131072.C011594
import PlattCertificates.Count131072.C011595
import PlattCertificates.Count131072.C011596
import PlattCertificates.Count131072.C011597
import PlattCertificates.Count131072.C011598
import PlattCertificates.Count131072.C011599
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000049
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11568 : List PrefixCut := [⟨24,215339047,215339214⟩,
⟨71,624528976,624529466⟩,
⟨118,1045370246,1045371071⟩,
⟨128,1136646436,1136647333⟩]
theorem checked11568 : checkPrefixCuts (2^48) 1520173057 9 Manual.Count131072.C011568.packed 128 cuts11568 = true := by
 decide +kernel
def pointBounds11568 : List (Nat × Nat × Nat) := [(1520197632,92839109435224,92839484994295),(1520245760,92839518625153,92839894184547),(1520293888,92839939466423,92840315026152)]
theorem point_links_checked11568 : (cuts11568.take 3).map (fun c => (1520173057-1+2*2^9*c.k,92838894096177+c.lower,92839269655081+c.upper)) = pointBounds11568 := by
 decide +kernel
def cuts11569 : List PrefixCut := [⟨37,330292443,330292702⟩,
⟨84,748515225,748515815⟩,
⟨128,1140066320,1140067218⟩]
theorem checked11569 : checkPrefixCuts (2^48) 1520304129 9 Manual.Count131072.C011569.packed 128 cuts11569 = true := by
 decide +kernel
def pointBounds11569 : List (Nat × Nat × Nat) := [(1520342016,92840361035056,92840736595116),(1520390144,92840779257838,92841154818229)]
theorem point_links_checked11569 : (cuts11569.take 2).map (fun c => (1520304129-1+2*2^9*c.k,92840030742613+c.lower,92840406302414+c.upper)) = pointBounds11569 := by
 decide +kernel
def cuts11570 : List PrefixCut := [⟨3,27398891,27398911⟩,
⟨50,450593588,450593941⟩,
⟨97,875440897,875441587⟩,
⟨128,1158109696,1158110606⟩]
theorem checked11570 : checkPrefixCuts (2^48) 1520435201 9 Manual.Count131072.C011570.packed 128 cuts11570 = true := by
 decide +kernel
def pointBounds11570 : List (Nat × Nat × Nat) := [(1520438272,92841198207824,92841573768543),(1520486400,92841621402521,92841996963573),(1520534528,92842046249830,92842421811219)]
theorem point_links_checked11570 : (cuts11570.take 3).map (fun c => (1520435201-1+2*2^9*c.k,92841170808933+c.lower,92841546369632+c.upper)) = pointBounds11570 := by
 decide +kernel
def cuts11571 : List PrefixCut := [⟨16,140314054,140314164⟩,
⟨63,566060085,566060529⟩,
⟨110,980316237,980317003⟩,
⟨128,1139314607,1139315498⟩]
theorem checked11571 : checkPrefixCuts (2^48) 1520566273 9 Manual.Count131072.C011571.packed 128 cuts11571 = true := by
 decide +kernel
def pointBounds11571 : List (Nat × Nat × Nat) := [(1520582656,92842469232683,92842844794402),(1520630784,92842894978714,92843270540767),(1520678912,92843309234866,92843684797241)]
theorem point_links_checked11571 : (cuts11571.take 3).map (fun c => (1520566273-1+2*2^9*c.k,92842328918629+c.lower,92842704480238+c.upper)) = pointBounds11571 := by
 decide +kernel
def cuts11572 : List PrefixCut := [⟨29,255985157,255985357⟩,
⟨76,682245837,682246377⟩,
⟨123,1096277664,1096278533⟩,
⟨128,1139216285,1139217188⟩]
theorem checked11572 : checkPrefixCuts (2^48) 1520697345 9 Manual.Count131072.C011572.packed 128 cuts11572 = true := by
 decide +kernel
def pointBounds11572 : List (Nat × Nat × Nat) := [(1520727040,92843724218393,92844099781093),(1520775168,92844150479073,92844526042113),(1520823296,92844564510900,92844940074269)]
theorem point_links_checked11572 : (cuts11572.take 3).map (fun c => (1520697345-1+2*2^9*c.k,92843468233236+c.lower,92843843795736+c.upper)) = pointBounds11572 := by
 decide +kernel
def cuts11573 : List PrefixCut := [⟨42,376262276,376262572⟩,
⟨89,799151357,799151988⟩,
⟨128,1149482124,1149483027⟩]
theorem checked11573 : checkPrefixCuts (2^48) 1520828417 9 Manual.Count131072.C011573.packed 128 cuts11573 = true := by
 decide +kernel
def pointBounds11573 : List (Nat × Nat × Nat) := [(1520871424,92844983711797,92845359275496),(1520919552,92845406600878,92845782164912)]
theorem point_links_checked11573 : (cuts11573.take 2).map (fun c => (1520828417-1+2*2^9*c.k,92844607449521+c.lower,92844983012924+c.upper)) = pointBounds11573 := by
 decide +kernel
def cuts11574 : List PrefixCut := [⟨8,74025400,74025458⟩,
⟨55,495036931,495037322⟩,
⟨102,918626103,918626827⟩,
⟨128,1152898986,1152899895⟩]
theorem checked11574 : checkPrefixCuts (2^48) 1520959489 9 Manual.Count131072.C011574.packed 128 cuts11574 = true := by
 decide +kernel
def pointBounds11574 : List (Nat × Nat × Nat) := [(1520967680,92845830957045,92846206521409),(1521015808,92846251968576,92846627533273),(1521063936,92846675557748,92847051122778)]
theorem point_links_checked11574 : (cuts11574.take 3).map (fun c => (1520959489-1+2*2^9*c.k,92845756931645+c.lower,92846132495951+c.upper)) = pointBounds11574 := by
 decide +kernel
def cuts11575 : List PrefixCut := [⟨21,193928979,193929130⟩,
⟨68,609904631,609905108⟩,
⟨115,1031603234,1031604043⟩,
⟨128,1142993048,1142993947⟩]
theorem checked11575 : checkPrefixCuts (2^48) 1521090561 9 Manual.Count131072.C011575.packed 128 cuts11575 = true := by
 decide +kernel
def pointBounds11575 : List (Nat × Nat × Nat) := [(1521112064,92847103759610,92847479324976),(1521160192,92847519735262,92847895300954),(1521208320,92847941433865,92848316999889)]
theorem point_links_checked11575 : (cuts11575.take 3).map (fun c => (1521090561-1+2*2^9*c.k,92846909830631+c.lower,92847285395846+c.upper)) = pointBounds11575 := by
 decide +kernel
def cuts11576 : List PrefixCut := [⟨34,303449255,303449491⟩,
⟨81,721605652,721606215⟩,
⟨128,1137713630,1137714529⟩]
theorem checked11576 : checkPrefixCuts (2^48) 1521221633 9 Manual.Count131072.C011576.packed 128 cuts11576 = true := by
 decide +kernel
def pointBounds11576 : List (Nat × Nat × Nat) := [(1521256448,92848356272934,92848731839284),(1521304576,92848774429331,92849149996008),(1521352704,92849190537309,92849566104322)]
theorem point_links_checked11576 : (cuts11576.take 3).map (fun c => (1521221633-1+2*2^9*c.k,92848052823679+c.lower,92848428389793+c.upper)) = pointBounds11576 := by
 decide +kernel
def cuts11577 : List PrefixCut := [⟨47,412024480,412024803⟩,
⟨94,834951295,834951957⟩,
⟨128,1135395090,1135395992⟩]
theorem checked11577 : checkPrefixCuts (2^48) 1521352705 9 Manual.Count131072.C011577.packed 128 cuts11577 = true := by
 decide +kernel
def pointBounds11577 : List (Nat × Nat × Nat) := [(1521400832,92849602561789,92849978129125),(1521448960,92850025488604,92850401056279)]
theorem point_links_checked11577 : (cuts11577.take 2).map (fun c => (1521352705-1+2*2^9*c.k,92849190537309+c.lower,92849566104322+c.upper)) = pointBounds11577 := by
 decide +kernel
def cuts11578 : List PrefixCut := [⟨13,118584635,118584727⟩,
⟨60,544444766,544445192⟩,
⟨107,974546226,974546992⟩,
⟨128,1164896422,1164897337⟩]
theorem checked11578 : checkPrefixCuts (2^48) 1521483777 9 Manual.Count131072.C011578.packed 128 cuts11578 = true := by
 decide +kernel
def pointBounds11578 : List (Nat × Nat × Nat) := [(1521497088,92850444517034,92850820085041),(1521545216,92850870377165,92851245945506),(1521593344,92851300478625,92851676047306)]
theorem point_links_checked11578 : (cuts11578.take 3).map (fun c => (1521483777-1+2*2^9*c.k,92850325932399+c.lower,92850701500314+c.upper)) = pointBounds11578 := by
 decide +kernel
def cuts11579 : List PrefixCut := [⟨26,232523224,232523408⟩,
⟨73,657603036,657603555⟩,
⟨120,1076380369,1076381216⟩,
⟨128,1145928666,1145929565⟩]
theorem checked11579 : checkPrefixCuts (2^48) 1521614849 9 Manual.Count131072.C011579.packed 128 cuts11579 = true := by
 decide +kernel
def pointBounds11579 : List (Nat × Nat × Nat) := [(1521641472,92851723352045,92852098921059),(1521689600,92852148431857,92852524001206),(1521737728,92852567209190,92852942778867)]
theorem point_links_checked11579 : (cuts11579.take 3).map (fun c => (1521614849-1+2*2^9*c.k,92851490828821+c.lower,92851866397651+c.upper)) = pointBounds11579 := by
 decide +kernel
def cuts11580 : List PrefixCut := [⟨39,347920984,347921255⟩,
⟨86,756868931,756869525⟩,
⟨128,1133252537,1133253426⟩]
theorem checked11580 : checkPrefixCuts (2^48) 1521745921 9 Manual.Count131072.C011580.packed 128 cuts11580 = true := by
 decide +kernel
def pointBounds11580 : List (Nat × Nat × Nat) := [(1521785856,92852984678471,92853360248471),(1521833984,92853393626418,92853769196741)]
theorem point_links_checked11580 : (cuts11580.take 2).map (fun c => (1521745921-1+2*2^9*c.k,92852636757487+c.lower,92853012327216+c.upper)) = pointBounds11580 := by
 decide +kernel
def cuts11581 : List PrefixCut := [⟨5,46792889,46792924⟩,
⟨52,466811818,466812182⟩,
⟨99,882748721,882749415⟩,
⟨128,1143141880,1143142778⟩]
theorem checked11581 : checkPrefixCuts (2^48) 1521876993 9 Manual.Count131072.C011581.packed 128 cuts11581 = true := by
 decide +kernel
def pointBounds11581 : List (Nat × Nat × Nat) := [(1521882112,92853816802913,92854192373566),(1521930240,92854236821842,92854612392824),(1521978368,92854652758745,92855028330057)]
theorem point_links_checked11581 : (cuts11581.take 3).map (fun c => (1521876993-1+2*2^9*c.k,92853770010024+c.lower,92854145580642+c.upper)) = pointBounds11581 := by
 decide +kernel
def cuts11582 : List PrefixCut := [⟨18,163667815,163667940⟩,
⟨65,589194909,589195365⟩,
⟨112,1012304447,1012305235⟩,
⟨128,1156358345,1156359249⟩]
theorem checked11582 : checkPrefixCuts (2^48) 1522008065 9 Manual.Count131072.C011582.packed 128 cuts11582 = true := by
 decide +kernel
def pointBounds11582 : List (Nat × Nat × Nat) := [(1522026496,92855076819719,92855452391360),(1522074624,92855502346813,92855877918785),(1522122752,92855925456351,92856301028655)]
theorem point_links_checked11582 : (cuts11582.take 3).map (fun c => (1522008065-1+2*2^9*c.k,92854913151904+c.lower,92855288723420+c.upper)) = pointBounds11582 := by
 decide +kernel
def cuts11583 : List PrefixCut := [⟨31,273494724,273494939⟩,
⟨78,703604294,703604846⟩,
⟨125,1133885114,1133886001⟩,
⟨128,1160141604,1160142512⟩]
theorem checked11583 : checkPrefixCuts (2^48) 1522139137 9 Manual.Count131072.C011583.packed 128 cuts11583 = true := by
 decide +kernel
def pointBounds11583 : List (Nat × Nat × Nat) := [(1522170880,92856343004973,92856718577608),(1522219008,92856773114543,92857148687515),(1522267136,92857203395363,92857578968670)]
theorem point_links_checked11583 : (cuts11583.take 3).map (fun c => (1522139137-1+2*2^9*c.k,92856069510249+c.lower,92856445082669+c.upper)) = pointBounds11583 := by
 decide +kernel
def cuts11584 : List PrefixCut := [⟨44,393471354,393471661⟩,
⟨91,820951507,820952143⟩,
⟨128,1146544657,1146545546⟩]
theorem checked11584 : checkPrefixCuts (2^48) 1522270209 9 Manual.Count131072.C011584.packed 128 cuts11584 = true := by
 decide +kernel
def pointBounds11584 : List (Nat × Nat × Nat) := [(1522315264,92857623123207,92857998696842),(1522363392,92858050603360,92858426177324)]
theorem point_links_checked11584 : (cuts11584.take 2).map (fun c => (1522270209-1+2*2^9*c.k,92857229651853+c.lower,92857605225181+c.upper)) = pointBounds11584 := by
 decide +kernel
def cuts11585 : List PrefixCut := [⟨10,93738280,93738351⟩,
⟨57,514905407,514905806⟩,
⟨104,940496358,940497088⟩,
⟨128,1147555608,1147556499⟩]
theorem checked11585 : checkPrefixCuts (2^48) 1522401281 9 Manual.Count131072.C011585.packed 128 cuts11585 = true := by
 decide +kernel
def pointBounds11585 : List (Nat × Nat × Nat) := [(1522411520,92858469934790,92858845509078),(1522459648,92858891101917,92859266676533),(1522507776,92859316692868,92859692267815)]
theorem point_links_checked11585 : (cuts11585.take 3).map (fun c => (1522401281-1+2*2^9*c.k,92858376196510+c.lower,92858751770727+c.upper)) = pointBounds11585 := by
 decide +kernel
def cuts11586 : List PrefixCut := [⟨23,220921324,220921493⟩,
⟨70,636687396,636687892⟩,
⟨117,1062422843,1062423671⟩,
⟨128,1159842793,1159843697⟩]
theorem checked11586 : checkPrefixCuts (2^48) 1522532353 9 Manual.Count131072.C011586.packed 128 cuts11586 = true := by
 decide +kernel
def pointBounds11586 : List (Nat × Nat × Nat) := [(1522555904,92859744673442,92860120248719),(1522604032,92860160439514,92860536015118),(1522652160,92860586174961,92860961750897)]
theorem point_links_checked11586 : (cuts11586.take 3).map (fun c => (1522532353-1+2*2^9*c.k,92859523752118+c.lower,92859899327226+c.upper)) = pointBounds11586 := by
 decide +kernel
def cuts11587 : List PrefixCut := [⟨36,321092589,321092839⟩,
⟨83,739776714,739777295⟩,
⟨128,1143105866,1143106759⟩]
theorem checked11587 : checkPrefixCuts (2^48) 1522663425 9 Manual.Count131072.C011587.packed 128 cuts11587 = true := by
 decide +kernel
def pointBounds11587 : List (Nat × Nat × Nat) := [(1522700288,92861004687500,92861380263762),(1522748416,92861423371625,92861798948218)]
theorem point_links_checked11587 : (cuts11587.take 2).map (fun c => (1522663425-1+2*2^9*c.k,92860683594911+c.lower,92861059170923+c.upper)) = pointBounds11587 := by
 decide +kernel
def cuts11588 : List PrefixCut := [⟨2,18853770,18853784⟩,
⟨49,431042225,431042564⟩,
⟨96,839705746,839706400⟩,
⟨128,1121012553,1121013428⟩]
theorem checked11588 : checkPrefixCuts (2^48) 1522794497 9 Manual.Count131072.C011588.packed 128 cuts11588 = true := by
 decide +kernel
def pointBounds11588 : List (Nat × Nat × Nat) := [(1522796544,92861845554547,92862221131466),(1522844672,92862257743002,92862633320246),(1522892800,92862666406523,92863041984082)]
theorem point_links_checked11588 : (cuts11588.take 3).map (fun c => (1522794497-1+2*2^9*c.k,92861826700777+c.lower,92862202277682+c.upper)) = pointBounds11588 := by
 decide +kernel
def cuts11589 : List PrefixCut := [⟨15,138987783,138987890⟩,
⟨62,567770961,567771401⟩,
⟨109,981570635,981571394⟩,
⟨128,1155107579,1155108474⟩]
theorem checked11589 : checkPrefixCuts (2^48) 1522925569 9 Manual.Count131072.C011589.packed 128 cuts11589 = true := by
 decide +kernel
def pointBounds11589 : List (Nat × Nat × Nat) := [(1522940928,92863086701113,92863462279000),(1522989056,92863515484291,92863891062511),(1523037184,92863929283965,92864304862504)]
theorem point_links_checked11589 : (cuts11589.take 3).map (fun c => (1522925569-1+2*2^9*c.k,92862947713330+c.lower,92863323291110+c.upper)) = pointBounds11589 := by
 decide +kernel
def cuts11590 : List PrefixCut := [⟨28,254849490,254849689⟩,
⟨75,676199895,676200422⟩,
⟨122,1100308963,1100309824⟩,
⟨128,1151866395,1151867297⟩]
theorem checked11590 : checkPrefixCuts (2^48) 1523056641 9 Manual.Count131072.C011590.packed 128 cuts11590 = true := by
 decide +kernel
def pointBounds11590 : List (Nat × Nat × Nat) := [(1523085312,92864357670399,92864733249273),(1523133440,92864779020804,92865154600006),(1523181568,92865203129872,92865578709408)]
theorem point_links_checked11590 : (cuts11590.take 3).map (fun c => (1523056641-1+2*2^9*c.k,92864102820909+c.lower,92864478399584+c.upper)) = pointBounds11590 := by
 decide +kernel
def cuts11591 : List PrefixCut := [⟨41,363483385,363483667⟩,
⟨88,784608917,784609527⟩,
⟨128,1137723235,1137724127⟩]
theorem checked11591 : checkPrefixCuts (2^48) 1523187713 9 Manual.Count131072.C011591.packed 128 cuts11591 = true := by
 decide +kernel
def pointBounds11591 : List (Nat × Nat × Nat) := [(1523229696,92865618170689,92865993750548),(1523277824,92866039296221,92866414876408)]
theorem point_links_checked11591 : (cuts11591.take 2).map (fun c => (1523187713-1+2*2^9*c.k,92865254687304+c.lower,92865630266881+c.upper)) = pointBounds11591 := by
 decide +kernel
def cuts11592 : List PrefixCut := [⟨7,63932827,63932876⟩,
⟨54,480412538,480412916⟩,
⟨101,905563194,905563905⟩,
⟨128,1147972492,1147973391⟩]
theorem checked11592 : checkPrefixCuts (2^48) 1523318785 9 Manual.Count131072.C011592.packed 128 cuts11592 = true := by
 decide +kernel
def pointBounds11592 : List (Nat × Nat × Nat) := [(1523325952,92866456343366,92866831923884),(1523374080,92866872823077,92867248403924),(1523422208,92867297973733,92867673554913)]
theorem point_links_checked11592 : (cuts11592.take 3).map (fun c => (1523318785-1+2*2^9*c.k,92866392410539+c.lower,92866767991008+c.upper)) = pointBounds11592 := by
 decide +kernel
def cuts11593 : List PrefixCut := [⟨20,175522247,175522384⟩,
⟨67,589930222,589930684⟩,
⟨114,1016703305,1016704101⟩,
⟨128,1143993613,1143994508⟩]
theorem checked11593 : checkPrefixCuts (2^48) 1523449857 9 Manual.Count131072.C011593.packed 128 cuts11593 = true := by
 decide +kernel
def pointBounds11593 : List (Nat × Nat × Nat) := [(1523470336,92867715905278,92868091486783),(1523518464,92868130313253,92868505895083),(1523566592,92868557086336,92868932668500)]
theorem point_links_checked11593 : (cuts11593.take 3).map (fun c => (1523449857-1+2*2^9*c.k,92867540383031+c.lower,92867915964399+c.upper)) = pointBounds11593 := by
 decide +kernel
def cuts11594 : List PrefixCut := [⟨33,292264303,292264531⟩,
⟨80,710697151,710697708⟩,
⟨127,1136875633,1136876520⟩,
⟨128,1145188472,1145189366⟩]
theorem checked11594 : checkPrefixCuts (2^48) 1523580929 9 Manual.Count131072.C011594.packed 128 cuts11594 = true := by
 decide +kernel
def pointBounds11594 : List (Nat × Nat × Nat) := [(1523614720,92868976640947,92869352223438),(1523662848,92869395073795,92869770656615),(1523710976,92869821252277,92870196835427)]
theorem point_links_checked11594 : (cuts11594.take 3).map (fun c => (1523580929-1+2*2^9*c.k,92868684376644+c.lower,92869059958907+c.upper)) = pointBounds11594 := by
 decide +kernel
def cuts11595 : List PrefixCut := [⟨46,422285571,422285903⟩,
⟨93,838092698,838093353⟩,
⟨128,1154880524,1154881424⟩]
theorem checked11595 : checkPrefixCuts (2^48) 1523712001 9 Manual.Count131072.C011595.packed 128 cuts11595 = true := by
 decide +kernel
def pointBounds11595 : List (Nat × Nat × Nat) := [(1523759104,92870251850687,92870627434176),(1523807232,92870667657814,92871043241626)]
theorem point_links_checked11595 : (cuts11595.take 2).map (fun c => (1523712001-1+2*2^9*c.k,92869829565116+c.lower,92870205148273+c.upper)) = pointBounds11595 := by
 decide +kernel
def cuts11596 : List PrefixCut := [⟨12,106764154,106764237⟩,
⟨59,520143938,520144342⟩,
⟨106,936096364,936097093⟩,
⟨128,1131692945,1131693826⟩]
theorem checked11596 : checkPrefixCuts (2^48) 1523843073 9 Manual.Count131072.C011596.packed 128 cuts11596 = true := by
 decide +kernel
def pointBounds11596 : List (Nat × Nat × Nat) := [(1523855360,92871091209794,92871466793934),(1523903488,92871504589578,92871880174039),(1523951616,92871920542004,92872296126790)]
theorem point_links_checked11596 : (cuts11596.take 3).map (fun c => (1523843073-1+2*2^9*c.k,92870984445640+c.lower,92871360029697+c.upper)) = pointBounds11596 := by
 decide +kernel
def cuts11597 : List PrefixCut := [⟨25,232348032,232348214⟩,
⟨72,647904733,647905238⟩,
⟨119,1066034043,1066034877⟩,
⟨128,1144708826,1144709721⟩]
theorem checked11597 : checkPrefixCuts (2^48) 1523974145 9 Manual.Count131072.C011597.packed 128 cuts11597 = true := by
 decide +kernel
def pointBounds11597 : List (Nat × Nat × Nat) := [(1523999744,92872348486617,92872724071737),(1524047872,92872764043318,92873139628761),(1524096000,92873182172628,92873557758400)]
theorem point_links_checked11597 : (cuts11597.take 3).map (fun c => (1523974145-1+2*2^9*c.k,92872116138585+c.lower,92872491723523+c.upper)) = pointBounds11597 := by
 decide +kernel
def cuts11598 : List PrefixCut := [⟨38,339071969,339072229⟩,
⟨85,770286792,770287387⟩,
⟨128,1157167951,1157168851⟩]
theorem checked11598 : checkPrefixCuts (2^48) 1524105217 9 Manual.Count131072.C011598.packed 128 cuts11598 = true := by
 decide +kernel
def pointBounds11598 : List (Nat × Nat × Nat) := [(1524144128,92873599919380,92873975505473),(1524192256,92874031134203,92874406720631)]
theorem point_links_checked11598 : (cuts11598.take 2).map (fun c => (1524105217-1+2*2^9*c.k,92873260847411+c.lower,92873636433244+c.upper)) = pointBounds11598 := by
 decide +kernel
def cuts11599 : List PrefixCut := [⟨4,38041177,38041208⟩,
⟨51,458149002,458149361⟩,
⟨98,883967812,883968506⟩,
⟨128,1146173798,1146174697⟩]
theorem checked11599 : checkPrefixCuts (2^48) 1524236289 9 Manual.Count131072.C011599.packed 128 cuts11599 = true := by
 decide +kernel
def pointBounds11599 : List (Nat × Nat × Nat) := [(1524240384,92874456056539,92874831643303),(1524288512,92874876164364,92875251751456),(1524336640,92875301983174,92875677570601)]
theorem point_links_checked11599 : (cuts11599.take 3).map (fun c => (1524236289-1+2*2^9*c.k,92874418015362+c.lower,92874793602095+c.upper)) = pointBounds11599 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000049
