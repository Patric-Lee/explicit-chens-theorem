import PlattAssemblyKernel
import PlattCertificates.Count131072.C012144
import PlattCertificates.Count131072.C012145
import PlattCertificates.Count131072.C012146
import PlattCertificates.Count131072.C012147
import PlattCertificates.Count131072.C012148
import PlattCertificates.Count131072.C012149
import PlattCertificates.Count131072.C012150
import PlattCertificates.Count131072.C012151
import PlattCertificates.Count131072.C012152
import PlattCertificates.Count131072.C012153
import PlattCertificates.Count131072.C012154
import PlattCertificates.Count131072.C012155
import PlattCertificates.Count131072.C012156
import PlattCertificates.Count131072.C012157
import PlattCertificates.Count131072.C012158
import PlattCertificates.Count131072.C012159
import PlattCertificates.Count131072.C012160
import PlattCertificates.Count131072.C012161
import PlattCertificates.Count131072.C012162
import PlattCertificates.Count131072.C012163
import PlattCertificates.Count131072.C012164
import PlattCertificates.Count131072.C012165
import PlattCertificates.Count131072.C012166
import PlattCertificates.Count131072.C012167
import PlattCertificates.Count131072.C012168
import PlattCertificates.Count131072.C012169
import PlattCertificates.Count131072.C012170
import PlattCertificates.Count131072.C012171
import PlattCertificates.Count131072.C012172
import PlattCertificates.Count131072.C012173
import PlattCertificates.Count131072.C012174
import PlattCertificates.Count131072.C012175
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000067
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12144 : List PrefixCut := [⟨15,127535946,127536043⟩,
⟨64,549119301,549119720⟩,
⟨113,958518290,958519021⟩,
⟨128,1085515833,1085516662⟩]
theorem checked12144 : checkPrefixCuts (2^48) 1595670529 9 Manual.Count131072.C012144.packed 128 cuts12144 = true := by
 decide +kernel
def pointBounds12144 : List (Nat × Nat × Nat) := [(1595685888,93483555596071,93483931652589),(1595736064,93483977179426,93484353236266),(1595786240,93484386578415,93484762635567)]
theorem point_links_checked12144 : (cuts12144.take 3).map (fun c => (1595670529-1+2*2^9*c.k,93483428060125+c.lower,93483804116546+c.upper)) = pointBounds12144 := by
 decide +kernel
def cuts12145 : List PrefixCut := [⟨34,293853513,293853736⟩,
⟨83,715220582,715221125⟩,
⟨128,1103945965,1103946800⟩]
theorem checked12145 : checkPrefixCuts (2^48) 1595801601 9 Manual.Count131072.C012145.packed 128 cuts12145 = true := by
 decide +kernel
def pointBounds12145 : List (Nat × Nat × Nat) := [(1595836416,93484807429471,93485183486944),(1595886592,93485228796540,93485604854333)]
theorem point_links_checked12145 : (cuts12145.take 2).map (fun c => (1595801601-1+2*2^9*c.k,93484513575958+c.lower,93484889633208+c.upper)) = pointBounds12145 := by
 decide +kernel
def cuts12146 : List PrefixCut := [⟨4,32452064,32452089⟩,
⟨53,462434625,462434975⟩,
⟨102,866302143,866302803⟩,
⟨128,1089746612,1089747438⟩]
theorem checked12146 : checkPrefixCuts (2^48) 1595932673 9 Manual.Count131072.C012146.packed 128 cuts12146 = true := by
 decide +kernel
def pointBounds12146 : List (Nat × Nat × Nat) := [(1595936768,93485649973987,93486026032097),(1595986944,93486079956548,93486456014983),(1596037120,93486483824066,93486859882811)]
theorem point_links_checked12146 : (cuts12146.take 3).map (fun c => (1595932673-1+2*2^9*c.k,93485617521923+c.lower,93485993580008+c.upper)) = pointBounds12146 := by
 decide +kernel
def cuts12147 : List PrefixCut := [⟨23,201396661,201396814⟩,
⟨72,612292787,612293256⟩,
⟨121,1017180344,1017181121⟩,
⟨128,1075020376,1075021197⟩]
theorem checked12147 : checkPrefixCuts (2^48) 1596063745 9 Manual.Count131072.C012147.packed 128 cuts12147 = true := by
 decide +kernel
def pointBounds12147 : List (Nat × Nat × Nat) := [(1596087296,93486908665196,93487284724260),(1596137472,93487319561322,93487695620702),(1596187648,93487724448879,93488100508567)]
theorem point_links_checked12147 : (cuts12147.take 3).map (fun c => (1596063745-1+2*2^9*c.k,93486707268535+c.lower,93487083327446+c.upper)) = pointBounds12147 := by
 decide +kernel
def cuts12148 : List PrefixCut := [⟨42,358673094,358673363⟩,
⟨91,777641785,777642372⟩,
⟨128,1094152001,1094152831⟩]
theorem checked12148 : checkPrefixCuts (2^48) 1596194817 9 Manual.Count131072.C012148.packed 128 cuts12148 = true := by
 decide +kernel
def pointBounds12148 : List (Nat × Nat × Nat) := [(1596237824,93488140962005,93488517022006),(1596288000,93488559930696,93488935991015)]
theorem point_links_checked12148 : (cuts12148.take 2).map (fun c => (1596194817-1+2*2^9*c.k,93487782288911+c.lower,93488158348643+c.upper)) = pointBounds12148 := by
 decide +kernel
def cuts12149 : List PrefixCut := [⟨12,103327052,103327132⟩,
⟨61,515040222,515040612⟩,
⟨110,928856282,928856982⟩,
⟨128,1079075166,1079075981⟩]
theorem checked12149 : checkPrefixCuts (2^48) 1596325889 9 Manual.Count131072.C012149.packed 128 cuts12149 = true := by
 decide +kernel
def pointBounds12149 : List (Nat × Nat × Nat) := [(1596338176,93488979767964,93489355828606),(1596388352,93489391481134,93489767542086),(1596438528,93489805297194,93490181358456)]
theorem point_links_checked12149 : (cuts12149.take 3).map (fun c => (1596325889-1+2*2^9*c.k,93488876440912+c.lower,93489252501474+c.upper)) = pointBounds12149 := by
 decide +kernel
def cuts12150 : List PrefixCut := [⟨31,262526321,262526523⟩,
⟨80,677726887,677727404⟩,
⟨128,1083041658,1083042481⟩]
theorem checked12150 : checkPrefixCuts (2^48) 1596456961 9 Manual.Count131072.C012150.packed 128 cuts12150 = true := by
 decide +kernel
def pointBounds12150 : List (Nat × Nat × Nat) := [(1596488704,93490218042399,93490594103978),(1596538880,93490633242965,93491009304859)]
theorem point_links_checked12150 : (cuts12150.take 2).map (fun c => (1596456961-1+2*2^9*c.k,93489955516078+c.lower,93490331577455+c.upper)) = pointBounds12150 := by
 decide +kernel
def cuts12151 : List PrefixCut := [⟨1,8814884,8814891⟩,
⟨50,425928580,425928907⟩,
⟨99,844968296,844968941⟩,
⟨128,1091062024,1091062855⟩]
theorem checked12151 : checkPrefixCuts (2^48) 1596588033 9 Manual.Count131072.C012151.packed 128 cuts12151 = true := by
 decide +kernel
def pointBounds12151 : List (Nat × Nat × Nat) := [(1596589056,93491047372620,93491423434827),(1596639232,93491464486316,93491840548843),(1596689408,93491883526032,93492259588877)]
theorem point_links_checked12151 : (cuts12151.take 3).map (fun c => (1596588033-1+2*2^9*c.k,93491038557736+c.lower,93491414619936+c.upper)) = pointBounds12151 := by
 decide +kernel
def cuts12152 : List PrefixCut := [⟨20,173814229,173814362⟩,
⟨69,597410863,597411314⟩,
⟨118,1010065217,1010065983⟩,
⟨128,1097671086,1097671919⟩]
theorem checked12152 : checkPrefixCuts (2^48) 1596719105 9 Manual.Count131072.C012152.packed 128 cuts12152 = true := by
 decide +kernel
def pointBounds12152 : List (Nat × Nat × Nat) := [(1596739584,93492303433989,93492679497153),(1596789760,93492727030623,93493103094105),(1596839936,93493139684977,93493515748774)]
theorem point_links_checked12152 : (cuts12152.take 3).map (fun c => (1596719105-1+2*2^9*c.k,93492129619760+c.lower,93492505682791+c.upper)) = pointBounds12152 := by
 decide +kernel
def cuts12153 : List PrefixCut := [⟨39,341957217,341957476⟩,
⟨88,757405877,757406454⟩,
⟨128,1093527170,1093528001⟩]
theorem checked12153 : checkPrefixCuts (2^48) 1596850177 9 Manual.Count131072.C012153.packed 128 cuts12153 = true := by
 decide +kernel
def pointBounds12153 : List (Nat × Nat × Nat) := [(1596890112,93493569248063,93493945312186),(1596940288,93493984696723,93494360761164)]
theorem point_links_checked12153 : (cuts12153.take 2).map (fun c => (1596850177-1+2*2^9*c.k,93493227290846+c.lower,93493603354710+c.upper)) = pointBounds12153 := by
 decide +kernel
def cuts12154 : List PrefixCut := [⟨9,76846665,76846724⟩,
⟨58,491035571,491035945⟩,
⟨107,892521682,892522361⟩,
⟨128,1076341101,1076341918⟩]
theorem checked12154 : checkPrefixCuts (2^48) 1596981249 9 Manual.Count131072.C012154.packed 128 cuts12154 = true := by
 decide +kernel
def pointBounds12154 : List (Nat × Nat × Nat) := [(1596990464,93494397664681,93494773729435),(1597040640,93494811853587,93495187918656),(1597090816,93495213339698,93495589405072)]
theorem point_links_checked12154 : (cuts12154.take 3).map (fun c => (1596981249-1+2*2^9*c.k,93494320818016+c.lower,93494696882711+c.upper)) = pointBounds12154 := by
 decide +kernel
def cuts12155 : List PrefixCut := [⟨28,241093996,241094178⟩,
⟨77,658768509,658769009⟩,
⟨126,1072552819,1072553635⟩,
⟨128,1089999145,1089999974⟩]
theorem checked12155 : checkPrefixCuts (2^48) 1597112321 9 Manual.Count131072.C012155.packed 128 cuts12155 = true := by
 decide +kernel
def pointBounds12155 : List (Nat × Nat × Nat) := [(1597140992,93495638253113,93496014318807),(1597191168,93496055927626,93496431993638),(1597241344,93496469711936,93496845778264)]
theorem point_links_checked12155 : (cuts12155.take 3).map (fun c => (1597112321-1+2*2^9*c.k,93495397159117+c.lower,93495773224629+c.upper)) = pointBounds12155 := by
 decide +kernel
def cuts12156 : List PrefixCut := [⟨47,403550135,403550442⟩,
⟨96,822947452,822948079⟩,
⟨128,1097134524,1097135356⟩]
theorem checked12156 : checkPrefixCuts (2^48) 1597243393 9 Manual.Count131072.C012156.packed 128 cuts12156 = true := by
 decide +kernel
def pointBounds12156 : List (Nat × Nat × Nat) := [(1597291520,93496890708397,93497266775045),(1597341696,93497310105714,93497686172682)]
theorem point_links_checked12156 : (cuts12156.take 2).map (fun c => (1597243393-1+2*2^9*c.k,93496487158262+c.lower,93496863224603+c.upper)) = pointBounds12156 := by
 decide +kernel
def cuts12157 : List PrefixCut := [⟨17,150130922,150131033⟩,
⟨66,568092146,568092571⟩,
⟨115,993440720,993441467⟩,
⟨128,1106383135,1106383968⟩]
theorem checked12157 : checkPrefixCuts (2^48) 1597374465 9 Manual.Count131072.C012157.packed 128 cuts12157 = true := by
 decide +kernel
def pointBounds12157 : List (Nat × Nat × Nat) := [(1597391872,93497734423708,93498110490992),(1597442048,93498152384932,93498528452530),(1597492224,93498577733506,93498953801426)]
theorem point_links_checked12157 : (cuts12157.take 3).map (fun c => (1597374465-1+2*2^9*c.k,93497584292786+c.lower,93497960359959+c.upper)) = pointBounds12157 := by
 decide +kernel
def cuts12158 : List PrefixCut := [⟨36,300587722,300587951⟩,
⟨85,716395281,716395822⟩,
⟨128,1082154228,1082155047⟩]
theorem checked12158 : checkPrefixCuts (2^48) 1597505537 9 Manual.Count131072.C012158.packed 128 cuts12158 = true := by
 decide +kernel
def pointBounds12158 : List (Nat × Nat × Nat) := [(1597542400,93498991263643,93499367331878),(1597592576,93499407071202,93499783139749)]
theorem point_links_checked12158 : (cuts12158.take 2).map (fun c => (1597505537-1+2*2^9*c.k,93498690675921+c.lower,93499066743927+c.upper)) = pointBounds12158 := by
 decide +kernel
def cuts12159 : List PrefixCut := [⟨6,51445054,51445095⟩,
⟨55,464936200,464936554⟩,
⟨104,887575328,887576004⟩,
⟨128,1093164468,1093165301⟩]
theorem checked12159 : checkPrefixCuts (2^48) 1597636609 9 Manual.Count131072.C012159.packed 128 cuts12159 = true := by
 decide +kernel
def pointBounds12159 : List (Nat × Nat × Nat) := [(1597642752,93499824275203,93500200344069),(1597692928,93500237766349,93500613835528),(1597743104,93500660405477,93501036474978)]
theorem point_links_checked12159 : (cuts12159.take 3).map (fun c => (1597636609-1+2*2^9*c.k,93499772830149+c.lower,93500148898974+c.upper)) = pointBounds12159 := by
 decide +kernel
def cuts12160 : List PrefixCut := [⟨25,212984954,212985109⟩,
⟨74,628198822,628199291⟩,
⟨123,1047979571,1047980359⟩,
⟨128,1092546389,1092547209⟩]
theorem checked12160 : checkPrefixCuts (2^48) 1597767681 9 Manual.Count131072.C012160.packed 128 cuts12160 = true := by
 decide +kernel
def pointBounds12160 : List (Nat × Nat × Nat) := [(1597793280,93501078979571,93501455049384),(1597843456,93501494193439,93501870263566),(1597893632,93501913974188,93502290044634)]
theorem point_links_checked12160 : (cuts12160.take 3).map (fun c => (1597767681-1+2*2^9*c.k,93500865994617+c.lower,93501242064275+c.upper)) = pointBounds12160 := by
 decide +kernel
def cuts12161 : List PrefixCut := [⟨44,376257720,376258003⟩,
⟨93,790551726,790552324⟩,
⟨128,1092985246,1092986071⟩]
theorem checked12161 : checkPrefixCuts (2^48) 1597898753 9 Manual.Count131072.C012161.packed 128 cuts12161 = true := by
 decide +kernel
def pointBounds12161 : List (Nat × Nat × Nat) := [(1597943808,93502334798726,93502710869487),(1597993984,93502749092732,93503125163808)]
theorem point_links_checked12161 : (cuts12161.take 2).map (fun c => (1597898753-1+2*2^9*c.k,93501958541006+c.lower,93502334611484+c.upper)) = pointBounds12161 := by
 decide +kernel
def cuts12162 : List PrefixCut := [⟨14,118540820,118540909⟩,
⟨63,532104260,532104667⟩,
⟨112,939137985,939138702⟩,
⟨128,1081799349,1081800176⟩]
theorem checked12162 : checkPrefixCuts (2^48) 1598029825 9 Manual.Count131072.C012162.packed 128 cuts12162 = true := by
 decide +kernel
def pointBounds12162 : List (Nat × Nat × Nat) := [(1598044160,93503170067072,93503546138464),(1598094336,93503583630512,93503959702222),(1598144512,93503990664237,93504366736257)]
theorem point_links_checked12162 : (cuts12162.take 3).map (fun c => (1598029825-1+2*2^9*c.k,93503051526252+c.lower,93503427597555+c.upper)) = pointBounds12162 := by
 decide +kernel
def cuts12163 : List PrefixCut := [⟨33,287431688,287431910⟩,
⟨82,700075515,700076046⟩,
⟨128,1098265661,1098266485⟩]
theorem checked12163 : checkPrefixCuts (2^48) 1598160897 9 Manual.Count131072.C012163.packed 128 cuts12163 = true := by
 decide +kernel
def pointBounds12163 : List (Nat × Nat × Nat) := [(1598194688,93504420757289,93504796829641),(1598244864,93504833401116,93505209473777)]
theorem point_links_checked12163 : (cuts12163.take 2).map (fun c => (1598160897-1+2*2^9*c.k,93504133325601+c.lower,93504509397731+c.upper)) = pointBounds12163 := by
 decide +kernel
def cuts12164 : List PrefixCut := [⟨3,24127021,24127038⟩,
⟨52,436921003,436921335⟩,
⟨101,857098399,857099050⟩,
⟨128,1083911162,1083911983⟩]
theorem checked12164 : checkPrefixCuts (2^48) 1598291969 9 Manual.Count131072.C012164.packed 128 cuts12164 = true := by
 decide +kernel
def pointBounds12164 : List (Nat × Nat × Nat) := [(1598295040,93505255718283,93505631791254),(1598345216,93505668512265,93506044585551),(1598395392,93506088689661,93506464763266)]
theorem point_links_checked12164 : (cuts12164.take 3).map (fun c => (1598291969-1+2*2^9*c.k,93505231591262+c.lower,93505607664216+c.upper)) = pointBounds12164 := by
 decide +kernel
def cuts12165 : List PrefixCut := [⟨22,178031142,178031276⟩,
⟨71,594660300,594660750⟩,
⟨120,999830961,999831721⟩,
⟨128,1066917966,1066918777⟩]
theorem checked12165 : checkPrefixCuts (2^48) 1598423041 9 Manual.Count131072.C012165.packed 128 cuts12165 = true := by
 decide +kernel
def pointBounds12165 : List (Nat × Nat × Nat) := [(1598445568,93506493533566,93506869607475),(1598495744,93506910162724,93507286236949),(1598545920,93507315333385,93507691407920)]
theorem point_links_checked12165 : (cuts12165.take 3).map (fun c => (1598423041-1+2*2^9*c.k,93506315502424+c.lower,93506691576199+c.upper)) = pointBounds12165 := by
 decide +kernel
def cuts12166 : List PrefixCut := [⟨41,352861605,352861875⟩,
⟨90,768042976,768043562⟩,
⟨128,1087607498,1087608326⟩]
theorem checked12166 : checkPrefixCuts (2^48) 1598554113 9 Manual.Count131072.C012166.packed 128 cuts12166 = true := by
 decide +kernel
def pointBounds12166 : List (Nat × Nat × Nat) := [(1598596096,93507735281995,93508111356851),(1598646272,93508150463366,93508526538538)]
theorem point_links_checked12166 : (cuts12166.take 2).map (fun c => (1598554113-1+2*2^9*c.k,93507382420390+c.lower,93507758494976+c.upper)) = pointBounds12166 := by
 decide +kernel
def cuts12167 : List PrefixCut := [⟨11,97540489,97540562⟩,
⟨60,514984548,514984938⟩,
⟨109,935584562,935585274⟩,
⟨128,1095264725,1095265559⟩]
theorem checked12167 : checkPrefixCuts (2^48) 1598685185 9 Manual.Count131072.C012167.packed 128 cuts12167 = true := by
 decide +kernel
def pointBounds12167 : List (Nat × Nat × Nat) := [(1598696448,93508567568377,93508943643864),(1598746624,93508985012436,93509361088240),(1598796800,93509405612450,93509781688576)]
theorem point_links_checked12167 : (cuts12167.take 3).map (fun c => (1598685185-1+2*2^9*c.k,93508470027888+c.lower,93508846103302+c.upper)) = pointBounds12167 := by
 decide +kernel
def cuts12168 : List PrefixCut := [⟨30,254744884,254745077⟩,
⟨79,666164138,666164649⟩,
⟨128,1068944616,1068945435⟩]
theorem checked12168 : checkPrefixCuts (2^48) 1598816257 9 Manual.Count131072.C012168.packed 128 cuts12168 = true := by
 decide +kernel
def pointBounds12168 : List (Nat × Nat × Nat) := [(1598846976,93509820037497,93510196113938),(1598897152,93510231456751,93510607533510),(1598947328,93510634237229,93511010314296)]
theorem point_links_checked12168 : (cuts12168.take 3).map (fun c => (1598816257-1+2*2^9*c.k,93509565292613+c.lower,93509941368861+c.upper)) = pointBounds12168 := by
 decide +kernel
def cuts12169 : List PrefixCut := [⟨49,417378631,417378944⟩,
⟨98,844953737,844954368⟩,
⟨128,1104942482,1104943307⟩]
theorem checked12169 : checkPrefixCuts (2^48) 1598947329 9 Manual.Count131072.C012169.packed 128 cuts12169 = true := by
 decide +kernel
def pointBounds12169 : List (Nat × Nat × Nat) := [(1598997504,93511051615860,93511427693240),(1599047680,93511479190966,93511855268664)]
theorem point_links_checked12169 : (cuts12169.take 2).map (fun c => (1598947329-1+2*2^9*c.k,93510634237229+c.lower,93511010314296+c.upper)) = pointBounds12169 := by
 decide +kernel
def cuts12170 : List PrefixCut := [⟨19,163700543,163700667⟩,
⟨68,581919962,581920410⟩,
⟨117,998542169,998542936⟩,
⟨128,1091827145,1091827980⟩]
theorem checked12170 : checkPrefixCuts (2^48) 1599078401 9 Manual.Count131072.C012170.packed 128 cuts12170 = true := by
 decide +kernel
def pointBounds12170 : List (Nat × Nat × Nat) := [(1599097856,93511902880254,93512278958270),(1599148032,93512321099673,93512697178013),(1599198208,93512737721880,93513113800539)]
theorem point_links_checked12170 : (cuts12170.take 3).map (fun c => (1599078401-1+2*2^9*c.k,93511739179711+c.lower,93512115257603+c.upper)) = pointBounds12170 := by
 decide +kernel
def cuts12171 : List PrefixCut := [⟨38,327196339,327196591⟩,
⟨87,740448336,740448903⟩,
⟨128,1087865697,1087866526⟩]
theorem checked12171 : checkPrefixCuts (2^48) 1599209473 9 Manual.Count131072.C012171.packed 128 cuts12171 = true := by
 decide +kernel
def pointBounds12171 : List (Nat × Nat × Nat) := [(1599248384,93513158203195,93513534282174),(1599298560,93513571455192,93513947534486)]
theorem point_links_checked12171 : (cuts12171.take 2).map (fun c => (1599209473-1+2*2^9*c.k,93512831006856+c.lower,93513207085583+c.upper)) = pointBounds12171 := by
 decide +kernel
def cuts12172 : List PrefixCut := [⟨8,67581647,67581696⟩,
⟨57,485207456,485207825⟩,
⟨106,910563647,910564337⟩,
⟨128,1101503155,1101503988⟩]
theorem checked12172 : checkPrefixCuts (2^48) 1599340545 9 Manual.Count131072.C012172.packed 128 cuts12172 = true := by
 decide +kernel
def pointBounds12172 : List (Nat × Nat × Nat) := [(1599348736,93513986454200,93514362533805),(1599398912,93514404080009,93514780159934),(1599449088,93514829436200,93515205516446)]
theorem point_links_checked12172 : (cuts12172.take 3).map (fun c => (1599340545-1+2*2^9*c.k,93513918872553+c.lower,93514294952109+c.upper)) = pointBounds12172 := by
 decide +kernel
def cuts12173 : List PrefixCut := [⟨27,230883640,230883814⟩,
⟨76,648998089,648998580⟩,
⟨125,1066395499,1066396308⟩,
⟨128,1091382623,1091383450⟩]
theorem checked12173 : checkPrefixCuts (2^48) 1599471617 9 Manual.Count131072.C012173.packed 128 cuts12173 = true := by
 decide +kernel
def pointBounds12173 : List (Nat × Nat × Nat) := [(1599499264,93515251259348,93515627339911),(1599549440,93515669373797,93516045454677),(1599599616,93516086771207,93516462852405)]
theorem point_links_checked12173 : (cuts12173.take 3).map (fun c => (1599471617-1+2*2^9*c.k,93515020375708+c.lower,93515396456097+c.upper)) = pointBounds12173 := by
 decide +kernel
def cuts12174 : List PrefixCut := [⟨46,387822259,387822554⟩,
⟨95,804313781,804314395⟩,
⟨128,1087070217,1087071044⟩]
theorem checked12174 : checkPrefixCuts (2^48) 1599602689 9 Manual.Count131072.C012174.packed 128 cuts12174 = true := by
 decide +kernel
def pointBounds12174 : List (Nat × Nat × Nat) := [(1599649792,93516499580590,93516875662101),(1599699968,93516916072112,93517292153942)]
theorem point_links_checked12174 : (cuts12174.take 2).map (fun c => (1599602689-1+2*2^9*c.k,93516111758331+c.lower,93516487839547+c.upper)) = pointBounds12174 := by
 decide +kernel
def cuts12175 : List PrefixCut := [⟨16,129499335,129499432⟩,
⟨65,543501465,543501878⟩,
⟨114,951508622,951509344⟩,
⟨128,1070442345,1070443157⟩]
theorem checked12175 : checkPrefixCuts (2^48) 1599733761 9 Manual.Count131072.C012175.packed 128 cuts12175 = true := by
 decide +kernel
def pointBounds12175 : List (Nat × Nat × Nat) := [(1599750144,93517328327883,93517704410023),(1599800320,93517742330013,93518118412469),(1599850496,93518150337170,93518526419935)]
theorem point_links_checked12175 : (cuts12175.take 3).map (fun c => (1599733761-1+2*2^9*c.k,93517198828548+c.lower,93517574910591+c.upper)) = pointBounds12175 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000067
