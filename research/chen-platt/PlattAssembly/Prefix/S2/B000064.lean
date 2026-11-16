import PlattAssemblyKernel
import PlattCertificates.Count131072.C012048
import PlattCertificates.Count131072.C012049
import PlattCertificates.Count131072.C012050
import PlattCertificates.Count131072.C012051
import PlattCertificates.Count131072.C012052
import PlattCertificates.Count131072.C012053
import PlattCertificates.Count131072.C012054
import PlattCertificates.Count131072.C012055
import PlattCertificates.Count131072.C012056
import PlattCertificates.Count131072.C012057
import PlattCertificates.Count131072.C012058
import PlattCertificates.Count131072.C012059
import PlattCertificates.Count131072.C012060
import PlattCertificates.Count131072.C012061
import PlattCertificates.Count131072.C012062
import PlattCertificates.Count131072.C012063
import PlattCertificates.Count131072.C012064
import PlattCertificates.Count131072.C012065
import PlattCertificates.Count131072.C012066
import PlattCertificates.Count131072.C012067
import PlattCertificates.Count131072.C012068
import PlattCertificates.Count131072.C012069
import PlattCertificates.Count131072.C012070
import PlattCertificates.Count131072.C012071
import PlattCertificates.Count131072.C012072
import PlattCertificates.Count131072.C012073
import PlattCertificates.Count131072.C012074
import PlattCertificates.Count131072.C012075
import PlattCertificates.Count131072.C012076
import PlattCertificates.Count131072.C012077
import PlattCertificates.Count131072.C012078
import PlattCertificates.Count131072.C012079
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000064
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12048 : List PrefixCut := [⟨4,35737993,35738020⟩,
⟨53,459252484,459252835⟩,
⟨102,885953918,885954589⟩,
⟨128,1105522106,1105522947⟩]
theorem checked12048 : checkPrefixCuts (2^48) 1583087617 9 Manual.Count131072.C012048.packed 128 cuts12048 = true := by
 decide +kernel
def pointBounds12048 : List (Nat × Nat × Nat) := [(1583091712,93378287058006,93378663034447),(1583141888,93378710572497,93379086549262),(1583192064,93379137273931,93379513251016)]
theorem point_links_checked12048 : (cuts12048.take 3).map (fun c => (1583087617-1+2*2^9*c.k,93378251320013+c.lower,93378627296427+c.upper)) = pointBounds12048 := by
 decide +kernel
def cuts12049 : List PrefixCut := [⟨23,206764141,206764300⟩,
⟨72,622593967,622594447⟩,
⟨121,1036455195,1036455988⟩,
⟨128,1099919853,1099920694⟩]
theorem checked12049 : checkPrefixCuts (2^48) 1583218689 9 Manual.Count131072.C012049.packed 128 cuts12049 = true := by
 decide +kernel
def pointBounds12049 : List (Nat × Nat × Nat) := [(1583242240,93379563606260,93379939583674),(1583292416,93379979436086,93380355413821),(1583342592,93380393297314,93380769275362)]
theorem point_links_checked12049 : (cuts12049.take 3).map (fun c => (1583218689-1+2*2^9*c.k,93379356842119+c.lower,93379732819374+c.upper)) = pointBounds12049 := by
 decide +kernel
def cuts12050 : List PrefixCut := [⟨42,362116242,362116519⟩,
⟨91,785905895,785906499⟩,
⟨128,1108183314,1108184164⟩]
theorem checked12050 : checkPrefixCuts (2^48) 1583349761 9 Manual.Count131072.C012050.packed 128 cuts12050 = true := by
 decide +kernel
def pointBounds12050 : List (Nat × Nat × Nat) := [(1583392768,93380818878214,93381194856587),(1583442944,93381242667867,93381618646567)]
theorem point_links_checked12050 : (cuts12050.take 2).map (fun c => (1583349761-1+2*2^9*c.k,93380456761972+c.lower,93380832740068+c.upper)) = pointBounds12050 := by
 decide +kernel
def cuts12051 : List PrefixCut := [⟨12,103276450,103276529⟩,
⟨61,527216952,527217351⟩,
⟨110,945811692,945812414⟩,
⟨128,1107024930,1107025772⟩]
theorem checked12051 : checkPrefixCuts (2^48) 1583480833 9 Manual.Count131072.C012051.packed 128 cuts12051 = true := by
 decide +kernel
def pointBounds12051 : List (Nat × Nat × Nat) := [(1583493120,93381668221736,93382044200761),(1583543296,93382092162238,93382468141583),(1583593472,93382510756978,93382886736646)]
theorem point_links_checked12051 : (cuts12051.take 3).map (fun c => (1583480833-1+2*2^9*c.k,93381564945286+c.lower,93381940924232+c.upper)) = pointBounds12051 := by
 decide +kernel
def cuts12052 : List PrefixCut := [⟨31,259501169,259501368⟩,
⟨80,684467799,684468325⟩,
⟨128,1099112904,1099113752⟩]
theorem checked12052 : checkPrefixCuts (2^48) 1583611905 9 Manual.Count131072.C012052.packed 128 cuts12052 = true := by
 decide +kernel
def pointBounds12052 : List (Nat × Nat × Nat) := [(1583643648,93382931471385,93383307451372),(1583693824,93383356438015,93383732418329)]
theorem point_links_checked12052 : (cuts12052.take 2).map (fun c => (1583611905-1+2*2^9*c.k,93382671970216+c.lower,93383047950004+c.upper)) = pointBounds12052 := by
 decide +kernel
def cuts12053 : List PrefixCut := [⟨1,8708651,8708657⟩,
⟨50,432937467,432937796⟩,
⟨99,855731068,855731714⟩,
⟨128,1110396010,1110396851⟩]
theorem checked12053 : checkPrefixCuts (2^48) 1583742977 9 Manual.Count131072.C012053.packed 128 cuts12053 = true := by
 decide +kernel
def pointBounds12053 : List (Nat × Nat × Nat) := [(1583744000,93383779791771,93384155772413),(1583794176,93384204020587,93384580001552),(1583844352,93384626814188,93385002795470)]
theorem point_links_checked12053 : (cuts12053.take 3).map (fun c => (1583742977-1+2*2^9*c.k,93383771083120+c.lower,93384147063756+c.upper)) = pointBounds12053 := by
 decide +kernel
def cuts12054 : List PrefixCut := [⟨20,169892442,169892573⟩,
⟨69,585551000,585551447⟩,
⟨118,1002440322,1002441087⟩,
⟨128,1088268833,1088269663⟩]
theorem checked12054 : checkPrefixCuts (2^48) 1583874049 9 Manual.Count131072.C012054.packed 128 cuts12054 = true := by
 decide +kernel
def pointBounds12054 : List (Nat × Nat × Nat) := [(1583894528,93385051371572,93385427353180),(1583944704,93385467030130,93385843012054),(1583994880,93385883919452,93386259901694)]
theorem point_links_checked12054 : (cuts12054.take 3).map (fun c => (1583874049-1+2*2^9*c.k,93384881479130+c.lower,93385257460607+c.upper)) = pointBounds12054 := by
 decide +kernel
def cuts12055 : List PrefixCut := [⟨39,325005893,325006143⟩,
⟨88,751819589,751820167⟩,
⟨128,1100616776,1100617620⟩]
theorem checked12055 : checkPrefixCuts (2^48) 1584005121 9 Manual.Count131072.C012055.packed 128 cuts12055 = true := by
 decide +kernel
def pointBounds12055 : List (Nat × Nat × Nat) := [(1584045056,93386294753856,93386670736413),(1584095232,93386721567552,93387097550437)]
theorem point_links_checked12055 : (cuts12055.take 2).map (fun c => (1584005121-1+2*2^9*c.k,93385969747963+c.lower,93386345730270+c.upper)) = pointBounds12055 := by
 decide +kernel
def cuts12056 : List PrefixCut := [⟨9,79601983,79602042⟩,
⟨58,508343029,508343414⟩,
⟨107,926943064,926943764⟩,
⟨128,1107278129,1107278967⟩]
theorem checked12056 : checkPrefixCuts (2^48) 1584136193 9 Manual.Count131072.C012056.packed 128 cuts12056 = true := by
 decide +kernel
def pointBounds12056 : List (Nat × Nat × Nat) := [(1584145408,93387149966722,93387525949932),(1584195584,93387578707768,93387954691304),(1584245760,93387997307803,93388373291654)]
theorem point_links_checked12056 : (cuts12056.take 3).map (fun c => (1584136193-1+2*2^9*c.k,93387070364739+c.lower,93387446347890+c.upper)) = pointBounds12056 := by
 decide +kernel
def cuts12057 : List PrefixCut := [⟨28,245003112,245003298⟩,
⟨77,656470058,656470559⟩,
⟨126,1078761052,1078761875⟩,
⟨128,1095460548,1095461384⟩]
theorem checked12057 : checkPrefixCuts (2^48) 1584267265 9 Manual.Count131072.C012057.packed 128 cuts12057 = true := by
 decide +kernel
def pointBounds12057 : List (Nat × Nat × Nat) := [(1584295936,93388422645980,93388798630155),(1584346112,93388834112926,93389210097416),(1584396288,93389256403920,93389632388732)]
theorem point_links_checked12057 : (cuts12057.take 3).map (fun c => (1584267265-1+2*2^9*c.k,93388177642868+c.lower,93388553626857+c.upper)) = pointBounds12057 := by
 decide +kernel
def cuts12058 : List PrefixCut := [⟨47,397583719,397584023⟩,
⟨96,821091513,821092143⟩,
⟨128,1096613099,1096613936⟩]
theorem checked12058 : checkPrefixCuts (2^48) 1584398337 9 Manual.Count131072.C012058.packed 128 cuts12058 = true := by
 decide +kernel
def pointBounds12058 : List (Nat × Nat × Nat) := [(1584446464,93389670687135,93390046672264),(1584496640,93390094194929,93390470180384)]
theorem point_links_checked12058 : (cuts12058.take 2).map (fun c => (1584398337-1+2*2^9*c.k,93389273103416+c.lower,93389649088241+c.upper)) = pointBounds12058 := by
 decide +kernel
def cuts12059 : List PrefixCut := [⟨17,142466010,142466117⟩,
⟨66,565591757,565592182⟩,
⟨115,988526462,988527216⟩,
⟨128,1099720017,1099720855⟩]
theorem checked12059 : checkPrefixCuts (2^48) 1584529409 9 Manual.Count131072.C012059.packed 128 cuts12059 = true := by
 decide +kernel
def pointBounds12059 : List (Nat × Nat × Nat) := [(1584546816,93390512182525,93390888168294),(1584596992,93390935308272,93391311294359),(1584647168,93391358242977,93391734229393)]
theorem point_links_checked12059 : (cuts12059.take 3).map (fun c => (1584529409-1+2*2^9*c.k,93390369716515+c.lower,93390745702177+c.upper)) = pointBounds12059 := by
 decide +kernel
def cuts12060 : List PrefixCut := [⟨36,312615911,312616146⟩,
⟨85,721136701,721137252⟩,
⟨128,1088084096,1088084925⟩]
theorem checked12060 : checkPrefixCuts (2^48) 1584660481 9 Manual.Count131072.C012060.packed 128 cuts12060 = true := by
 decide +kernel
def pointBounds12060 : List (Nat × Nat × Nat) := [(1584697344,93391782052443,93392158039178),(1584747520,93392190573233,93392566560284)]
theorem point_links_checked12060 : (cuts12060.take 2).map (fun c => (1584660481-1+2*2^9*c.k,93391469436532+c.lower,93391845423032+c.upper)) = pointBounds12060 := by
 decide +kernel
def cuts12061 : List PrefixCut := [⟨6,49375488,49375526⟩,
⟨55,468349250,468349606⟩,
⟨104,891927456,891928141⟩,
⟨128,1094565304,1094566145⟩]
theorem checked12061 : checkPrefixCuts (2^48) 1584791553 9 Manual.Count131072.C012061.packed 128 cuts12061 = true := by
 decide +kernel
def pointBounds12061 : List (Nat × Nat × Nat) := [(1584797696,93392606896116,93392982883483),(1584847872,93393025869878,93393401857563),(1584898048,93393449448084,93393825436098)]
theorem point_links_checked12061 : (cuts12061.take 3).map (fun c => (1584791553-1+2*2^9*c.k,93392557520628+c.lower,93392933507957+c.upper)) = pointBounds12061 := by
 decide +kernel
def cuts12062 : List PrefixCut := [⟨25,210626383,210626544⟩,
⟨74,627429326,627429806⟩,
⟨123,1046705315,1046706114⟩,
⟨128,1087726510,1087727341⟩]
theorem checked12062 : checkPrefixCuts (2^48) 1584922625 9 Manual.Count131072.C012062.packed 128 cuts12062 = true := by
 decide +kernel
def pointBounds12062 : List (Nat × Nat × Nat) := [(1584948224,93393862712315,93394238700646),(1584998400,93394279515258,93394655503908),(1585048576,93394698791247,93395074780216)]
theorem point_links_checked12062 : (cuts12062.take 3).map (fun c => (1584922625-1+2*2^9*c.k,93393652085932+c.lower,93394028074102+c.upper)) = pointBounds12062 := by
 decide +kernel
def cuts12063 : List PrefixCut := [⟨44,381082676,381082964⟩,
⟨93,800332074,800332679⟩,
⟨128,1097048126,1097048960⟩]
theorem checked12063 : checkPrefixCuts (2^48) 1585053697 9 Manual.Count131072.C012063.packed 128 cuts12063 = true := by
 decide +kernel
def pointBounds12063 : List (Nat × Nat × Nat) := [(1585098752,93395120895118,93395496884407),(1585148928,93395540144516,93395916134122)]
theorem point_links_checked12063 : (cuts12063.take 2).map (fun c => (1585053697-1+2*2^9*c.k,93394739812442+c.lower,93395115801443+c.upper)) = pointBounds12063 := by
 decide +kernel
def cuts12064 : List PrefixCut := [⟨14,115594921,115595009⟩,
⟨63,535350419,535350828⟩,
⟨112,962727602,962728338⟩,
⟨128,1095891749,1095892589⟩]
theorem checked12064 : checkPrefixCuts (2^48) 1585184769 9 Manual.Count131072.C012064.packed 128 cuts12064 = true := by
 decide +kernel
def pointBounds12064 : List (Nat × Nat × Nat) := [(1585199104,93395952455489,93396328445412),(1585249280,93396372210987,93396748201231),(1585299456,93396799588170,93397175578741)]
theorem point_links_checked12064 : (cuts12064.take 3).map (fun c => (1585184769-1+2*2^9*c.k,93395836860568+c.lower,93396212850403+c.upper)) = pointBounds12064 := by
 decide +kernel
def cuts12065 : List PrefixCut := [⟨33,277154564,277154775⟩,
⟨82,699000775,699001306⟩,
⟨128,1092960369,1092961201⟩]
theorem checked12065 : checkPrefixCuts (2^48) 1585315841 9 Manual.Count131072.C012065.packed 128 cuts12065 = true := by
 decide +kernel
def pointBounds12065 : List (Nat × Nat × Nat) := [(1585349632,93397209906881,93397585897767),(1585399808,93397631753092,93398007744298)]
theorem point_links_checked12065 : (cuts12065.take 2).map (fun c => (1585315841-1+2*2^9*c.k,93396932752317+c.lower,93397308742992+c.upper)) = pointBounds12065 := by
 decide +kernel
def cuts12066 : List PrefixCut := [⟨3,27695682,27695703⟩,
⟨52,443123966,443124303⟩,
⟨101,863154791,863155448⟩,
⟨128,1095888106,1095888938⟩]
theorem checked12066 : checkPrefixCuts (2^48) 1585446913 9 Manual.Count131072.C012066.packed 128 cuts12066 = true := by
 decide +kernel
def pointBounds12066 : List (Nat × Nat × Nat) := [(1585449984,93398053408368,93398429399896),(1585500160,93398468836652,93398844828496),(1585550336,93398888867477,93399264859641)]
theorem point_links_checked12066 : (cuts12066.take 3).map (fun c => (1585446913-1+2*2^9*c.k,93398025712686+c.lower,93398401704193+c.upper)) = pointBounds12066 := by
 decide +kernel
def cuts12067 : List PrefixCut := [⟨22,191544813,191544959⟩,
⟨71,614921946,614922411⟩,
⟨120,1031895227,1031896013⟩,
⟨128,1099880681,1099881522⟩]
theorem checked12067 : checkPrefixCuts (2^48) 1585577985 9 Manual.Count131072.C012067.packed 128 cuts12067 = true := by
 decide +kernel
def pointBounds12067 : List (Nat × Nat × Nat) := [(1585600512,93399313145605,93399689138090),(1585650688,93399736522738,93400112515542),(1585700864,93400153496019,93400529489144)]
theorem point_links_checked12067 : (cuts12067.take 3).map (fun c => (1585577985-1+2*2^9*c.k,93399121600792+c.lower,93399497593131+c.upper)) = pointBounds12067 := by
 decide +kernel
def cuts12068 : List PrefixCut := [⟨41,348087115,348087375⟩,
⟨90,755981527,755982098⟩,
⟨128,1089316753,1089317572⟩]
theorem checked12068 : checkPrefixCuts (2^48) 1585709057 9 Manual.Count131072.C012068.packed 128 cuts12068 = true := by
 decide +kernel
def pointBounds12068 : List (Nat × Nat × Nat) := [(1585751040,93400569568588,93400945562028),(1585801216,93400977463000,93401353456751)]
theorem point_links_checked12068 : (cuts12068.take 2).map (fun c => (1585709057-1+2*2^9*c.k,93400221481473+c.lower,93400597474653+c.upper)) = pointBounds12068 := by
 decide +kernel
def cuts12069 : List PrefixCut := [⟨11,96378139,96378212⟩,
⟨60,519865703,519866102⟩,
⟨109,940855205,940855923⟩,
⟨128,1102006149,1102006986⟩]
theorem checked12069 : checkPrefixCuts (2^48) 1585840129 9 Manual.Count131072.C012069.packed 128 cuts12069 = true := by
 decide +kernel
def pointBounds12069 : List (Nat × Nat × Nat) := [(1585851392,93401407176365,93401783170437),(1585901568,93401830663929,93402206658327),(1585951744,93402251653431,93402627648148)]
theorem point_links_checked12069 : (cuts12069.take 3).map (fun c => (1585840129-1+2*2^9*c.k,93401310798226+c.lower,93401686792225+c.upper)) = pointBounds12069 := by
 decide +kernel
def cuts12070 : List PrefixCut := [⟨30,263374690,263374890⟩,
⟨79,691258944,691259472⟩,
⟨128,1104222477,1104223317⟩]
theorem checked12070 : checkPrefixCuts (2^48) 1585971201 9 Manual.Count131072.C012070.packed 128 cuts12070 = true := by
 decide +kernel
def pointBounds12070 : List (Nat × Nat × Nat) := [(1586001920,93402676179065,93403052174101),(1586052096,93403104063319,93403480058683),(1586102272,93403517026852,93403893022528)]
theorem point_links_checked12070 : (cuts12070.take 3).map (fun c => (1585971201-1+2*2^9*c.k,93402412804375+c.lower,93402788799211+c.upper)) = pointBounds12070 := by
 decide +kernel
def cuts12071 : List PrefixCut := [⟨49,422888215,422888539⟩,
⟨98,840262004,840262644⟩,
⟨128,1102533582,1102534425⟩]
theorem checked12071 : checkPrefixCuts (2^48) 1586102273 9 Manual.Count131072.C012071.packed 128 cuts12071 = true := by
 decide +kernel
def pointBounds12071 : List (Nat × Nat × Nat) := [(1586152448,93403939915067,93404315911067),(1586202624,93404357288856,93404733285172)]
theorem point_links_checked12071 : (cuts12071.take 2).map (fun c => (1586102273-1+2*2^9*c.k,93403517026852+c.lower,93403893022528+c.upper)) = pointBounds12071 := by
 decide +kernel
def cuts12072 : List PrefixCut := [⟨19,166623230,166623363⟩,
⟨68,588051892,588052341⟩,
⟨117,1004144007,1004144775⟩,
⟨128,1094458191,1094459029⟩]
theorem checked12072 : checkPrefixCuts (2^48) 1586233345 9 Manual.Count131072.C012072.packed 128 cuts12072 = true := by
 decide +kernel
def pointBounds12072 : List (Nat × Nat × Nat) := [(1586252800,93404786183664,93405162180316),(1586302976,93405207612326,93405583609294),(1586353152,93405623704441,93405999701728)]
theorem point_links_checked12072 : (cuts12072.take 3).map (fun c => (1586233345-1+2*2^9*c.k,93404619560434+c.lower,93404995556953+c.upper)) = pointBounds12072 := by
 decide +kernel
def cuts12073 : List PrefixCut := [⟨38,323812947,323813193⟩,
⟨87,745911107,745911677⟩,
⟨128,1099512353,1099513194⟩]
theorem checked12073 : checkPrefixCuts (2^48) 1586364417 9 Manual.Count131072.C012073.packed 128 cuts12073 = true := by
 decide +kernel
def pointBounds12073 : List (Nat × Nat × Nat) := [(1586403328,93406037831572,93406413829175),(1586453504,93406459929732,93406835927659)]
theorem point_links_checked12073 : (cuts12073.take 2).map (fun c => (1586364417-1+2*2^9*c.k,93405714018625+c.lower,93406090015982+c.upper)) = pointBounds12073 := by
 decide +kernel
def cuts12074 : List PrefixCut := [⟨8,68128823,68128878⟩,
⟨57,496587412,496587787⟩,
⟨106,920419672,920420372⟩,
⟨128,1104212187,1104213027⟩]
theorem checked12074 : checkPrefixCuts (2^48) 1586495489 9 Manual.Count131072.C012074.packed 128 cuts12074 = true := by
 decide +kernel
def pointBounds12074 : List (Nat × Nat × Nat) := [(1586503680,93406881659801,93407257658054),(1586553856,93407310118390,93407686116963),(1586604032,93407733950650,93408109949548)]
theorem point_links_checked12074 : (cuts12074.take 3).map (fun c => (1586495489-1+2*2^9*c.k,93406813530978+c.lower,93407189529176+c.upper)) = pointBounds12074 := by
 decide +kernel
def cuts12075 : List PrefixCut := [⟨27,232575457,232575632⟩,
⟨76,660815924,660816426⟩,
⟨125,1084785465,1084786290⟩,
⟨128,1110684425,1110685269⟩]
theorem checked12075 : checkPrefixCuts (2^48) 1586626561 9 Manual.Count131072.C012075.packed 128 cuts12075 = true := by
 decide +kernel
def pointBounds12075 : List (Nat × Nat × Nat) := [(1586654208,93408150318622,93408526317835),(1586704384,93408578559089,93408954558629),(1586754560,93409002528630,93409378528493)]
theorem point_links_checked12075 : (cuts12075.take 3).map (fun c => (1586626561-1+2*2^9*c.k,93407917743165+c.lower,93408293742203+c.upper)) = pointBounds12075 := by
 decide +kernel
def cuts12076 : List PrefixCut := [⟨46,395573863,395574170⟩,
⟨95,809583124,809583748⟩,
⟨128,1094450891,1094451730⟩]
theorem checked12076 : checkPrefixCuts (2^48) 1586757633 9 Manual.Count131072.C012076.packed 128 cuts12076 = true := by
 decide +kernel
def pointBounds12076 : List (Nat × Nat × Nat) := [(1586804736,93409424001453,93409800001642),(1586854912,93409838010714,93410214011220)]
theorem point_links_checked12076 : (cuts12076.take 2).map (fun c => (1586757633-1+2*2^9*c.k,93409028427590+c.lower,93409404427472+c.upper)) = pointBounds12076 := by
 decide +kernel
def cuts12077 : List PrefixCut := [⟨16,137287781,137287884⟩,
⟨65,554463688,554464110⟩,
⟨114,971626255,971626993⟩,
⟨128,1089394270,1089395097⟩]
theorem checked12077 : checkPrefixCuts (2^48) 1586888705 9 Manual.Count131072.C012077.packed 128 cuts12077 = true := by
 decide +kernel
def pointBounds12077 : List (Nat × Nat × Nat) := [(1586905088,93410260166262,93410636167086),(1586955264,93410677342169,93411053343312),(1587005440,93411094504736,93411470506195)]
theorem point_links_checked12077 : (cuts12077.take 3).map (fun c => (1586888705-1+2*2^9*c.k,93410122878481+c.lower,93410498879202+c.upper)) = pointBounds12077 := by
 decide +kernel
def cuts12078 : List PrefixCut := [⟨35,296898380,296898606⟩,
⟨84,707649879,707650418⟩,
⟨128,1092850882,1092851718⟩]
theorem checked12078 : checkPrefixCuts (2^48) 1587019777 9 Manual.Count131072.C012078.packed 128 cuts12078 = true := by
 decide +kernel
def pointBounds12078 : List (Nat × Nat × Nat) := [(1587055616,93411509171131,93411885172905),(1587105792,93411919922630,93412295924717)]
theorem point_links_checked12078 : (cuts12078.take 2).map (fun c => (1587019777-1+2*2^9*c.k,93411212272751+c.lower,93411588274299+c.upper)) = pointBounds12078 := by
 decide +kernel
def cuts12079 : List PrefixCut := [⟨5,42030936,42030968⟩,
⟨54,462155599,462155953⟩,
⟨103,879252312,879252984⟩,
⟨128,1084958379,1084959207⟩]
theorem checked12079 : checkPrefixCuts (2^48) 1587150849 9 Manual.Count131072.C012079.packed 128 cuts12079 = true := by
 decide +kernel
def pointBounds12079 : List (Nat × Nat × Nat) := [(1587155968,93412347154569,93412723156985),(1587206144,93412767279232,93413143281970),(1587256320,93413184375945,93413560379001)]
theorem point_links_checked12079 : (cuts12079.take 3).map (fun c => (1587150849-1+2*2^9*c.k,93412305123633+c.lower,93412681126017+c.upper)) = pointBounds12079 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000064
