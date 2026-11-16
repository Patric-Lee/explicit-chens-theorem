import PlattAssemblyKernel
import PlattCertificates.Count131072.C023072
import PlattCertificates.Count131072.C023073
import PlattCertificates.Count131072.C023074
import PlattCertificates.Count131072.C023075
import PlattCertificates.Count131072.C023076
import PlattCertificates.Count131072.C023077
import PlattCertificates.Count131072.C023078
import PlattCertificates.Count131072.C023079
import PlattCertificates.Count131072.C023080
import PlattCertificates.Count131072.C023081
import PlattCertificates.Count131072.C023082
import PlattCertificates.Count131072.C023083
import PlattCertificates.Count131072.C023084
import PlattCertificates.Count131072.C023085
import PlattCertificates.Count131072.C023086
import PlattCertificates.Count131072.C023087
import PlattCertificates.Count131072.C023088
import PlattCertificates.Count131072.C023089
import PlattCertificates.Count131072.C023090
import PlattCertificates.Count131072.C023091
import PlattCertificates.Count131072.C023092
import PlattCertificates.Count131072.C023093
import PlattCertificates.Count131072.C023094
import PlattCertificates.Count131072.C023095
import PlattCertificates.Count131072.C023096
import PlattCertificates.Count131072.C023097
import PlattCertificates.Count131072.C023098
import PlattCertificates.Count131072.C023099
import PlattCertificates.Count131072.C023100
import PlattCertificates.Count131072.C023101
import PlattCertificates.Count131072.C023102
import PlattCertificates.Count131072.C023103
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000096
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23072 : List PrefixCut := [⟨60,266131975,266132123⟩,
⟨128,563304711,563305026⟩]
theorem checked23072 : checkPrefixCuts (2^48) 3028025345 9 Manual.Count131072.C023072.packed 128 cuts23072 = true := by
 decide +kernel
def pointBounds23072 : List (Nat × Nat × Nat) := [(3028086784,101866695303777,101867076738135)]
theorem point_links_checked23072 : (cuts23072.take 1).map (fun c => (3028025345-1+2*2^9*c.k,101866429171802+c.lower,101866810606012+c.upper)) = pointBounds23072 := by
 decide +kernel
def cuts23073 : List PrefixCut := [⟨25,107731560,107731620⟩,
⟨118,516619960,516620254⟩,
⟨128,561142382,561142700⟩]
theorem checked23073 : checkPrefixCuts (2^48) 3028156417 9 Manual.Count131072.C023073.packed 128 cuts23073 = true := by
 decide +kernel
def pointBounds23073 : List (Nat × Nat × Nat) := [(3028182016,101867100208073,101867481642658),(3028277248,101867509096473,101867890531292)]
theorem point_links_checked23073 : (cuts23073.take 2).map (fun c => (3028156417-1+2*2^9*c.k,101866992476513+c.lower,101867373911038+c.upper)) = pointBounds23073 := by
 decide +kernel
def cuts23074 : List PrefixCut := [⟨83,361564767,361564975⟩,
⟨128,560095790,560096108⟩]
theorem checked23074 : checkPrefixCuts (2^48) 3028287489 9 Manual.Count131072.C023074.packed 128 cuts23074 = true := by
 decide +kernel
def pointBounds23074 : List (Nat × Nat × Nat) := [(3028372480,101867915183662,101868296618713)]
theorem point_links_checked23074 : (cuts23074.take 1).map (fun c => (3028287489-1+2*2^9*c.k,101867553618895+c.lower,101867935053738+c.upper)) = pointBounds23074 := by
 decide +kernel
def cuts23075 : List PrefixCut := [⟨48,211354138,211354255⟩,
⟨128,557004525,557004836⟩]
theorem checked23075 : checkPrefixCuts (2^48) 3028418561 9 Manual.Count131072.C023075.packed 128 cuts23075 = true := by
 decide +kernel
def pointBounds23075 : List (Nat × Nat × Nat) := [(3028467712,101868325068823,101868706504101)]
theorem point_links_checked23075 : (cuts23075.take 1).map (fun c => (3028418561-1+2*2^9*c.k,101868113714685+c.lower,101868495149846+c.upper)) = pointBounds23075 := by
 decide +kernel
def cuts23076 : List PrefixCut := [⟨13,55020651,55020682⟩,
⟨106,463764662,463764931⟩,
⟨128,555400368,555400689⟩]
theorem checked23076 : checkPrefixCuts (2^48) 3028549633 9 Manual.Count131072.C023076.packed 128 cuts23076 = true := by
 decide +kernel
def pointBounds23076 : List (Nat × Nat × Nat) := [(3028562944,101868725739861,101869107175364),(3028658176,101869134483872,101869515919613)]
theorem point_links_checked23076 : (cuts23076.take 2).map (fun c => (3028549633-1+2*2^9*c.k,101868670719210+c.lower,101869052154682+c.upper)) = pointBounds23076 := by
 decide +kernel
def cuts23077 : List PrefixCut := [⟨71,310868734,310868910⟩,
⟨128,560115980,560116300⟩]
theorem checked23077 : checkPrefixCuts (2^48) 3028680705 9 Manual.Count131072.C023077.packed 128 cuts23077 = true := by
 decide +kernel
def pointBounds23077 : List (Nat × Nat × Nat) := [(3028753408,101869536988312,101869918424281)]
theorem point_links_checked23077 : (cuts23077.take 1).map (fun c => (3028680705-1+2*2^9*c.k,101869226119578+c.lower,101869607555371+c.upper)) = pointBounds23077 := by
 decide +kernel
def cuts23078 : List PrefixCut := [⟨36,159006459,159006553⟩,
⟨128,561299903,561300232⟩]
theorem checked23078 : checkPrefixCuts (2^48) 3028811777 9 Manual.Count131072.C023078.packed 128 cuts23078 = true := by
 decide +kernel
def pointBounds23078 : List (Nat × Nat × Nat) := [(3028848640,101869945242017,101870326678224)]
theorem point_links_checked23078 : (cuts23078.take 1).map (fun c => (3028811777-1+2*2^9*c.k,101869786235558+c.lower,101870167671671+c.upper)) = pointBounds23078 := by
 decide +kernel
def cuts23079 : List PrefixCut := [⟨1,4088850,4088852⟩,
⟨94,416126875,416127112⟩,
⟨128,560160536,560160854⟩]
theorem checked23079 : checkPrefixCuts (2^48) 3028942849 9 Manual.Count131072.C023079.packed 128 cuts23079 = true := by
 decide +kernel
def pointBounds23079 : List (Nat × Nat × Nat) := [(3028943872,101870351624311,101870733060755),(3029039104,101870763662336,101871145099015)]
theorem point_links_checked23079 : (cuts23079.take 2).map (fun c => (3028942849-1+2*2^9*c.k,101870347535461+c.lower,101870728971903+c.upper)) = pointBounds23079 := by
 decide +kernel
def cuts23080 : List PrefixCut := [⟨59,259628181,259628325⟩,
⟨128,565339825,565340144⟩]
theorem checked23080 : checkPrefixCuts (2^48) 3029073921 9 Manual.Count131072.C023080.packed 128 cuts23080 = true := by
 decide +kernel
def pointBounds23080 : List (Nat × Nat × Nat) := [(3029134336,101871167324178,101871548761082)]
theorem point_links_checked23080 : (cuts23080.take 1).map (fun c => (3029073921-1+2*2^9*c.k,101870907695997+c.lower,101871289132757+c.upper)) = pointBounds23080 := by
 decide +kernel
def cuts23081 : List PrefixCut := [⟨24,103327044,103327101⟩,
⟨117,509472419,509472703⟩,
⟨128,556209437,556209748⟩]
theorem checked23081 : checkPrefixCuts (2^48) 3029204993 9 Manual.Count131072.C023081.packed 128 cuts23081 = true := by
 decide +kernel
def pointBounds23081 : List (Nat × Nat × Nat) := [(3029229568,101871576362866,101871957800002),(3029324800,101871982508241,101872363945604)]
theorem point_links_checked23081 : (cuts23081.take 2).map (fun c => (3029204993-1+2*2^9*c.k,101871473035822+c.lower,101871854472901+c.upper)) = pointBounds23081 := by
 decide +kernel
def cuts23082 : List PrefixCut := [⟨82,352333905,352334108⟩,
⟨128,552468631,552468953⟩]
theorem checked23082 : checkPrefixCuts (2^48) 3029336065 9 Manual.Count131072.C023082.packed 128 cuts23082 = true := by
 decide +kernel
def pointBounds23082 : List (Nat × Nat × Nat) := [(3029420032,101872381579164,101872763016757)]
theorem point_links_checked23082 : (cuts23082.take 1).map (fun c => (3029336065-1+2*2^9*c.k,101872029245259+c.lower,101872410682649+c.upper)) = pointBounds23082 := by
 decide +kernel
def cuts23083 : List PrefixCut := [⟨47,202918943,202919062⟩,
⟨128,551701579,551701900⟩]
theorem checked23083 : checkPrefixCuts (2^48) 3029467137 9 Manual.Count131072.C023083.packed 128 cuts23083 = true := by
 decide +kernel
def pointBounds23083 : List (Nat × Nat × Nat) := [(3029515264,101872784632833,101873166070664)]
theorem point_links_checked23083 : (cuts23083.take 1).map (fun c => (3029467137-1+2*2^9*c.k,101872581713890+c.lower,101872963151602+c.upper)) = pointBounds23083 := by
 decide +kernel
def cuts23084 : List PrefixCut := [⟨12,53236362,53236391⟩,
⟨105,452083964,452084217⟩,
⟨128,550562908,550563215⟩]
theorem checked23084 : checkPrefixCuts (2^48) 3029598209 9 Manual.Count131072.C023084.packed 128 cuts23084 = true := by
 decide +kernel
def pointBounds23084 : List (Nat × Nat × Nat) := [(3029610496,101873186651831,101873568089893),(3029705728,101873585499433,101873966937719)]
theorem point_links_checked23084 : (cuts23084.take 2).map (fun c => (3029598209-1+2*2^9*c.k,101873133415469+c.lower,101873514853502+c.upper)) = pointBounds23084 := by
 decide +kernel
def cuts23085 : List PrefixCut := [⟨70,302307029,302307202⟩,
⟨128,556020166,556020482⟩]
theorem checked23085 : checkPrefixCuts (2^48) 3029729281 9 Manual.Count131072.C023085.packed 128 cuts23085 = true := by
 decide +kernel
def pointBounds23085 : List (Nat × Nat × Nat) := [(3029800960,101873986285406,101874367723919)]
theorem point_links_checked23085 : (cuts23085.take 1).map (fun c => (3029729281-1+2*2^9*c.k,101873683978377+c.lower,101874065416717+c.upper)) = pointBounds23085 := by
 decide +kernel
def cuts23086 : List PrefixCut := [⟨35,151612386,151612471⟩,
⟨128,557389720,557390034⟩]
theorem checked23086 : checkPrefixCuts (2^48) 3029860353 9 Manual.Count131072.C023086.packed 128 cuts23086 = true := by
 decide +kernel
def pointBounds23086 : List (Nat × Nat × Nat) := [(3029896192,101874391610929,101874773049670),(3029991424,101874797388263,101875178827233)]
theorem point_links_checked23086 : (cuts23086.take 2).map (fun c => (3029860353-1+2*2^9*c.k,101874239998543+c.lower,101874621437199+c.upper)) = pointBounds23086 := by
 decide +kernel
def cuts23087 : List PrefixCut := [⟨93,404649797,404650037⟩,
⟨128,560988393,560988721⟩]
theorem checked23087 : checkPrefixCuts (2^48) 3029991425 9 Manual.Count131072.C023087.packed 128 cuts23087 = true := by
 decide +kernel
def pointBounds23087 : List (Nat × Nat × Nat) := [(3030086656,101875202038060,101875583477270)]
theorem point_links_checked23087 : (cuts23087.take 1).map (fun c => (3029991425-1+2*2^9*c.k,101874797388263+c.lower,101875178827233+c.upper)) = pointBounds23087 := by
 decide +kernel
def cuts23088 : List PrefixCut := [⟨58,245140237,245140385⟩,
⟨128,551117675,551117997⟩]
theorem checked23088 : checkPrefixCuts (2^48) 3030122497 9 Manual.Count131072.C023088.packed 128 cuts23088 = true := by
 decide +kernel
def pointBounds23088 : List (Nat × Nat × Nat) := [(3030181888,101875603516893,101875984956339)]
theorem point_links_checked23088 : (cuts23088.take 1).map (fun c => (3030122497-1+2*2^9*c.k,101875358376656+c.lower,101875739815954+c.upper)) = pointBounds23088 := by
 decide +kernel
def cuts23089 : List PrefixCut := [⟨23,96974941,96974998⟩,
⟨116,502050987,502051277⟩,
⟨128,553880481,553880801⟩]
theorem checked23089 : checkPrefixCuts (2^48) 3030253569 9 Manual.Count131072.C023089.packed 128 cuts23089 = true := by
 decide +kernel
def pointBounds23089 : List (Nat × Nat × Nat) := [(3030277120,101876006469272,101876387908949),(3030372352,101876411545318,101876792985228)]
theorem point_links_checked23089 : (cuts23089.take 2).map (fun c => (3030253569-1+2*2^9*c.k,101875909494331+c.lower,101876290933951+c.upper)) = pointBounds23089 := by
 decide +kernel
def cuts23090 : List PrefixCut := [⟨81,356484705,356484901⟩,
⟨128,555528586,555528891⟩]
theorem checked23090 : checkPrefixCuts (2^48) 3030384641 9 Manual.Count131072.C023090.packed 128 cuts23090 = true := by
 decide +kernel
def pointBounds23090 : List (Nat × Nat × Nat) := [(3030467584,101876819859517,101877201299653)]
theorem point_links_checked23090 : (cuts23090.take 1).map (fun c => (3030384641-1+2*2^9*c.k,101876463374812+c.lower,101876844814752+c.upper)) = pointBounds23090 := by
 decide +kernel
def cuts23091 : List PrefixCut := [⟨46,200062389,200062504⟩,
⟨128,559126644,559126968⟩]
theorem checked23091 : checkPrefixCuts (2^48) 3030515713 9 Manual.Count131072.C023091.packed 128 cuts23091 = true := by
 decide +kernel
def pointBounds23091 : List (Nat × Nat × Nat) := [(3030562816,101877218965787,101877600406147)]
theorem point_links_checked23091 : (cuts23091.take 1).map (fun c => (3030515713-1+2*2^9*c.k,101877018903398+c.lower,101877400343643+c.upper)) = pointBounds23091 := by
 decide +kernel
def cuts23092 : List PrefixCut := [⟨11,49317158,49317184⟩,
⟨104,452299044,452299294⟩,
⟨128,555201824,555202130⟩]
theorem checked23092 : checkPrefixCuts (2^48) 3030646785 9 Manual.Count131072.C023092.packed 128 cuts23092 = true := by
 decide +kernel
def pointBounds23092 : List (Nat × Nat × Nat) := [(3030658048,101877627347200,101878008787795),(3030753280,101878030329086,101878411769905)]
theorem point_links_checked23092 : (cuts23092.take 2).map (fun c => (3030646785-1+2*2^9*c.k,101877578030042+c.lower,101877959470611+c.upper)) = pointBounds23092 := by
 decide +kernel
def cuts23093 : List PrefixCut := [⟨69,303502682,303502859⟩,
⟨128,561678746,561679062⟩]
theorem checked23093 : checkPrefixCuts (2^48) 3030777857 9 Manual.Count131072.C023093.packed 128 cuts23093 = true := by
 decide +kernel
def pointBounds23093 : List (Nat × Nat × Nat) := [(3030848512,101878436734548,101878818175600)]
theorem point_links_checked23093 : (cuts23093.take 1).map (fun c => (3030777857-1+2*2^9*c.k,101878133231866+c.lower,101878514672741+c.upper)) = pointBounds23093 := by
 decide +kernel
def cuts23094 : List PrefixCut := [⟨34,153324442,153324533⟩,
⟨127,554039564,554039885⟩,
⟨128,558311315,558311638⟩]
theorem checked23094 : checkPrefixCuts (2^48) 3030908929 9 Manual.Count131072.C023094.packed 128 cuts23094 = true := by
 decide +kernel
def pointBounds23094 : List (Nat × Nat × Nat) := [(3030943744,101878848235054,101879229676336),(3031038976,101879248950176,101879630391688)]
theorem point_links_checked23094 : (cuts23094.take 2).map (fun c => (3030908929-1+2*2^9*c.k,101878694910612+c.lower,101879076351803+c.upper)) = pointBounds23094 := by
 decide +kernel
def cuts23095 : List PrefixCut := [⟨92,406831392,406831625⟩,
⟨128,563858801,563859123⟩]
theorem checked23095 : checkPrefixCuts (2^48) 3031040001 9 Manual.Count131072.C023095.packed 128 cuts23095 = true := by
 decide +kernel
def pointBounds23095 : List (Nat × Nat × Nat) := [(3031134208,101879660053319,101880041495066)]
theorem point_links_checked23095 : (cuts23095.take 1).map (fun c => (3031040001-1+2*2^9*c.k,101879253221927+c.lower,101879634663441+c.upper)) = pointBounds23095 := by
 decide +kernel
def cuts23096 : List PrefixCut := [⟨57,250719892,250720035⟩,
⟨128,559377271,559377587⟩]
theorem checked23096 : checkPrefixCuts (2^48) 3031171073 9 Manual.Count131072.C023096.packed 128 cuts23096 = true := by
 decide +kernel
def pointBounds23096 : List (Nat × Nat × Nat) := [(3031229440,101880067800620,101880449242599)]
theorem point_links_checked23096 : (cuts23096.take 1).map (fun c => (3031171073-1+2*2^9*c.k,101879817080728+c.lower,101880198522564+c.upper)) = pointBounds23096 := by
 decide +kernel
def cuts23097 : List PrefixCut := [⟨22,97034260,97034314⟩,
⟨115,501320430,501320721⟩,
⟨128,556567545,556567866⟩]
theorem checked23097 : checkPrefixCuts (2^48) 3031302145 9 Manual.Count131072.C023097.packed 128 cuts23097 = true := by
 decide +kernel
def pointBounds23097 : List (Nat × Nat × Nat) := [(3031324672,101880473492259,101880854934465),(3031419904,101880877778429,101881259220872)]
theorem point_links_checked23097 : (cuts23097.take 2).map (fun c => (3031302145-1+2*2^9*c.k,101880376457999+c.lower,101880757900151+c.upper)) = pointBounds23097 := by
 decide +kernel
def cuts23098 : List PrefixCut := [⟨80,352740331,352740532⟩,
⟨128,560721686,560722010⟩]
theorem checked23098 : checkPrefixCuts (2^48) 3031433217 9 Manual.Count131072.C023098.packed 128 cuts23098 = true := by
 decide +kernel
def pointBounds23098 : List (Nat × Nat × Nat) := [(3031515136,101881285765875,101881667208549)]
theorem point_links_checked23098 : (cuts23098.take 1).map (fun c => (3031433217-1+2*2^9*c.k,101880933025544+c.lower,101881314468017+c.upper)) = pointBounds23098 := by
 decide +kernel
def cuts23099 : List PrefixCut := [⟨45,194050991,194051101⟩,
⟨128,563018474,563018795⟩]
theorem checked23099 : checkPrefixCuts (2^48) 3031564289 9 Manual.Count131072.C023099.packed 128 cuts23099 = true := by
 decide +kernel
def pointBounds23099 : List (Nat × Nat × Nat) := [(3031610368,101881687798221,101882069241128)]
theorem point_links_checked23099 : (cuts23099.take 1).map (fun c => (3031564289-1+2*2^9*c.k,101881493747230+c.lower,101881875190027+c.upper)) = pointBounds23099 := by
 decide +kernel
def cuts23100 : List PrefixCut := [⟨10,44286540,44286566⟩,
⟨103,452142692,452142950⟩,
⟨128,560116122,560116436⟩]
theorem checked23100 : checkPrefixCuts (2^48) 3031695361 9 Manual.Count131072.C023100.packed 128 cuts23100 = true := by
 decide +kernel
def pointBounds23100 : List (Nat × Nat × Nat) := [(3031705600,101882101052244,101882482495388),(3031800832,101882508908396,101882890351772)]
theorem point_links_checked23100 : (cuts23100.take 2).map (fun c => (3031695361-1+2*2^9*c.k,101882056765704+c.lower,101882438208822+c.upper)) = pointBounds23100 := by
 decide +kernel
def cuts23101 : List PrefixCut := [⟨68,294856579,294856739⟩,
⟨128,560091809,560092116⟩]
theorem checked23101 : checkPrefixCuts (2^48) 3031826433 9 Manual.Count131072.C023101.packed 128 cuts23101 = true := by
 decide +kernel
def pointBounds23101 : List (Nat × Nat × Nat) := [(3031896064,101882911738405,101883293181997)]
theorem point_links_checked23101 : (cuts23101.take 1).map (fun c => (3031826433-1+2*2^9*c.k,101882616881826+c.lower,101882998325258+c.upper)) = pointBounds23101 := by
 decide +kernel
def cuts23102 : List PrefixCut := [⟨33,145009075,145009159⟩,
⟨126,551527146,551527459⟩,
⟨128,560067694,560068013⟩]
theorem checked23102 : checkPrefixCuts (2^48) 3031957505 9 Manual.Count131072.C023102.packed 128 cuts23102 = true := by
 decide +kernel
def pointBounds23102 : List (Nat × Nat × Nat) := [(3031991296,101883321982710,101883703426533),(3032086528,101883728500781,101884109944833)]
theorem point_links_checked23102 : (cuts23102.take 2).map (fun c => (3031957505-1+2*2^9*c.k,101883176973635+c.lower,101883558417374+c.upper)) = pointBounds23102 := by
 decide +kernel
def cuts23103 : List PrefixCut := [⟨91,400656790,400657017⟩,
⟨128,561807227,561807543⟩]
theorem checked23103 : checkPrefixCuts (2^48) 3032088577 9 Manual.Count131072.C023103.packed 128 cuts23103 = true := by
 decide +kernel
def pointBounds23103 : List (Nat × Nat × Nat) := [(3032181760,101884137698119,101884519142404)]
theorem point_links_checked23103 : (cuts23103.take 1).map (fun c => (3032088577-1+2*2^9*c.k,101883737041329+c.lower,101884118485387+c.upper)) = pointBounds23103 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000096
