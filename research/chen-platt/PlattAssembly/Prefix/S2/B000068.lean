import PlattAssemblyKernel
import PlattCertificates.Count131072.C012176
import PlattCertificates.Count131072.C012177
import PlattCertificates.Count131072.C012178
import PlattCertificates.Count131072.C012179
import PlattCertificates.Count131072.C012180
import PlattCertificates.Count131072.C012181
import PlattCertificates.Count131072.C012182
import PlattCertificates.Count131072.C012183
import PlattCertificates.Count131072.C012184
import PlattCertificates.Count131072.C012185
import PlattCertificates.Count131072.C012186
import PlattCertificates.Count131072.C012187
import PlattCertificates.Count131072.C012188
import PlattCertificates.Count131072.C012189
import PlattCertificates.Count131072.C012190
import PlattCertificates.Count131072.C012191
import PlattCertificates.Count131072.C012192
import PlattCertificates.Count131072.C012193
import PlattCertificates.Count131072.C012194
import PlattCertificates.Count131072.C012195
import PlattCertificates.Count131072.C012196
import PlattCertificates.Count131072.C012197
import PlattCertificates.Count131072.C012198
import PlattCertificates.Count131072.C012199
import PlattCertificates.Count131072.C012200
import PlattCertificates.Count131072.C012201
import PlattCertificates.Count131072.C012202
import PlattCertificates.Count131072.C012203
import PlattCertificates.Count131072.C012204
import PlattCertificates.Count131072.C012205
import PlattCertificates.Count131072.C012206
import PlattCertificates.Count131072.C012207
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000068
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12176 : List PrefixCut := [⟨35,293459030,293459256⟩,
⟨84,719033650,719034196⟩,
⟨128,1100086612,1100087447⟩]
theorem checked12176 : checkPrefixCuts (2^48) 1599864833 9 Manual.Count131072.C012176.packed 128 cuts12176 = true := by
 decide +kernel
def pointBounds12176 : List (Nat × Nat × Nat) := [(1599900672,93518562729923,93518938813004),(1599950848,93518988304543,93519364387944)]
theorem point_links_checked12176 : (cuts12176.take 2).map (fun c => (1599864833-1+2*2^9*c.k,93518269270893+c.lower,93518645353748+c.upper)) = pointBounds12176 := by
 decide +kernel
def cuts12177 : List PrefixCut := [⟨5,40813898,40813929⟩,
⟨54,458269546,458269901⟩,
⟨103,872369633,872370301⟩,
⟨128,1082405265,1082406094⟩]
theorem checked12177 : checkPrefixCuts (2^48) 1599995905 9 Manual.Count131072.C012177.packed 128 cuts12177 = true := by
 decide +kernel
def pointBounds12177 : List (Nat × Nat × Nat) := [(1600001024,93519410171403,93519786255124),(1600051200,93519827627051,93520203711096),(1600101376,93520241727138,93520617811496)]
theorem point_links_checked12177 : (cuts12177.take 3).map (fun c => (1599995905-1+2*2^9*c.k,93519369357505+c.lower,93519745441195+c.upper)) = pointBounds12177 := by
 decide +kernel
def cuts12178 : List PrefixCut := [⟨24,214781819,214781984⟩,
⟨73,628504223,628504705⟩,
⟨122,1053646928,1053647725⟩,
⟨128,1104480225,1104481061⟩]
theorem checked12178 : checkPrefixCuts (2^48) 1600126977 9 Manual.Count131072.C012178.packed 128 cuts12178 = true := by
 decide +kernel
def pointBounds12178 : List (Nat × Nat × Nat) := [(1600151552,93520666544589,93521042629273),(1600201728,93521080266993,93521456351994),(1600251904,93521505409698,93521881495014)]
theorem point_links_checked12178 : (cuts12178.take 3).map (fun c => (1600126977-1+2*2^9*c.k,93520451762770+c.lower,93520827847289+c.upper)) = pointBounds12178 := by
 decide +kernel
def cuts12179 : List PrefixCut := [⟨43,366556879,366557162⟩,
⟨92,781295646,781296245⟩,
⟨128,1075368776,1075369595⟩]
theorem checked12179 : checkPrefixCuts (2^48) 1600258049 9 Manual.Count131072.C012179.packed 128 cuts12179 = true := by
 decide +kernel
def pointBounds12179 : List (Nat × Nat × Nat) := [(1600302080,93521922799874,93522298885512),(1600352256,93522337538641,93522713624595)]
theorem point_links_checked12179 : (cuts12179.take 2).map (fun c => (1600258049-1+2*2^9*c.k,93521556242995+c.lower,93521932328350+c.upper)) = pointBounds12179 := by
 decide +kernel
def cuts12180 : List PrefixCut := [⟨13,109572187,109572267⟩,
⟨62,530088774,530089167⟩,
⟨111,952878463,952879175⟩,
⟨128,1094977862,1094978682⟩]
theorem checked12180 : checkPrefixCuts (2^48) 1600389121 9 Manual.Count131072.C012180.packed 128 cuts12180 = true := by
 decide +kernel
def pointBounds12180 : List (Nat × Nat × Nat) := [(1600402432,93522741183958,93523117270212),(1600452608,93523161700545,93523537787112),(1600502784,93523584490234,93523960577120)]
theorem point_links_checked12180 : (cuts12180.take 3).map (fun c => (1600389121-1+2*2^9*c.k,93522631611771+c.lower,93523007697945+c.upper)) = pointBounds12180 := by
 decide +kernel
def cuts12181 : List PrefixCut := [⟨32,270476965,270477171⟩,
⟨81,689898963,689899488⟩,
⟨128,1078006221,1078007042⟩]
theorem checked12181 : checkPrefixCuts (2^48) 1600520193 9 Manual.Count131072.C012181.packed 128 cuts12181 = true := by
 decide +kernel
def pointBounds12181 : List (Nat × Nat × Nat) := [(1600552960,93523997066598,93524373153798),(1600603136,93524416488596,93524792576115)]
theorem point_links_checked12181 : (cuts12181.take 2).map (fun c => (1600520193-1+2*2^9*c.k,93523726589633+c.lower,93524102676627+c.upper)) = pointBounds12181 := by
 decide +kernel
def cuts12182 : List PrefixCut := [⟨2,17409160,17409174⟩,
⟨51,431529408,431529734⟩,
⟨100,854780399,854781045⟩,
⟨128,1092864174,1092865000⟩]
theorem checked12182 : checkPrefixCuts (2^48) 1600651265 9 Manual.Count131072.C012182.packed 128 cuts12182 = true := by
 decide +kernel
def pointBounds12182 : List (Nat × Nat × Nat) := [(1600653312,93524822005014,93525198092843),(1600703488,93525236125262,93525612213403),(1600753664,93525659376253,93526035464714)]
theorem point_links_checked12182 : (cuts12182.take 3).map (fun c => (1600651265-1+2*2^9*c.k,93524804595854+c.lower,93525180683669+c.upper)) = pointBounds12182 := by
 decide +kernel
def cuts12183 : List PrefixCut := [⟨21,172493785,172493918⟩,
⟨70,589915918,589916363⟩,
⟨119,1007500725,1007501484⟩,
⟨128,1083983268,1083984085⟩]
theorem checked12183 : checkPrefixCuts (2^48) 1600782337 9 Manual.Count131072.C012183.packed 128 cuts12183 = true := by
 decide +kernel
def pointBounds12183 : List (Nat × Nat × Nat) := [(1600803840,93526069953813,93526446042587),(1600854016,93526487375946,93526863465032),(1600904192,93526904960753,93527281050153)]
theorem point_links_checked12183 : (cuts12183.take 3).map (fun c => (1600782337-1+2*2^9*c.k,93525897460028+c.lower,93526273548669+c.upper)) = pointBounds12183 := by
 decide +kernel
def cuts12184 : List PrefixCut := [⟨40,342671552,342671813⟩,
⟨89,761812519,761813096⟩,
⟨128,1094619356,1094620182⟩]
theorem checked12184 : checkPrefixCuts (2^48) 1600913409 9 Manual.Count131072.C012184.packed 128 cuts12184 = true := by
 decide +kernel
def pointBounds12184 : List (Nat × Nat × Nat) := [(1600954368,93527324114848,93527700204567),(1601004544,93527743255815,93528119345850)]
theorem point_links_checked12184 : (cuts12184.take 2).map (fun c => (1600913409-1+2*2^9*c.k,93526981443296+c.lower,93527357532754+c.upper)) = pointBounds12184 := by
 decide +kernel
def cuts12185 : List PrefixCut := [⟨10,86145176,86145243⟩,
⟨59,503501906,503502285⟩,
⟨108,913110415,913111104⟩,
⟨128,1081872422,1081873239⟩]
theorem checked12185 : checkPrefixCuts (2^48) 1601044481 9 Manual.Count131072.C012185.packed 128 cuts12185 = true := by
 decide +kernel
def pointBounds12185 : List (Nat × Nat × Nat) := [(1601054720,93528162207828,93528538298179),(1601104896,93528579564558,93528955655221),(1601155072,93528989173067,93529365264040)]
theorem point_links_checked12185 : (cuts12185.take 3).map (fun c => (1601044481-1+2*2^9*c.k,93528076062652+c.lower,93528452152936+c.upper)) = pointBounds12185 := by
 decide +kernel
def cuts12186 : List PrefixCut := [⟨29,242064218,242064401⟩,
⟨78,658151201,658151699⟩,
⟨127,1085650865,1085651689⟩,
⟨128,1093209332,1093210162⟩]
theorem checked12186 : checkPrefixCuts (2^48) 1601175553 9 Manual.Count131072.C012186.packed 128 cuts12186 = true := by
 decide +kernel
def pointBounds12186 : List (Nat × Nat × Nat) := [(1601205248,93529399999292,93529776090576),(1601255424,93529816086275,93530192177874),(1601305600,93530243585939,93530619677864)]
theorem point_links_checked12186 : (cuts12186.take 3).map (fun c => (1601175553-1+2*2^9*c.k,93529157935074+c.lower,93529534026175+c.upper)) = pointBounds12186 := by
 decide +kernel
def cuts12187 : List PrefixCut := [⟨48,406041536,406041844⟩,
⟨97,818046551,818047171⟩,
⟨128,1065700277,1065701088⟩]
theorem checked12187 : checkPrefixCuts (2^48) 1601306625 9 Manual.Count131072.C012187.packed 128 cuts12187 = true := by
 decide +kernel
def pointBounds12187 : List (Nat × Nat × Nat) := [(1601355776,93530657185942,93531033278181),(1601405952,93531069190957,93531445283508)]
theorem point_links_checked12187 : (cuts12187.take 2).map (fun c => (1601306625-1+2*2^9*c.k,93530251144406+c.lower,93530627236337+c.upper)) = pointBounds12187 := by
 decide +kernel
def cuts12188 : List PrefixCut := [⟨18,152737930,152738046⟩,
⟨67,560147442,560147868⟩,
⟨116,983361990,983362734⟩,
⟨128,1085297063,1085297883⟩]
theorem checked12188 : checkPrefixCuts (2^48) 1601437697 9 Manual.Count131072.C012188.packed 128 cuts12188 = true := by
 decide +kernel
def pointBounds12188 : List (Nat × Nat × Nat) := [(1601456128,93531469582613,93531845675471),(1601506304,93531876992125,93532253085293),(1601556480,93532300206673,93532676300159)]
theorem point_links_checked12188 : (cuts12188.take 3).map (fun c => (1601437697-1+2*2^9*c.k,93531316844683+c.lower,93531692937425+c.upper)) = pointBounds12188 := by
 decide +kernel
def cuts12189 : List PrefixCut := [⟨37,315115071,315115307⟩,
⟨86,734261051,734261602⟩,
⟨128,1098916286,1098917112⟩]
theorem checked12189 : checkPrefixCuts (2^48) 1601568769 9 Manual.Count131072.C012189.packed 128 cuts12189 = true := by
 decide +kernel
def pointBounds12189 : List (Nat × Nat × Nat) := [(1601606656,93532717256817,93533093350615),(1601656832,93533136402797,93533512496910)]
theorem point_links_checked12189 : (cuts12189.take 2).map (fun c => (1601568769-1+2*2^9*c.k,93532402141746+c.lower,93532778235308+c.upper)) = pointBounds12189 := by
 decide +kernel
def cuts12190 : List PrefixCut := [⟨7,57992455,57992498⟩,
⟨56,469907295,469907648⟩,
⟨105,891649927,891650599⟩,
⟨128,1086525621,1086526442⟩]
theorem checked12190 : checkPrefixCuts (2^48) 1601699841 9 Manual.Count131072.C012190.packed 128 cuts12190 = true := by
 decide +kernel
def pointBounds12190 : List (Nat × Nat × Nat) := [(1601707008,93533559050487,93533935144918),(1601757184,93533970965327,93534347060068),(1601807360,93534392707959,93534768803019)]
theorem point_links_checked12190 : (cuts12190.take 3).map (fun c => (1601699841-1+2*2^9*c.k,93533501058032+c.lower,93533877152420+c.upper)) = pointBounds12190 := by
 decide +kernel
def cuts12191 : List PrefixCut := [⟨26,219473354,219473520⟩,
⟨75,628362217,628362697⟩,
⟨124,1052524999,1052525801⟩,
⟨128,1090653323,1090654152⟩]
theorem checked12191 : checkPrefixCuts (2^48) 1601830913 9 Manual.Count131072.C012191.packed 128 cuts12191 = true := by
 decide +kernel
def pointBounds12191 : List (Nat × Nat × Nat) := [(1601857536,93534807057007,93535183152382),(1601907712,93535215945870,93535592041559),(1601957888,93535640108652,93536016204663)]
theorem point_links_checked12191 : (cuts12191.take 3).map (fun c => (1601830913-1+2*2^9*c.k,93534587583653+c.lower,93534963678862+c.upper)) = pointBounds12191 := by
 decide +kernel
def cuts12192 : List PrefixCut := [⟨45,377060273,377060561⟩,
⟨94,791708765,791709367⟩,
⟨128,1075454374,1075455190⟩]
theorem checked12192 : checkPrefixCuts (2^48) 1601961985 9 Manual.Count131072.C012192.packed 128 cuts12192 = true := by
 decide +kernel
def pointBounds12192 : List (Nat × Nat × Nat) := [(1602008064,93536055297249,93536431393575),(1602058240,93536469945741,93536846042381)]
theorem point_links_checked12192 : (cuts12192.take 2).map (fun c => (1601961985-1+2*2^9*c.k,93535678236976+c.lower,93536054333014+c.upper)) = pointBounds12192 := by
 decide +kernel
def cuts12193 : List PrefixCut := [⟨15,123159472,123159564⟩,
⟨64,535146761,535147169⟩,
⟨113,949931948,949932668⟩,
⟨128,1077123138,1077123954⟩]
theorem checked12193 : checkPrefixCuts (2^48) 1602093057 9 Manual.Count131072.C012193.packed 128 cuts12193 = true := by
 decide +kernel
def pointBounds12193 : List (Nat × Nat × Nat) := [(1602108416,93536876850822,93537252947768),(1602158592,93537288838111,93537664935373),(1602208768,93537703623298,93538079720872)]
theorem point_links_checked12193 : (cuts12193.take 3).map (fun c => (1602093057-1+2*2^9*c.k,93536753691350+c.lower,93537129788204+c.upper)) = pointBounds12193 := by
 decide +kernel
def cuts12194 : List PrefixCut := [⟨34,289864880,289865099⟩,
⟨83,702691755,702692282⟩,
⟨128,1082129809,1082130620⟩]
theorem checked12194 : checkPrefixCuts (2^48) 1602224129 9 Manual.Count131072.C012194.packed 128 cuts12194 = true := by
 decide +kernel
def pointBounds12194 : List (Nat × Nat × Nat) := [(1602258944,93538120679368,93538496777257),(1602309120,93538533506243,93538909604440)]
theorem point_links_checked12194 : (cuts12194.take 2).map (fun c => (1602224129-1+2*2^9*c.k,93537830814488+c.lower,93538206912158+c.upper)) = pointBounds12194 := by
 decide +kernel
def cuts12195 : List PrefixCut := [⟨4,32146328,32146353⟩,
⟨53,447757988,447758327⟩,
⟨102,854046860,854047514⟩,
⟨128,1078879247,1078880074⟩]
theorem checked12195 : checkPrefixCuts (2^48) 1602355201 9 Manual.Count131072.C012195.packed 128 cuts12195 = true := by
 decide +kernel
def pointBounds12195 : List (Nat × Nat × Nat) := [(1602359296,93538945090625,93539321189131),(1602409472,93539360702285,93539736801105),(1602459648,93539766991157,93540143090292)]
theorem point_links_checked12195 : (cuts12195.take 3).map (fun c => (1602355201-1+2*2^9*c.k,93538912944297+c.lower,93539289042778+c.upper)) = pointBounds12195 := by
 decide +kernel
def cuts12196 : List PrefixCut := [⟨23,193914910,193915058⟩,
⟨72,615986260,615986729⟩,
⟨121,1028384417,1028385196⟩,
⟨128,1087397736,1087398559⟩]
theorem checked12196 : checkPrefixCuts (2^48) 1602486273 9 Manual.Count131072.C012196.packed 128 cuts12196 = true := by
 decide +kernel
def pointBounds12196 : List (Nat × Nat × Nat) := [(1602509824,93540185738454,93540561837910),(1602560000,93540607809804,93540983909581),(1602610176,93541020207961,93541396308048)]
theorem point_links_checked12196 : (cuts12196.take 3).map (fun c => (1602486273-1+2*2^9*c.k,93539991823544+c.lower,93540367922852+c.upper)) = pointBounds12196 := by
 decide +kernel
def cuts12197 : List PrefixCut := [⟨42,355128144,355128415⟩,
⟨91,780672407,780672994⟩,
⟨128,1101709754,1101710586⟩]
theorem checked12197 : checkPrefixCuts (2^48) 1602617345 9 Manual.Count131072.C012197.packed 128 cuts12197 = true := by
 decide +kernel
def pointBounds12197 : List (Nat × Nat × Nat) := [(1602660352,93541434349424,93541810449826),(1602710528,93541859893687,93542235994405)]
theorem point_links_checked12197 : (cuts12197.take 2).map (fun c => (1602617345-1+2*2^9*c.k,93541079221280+c.lower,93541455321411+c.upper)) = pointBounds12197 := by
 decide +kernel
def cuts12198 : List PrefixCut := [⟨12,100278697,100278773⟩,
⟨61,513327587,513327980⟩,
⟨110,928470822,928471531⟩,
⟨128,1080370675,1080371497⟩]
theorem checked12198 : checkPrefixCuts (2^48) 1602748417 9 Manual.Count131072.C012198.packed 128 cuts12198 = true := by
 decide +kernel
def pointBounds12198 : List (Nat × Nat × Nat) := [(1602760704,93542281209731,93542657310770),(1602810880,93542694258621,93543070359977),(1602861056,93543109401856,93543485503528)]
theorem point_links_checked12198 : (cuts12198.take 3).map (fun c => (1602748417-1+2*2^9*c.k,93542180931034+c.lower,93542557031997+c.upper)) = pointBounds12198 := by
 decide +kernel
def cuts12199 : List PrefixCut := [⟨31,262001254,262001449⟩,
⟨80,680279390,680279904⟩,
⟨128,1096261854,1096262684⟩]
theorem checked12199 : checkPrefixCuts (2^48) 1602879489 9 Manual.Count131072.C012199.packed 128 cuts12199 = true := by
 decide +kernel
def pointBounds12199 : List (Nat × Nat × Nat) := [(1602911232,93543523302963,93543899404943),(1602961408,93543941581099,93544317683398)]
theorem point_links_checked12199 : (cuts12199.take 2).map (fun c => (1602879489-1+2*2^9*c.k,93543261301709+c.lower,93543637403494+c.upper)) = pointBounds12199 := by
 decide +kernel
def cuts12200 : List PrefixCut := [⟨1,8077202,8077208⟩,
⟨50,425275578,425275897⟩,
⟨99,838422462,838423093⟩,
⟨128,1084408154,1084408975⟩]
theorem checked12200 : checkPrefixCuts (2^48) 1603010561 9 Manual.Count131072.C012200.packed 128 cuts12200 = true := by
 decide +kernel
def pointBounds12200 : List (Nat × Nat × Nat) := [(1603011584,93544365640765,93544741743386),(1603061760,93544782839141,93545158942075),(1603111936,93545195986025,93545572089271)]
theorem point_links_checked12200 : (cuts12200.take 3).map (fun c => (1603010561-1+2*2^9*c.k,93544357563563+c.lower,93544733666178+c.upper)) = pointBounds12200 := by
 decide +kernel
def cuts12201 : List PrefixCut := [⟨20,176980557,176980691⟩,
⟨69,598880102,598880550⟩,
⟨118,1009003519,1009004279⟩,
⟨128,1096609586,1096610410⟩]
theorem checked12201 : checkPrefixCuts (2^48) 1603141633 9 Manual.Count131072.C012201.packed 128 cuts12201 = true := by
 decide +kernel
def pointBounds12201 : List (Nat × Nat × Nat) := [(1603162112,93545618952274,93545995055844),(1603212288,93546040851819,93546416955703),(1603262464,93546450975236,93546827079432)]
theorem point_links_checked12201 : (cuts12201.take 3).map (fun c => (1603141633-1+2*2^9*c.k,93545441971717+c.lower,93545818075153+c.upper)) = pointBounds12201 := by
 decide +kernel
def cuts12202 : List PrefixCut := [⟨39,335847172,335847427⟩,
⟨88,759111660,759112236⟩,
⟨128,1105648451,1105649290⟩]
theorem checked12202 : checkPrefixCuts (2^48) 1603272705 9 Manual.Count131072.C012202.packed 128 cuts12202 = true := by
 decide +kernel
def pointBounds12202 : List (Nat × Nat × Nat) := [(1603312640,93546874428475,93547250532990),(1603362816,93547297692963,93547673797799)]
theorem point_links_checked12202 : (cuts12202.take 2).map (fun c => (1603272705-1+2*2^9*c.k,93546538581303+c.lower,93546914685563+c.upper)) = pointBounds12202 := by
 decide +kernel
def cuts12203 : List PrefixCut := [⟨9,76363314,76363371⟩,
⟨58,490999694,491000065⟩,
⟨107,908431582,908432269⟩,
⟨128,1089232816,1089233642⟩]
theorem checked12203 : checkPrefixCuts (2^48) 1603403777 9 Manual.Count131072.C012203.packed 128 cuts12203 = true := by
 decide +kernel
def pointBounds12203 : List (Nat × Nat × Nat) := [(1603412992,93547720593068,93548096698224),(1603463168,93548135229448,93548511334918),(1603513344,93548552661336,93548928767122)]
theorem point_links_checked12203 : (cuts12203.take 3).map (fun c => (1603403777-1+2*2^9*c.k,93547644229754+c.lower,93548020334853+c.upper)) = pointBounds12203 := by
 decide +kernel
def cuts12204 : List PrefixCut := [⟨28,243463497,243463678⟩,
⟨77,655427884,655428377⟩,
⟨126,1068608077,1068608881⟩,
⟨128,1086335572,1086336389⟩]
theorem checked12204 : checkPrefixCuts (2^48) 1603534849 9 Manual.Count131072.C012204.packed 128 cuts12204 = true := by
 decide +kernel
def pointBounds12204 : List (Nat × Nat × Nat) := [(1603563520,93548976926067,93549353032173),(1603613696,93549388890454,93549764996872),(1603663872,93549802070647,93550178177376)]
theorem point_links_checked12204 : (cuts12204.take 3).map (fun c => (1603534849-1+2*2^9*c.k,93548733462570+c.lower,93549109568495+c.upper)) = pointBounds12204 := by
 decide +kernel
def cuts12205 : List PrefixCut := [⟨47,410358811,410359118⟩,
⟨96,827900981,827901602⟩,
⟨128,1098883964,1098884793⟩]
theorem checked12205 : checkPrefixCuts (2^48) 1603665921 9 Manual.Count131072.C012205.packed 128 cuts12205 = true := by
 decide +kernel
def pointBounds12205 : List (Nat × Nat × Nat) := [(1603714048,93550230156953,93550606264002),(1603764224,93550647699123,93551023806486)]
theorem point_links_checked12205 : (cuts12205.take 2).map (fun c => (1603665921-1+2*2^9*c.k,93549819798142+c.lower,93550195904884+c.upper)) = pointBounds12205 := by
 decide +kernel
def cuts12206 : List PrefixCut := [⟨17,141983008,141983117⟩,
⟨66,545634482,545634895⟩,
⟨115,967700303,967701038⟩,
⟨128,1074399250,1074400063⟩]
theorem checked12206 : checkPrefixCuts (2^48) 1603796993 9 Manual.Count131072.C012206.packed 128 cuts12206 = true := by
 decide +kernel
def pointBounds12206 : List (Nat × Nat × Nat) := [(1603814400,93551060665114,93551436772794),(1603864576,93551464316588,93551840424572),(1603914752,93551886382409,93552262490715)]
theorem point_links_checked12206 : (cuts12206.take 3).map (fun c => (1603796993-1+2*2^9*c.k,93550918682106+c.lower,93551294789677+c.upper)) = pointBounds12206 := by
 decide +kernel
def cuts12207 : List PrefixCut := [⟨36,300261594,300261820⟩,
⟨85,703348754,703349285⟩,
⟨128,1072381065,1072381873⟩]
theorem checked12207 : checkPrefixCuts (2^48) 1603928065 9 Manual.Count131072.C012207.packed 128 cuts12207 = true := by
 decide +kernel
def pointBounds12207 : List (Nat × Nat × Nat) := [(1603964928,93552293342950,93552669451560),(1604015104,93552696430110,93553072539025)]
theorem point_links_checked12207 : (cuts12207.take 2).map (fun c => (1603928065-1+2*2^9*c.k,93551993081356+c.lower,93552369189740+c.upper)) = pointBounds12207 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000068
