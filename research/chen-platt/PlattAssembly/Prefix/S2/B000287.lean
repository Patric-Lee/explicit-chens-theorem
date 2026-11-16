import PlattAssemblyKernel
import PlattCertificates.Count131072.C019184
import PlattCertificates.Count131072.C019185
import PlattCertificates.Count131072.C019186
import PlattCertificates.Count131072.C019187
import PlattCertificates.Count131072.C019188
import PlattCertificates.Count131072.C019189
import PlattCertificates.Count131072.C019190
import PlattCertificates.Count131072.C019191
import PlattCertificates.Count131072.C019192
import PlattCertificates.Count131072.C019193
import PlattCertificates.Count131072.C019194
import PlattCertificates.Count131072.C019195
import PlattCertificates.Count131072.C019196
import PlattCertificates.Count131072.C019197
import PlattCertificates.Count131072.C019198
import PlattCertificates.Count131072.C019199
import PlattCertificates.Count131072.C019200
import PlattCertificates.Count131072.C019201
import PlattCertificates.Count131072.C019202
import PlattCertificates.Count131072.C019203
import PlattCertificates.Count131072.C019204
import PlattCertificates.Count131072.C019205
import PlattCertificates.Count131072.C019206
import PlattCertificates.Count131072.C019207
import PlattCertificates.Count131072.C019208
import PlattCertificates.Count131072.C019209
import PlattCertificates.Count131072.C019210
import PlattCertificates.Count131072.C019211
import PlattCertificates.Count131072.C019212
import PlattCertificates.Count131072.C019213
import PlattCertificates.Count131072.C019214
import PlattCertificates.Count131072.C019215
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000287
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19184 : List PrefixCut := [⟨58,307913314,307913502⟩,
⟨128,677511425,677511832⟩]
theorem checked19184 : checkPrefixCuts (2^48) 2518417409 9 Manual.Count131072.C019184.packed 128 cuts19184 = true := by
 decide +kernel
def pointBounds19184 : List (Nat × Nat × Nat) := [(2518476800,99480767648195,99481147698216)]
theorem point_links_checked19184 : (cuts19184.take 1).map (fun c => (2518417409-1+2*2^9*c.k,99480459734881+c.lower,99480839784714+c.upper)) = pointBounds19184 := by
 decide +kernel
def cuts19185 : List PrefixCut := [⟨7,36098673,36098696⟩,
⟨84,438541691,438541955⟩,
⟨128,671329333,671329736⟩]
theorem checked19185 : checkPrefixCuts (2^48) 2518548481 9 Manual.Count131072.C019185.packed 128 cuts19185 = true := by
 decide +kernel
def pointBounds19185 : List (Nat × Nat × Nat) := [(2518555648,99481173344979,99481553395242),(2518634496,99481575787997,99481955838501)]
theorem point_links_checked19185 : (cuts19185.take 2).map (fun c => (2518548481-1+2*2^9*c.k,99481137246306+c.lower,99481517296546+c.upper)) = pointBounds19185 := by
 decide +kernel
def cuts19186 : List PrefixCut := [⟨33,174895322,174895425⟩,
⟨110,579883506,579883853⟩,
⟨128,676211607,676212012⟩]
theorem checked19186 : checkPrefixCuts (2^48) 2518679553 9 Manual.Count131072.C019186.packed 128 cuts19186 = true := by
 decide +kernel
def pointBounds19186 : List (Nat × Nat × Nat) := [(2518713344,99481983470961,99482363521707),(2518792192,99482388459145,99482768510135)]
theorem point_links_checked19186 : (cuts19186.take 2).map (fun c => (2518679553-1+2*2^9*c.k,99481808575639+c.lower,99482188626282+c.upper)) = pointBounds19186 := by
 decide +kernel
def cuts19187 : List PrefixCut := [⟨59,310994078,310994266⟩,
⟨128,674164892,674165298⟩]
theorem checked19187 : checkPrefixCuts (2^48) 2518810625 9 Manual.Count131072.C019187.packed 128 cuts19187 = true := by
 decide +kernel
def pointBounds19187 : List (Nat × Nat × Nat) := [(2518871040,99482795781324,99483175832560)]
theorem point_links_checked19187 : (cuts19187.take 1).map (fun c => (2518810625-1+2*2^9*c.k,99482484787246+c.lower,99482864838294+c.upper)) = pointBounds19187 := by
 decide +kernel
def cuts19188 : List PrefixCut := [⟨8,40451014,40451038⟩,
⟨85,444954157,444954418⟩,
⟨128,674911935,674912333⟩]
theorem checked19188 : checkPrefixCuts (2^48) 2518941697 9 Manual.Count131072.C019188.packed 128 cuts19188 = true := by
 decide +kernel
def pointBounds19188 : List (Nat × Nat × Nat) := [(2518949888,99483199403152,99483579454630),(2519028736,99483603906295,99483983958010)]
theorem point_links_checked19188 : (cuts19188.take 2).map (fun c => (2518941697-1+2*2^9*c.k,99483158952138+c.lower,99483539003592+c.upper)) = pointBounds19188 := by
 decide +kernel
def cuts19189 : List PrefixCut := [⟨34,180007863,180007970⟩,
⟨111,584150519,584150867⟩,
⟨128,673983095,673983497⟩]
theorem checked19189 : checkPrefixCuts (2^48) 2519072769 9 Manual.Count131072.C019189.packed 128 cuts19189 = true := by
 decide +kernel
def pointBounds19189 : List (Nat × Nat × Nat) := [(2519107584,99484013871936,99484393923895),(2519186432,99484418014592,99484798066792)]
theorem point_links_checked19189 : (cuts19189.take 2).map (fun c => (2519072769-1+2*2^9*c.k,99483833864073+c.lower,99484213915925+c.upper)) = pointBounds19189 := by
 decide +kernel
def cuts19190 : List PrefixCut := [⟨60,322118484,322118678⟩,
⟨128,685456057,685456467⟩]
theorem checked19190 : checkPrefixCuts (2^48) 2519203841 9 Manual.Count131072.C019190.packed 128 cuts19190 = true := by
 decide +kernel
def pointBounds19190 : List (Nat × Nat × Nat) := [(2519265280,99484829965652,99485210018100)]
theorem point_links_checked19190 : (cuts19190.take 1).map (fun c => (2519203841-1+2*2^9*c.k,99484507847168+c.lower,99484887899422+c.upper)) = pointBounds19190 := by
 decide +kernel
def cuts19191 : List PrefixCut := [⟨9,47595136,47595166⟩,
⟨86,455721862,455722133⟩,
⟨128,673466161,673466558⟩]
theorem checked19191 : checkPrefixCuts (2^48) 2519334913 9 Manual.Count131072.C019191.packed 128 cuts19191 = true := by
 decide +kernel
def pointBounds19191 : List (Nat × Nat × Nat) := [(2519344128,99485240898361,99485620951055),(2519422976,99485649025087,99486029078022)]
theorem point_links_checked19191 : (cuts19191.take 2).map (fun c => (2519334913-1+2*2^9*c.k,99485193303225+c.lower,99485573355889+c.upper)) = pointBounds19191 := by
 decide +kernel
def cuts19192 : List PrefixCut := [⟨35,186571183,186571296⟩,
⟨112,595454405,595454764⟩,
⟨128,679352086,679352498⟩]
theorem checked19192 : checkPrefixCuts (2^48) 2519465985 9 Manual.Count131072.C019192.packed 128 cuts19192 = true := by
 decide +kernel
def pointBounds19192 : List (Nat × Nat × Nat) := [(2519501824,99486053340569,99486433393743),(2519580672,99486462223791,99486842277211)]
theorem point_links_checked19192 : (cuts19192.take 2).map (fun c => (2519465985-1+2*2^9*c.k,99485866769386+c.lower,99486246822447+c.upper)) = pointBounds19192 := by
 decide +kernel
def cuts19193 : List PrefixCut := [⟨61,319387066,319387259⟩,
⟨128,674289516,674289922⟩]
theorem checked19193 : checkPrefixCuts (2^48) 2519597057 9 Manual.Count131072.C019193.packed 128 cuts19193 = true := by
 decide +kernel
def pointBounds19193 : List (Nat × Nat × Nat) := [(2519659520,99486865508538,99487245562204)]
theorem point_links_checked19193 : (cuts19193.take 1).map (fun c => (2519597057-1+2*2^9*c.k,99486546121472+c.lower,99486926174945+c.upper)) = pointBounds19193 := by
 decide +kernel
def cuts19194 : List PrefixCut := [⟨10,53508233,53508264⟩,
⟨87,459448624,459448898⟩,
⟨128,671015177,671015576⟩]
theorem checked19194 : checkPrefixCuts (2^48) 2519728129 9 Manual.Count131072.C019194.packed 128 cuts19194 = true := by
 decide +kernel
def pointBounds19194 : List (Nat × Nat × Nat) := [(2519738368,99487273919221,99487653973131),(2519817216,99487679859612,99488059913765)]
theorem point_links_checked19194 : (cuts19194.take 2).map (fun c => (2519728129-1+2*2^9*c.k,99487220410988+c.lower,99487600464867+c.upper)) = pointBounds19194 := by
 decide +kernel
def cuts19195 : List PrefixCut := [⟨36,187882422,187882535⟩,
⟨113,597930354,597930717⟩,
⟨128,678017213,678017626⟩]
theorem checked19195 : checkPrefixCuts (2^48) 2519859201 9 Manual.Count131072.C019195.packed 128 cuts19195 = true := by
 decide +kernel
def pointBounds19195 : List (Nat × Nat × Nat) := [(2519896064,99488079308587,99488459362978),(2519974912,99488489356519,99488869411160)]
theorem point_links_checked19195 : (cuts19195.take 2).map (fun c => (2519859201-1+2*2^9*c.k,99487891426165+c.lower,99488271480443+c.upper)) = pointBounds19195 := by
 decide +kernel
def cuts19196 : List PrefixCut := [⟨62,325368737,325368934⟩,
⟨128,671057021,671057428⟩]
theorem checked19196 : checkPrefixCuts (2^48) 2519990273 9 Manual.Count131072.C019196.packed 128 cuts19196 = true := by
 decide +kernel
def pointBounds19196 : List (Nat × Nat × Nat) := [(2520053760,99488894812115,99489274867003)]
theorem point_links_checked19196 : (cuts19196.take 1).map (fun c => (2519990273-1+2*2^9*c.k,99488569443378+c.lower,99488949498069+c.upper)) = pointBounds19196 := by
 decide +kernel
def cuts19197 : List PrefixCut := [⟨11,57073977,57074010⟩,
⟨88,465519839,465520114⟩,
⟨128,677723453,677723856⟩]
theorem checked19197 : checkPrefixCuts (2^48) 2520121345 9 Manual.Count131072.C019197.packed 128 cuts19197 = true := by
 decide +kernel
def pointBounds19197 : List (Nat × Nat × Nat) := [(2520132608,99489297574376,99489677629507),(2520211456,99489706020238,99490086075611)]
theorem point_links_checked19197 : (cuts19197.take 2).map (fun c => (2520121345-1+2*2^9*c.k,99489240500399+c.lower,99489620555497+c.upper)) = pointBounds19197 := by
 decide +kernel
def cuts19198 : List PrefixCut := [⟨37,195335951,195336068⟩,
⟨114,603867882,603868241⟩,
⟨128,681932000,681932405⟩]
theorem checked19198 : checkPrefixCuts (2^48) 2520252417 9 Manual.Count131072.C019198.packed 128 cuts19198 = true := by
 decide +kernel
def pointBounds19198 : List (Nat × Nat × Nat) := [(2520290304,99490113559803,99490493615421),(2520369152,99490522091734,99490902147594)]
theorem point_links_checked19198 : (cuts19198.take 2).map (fun c => (2520252417-1+2*2^9*c.k,99489918223852+c.lower,99490298279353+c.upper)) = pointBounds19198 := by
 decide +kernel
def cuts19199 : List PrefixCut := [⟨63,335480622,335480822⟩,
⟨128,679774793,679775195⟩]
theorem checked19199 : checkPrefixCuts (2^48) 2520383489 9 Manual.Count131072.C019199.packed 128 cuts19199 = true := by
 decide +kernel
def pointBounds19199 : List (Nat × Nat × Nat) := [(2520448000,99490935636474,99491315692580)]
theorem point_links_checked19199 : (cuts19199.take 1).map (fun c => (2520383489-1+2*2^9*c.k,99490600155852+c.lower,99490980211758+c.upper)) = pointBounds19199 := by
 decide +kernel
def cuts19200 : List PrefixCut := [⟨12,63653787,63653824⟩,
⟨89,466452160,466452438⟩,
⟨128,674825885,674826285⟩]
theorem checked19200 : checkPrefixCuts (2^48) 2520514561 9 Manual.Count131072.C019200.packed 128 cuts19200 = true := by
 decide +kernel
def pointBounds19200 : List (Nat × Nat × Nat) := [(2520526848,99491343584432,99491723640777),(2520605696,99491746382805,99492126439391)]
theorem point_links_checked19200 : (cuts19200.take 2).map (fun c => (2520514561-1+2*2^9*c.k,99491279930645+c.lower,99491659986953+c.upper)) = pointBounds19200 := by
 decide +kernel
def cuts19201 : List PrefixCut := [⟨38,198320445,198320562⟩,
⟨115,603326897,603327255⟩,
⟨128,673785783,673786184⟩]
theorem checked19201 : checkPrefixCuts (2^48) 2520645633 9 Manual.Count131072.C019201.packed 128 cuts19201 = true := by
 decide +kernel
def pointBounds19201 : List (Nat × Nat × Nat) := [(2520684544,99492153076975,99492533133800),(2520763392,99492558083427,99492938140493)]
theorem point_links_checked19201 : (cuts19201.take 2).map (fun c => (2520645633-1+2*2^9*c.k,99491954756530+c.lower,99492334813238+c.upper)) = pointBounds19201 := by
 decide +kernel
def cuts19202 : List PrefixCut := [⟨64,330850086,330850282⟩,
⟨128,671740849,671741247⟩]
theorem checked19202 : checkPrefixCuts (2^48) 2520776705 9 Manual.Count131072.C019202.packed 128 cuts19202 = true := by
 decide +kernel
def pointBounds19202 : List (Nat × Nat × Nat) := [(2520842240,99492959392399,99493339449704)]
theorem point_links_checked19202 : (cuts19202.take 1).map (fun c => (2520776705-1+2*2^9*c.k,99492628542313+c.lower,99493008599422+c.upper)) = pointBounds19202 := by
 decide +kernel
def cuts19203 : List PrefixCut := [⟨13,70454851,70454895⟩,
⟨90,483797381,483797674⟩,
⟨128,682536570,682536980⟩]
theorem checked19203 : checkPrefixCuts (2^48) 2520907777 9 Manual.Count131072.C019203.packed 128 cuts19203 = true := by
 decide +kernel
def pointBounds19203 : List (Nat × Nat × Nat) := [(2520921088,99493370738013,99493750795564),(2520999936,99493784080543,99494164138343)]
theorem point_links_checked19203 : (cuts19203.take 2).map (fun c => (2520907777-1+2*2^9*c.k,99493300283162+c.lower,99493680340669+c.upper)) = pointBounds19203 := by
 decide +kernel
def cuts19204 : List PrefixCut := [⟨39,205546685,205546808⟩,
⟨116,607252088,607252454⟩,
⟨128,669326617,669327020⟩]
theorem checked19204 : checkPrefixCuts (2^48) 2521038849 9 Manual.Count131072.C019204.packed 128 cuts19204 = true := by
 decide +kernel
def pointBounds19204 : List (Nat × Nat × Nat) := [(2521078784,99494188366417,99494568424457),(2521157632,99494590071820,99494970130103)]
theorem point_links_checked19204 : (cuts19204.take 2).map (fun c => (2521038849-1+2*2^9*c.k,99493982819732+c.lower,99494362877649+c.upper)) = pointBounds19204 := by
 decide +kernel
def cuts19205 : List PrefixCut := [⟨65,343525825,343526028⟩,
⟨128,668622070,668622464⟩]
theorem checked19205 : checkPrefixCuts (2^48) 2521169921 9 Manual.Count131072.C019205.packed 128 cuts19205 = true := by
 decide +kernel
def pointBounds19205 : List (Nat × Nat × Nat) := [(2521236480,99494995672174,99495375730697)]
theorem point_links_checked19205 : (cuts19205.take 1).map (fun c => (2521169921-1+2*2^9*c.k,99494652146349+c.lower,99495032204669+c.upper)) = pointBounds19205 := by
 decide +kernel
def cuts19206 : List PrefixCut := [⟨14,74686113,74686157⟩,
⟨91,483610048,483610337⟩,
⟨128,678299379,678299781⟩]
theorem checked19206 : checkPrefixCuts (2^48) 2521300993 9 Manual.Count131072.C019206.packed 128 cuts19206 = true := by
 decide +kernel
def pointBounds19206 : List (Nat × Nat × Nat) := [(2521315328,99495395454532,99495775513290),(2521394176,99495804378467,99496184437470)]
theorem point_links_checked19206 : (cuts19206.take 2).map (fun c => (2521300993-1+2*2^9*c.k,99495320768419+c.lower,99495700827133+c.upper)) = pointBounds19206 := by
 decide +kernel
def cuts19207 : List PrefixCut := [⟨40,212993948,212994073⟩,
⟨117,617427276,617427642⟩,
⟨128,675027010,675027411⟩]
theorem checked19207 : checkPrefixCuts (2^48) 2521432065 9 Manual.Count131072.C019207.packed 128 cuts19207 = true := by
 decide +kernel
def pointBounds19207 : List (Nat × Nat × Nat) := [(2521473024,99496212061746,99496592120987),(2521551872,99496616495074,99496996554556)]
theorem point_links_checked19207 : (cuts19207.take 2).map (fun c => (2521432065-1+2*2^9*c.k,99495999067798+c.lower,99496379126914+c.upper)) = pointBounds19207 := by
 decide +kernel
def cuts19208 : List PrefixCut := [⟨66,355081204,355081415⟩,
⟨128,681577744,681578148⟩]
theorem checked19208 : checkPrefixCuts (2^48) 2521563137 9 Manual.Count131072.C019208.packed 128 cuts19208 = true := by
 decide +kernel
def pointBounds19208 : List (Nat × Nat × Nat) := [(2521630720,99497029176012,99497409235740)]
theorem point_links_checked19208 : (cuts19208.take 1).map (fun c => (2521563137-1+2*2^9*c.k,99496674094808+c.lower,99497054154325+c.upper)) = pointBounds19208 := by
 decide +kernel
def cuts19209 : List PrefixCut := [⟨15,80255494,80255542⟩,
⟨92,484204325,484204614⟩,
⟨128,679198119,679198524⟩]
theorem checked19209 : checkPrefixCuts (2^48) 2521694209 9 Manual.Count131072.C019209.packed 128 cuts19209 = true := by
 decide +kernel
def pointBounds19209 : List (Nat × Nat × Nat) := [(2521709568,99497435928046,99497815988015),(2521788416,99497839876877,99498219937087)]
theorem point_links_checked19209 : (cuts19209.take 2).map (fun c => (2521694209-1+2*2^9*c.k,99497355672552+c.lower,99497735732473+c.upper)) = pointBounds19209 := by
 decide +kernel
def cuts19210 : List PrefixCut := [⟨41,216085878,216086002⟩,
⟨118,626259765,626260136⟩,
⟨128,674698491,674698892⟩]
theorem checked19210 : checkPrefixCuts (2^48) 2521825281 9 Manual.Count131072.C019210.packed 128 cuts19210 = true := by
 decide +kernel
def pointBounds19210 : List (Nat × Nat × Nat) := [(2521867264,99498250956549,99498631016999),(2521946112,99498661130436,99499041191133)]
theorem point_links_checked19210 : (cuts19210.take 2).map (fun c => (2521825281-1+2*2^9*c.k,99498034870671+c.lower,99498414930997+c.upper)) = pointBounds19210 := by
 decide +kernel
def cuts19211 : List PrefixCut := [⟨67,358932033,358932247⟩,
⟨128,681694617,681695025⟩]
theorem checked19211 : checkPrefixCuts (2^48) 2521956353 9 Manual.Count131072.C019211.packed 128 cuts19211 = true := by
 decide +kernel
def pointBounds19211 : List (Nat × Nat × Nat) := [(2522024960,99499068501195,99499448562136)]
theorem point_links_checked19211 : (cuts19211.take 1).map (fun c => (2521956353-1+2*2^9*c.k,99498709569162+c.lower,99499089629889+c.upper)) = pointBounds19211 := by
 decide +kernel
def cuts19212 : List PrefixCut := [⟨16,84707118,84707168⟩,
⟨93,489820446,489820737⟩,
⟨128,680877827,680878228⟩]
theorem checked19212 : checkPrefixCuts (2^48) 2522087425 9 Manual.Count131072.C019212.packed 128 cuts19212 = true := by
 decide +kernel
def pointBounds19212 : List (Nat × Nat × Nat) := [(2522103808,99499475970897,99499856032082),(2522182656,99499881084225,99500261145651)]
theorem point_links_checked19212 : (cuts19212.take 2).map (fun c => (2522087425-1+2*2^9*c.k,99499391263779+c.lower,99499771324914+c.upper)) = pointBounds19212 := by
 decide +kernel
def cuts19213 : List PrefixCut := [⟨42,221408841,221408974⟩,
⟨119,630737343,630737722⟩,
⟨128,676490285,676490691⟩]
theorem checked19213 : checkPrefixCuts (2^48) 2522218497 9 Manual.Count131072.C019213.packed 128 cuts19213 = true := by
 decide +kernel
def pointBounds19213 : List (Nat × Nat × Nat) := [(2522261504,99500293550447,99500673612116),(2522340352,99500702878949,99501082940864)]
theorem point_links_checked19213 : (cuts19213.take 2).map (fun c => (2522218497-1+2*2^9*c.k,99500072141606+c.lower,99500452203142+c.upper)) = pointBounds19213 := by
 decide +kernel
def cuts19214 : List PrefixCut := [⟨68,358206452,358206664⟩,
⟨128,672326377,672326778⟩]
theorem checked19214 : checkPrefixCuts (2^48) 2522349569 9 Manual.Count131072.C019214.packed 128 cuts19214 = true := by
 decide +kernel
def pointBounds19214 : List (Nat × Nat × Nat) := [(2522419200,99501106838343,99501486900497)]
theorem point_links_checked19214 : (cuts19214.take 1).map (fun c => (2522349569-1+2*2^9*c.k,99500748631891+c.lower,99501128693833+c.upper)) = pointBounds19214 := by
 decide +kernel
def cuts19215 : List PrefixCut := [⟨17,89826858,89826910⟩,
⟨94,493984245,493984540⟩,
⟨128,672403107,672403508⟩]
theorem checked19215 : checkPrefixCuts (2^48) 2522480641 9 Manual.Count131072.C019215.packed 128 cuts19215 = true := by
 decide +kernel
def pointBounds19215 : List (Nat × Nat × Nat) := [(2522498048,99501510785126,99501890847521),(2522576896,99501914942513,99502295005151)]
theorem point_links_checked19215 : (cuts19215.take 2).map (fun c => (2522480641-1+2*2^9*c.k,99501420958268+c.lower,99501801020611+c.upper)) = pointBounds19215 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000287
