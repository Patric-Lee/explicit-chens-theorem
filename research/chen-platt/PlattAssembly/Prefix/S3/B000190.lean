import PlattAssemblyKernel
import PlattCertificates.Count131072.C026080
import PlattCertificates.Count131072.C026081
import PlattCertificates.Count131072.C026082
import PlattCertificates.Count131072.C026083
import PlattCertificates.Count131072.C026084
import PlattCertificates.Count131072.C026085
import PlattCertificates.Count131072.C026086
import PlattCertificates.Count131072.C026087
import PlattCertificates.Count131072.C026088
import PlattCertificates.Count131072.C026089
import PlattCertificates.Count131072.C026090
import PlattCertificates.Count131072.C026091
import PlattCertificates.Count131072.C026092
import PlattCertificates.Count131072.C026093
import PlattCertificates.Count131072.C026094
import PlattCertificates.Count131072.C026095
import PlattCertificates.Count131072.C026096
import PlattCertificates.Count131072.C026097
import PlattCertificates.Count131072.C026098
import PlattCertificates.Count131072.C026099
import PlattCertificates.Count131072.C026100
import PlattCertificates.Count131072.C026101
import PlattCertificates.Count131072.C026102
import PlattCertificates.Count131072.C026103
import PlattCertificates.Count131072.C026104
import PlattCertificates.Count131072.C026105
import PlattCertificates.Count131072.C026106
import PlattCertificates.Count131072.C026107
import PlattCertificates.Count131072.C026108
import PlattCertificates.Count131072.C026109
import PlattCertificates.Count131072.C026110
import PlattCertificates.Count131072.C026111
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000190
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26080 : List PrefixCut := [⟨60,232100436,232100573⟩,
⟨128,495449632,495449915⟩]
theorem checked26080 : checkPrefixCuts (2^48) 3422289921 9 Manual.Count131072.C026080.packed 128 cuts26080 = true := by
 decide +kernel
def pointBounds26080 : List (Nat × Nat × Nat) := [(3422351360,103440360743198,103440743063579)]
theorem point_links_checked26080 : (cuts26080.take 1).map (fun c => (3422289921-1+2*2^9*c.k,103440128642762+c.lower,103440510963006+c.upper)) = pointBounds26080 := by
 decide +kernel
def cuts26081 : List PrefixCut := [⟨37,142446485,142446571⟩,
⟨128,493703514,493703791⟩]
theorem checked26081 : checkPrefixCuts (2^48) 3422420993 9 Manual.Count131072.C026081.packed 128 cuts26081 = true := by
 decide +kernel
def pointBounds26081 : List (Nat × Nat × Nat) := [(3422458880,103440766538879,103441148859492)]
theorem point_links_checked26081 : (cuts26081.take 1).map (fun c => (3422420993-1+2*2^9*c.k,103440624092394+c.lower,103441006412921+c.upper)) = pointBounds26081 := by
 decide +kernel
def cuts26082 : List PrefixCut := [⟨14,53127726,53127755⟩,
⟨119,454703676,454703928⟩,
⟨128,488832527,488832799⟩]
theorem checked26082 : checkPrefixCuts (2^48) 3422552065 9 Manual.Count131072.C026082.packed 128 cuts26082 = true := by
 decide +kernel
def pointBounds26082 : List (Nat × Nat × Nat) := [(3422566400,103441170923634,103441553244467),(3422673920,103441572499584,103441954820640)]
theorem point_links_checked26082 : (cuts26082.take 2).map (fun c => (3422552065-1+2*2^9*c.k,103441117795908+c.lower,103441500116712+c.upper)) = pointBounds26082 := by
 decide +kernel
def cuts26083 : List PrefixCut := [⟨96,372121967,372122174⟩,
⟨128,497284124,497284402⟩]
theorem checked26083 : checkPrefixCuts (2^48) 3422683137 9 Manual.Count131072.C026083.packed 128 cuts26083 = true := by
 decide +kernel
def pointBounds26083 : List (Nat × Nat × Nat) := [(3422781440,103441978750402,103442361071685)]
theorem point_links_checked26083 : (cuts26083.take 1).map (fun c => (3422683137-1+2*2^9*c.k,103441606628435+c.lower,103441988949511+c.upper)) = pointBounds26083 := by
 decide +kernel
def cuts26084 : List PrefixCut := [⟨73,280993695,280993856⟩,
⟨128,496607224,496607504⟩]
theorem checked26084 : checkPrefixCuts (2^48) 3422814209 9 Manual.Count131072.C026084.packed 128 cuts26084 = true := by
 decide +kernel
def pointBounds26084 : List (Nat × Nat × Nat) := [(3422888960,103442384906254,103442767227769)]
theorem point_links_checked26084 : (cuts26084.take 1).map (fun c => (3422814209-1+2*2^9*c.k,103442103912559+c.lower,103442486233913+c.upper)) = pointBounds26084 := by
 decide +kernel
def cuts26085 : List PrefixCut := [⟨50,187980456,187980561⟩,
⟨128,487378436,487378707⟩]
theorem checked26085 : checkPrefixCuts (2^48) 3422945281 9 Manual.Count131072.C026085.packed 128 cuts26085 = true := by
 decide +kernel
def pointBounds26085 : List (Nat × Nat × Nat) := [(3422996480,103442788500239,103443170821978)]
theorem point_links_checked26085 : (cuts26085.take 1).map (fun c => (3422945281-1+2*2^9*c.k,103442600519783+c.lower,103442982841417+c.upper)) = pointBounds26085 := by
 decide +kernel
def cuts26086 : List PrefixCut := [⟨27,105087769,105087830⟩,
⟨128,493526809,493527082⟩]
theorem checked26086 : checkPrefixCuts (2^48) 3423076353 9 Manual.Count131072.C026086.packed 128 cuts26086 = true := by
 decide +kernel
def pointBounds26086 : List (Nat × Nat × Nat) := [(3423104000,103443192985988,103443575307954)]
theorem point_links_checked26086 : (cuts26086.take 1).map (fun c => (3423076353-1+2*2^9*c.k,103443087898219+c.lower,103443470220124+c.upper)) = pointBounds26086 := by
 decide +kernel
def cuts26087 : List PrefixCut := [⟨4,16445088,16445097⟩,
⟨109,416958632,416958868⟩,
⟨128,487752261,487752538⟩]
theorem checked26087 : checkPrefixCuts (2^48) 3423207425 9 Manual.Count131072.C026087.packed 128 cuts26087 = true := by
 decide +kernel
def pointBounds26087 : List (Nat × Nat × Nat) := [(3423211520,103443597870116,103443980192303),(3423319040,103443998383660,103444380706074)]
theorem point_links_checked26087 : (cuts26087.take 2).map (fun c => (3423207425-1+2*2^9*c.k,103443581425028+c.lower,103443963747206+c.upper)) = pointBounds26087 := by
 decide +kernel
def cuts26088 : List PrefixCut := [⟨86,330694008,330694192⟩,
⟨128,493160142,493160423⟩]
theorem checked26088 : checkPrefixCuts (2^48) 3423338497 9 Manual.Count131072.C026088.packed 128 cuts26088 = true := by
 decide +kernel
def pointBounds26088 : List (Nat × Nat × Nat) := [(3423426560,103444399871297,103444782193936)]
theorem point_links_checked26088 : (cuts26088.take 1).map (fun c => (3423338497-1+2*2^9*c.k,103444069177289+c.lower,103444451499744+c.upper)) = pointBounds26088 := by
 decide +kernel
def cuts26089 : List PrefixCut := [⟨63,244846420,244846557⟩,
⟨128,493223491,493223762⟩]
theorem checked26089 : checkPrefixCuts (2^48) 3423469569 9 Manual.Count131072.C026089.packed 128 cuts26089 = true := by
 decide +kernel
def pointBounds26089 : List (Nat × Nat × Nat) := [(3423534080,103444807183851,103445189506724)]
theorem point_links_checked26089 : (cuts26089.take 1).map (fun c => (3423469569-1+2*2^9*c.k,103444562337431+c.lower,103444944660167+c.upper)) = pointBounds26089 := by
 decide +kernel
def cuts26090 : List PrefixCut := [⟨40,150207800,150207883⟩,
⟨128,489504905,489505179⟩]
theorem checked26090 : checkPrefixCuts (2^48) 3423600641 9 Manual.Count131072.C026090.packed 128 cuts26090 = true := by
 decide +kernel
def pointBounds26090 : List (Nat × Nat × Nat) := [(3423641600,103445205768722,103445588091812)]
theorem point_links_checked26090 : (cuts26090.take 1).map (fun c => (3423600641-1+2*2^9*c.k,103445055560922+c.lower,103445437883929+c.upper)) = pointBounds26090 := by
 decide +kernel
def cuts26091 : List PrefixCut := [⟨17,65605726,65605764⟩,
⟨122,469838108,469838376⟩,
⟨128,492445808,492446090⟩]
theorem checked26091 : checkPrefixCuts (2^48) 3423731713 9 Manual.Count131072.C026091.packed 128 cuts26091 = true := by
 decide +kernel
def pointBounds26091 : List (Nat × Nat × Nat) := [(3423749120,103445610671553,103445992994872),(3423856640,103446014903935,103446397227484)]
theorem point_links_checked26091 : (cuts26091.take 2).map (fun c => (3423731713-1+2*2^9*c.k,103445545065827+c.lower,103445927389108+c.upper)) = pointBounds26091 := by
 decide +kernel
def cuts26092 : List PrefixCut := [⟨99,376186240,376186448⟩,
⟨128,487001224,487001495⟩]
theorem checked26092 : checkPrefixCuts (2^48) 3423862785 9 Manual.Count131072.C026092.packed 128 cuts26092 = true := by
 decide +kernel
def pointBounds26092 : List (Nat × Nat × Nat) := [(3423964160,103446413697875,103446796021646)]
theorem point_links_checked26092 : (cuts26092.take 1).map (fun c => (3423862785-1+2*2^9*c.k,103446037511635+c.lower,103446419835198+c.upper)) = pointBounds26092 := by
 decide +kernel
def cuts26093 : List PrefixCut := [⟨76,286897830,286897995⟩,
⟨128,486489358,486489636⟩]
theorem checked26093 : checkPrefixCuts (2^48) 3423993857 9 Manual.Count131072.C026093.packed 128 cuts26093 = true := by
 decide +kernel
def pointBounds26093 : List (Nat × Nat × Nat) := [(3424071680,103446811410689,103447193734688)]
theorem point_links_checked26093 : (cuts26093.take 1).map (fun c => (3423993857-1+2*2^9*c.k,103446524512859+c.lower,103446906836693+c.upper)) = pointBounds26093 := by
 decide +kernel
def cuts26094 : List PrefixCut := [⟨53,205507009,205507122⟩,
⟨128,494362139,494362409⟩]
theorem checked26094 : checkPrefixCuts (2^48) 3424124929 9 Manual.Count131072.C026094.packed 128 cuts26094 = true := by
 decide +kernel
def pointBounds26094 : List (Nat × Nat × Nat) := [(3424179200,103447216509226,103447598833451)]
theorem point_links_checked26094 : (cuts26094.take 1).map (fun c => (3424124929-1+2*2^9*c.k,103447011002217+c.lower,103447393326329+c.upper)) = pointBounds26094 := by
 decide +kernel
def cuts26095 : List PrefixCut := [⟨30,112613920,112613981⟩,
⟨128,486534302,486534572⟩]
theorem checked26095 : checkPrefixCuts (2^48) 3424256001 9 Manual.Count131072.C026095.packed 128 cuts26095 = true := by
 decide +kernel
def pointBounds26095 : List (Nat × Nat × Nat) := [(3424286720,103447617978276,103448000302719)]
theorem point_links_checked26095 : (cuts26095.take 1).map (fun c => (3424256001-1+2*2^9*c.k,103447505364356+c.lower,103447887688738+c.upper)) = pointBounds26095 := by
 decide +kernel
def cuts26096 : List PrefixCut := [⟨7,27125036,27125051⟩,
⟨112,432349854,432350095⟩,
⟨128,494159899,494160175⟩]
theorem checked26096 : checkPrefixCuts (2^48) 3424387073 9 Manual.Count131072.C026096.packed 128 cuts26096 = true := by
 decide +kernel
def pointBounds26096 : List (Nat × Nat × Nat) := [(3424394240,103448019023694,103448401348361),(3424501760,103448424248512,103448806573405)]
theorem point_links_checked26096 : (cuts26096.take 2).map (fun c => (3424387073-1+2*2^9*c.k,103447991898658+c.lower,103448374223310+c.upper)) = pointBounds26096 := by
 decide +kernel
def cuts26097 : List PrefixCut := [⟨89,338306010,338306200⟩,
⟨128,489373703,489373980⟩]
theorem checked26097 : checkPrefixCuts (2^48) 3424518145 9 Manual.Count131072.C026097.packed 128 cuts26097 = true := by
 decide +kernel
def pointBounds26097 : List (Nat × Nat × Nat) := [(3424609280,103448824364567,103449206689685)]
theorem point_links_checked26097 : (cuts26097.take 1).map (fun c => (3424518145-1+2*2^9*c.k,103448486058557+c.lower,103448868383485+c.upper)) = pointBounds26097 := by
 decide +kernel
def cuts26098 : List PrefixCut := [⟨66,251501556,251501701⟩,
⟨128,486971580,486971855⟩]
theorem checked26098 : checkPrefixCuts (2^48) 3424649217 9 Manual.Count131072.C026098.packed 128 cuts26098 = true := by
 decide +kernel
def pointBounds26098 : List (Nat × Nat × Nat) := [(3424716800,103449226933816,103449609259166)]
theorem point_links_checked26098 : (cuts26098.take 1).map (fun c => (3424649217-1+2*2^9*c.k,103448975432260+c.lower,103449357757465+c.upper)) = pointBounds26098 := by
 decide +kernel
def cuts26099 : List PrefixCut := [⟨43,163963463,163963559⟩,
⟨128,484569606,484569876⟩]
theorem checked26099 : checkPrefixCuts (2^48) 3424780289 9 Manual.Count131072.C026099.packed 128 cuts26099 = true := by
 decide +kernel
def pointBounds26099 : List (Nat × Nat × Nat) := [(3424824320,103449626367303,103450008692879)]
theorem point_links_checked26099 : (cuts26099.take 1).map (fun c => (3424780289-1+2*2^9*c.k,103449462403840+c.lower,103449844729320+c.upper)) = pointBounds26099 := by
 decide +kernel
def cuts26100 : List PrefixCut := [⟨20,77828560,77828605⟩,
⟨125,481592688,481592954⟩,
⟨128,492276279,492276551⟩]
theorem checked26100 : checkPrefixCuts (2^48) 3424911361 9 Manual.Count131072.C026100.packed 128 cuts26100 = true := by
 decide +kernel
def pointBounds26100 : List (Nat × Nat × Nat) := [(3424931840,103450024802006,103450407127801),(3425039360,103450428566134,103450810892150)]
theorem point_links_checked26100 : (cuts26100.take 2).map (fun c => (3424911361-1+2*2^9*c.k,103449946973446+c.lower,103450329299196+c.upper)) = pointBounds26100 := by
 decide +kernel
def cuts26101 : List PrefixCut := [⟨102,391835089,391835315⟩,
⟨128,493818743,493819023⟩]
theorem checked26101 : checkPrefixCuts (2^48) 3425042433 9 Manual.Count131072.C026101.packed 128 cuts26101 = true := by
 decide +kernel
def pointBounds26101 : List (Nat × Nat × Nat) := [(3425146880,103450831084814,103451213411062)]
theorem point_links_checked26101 : (cuts26101.take 1).map (fun c => (3425042433-1+2*2^9*c.k,103450439249725+c.lower,103450821575747+c.upper)) = pointBounds26101 := by
 decide +kernel
def cuts26102 : List PrefixCut := [⟨79,299371959,299372130⟩,
⟨128,487883120,487883400⟩]
theorem checked26102 : checkPrefixCuts (2^48) 3425173505 9 Manual.Count131072.C026102.packed 128 cuts26102 = true := by
 decide +kernel
def pointBounds26102 : List (Nat × Nat × Nat) := [(3425254400,103451232440427,103451614766900)]
theorem point_links_checked26102 : (cuts26102.take 1).map (fun c => (3425173505-1+2*2^9*c.k,103450933068468+c.lower,103451315394770+c.upper)) = pointBounds26102 := by
 decide +kernel
def cuts26103 : List PrefixCut := [⟨56,214557510,214557630⟩,
⟨128,495917437,495917712⟩]
theorem checked26103 : checkPrefixCuts (2^48) 3425304577 9 Manual.Count131072.C026103.packed 128 cuts26103 = true := by
 decide +kernel
def pointBounds26103 : List (Nat × Nat × Nat) := [(3425361920,103451635509098,103452017835800)]
theorem point_links_checked26103 : (cuts26103.take 1).map (fun c => (3425304577-1+2*2^9*c.k,103451420951588+c.lower,103451803278170+c.upper)) = pointBounds26103 := by
 decide +kernel
def cuts26104 : List PrefixCut := [⟨33,128598545,128598617⟩,
⟨128,491461380,491461661⟩]
theorem checked26104 : checkPrefixCuts (2^48) 3425435649 9 Manual.Count131072.C026104.packed 128 cuts26104 = true := by
 decide +kernel
def pointBounds26104 : List (Nat × Nat × Nat) := [(3425469440,103452045467570,103452427794499)]
theorem point_links_checked26104 : (cuts26104.take 1).map (fun c => (3425435649-1+2*2^9*c.k,103451916869025+c.lower,103452299195882+c.upper)) = pointBounds26104 := by
 decide +kernel
def cuts26105 : List PrefixCut := [⟨10,39194484,39194507⟩,
⟨115,444279367,444279616⟩,
⟨128,493168059,493168338⟩]
theorem checked26105 : checkPrefixCuts (2^48) 3425566721 9 Manual.Count131072.C026105.packed 128 cuts26105 = true := by
 decide +kernel
def pointBounds26105 : List (Nat × Nat × Nat) := [(3425576960,103452447524889,103452829852050),(3425684480,103452852609772,103453234937159)]
theorem point_links_checked26105 : (cuts26105.take 2).map (fun c => (3425566721-1+2*2^9*c.k,103452408330405+c.lower,103452790657543+c.upper)) = pointBounds26105 := by
 decide +kernel
def cuts26106 : List PrefixCut := [⟨92,355526143,355526343⟩,
⟨128,496435709,496435990⟩]
theorem checked26106 : checkPrefixCuts (2^48) 3425697793 9 Manual.Count131072.C026106.packed 128 cuts26106 = true := by
 decide +kernel
def pointBounds26106 : List (Nat × Nat × Nat) := [(3425792000,103453257024607,103453639352224)]
theorem point_links_checked26106 : (cuts26106.take 1).map (fun c => (3425697793-1+2*2^9*c.k,103452901498464+c.lower,103453283825881+c.upper)) = pointBounds26106 := by
 decide +kernel
def cuts26107 : List PrefixCut := [⟨69,264971554,264971701⟩,
⟨128,486968270,486968542⟩]
theorem checked26107 : checkPrefixCuts (2^48) 3425828865 9 Manual.Count131072.C026107.packed 128 cuts26107 = true := by
 decide +kernel
def pointBounds26107 : List (Nat × Nat × Nat) := [(3425899520,103453662905727,103454045233572)]
theorem point_links_checked26107 : (cuts26107.take 1).map (fun c => (3425828865-1+2*2^9*c.k,103453397934173+c.lower,103453780261871+c.upper)) = pointBounds26107 := by
 decide +kernel
def cuts26108 : List PrefixCut := [⟨46,176723712,176723808⟩,
⟨128,490071570,490071838⟩]
theorem checked26108 : checkPrefixCuts (2^48) 3425959937 9 Manual.Count131072.C026108.packed 128 cuts26108 = true := by
 decide +kernel
def pointBounds26108 : List (Nat × Nat × Nat) := [(3426007040,103454061626155,103454443954221)]
theorem point_links_checked26108 : (cuts26108.take 1).map (fun c => (3425959937-1+2*2^9*c.k,103453884902443+c.lower,103454267230413+c.upper)) = pointBounds26108 := by
 decide +kernel
def cuts26109 : List PrefixCut := [⟨23,89714350,89714401⟩,
⟨128,483644807,483645075⟩]
theorem checked26109 : checkPrefixCuts (2^48) 3426091009 9 Manual.Count131072.C026109.packed 128 cuts26109 = true := by
 decide +kernel
def pointBounds26109 : List (Nat × Nat × Nat) := [(3426114560,103454464688363,103454847016652),(3426222080,103454858618820,103455240947326)]
theorem point_links_checked26109 : (cuts26109.take 2).map (fun c => (3426091009-1+2*2^9*c.k,103454374974013+c.lower,103454757302251+c.upper)) = pointBounds26109 := by
 decide +kernel
def cuts26110 : List PrefixCut := [⟨105,396875534,396875761⟩,
⟨128,486337193,486337470⟩]
theorem checked26110 : checkPrefixCuts (2^48) 3426222081 9 Manual.Count131072.C026110.packed 128 cuts26110 = true := by
 decide +kernel
def pointBounds26110 : List (Nat × Nat × Nat) := [(3426329600,103455255494354,103455637823087)]
theorem point_links_checked26110 : (cuts26110.take 1).map (fun c => (3426222081-1+2*2^9*c.k,103454858618820+c.lower,103455240947326+c.upper)) = pointBounds26110 := by
 decide +kernel
def cuts26111 : List PrefixCut := [⟨82,317834431,317834608⟩,
⟨128,493794215,493794488⟩]
theorem checked26111 : checkPrefixCuts (2^48) 3426353153 9 Manual.Count131072.C026111.packed 128 cuts26111 = true := by
 decide +kernel
def pointBounds26111 : List (Nat × Nat × Nat) := [(3426437120,103455662790444,103456045119404)]
theorem point_links_checked26111 : (cuts26111.take 1).map (fun c => (3426353153-1+2*2^9*c.k,103455344956013+c.lower,103455727284796+c.upper)) = pointBounds26111 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000190
