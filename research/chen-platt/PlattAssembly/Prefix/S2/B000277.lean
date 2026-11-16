import PlattAssemblyKernel
import PlattCertificates.Count131072.C018864
import PlattCertificates.Count131072.C018865
import PlattCertificates.Count131072.C018866
import PlattCertificates.Count131072.C018867
import PlattCertificates.Count131072.C018868
import PlattCertificates.Count131072.C018869
import PlattCertificates.Count131072.C018870
import PlattCertificates.Count131072.C018871
import PlattCertificates.Count131072.C018872
import PlattCertificates.Count131072.C018873
import PlattCertificates.Count131072.C018874
import PlattCertificates.Count131072.C018875
import PlattCertificates.Count131072.C018876
import PlattCertificates.Count131072.C018877
import PlattCertificates.Count131072.C018878
import PlattCertificates.Count131072.C018879
import PlattCertificates.Count131072.C018880
import PlattCertificates.Count131072.C018881
import PlattCertificates.Count131072.C018882
import PlattCertificates.Count131072.C018883
import PlattCertificates.Count131072.C018884
import PlattCertificates.Count131072.C018885
import PlattCertificates.Count131072.C018886
import PlattCertificates.Count131072.C018887
import PlattCertificates.Count131072.C018888
import PlattCertificates.Count131072.C018889
import PlattCertificates.Count131072.C018890
import PlattCertificates.Count131072.C018891
import PlattCertificates.Count131072.C018892
import PlattCertificates.Count131072.C018893
import PlattCertificates.Count131072.C018894
import PlattCertificates.Count131072.C018895
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000277
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18864 : List PrefixCut := [⟨2,11365947,11365954⟩,
⟨78,418487684,418487932⟩,
⟨128,688417563,688417972⟩]
theorem checked18864 : checkPrefixCuts (2^48) 2476474369 9 Manual.Count131072.C018864.packed 128 cuts18864 = true := by
 decide +kernel
def pointBounds18864 : List (Nat × Nat × Nat) := [(2476476416,99262003613138,99262383532396),(2476554240,99262410734875,99262790654374)]
theorem point_links_checked18864 : (cuts18864.take 2).map (fun c => (2476474369-1+2*2^9*c.k,99261992247191+c.lower,99262372166442+c.upper)) = pointBounds18864 := by
 decide +kernel
def cuts18865 : List PrefixCut := [⟨26,141156897,141156984⟩,
⟨102,548821261,548821587⟩,
⟨128,690426793,690427205⟩]
theorem checked18865 : checkPrefixCuts (2^48) 2476605441 9 Manual.Count131072.C018865.packed 128 cuts18865 = true := by
 decide +kernel
def pointBounds18865 : List (Nat × Nat × Nat) := [(2476632064,99262821821651,99263201741398),(2476709888,99263229486015,99263609406001)]
theorem point_links_checked18865 : (cuts18865.take 2).map (fun c => (2476605441-1+2*2^9*c.k,99262680664754+c.lower,99263060584414+c.upper)) = pointBounds18865 := by
 decide +kernel
def cuts18866 : List PrefixCut := [⟨50,263545791,263545953⟩,
⟨126,670729876,670730285⟩,
⟨128,681753104,681753520⟩]
theorem checked18866 : checkPrefixCuts (2^48) 2476736513 9 Manual.Count131072.C018866.packed 128 cuts18866 = true := by
 decide +kernel
def pointBounds18866 : List (Nat × Nat × Nat) := [(2476787712,99263634637338,99264014557572),(2476865536,99264041821423,99264421741904)]
theorem point_links_checked18866 : (cuts18866.take 2).map (fun c => (2476736513-1+2*2^9*c.k,99263371091547+c.lower,99263751011619+c.upper)) = pointBounds18866 := by
 decide +kernel
def cuts18867 : List PrefixCut := [⟨74,407171164,407171401⟩,
⟨128,696603896,696604305⟩]
theorem checked18867 : checkPrefixCuts (2^48) 2476867585 9 Manual.Count131072.C018867.packed 128 cuts18867 = true := by
 decide +kernel
def pointBounds18867 : List (Nat × Nat × Nat) := [(2476943360,99264460015815,99264839936540)]
theorem point_links_checked18867 : (cuts18867.take 1).map (fun c => (2476867585-1+2*2^9*c.k,99264052844651+c.lower,99264432765139+c.upper)) = pointBounds18867 := by
 decide +kernel
def cuts18868 : List PrefixCut := [⟨22,117498543,117498612⟩,
⟨98,524416957,524417272⟩,
⟨128,687703503,687703918⟩]
theorem checked18868 : checkPrefixCuts (2^48) 2476998657 9 Manual.Count131072.C018868.packed 128 cuts18868 = true := by
 decide +kernel
def pointBounds18868 : List (Nat × Nat × Nat) := [(2477021184,99264866947090,99265246868056),(2477099008,99265273865504,99265653786716)]
theorem point_links_checked18868 : (cuts18868.take 2).map (fun c => (2476998657-1+2*2^9*c.k,99264749448547+c.lower,99265129369444+c.upper)) = pointBounds18868 := by
 decide +kernel
def cuts18869 : List PrefixCut := [⟨46,255322939,255323088⟩,
⟨122,664715683,664716079⟩,
⟨128,695848543,695848959⟩]
theorem checked18869 : checkPrefixCuts (2^48) 2477129729 9 Manual.Count131072.C018869.packed 128 cuts18869 = true := by
 decide +kernel
def pointBounds18869 : List (Nat × Nat × Nat) := [(2477176832,99265692474989,99266072396450),(2477254656,99266101867733,99266481789441)]
theorem point_links_checked18869 : (cuts18869.take 2).map (fun c => (2477129729-1+2*2^9*c.k,99265437152050+c.lower,99265817073362+c.upper)) = pointBounds18869 := by
 decide +kernel
def cuts18870 : List PrefixCut := [⟨70,374951907,374952135⟩,
⟨128,686721864,686722274⟩]
theorem checked18870 : checkPrefixCuts (2^48) 2477260801 9 Manual.Count131072.C018870.packed 128 cuts18870 = true := by
 decide +kernel
def pointBounds18870 : List (Nat × Nat × Nat) := [(2477332480,99266507952500,99266887874456)]
theorem point_links_checked18870 : (cuts18870.take 1).map (fun c => (2477260801-1+2*2^9*c.k,99266133000593+c.lower,99266512922321+c.upper)) = pointBounds18870 := by
 decide +kernel
def cuts18871 : List PrefixCut := [⟨18,94188493,94188551⟩,
⟨94,501270244,501270540⟩,
⟨128,684072302,684072706⟩]
theorem checked18871 : checkPrefixCuts (2^48) 2477391873 9 Manual.Count131072.C018871.packed 128 cuts18871 = true := by
 decide +kernel
def pointBounds18871 : List (Nat × Nat × Nat) := [(2477410304,99266913910950,99267293833146),(2477488128,99267320992701,99267700915135)]
theorem point_links_checked18871 : (cuts18871.take 2).map (fun c => (2477391873-1+2*2^9*c.k,99266819722457+c.lower,99267199644595+c.upper)) = pointBounds18871 := by
 decide +kernel
def cuts18872 : List PrefixCut := [⟨42,226084740,226084874⟩,
⟨118,631550419,631550798⟩,
⟨128,685853915,685854326⟩]
theorem checked18872 : checkPrefixCuts (2^48) 2477522945 9 Manual.Count131072.C018872.packed 128 cuts18872 = true := by
 decide +kernel
def pointBounds18872 : List (Nat × Nat × Nat) := [(2477565952,99267729879499,99268109802175),(2477643776,99268135345178,99268515268099)]
theorem point_links_checked18872 : (cuts18872.take 2).map (fun c => (2477522945-1+2*2^9*c.k,99267503794759+c.lower,99267883717301+c.upper)) = pointBounds18872 := by
 decide +kernel
def cuts18873 : List PrefixCut := [⟨66,347059747,347059961⟩,
⟨128,684681464,684681879⟩]
theorem checked18873 : checkPrefixCuts (2^48) 2477654017 9 Manual.Count131072.C018873.packed 128 cuts18873 = true := by
 decide +kernel
def pointBounds18873 : List (Nat × Nat × Nat) := [(2477721600,99268536708421,99268916631588)]
theorem point_links_checked18873 : (cuts18873.take 1).map (fun c => (2477654017-1+2*2^9*c.k,99268189648674+c.lower,99268569571627+c.upper)) = pointBounds18873 := by
 decide +kernel
def cuts18874 : List PrefixCut := [⟨14,79064952,79065000⟩,
⟨90,489717986,489718279⟩,
⟨128,684532211,684532621⟩]
theorem checked18874 : checkPrefixCuts (2^48) 2477785089 9 Manual.Count131072.C018874.packed 128 cuts18874 = true := by
 decide +kernel
def pointBounds18874 : List (Nat × Nat × Nat) := [(2477799424,99268953395090,99269333318506),(2477877248,99269364048124,99269743971785)]
theorem point_links_checked18874 : (cuts18874.take 2).map (fun c => (2477785089-1+2*2^9*c.k,99268874330138+c.lower,99269254253506+c.upper)) = pointBounds18874 := by
 decide +kernel
def cuts18875 : List PrefixCut := [⟨38,202308234,202308358⟩,
⟨114,607710311,607710678⟩,
⟨128,685858655,685859067⟩]
theorem checked18875 : checkPrefixCuts (2^48) 2477916161 9 Manual.Count131072.C018875.packed 128 cuts18875 = true := by
 decide +kernel
def pointBounds18875 : List (Nat × Nat × Nat) := [(2477955072,99269761170583,99270141094485),(2478032896,99270166572660,99270546496805)]
theorem point_links_checked18875 : (cuts18875.take 2).map (fun c => (2477916161-1+2*2^9*c.k,99269558862349+c.lower,99269938786127+c.upper)) = pointBounds18875 := by
 decide +kernel
def cuts18876 : List PrefixCut := [⟨62,331102967,331103174⟩,
⟨128,683096421,683096835⟩]
theorem checked18876 : checkPrefixCuts (2^48) 2478047233 9 Manual.Count131072.C018876.packed 128 cuts18876 = true := by
 decide +kernel
def pointBounds18876 : List (Nat × Nat × Nat) := [(2478110720,99270575823971,99270955748368)]
theorem point_links_checked18876 : (cuts18876.take 1).map (fun c => (2478047233-1+2*2^9*c.k,99270244721004+c.lower,99270624645194+c.upper)) = pointBounds18876 := by
 decide +kernel
def cuts18877 : List PrefixCut := [⟨10,52701642,52701675⟩,
⟨86,462608691,462608968⟩,
⟨128,690669996,690670405⟩]
theorem checked18877 : checkPrefixCuts (2^48) 2478178305 9 Manual.Count131072.C018877.packed 128 cuts18877 = true := by
 decide +kernel
def pointBounds18877 : List (Nat × Nat × Nat) := [(2478188544,99270980519067,99271360443704),(2478266368,99271390426116,99271770350997)]
theorem point_links_checked18877 : (cuts18877.take 2).map (fun c => (2478178305-1+2*2^9*c.k,99270927817425+c.lower,99271307742029+c.upper)) = pointBounds18877 := by
 decide +kernel
def cuts18878 : List PrefixCut := [⟨34,183082200,183082309⟩,
⟨110,603185003,603185369⟩,
⟨128,700060024,700060448⟩]
theorem checked18878 : checkPrefixCuts (2^48) 2478309377 9 Manual.Count131072.C018878.packed 128 cuts18878 = true := by
 decide +kernel
def pointBounds18878 : List (Nat × Nat × Nat) := [(2478344192,99271801569621,99272181494743),(2478422016,99272221672424,99272601597803)]
theorem point_links_checked18878 : (cuts18878.take 2).map (fun c => (2478309377-1+2*2^9*c.k,99271618487421+c.lower,99271998412434+c.upper)) = pointBounds18878 := by
 decide +kernel
def cuts18879 : List PrefixCut := [⟨58,310494916,310495101⟩,
⟨128,688325664,688326076⟩]
theorem checked18879 : checkPrefixCuts (2^48) 2478440449 9 Manual.Count131072.C018879.packed 128 cuts18879 = true := by
 decide +kernel
def pointBounds18879 : List (Nat × Nat × Nat) := [(2478499840,99272629042361,99273008967983)]
theorem point_links_checked18879 : (cuts18879.take 1).map (fun c => (2478440449-1+2*2^9*c.k,99272318547445+c.lower,99272698472882+c.upper)) = pointBounds18879 := by
 decide +kernel
def cuts18880 : List PrefixCut := [⟨6,32138391,32138410⟩,
⟨82,445274321,445274590⟩,
⟨128,694648622,694649035⟩]
theorem checked18880 : checkPrefixCuts (2^48) 2478571521 9 Manual.Count131072.C018880.packed 128 cuts18880 = true := by
 decide +kernel
def pointBounds18880 : List (Nat × Nat × Nat) := [(2478577664,99273039011500,99273418937368),(2478655488,99273452147430,99273832073548)]
theorem point_links_checked18880 : (cuts18880.take 2).map (fun c => (2478571521-1+2*2^9*c.k,99273006873109+c.lower,99273386798958+c.upper)) = pointBounds18880 := by
 decide +kernel
def cuts18881 : List PrefixCut := [⟨30,164543569,164543669⟩,
⟨106,570953933,570954281⟩,
⟨128,687912354,687912773⟩]
theorem checked18881 : checkPrefixCuts (2^48) 2478702593 9 Manual.Count131072.C018881.packed 128 cuts18881 = true := by
 decide +kernel
def pointBounds18881 : List (Nat × Nat × Nat) := [(2478733312,99273866065300,99274245991662),(2478811136,99274272475664,99274652402274)]
theorem point_links_checked18881 : (cuts18881.take 2).map (fun c => (2478702593-1+2*2^9*c.k,99273701521731+c.lower,99274081447993+c.upper)) = pointBounds18881 := by
 decide +kernel
def cuts18882 : List PrefixCut := [⟨54,292505041,292505216⟩,
⟨128,695597154,695597572⟩]
theorem checked18882 : checkPrefixCuts (2^48) 2478833665 9 Manual.Count131072.C018882.packed 128 cuts18882 = true := by
 decide +kernel
def pointBounds18882 : List (Nat × Nat × Nat) := [(2478888960,99274681939126,99275061865982)]
theorem point_links_checked18882 : (cuts18882.take 1).map (fun c => (2478833665-1+2*2^9*c.k,99274389434085+c.lower,99274769360766+c.upper)) = pointBounds18882 := by
 decide +kernel
def cuts18883 : List PrefixCut := [⟨2,11468075,11468081⟩,
⟨78,422835951,422836200⟩,
⟨128,692608212,692608624⟩]
theorem checked18883 : checkPrefixCuts (2^48) 2478964737 9 Manual.Count131072.C018883.packed 128 cuts18883 = true := by
 decide +kernel
def pointBounds18883 : List (Nat × Nat × Nat) := [(2478966784,99275096499314,99275476426419),(2479044608,99275507867190,99275887794538)]
theorem point_links_checked18883 : (cuts18883.take 2).map (fun c => (2478964737-1+2*2^9*c.k,99275085031239+c.lower,99275464958338+c.upper)) = pointBounds18883 := by
 decide +kernel
def cuts18884 : List PrefixCut := [⟨26,137722484,137722570⟩,
⟨102,552584265,552584594⟩,
⟨128,689846810,689847223⟩]
theorem checked18884 : checkPrefixCuts (2^48) 2479095809 9 Manual.Count131072.C018884.packed 128 cuts18884 = true := by
 decide +kernel
def pointBounds18884 : List (Nat × Nat × Nat) := [(2479122432,99275915361935,99276295289532),(2479200256,99276330223716,99276710151556)]
theorem point_links_checked18884 : (cuts18884.take 2).map (fun c => (2479095809-1+2*2^9*c.k,99275777639451+c.lower,99276157566962+c.upper)) = pointBounds18884 := by
 decide +kernel
def cuts18885 : List PrefixCut := [⟨50,263621668,263621827⟩,
⟨126,671645616,671646019⟩,
⟨128,681181916,681182325⟩]
theorem checked18885 : checkPrefixCuts (2^48) 2479226881 9 Manual.Count131072.C018885.packed 128 cuts18885 = true := by
 decide +kernel
def pointBounds18885 : List (Nat × Nat × Nat) := [(2479278080,99276731107929,99277111036012),(2479355904,99277139131877,99277519060204)]
theorem point_links_checked18885 : (cuts18885.take 2).map (fun c => (2479226881-1+2*2^9*c.k,99276467486261+c.lower,99276847414185+c.upper)) = pointBounds18885 := by
 decide +kernel
def cuts18886 : List PrefixCut := [⟨74,392003905,392004139⟩,
⟨128,682848803,682849208⟩]
theorem checked18886 : checkPrefixCuts (2^48) 2479357953 9 Manual.Count131072.C018886.packed 128 cuts18886 = true := by
 decide +kernel
def pointBounds18886 : List (Nat × Nat × Nat) := [(2479433728,99277540672082,99277920600649)]
theorem point_links_checked18886 : (cuts18886.take 1).map (fun c => (2479357953-1+2*2^9*c.k,99277148668177+c.lower,99277528596510+c.upper)) = pointBounds18886 := by
 decide +kernel
def cuts18887 : List PrefixCut := [⟨22,117834609,117834682⟩,
⟨98,529112214,529112525⟩,
⟨128,694845624,694846036⟩]
theorem checked18887 : checkPrefixCuts (2^48) 2479489025 9 Manual.Count131072.C018887.packed 128 cuts18887 = true := by
 decide +kernel
def pointBounds18887 : List (Nat × Nat × Nat) := [(2479511552,99277949351589,99278329280400),(2479589376,99278360629194,99278740558243)]
theorem point_links_checked18887 : (cuts18887.take 2).map (fun c => (2479489025-1+2*2^9*c.k,99277831516980+c.lower,99278211445718+c.upper)) = pointBounds18887 := by
 decide +kernel
def cuts18888 : List PrefixCut := [⟨46,241331311,241331458⟩,
⟨122,647929128,647929519⟩,
⟨128,681414423,681414834⟩]
theorem checked18888 : checkPrefixCuts (2^48) 2479620097 9 Manual.Count131072.C018888.packed 128 cuts18888 = true := by
 decide +kernel
def pointBounds18888 : List (Nat × Nat × Nat) := [(2479667200,99278767693915,99279147623212),(2479745024,99279174291732,99279554221273)]
theorem point_links_checked18888 : (cuts18888.take 2).map (fun c => (2479620097-1+2*2^9*c.k,99278526362604+c.lower,99278906291754+c.upper)) = pointBounds18888 := by
 decide +kernel
def cuts18889 : List PrefixCut := [⟨70,379683254,379683483⟩,
⟨128,686145896,686146311⟩]
theorem checked18889 : checkPrefixCuts (2^48) 2479751169 9 Manual.Count131072.C018889.packed 128 cuts18889 = true := by
 decide +kernel
def pointBounds18889 : List (Nat × Nat × Nat) := [(2479822848,99279587460281,99279967390071)]
theorem point_links_checked18889 : (cuts18889.take 1).map (fun c => (2479751169-1+2*2^9*c.k,99279207777027+c.lower,99279587706588+c.upper)) = pointBounds18889 := by
 decide +kernel
def cuts18890 : List PrefixCut := [⟨18,93866906,93866963⟩,
⟨94,491232904,491233206⟩,
⟨128,666928015,666928424⟩]
theorem checked18890 : checkPrefixCuts (2^48) 2479882241 9 Manual.Count131072.C018890.packed 128 cuts18890 = true := by
 decide +kernel
def pointBounds18890 : List (Nat × Nat × Nat) := [(2479900672,99279987789829,99280367719862),(2479978496,99280385155827,99280765086105)]
theorem point_links_checked18890 : (cuts18890.take 2).map (fun c => (2479882241-1+2*2^9*c.k,99279893922923+c.lower,99280273852899+c.upper)) = pointBounds18890 := by
 decide +kernel
def cuts18891 : List PrefixCut := [⟨42,231986551,231986690⟩,
⟨118,641244377,641244762⟩,
⟨128,692315579,692315997⟩]
theorem checked18891 : checkPrefixCuts (2^48) 2480013313 9 Manual.Count131072.C018891.packed 128 cuts18891 = true := by
 decide +kernel
def pointBounds18891 : List (Nat × Nat × Nat) := [(2480056320,99280792837489,99281172768013),(2480134144,99281202095315,99281582026085)]
theorem point_links_checked18891 : (cuts18891.take 2).map (fun c => (2480013313-1+2*2^9*c.k,99280560850938+c.lower,99280940781323+c.upper)) = pointBounds18891 := by
 decide +kernel
def cuts18892 : List PrefixCut := [⟨66,360670512,360670726⟩,
⟨128,689895667,689896078⟩]
theorem checked18892 : checkPrefixCuts (2^48) 2480144385 9 Manual.Count131072.C018892.packed 128 cuts18892 = true := by
 decide +kernel
def pointBounds18892 : List (Nat × Nat × Nat) := [(2480211968,99281613837029,99281993768046)]
theorem point_links_checked18892 : (cuts18892.take 1).map (fun c => (2480144385-1+2*2^9*c.k,99281253166517+c.lower,99281633097320+c.upper)) = pointBounds18892 := by
 decide +kernel
def cuts18893 : List PrefixCut := [⟨14,77056319,77056367⟩,
⟨90,492857638,492857938⟩,
⟨128,700753417,700753842⟩]
theorem checked18893 : checkPrefixCuts (2^48) 2480275457 9 Manual.Count131072.C018893.packed 128 cuts18893 = true := by
 decide +kernel
def pointBounds18893 : List (Nat × Nat × Nat) := [(2480289792,99282020118503,99282400049765),(2480367616,99282435919822,99282815851336)]
theorem point_links_checked18893 : (cuts18893.take 2).map (fun c => (2480275457-1+2*2^9*c.k,99281943062184+c.lower,99282322993398+c.upper)) = pointBounds18893 := by
 decide +kernel
def cuts18894 : List PrefixCut := [⟨38,208119448,208119572⟩,
⟨114,613795369,613795737⟩,
⟨128,690276627,690277040⟩]
theorem checked18894 : checkPrefixCuts (2^48) 2480406529 9 Manual.Count131072.C018894.packed 128 cuts18894 = true := by
 decide +kernel
def pointBounds18894 : List (Nat × Nat × Nat) := [(2480445440,99282851935049,99283231866812),(2480523264,99283257610970,99283637542977)]
theorem point_links_checked18894 : (cuts18894.take 2).map (fun c => (2480406529-1+2*2^9*c.k,99282643815601+c.lower,99283023747240+c.upper)) = pointBounds18894 := by
 decide +kernel
def cuts18895 : List PrefixCut := [⟨62,337125015,337125209⟩,
⟨128,692623083,692623488⟩]
theorem checked18895 : checkPrefixCuts (2^48) 2480537601 9 Manual.Count131072.C018895.packed 128 cuts18895 = true := by
 decide +kernel
def pointBounds18895 : List (Nat × Nat × Nat) := [(2480601088,99283671217243,99284051149489)]
theorem point_links_checked18895 : (cuts18895.take 1).map (fun c => (2480537601-1+2*2^9*c.k,99283334092228+c.lower,99283714024280+c.upper)) = pointBounds18895 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000277
