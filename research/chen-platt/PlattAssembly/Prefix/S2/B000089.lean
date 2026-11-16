import PlattAssemblyKernel
import PlattCertificates.Count131072.C012848
import PlattCertificates.Count131072.C012849
import PlattCertificates.Count131072.C012850
import PlattCertificates.Count131072.C012851
import PlattCertificates.Count131072.C012852
import PlattCertificates.Count131072.C012853
import PlattCertificates.Count131072.C012854
import PlattCertificates.Count131072.C012855
import PlattCertificates.Count131072.C012856
import PlattCertificates.Count131072.C012857
import PlattCertificates.Count131072.C012858
import PlattCertificates.Count131072.C012859
import PlattCertificates.Count131072.C012860
import PlattCertificates.Count131072.C012861
import PlattCertificates.Count131072.C012862
import PlattCertificates.Count131072.C012863
import PlattCertificates.Count131072.C012864
import PlattCertificates.Count131072.C012865
import PlattCertificates.Count131072.C012866
import PlattCertificates.Count131072.C012867
import PlattCertificates.Count131072.C012868
import PlattCertificates.Count131072.C012869
import PlattCertificates.Count131072.C012870
import PlattCertificates.Count131072.C012871
import PlattCertificates.Count131072.C012872
import PlattCertificates.Count131072.C012873
import PlattCertificates.Count131072.C012874
import PlattCertificates.Count131072.C012875
import PlattCertificates.Count131072.C012876
import PlattCertificates.Count131072.C012877
import PlattCertificates.Count131072.C012878
import PlattCertificates.Count131072.C012879
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000089
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12848 : List PrefixCut := [⟨10,78541799,78541857⟩,
⟨62,505427656,505428025⟩,
⟨114,920461030,920461703⟩,
⟨128,1032346034,1032346787⟩]
theorem checked12848 : checkPrefixCuts (2^48) 1687945217 9 Manual.Count131072.C012848.packed 128 cuts12848 = true := by
 decide +kernel
def pointBounds12848 : List (Nat × Nat × Nat) := [(1687955456,94229190599072,94229567210924),(1688008704,94229617484929,94229994097092),(1688061952,94230032518303,94230409130770)]
theorem point_links_checked12848 : (cuts12848.take 3).map (fun c => (1687945217-1+2*2^9*c.k,94229112057273+c.lower,94229488669067+c.upper)) = pointBounds12848 := by
 decide +kernel
def cuts12849 : List PrefixCut := [⟨38,306970262,306970493⟩,
⟨90,725979158,725979694⟩,
⟨128,1032765997,1032766752⟩]
theorem checked12849 : checkPrefixCuts (2^48) 1688076289 9 Manual.Count131072.C012849.packed 128 cuts12849 = true := by
 decide +kernel
def pointBounds12849 : List (Nat × Nat × Nat) := [(1688115200,94230451373569,94230827986347),(1688168448,94230870382465,94231246995548)]
theorem point_links_checked12849 : (cuts12849.take 2).map (fun c => (1688076289-1+2*2^9*c.k,94230144403307+c.lower,94230521015854+c.upper)) = pointBounds12849 := by
 decide +kernel
def cuts12850 : List PrefixCut := [⟨14,115043245,115043329⟩,
⟨66,532358517,532358903⟩,
⟨118,951161005,951161694⟩,
⟨128,1036020268,1036021017⟩]
theorem checked12850 : checkPrefixCuts (2^48) 1688207361 9 Manual.Count131072.C012850.packed 128 cuts12850 = true := by
 decide +kernel
def pointBounds12850 : List (Nat × Nat × Nat) := [(1688221696,94231292212549,94231668825935),(1688274944,94231709527821,94232086141509),(1688328192,94232128330309,94232504944300)]
theorem point_links_checked12850 : (cuts12850.take 3).map (fun c => (1688207361-1+2*2^9*c.k,94231177169304+c.lower,94231553782606+c.upper)) = pointBounds12850 := by
 decide +kernel
def cuts12851 : List PrefixCut := [⟨42,337931203,337931452⟩,
⟨94,755540277,755540830⟩,
⟨128,1040107211,1040107970⟩]
theorem checked12851 : checkPrefixCuts (2^48) 1688338433 9 Manual.Count131072.C012851.packed 128 cuts12851 = true := by
 decide +kernel
def pointBounds12851 : List (Nat × Nat × Nat) := [(1688381440,94232551120775,94232927735075),(1688434688,94232968729849,94233345344453)]
theorem point_links_checked12851 : (cuts12851.take 2).map (fun c => (1688338433-1+2*2^9*c.k,94232213189572+c.lower,94232589803623+c.upper)) = pointBounds12851 := by
 decide +kernel
def cuts12852 : List PrefixCut := [⟨18,142197869,142197970⟩,
⟨70,556613391,556613796⟩,
⟨122,991852539,991853265⟩,
⟨128,1040193081,1040193841⟩]
theorem checked12852 : checkPrefixCuts (2^48) 1688469505 9 Manual.Count131072.C012852.packed 128 cuts12852 = true := by
 decide +kernel
def pointBounds12852 : List (Nat × Nat × Nat) := [(1688487936,94233395494652,94233772109563),(1688541184,94233809910174,94234186525389),(1688594432,94234245149322,94234621764858)]
theorem point_links_checked12852 : (cuts12852.take 3).map (fun c => (1688469505-1+2*2^9*c.k,94233253296783+c.lower,94233629911593+c.upper)) = pointBounds12852 := by
 decide +kernel
def cuts12853 : List PrefixCut := [⟨46,375383402,375383672⟩,
⟨98,792759885,792760463⟩,
⟨128,1034612249,1034613005⟩]
theorem checked12853 : checkPrefixCuts (2^48) 1688600577 9 Manual.Count131072.C012853.packed 128 cuts12853 = true := by
 decide +kernel
def pointBounds12853 : List (Nat × Nat × Nat) := [(1688647680,94234668873266,94235045489106),(1688700928,94235086249749,94235462865897)]
theorem point_links_checked12853 : (cuts12853.take 2).map (fun c => (1688600577-1+2*2^9*c.k,94234293489864+c.lower,94234670105434+c.upper)) = pointBounds12853 := by
 decide +kernel
def cuts12854 : List PrefixCut := [⟨22,172844214,172844341⟩,
⟨74,585194237,585194666⟩,
⟨126,1007531284,1007532025⟩,
⟨128,1022197843,1022198595⟩]
theorem checked12854 : checkPrefixCuts (2^48) 1688731649 9 Manual.Count131072.C012854.packed 128 cuts12854 = true := by
 decide +kernel
def pointBounds12854 : List (Nat × Nat × Nat) := [(1688754176,94235500946327,94235877562780),(1688807424,94235913296350,94236289913105),(1688860672,94236335633397,94236712250464)]
theorem point_links_checked12854 : (cuts12854.take 3).map (fun c => (1688731649-1+2*2^9*c.k,94235328102113+c.lower,94235704718439+c.upper)) = pointBounds12854 := by
 decide +kernel
def cuts12855 : List PrefixCut := [⟨50,398324165,398324465⟩,
⟨102,803635628,803636228⟩,
⟨128,1010619589,1010620341⟩]
theorem checked12855 : checkPrefixCuts (2^48) 1688862721 9 Manual.Count131072.C012855.packed 128 cuts12855 = true := by
 decide +kernel
def pointBounds12855 : List (Nat × Nat × Nat) := [(1688913920,94236748624121,94237125241499),(1688967168,94237153935584,94237530553262)]
theorem point_links_checked12855 : (cuts12855.take 2).map (fun c => (1688862721-1+2*2^9*c.k,94236350299956+c.lower,94236726917034+c.upper)) = pointBounds12855 := by
 decide +kernel
def cuts12856 : List PrefixCut := [⟨26,211646867,211647025⟩,
⟨78,628931309,628931772⟩,
⟨128,1025705977,1025706729⟩]
theorem checked12856 : checkPrefixCuts (2^48) 1688993793 9 Manual.Count131072.C012856.packed 128 cuts12856 = true := by
 decide +kernel
def pointBounds12856 : List (Nat × Nat × Nat) := [(1689020416,94237572566412,94237949184400),(1689073664,94237989850854,94238366469147)]
theorem point_links_checked12856 : (cuts12856.take 2).map (fun c => (1688993793-1+2*2^9*c.k,94237360919545+c.lower,94237737537375+c.upper)) = pointBounds12856 := by
 decide +kernel
def cuts12857 : List PrefixCut := [⟨2,18163692,18163706⟩,
⟨54,436921556,436921877⟩,
⟨106,856665985,856666612⟩,
⟨128,1028125861,1028126614⟩]
theorem checked12857 : checkPrefixCuts (2^48) 1689124865 9 Manual.Count131072.C012857.packed 128 cuts12857 = true := by
 decide +kernel
def pointBounds12857 : List (Nat × Nat × Nat) := [(1689126912,94238404789214,94238781407810),(1689180160,94238823547078,94239200165981),(1689233408,94239243291507,94239619910716)]
theorem point_links_checked12857 : (cuts12857.take 3).map (fun c => (1689124865-1+2*2^9*c.k,94238386625522+c.lower,94238763244104+c.upper)) = pointBounds12857 := by
 decide +kernel
def cuts12858 : List PrefixCut := [⟨30,243939065,243939245⟩,
⟨82,656325724,656326209⟩,
⟨128,1036376603,1036377366⟩]
theorem checked12858 : checkPrefixCuts (2^48) 1689255937 9 Manual.Count131072.C012858.packed 128 cuts12858 = true := by
 decide +kernel
def pointBounds12858 : List (Nat × Nat × Nat) := [(1689286656,94239658690448,94240035309963),(1689339904,94240071077107,94240447696927)]
theorem point_links_checked12858 : (cuts12858.take 2).map (fun c => (1689255937-1+2*2^9*c.k,94239414751383+c.lower,94239791370718+c.upper)) = pointBounds12858 := by
 decide +kernel
def cuts12859 : List PrefixCut := [⟨6,47818017,47818054⟩,
⟨58,462677880,462678220⟩,
⟨110,886521373,886522024⟩,
⟨128,1038795243,1038796006⟩]
theorem checked12859 : checkPrefixCuts (2^48) 1689387009 9 Manual.Count131072.C012859.packed 128 cuts12859 = true := by
 decide +kernel
def pointBounds12859 : List (Nat × Nat × Nat) := [(1689393152,94240498946003,94240875566138),(1689446400,94240913805866,94241290426304),(1689499648,94241337649359,94241714270108)]
theorem point_links_checked12859 : (cuts12859.take 3).map (fun c => (1689387009-1+2*2^9*c.k,94240451127986+c.lower,94240827748084+c.upper)) = pointBounds12859 := by
 decide +kernel
def cuts12860 : List PrefixCut := [⟨34,275554650,275554849⟩,
⟨86,691041693,691042199⟩,
⟨128,1025221036,1025221788⟩]
theorem checked12860 : checkPrefixCuts (2^48) 1689518081 9 Manual.Count131072.C012860.packed 128 cuts12860 = true := by
 decide +kernel
def pointBounds12860 : List (Nat × Nat × Nat) := [(1689552896,94241765477879,94242142098939),(1689606144,94242180964922,94242557586289)]
theorem point_links_checked12860 : (cuts12860.take 2).map (fun c => (1689518081-1+2*2^9*c.k,94241489923229+c.lower,94241866544090+c.upper)) = pointBounds12860 := by
 decide +kernel
def cuts12861 : List PrefixCut := [⟨10,79628713,79628771⟩,
⟨62,496588676,496589037⟩,
⟨114,913368990,913369656⟩,
⟨128,1022642548,1022643294⟩]
theorem checked12861 : checkPrefixCuts (2^48) 1689649153 9 Manual.Count131072.C012861.packed 128 cuts12861 = true := by
 decide +kernel
def pointBounds12861 : List (Nat × Nat × Nat) := [(1689659392,94242594772978,94242971394649),(1689712640,94243011732941,94243388354915),(1689765888,94243428513255,94243805135534)]
theorem point_links_checked12861 : (cuts12861.take 3).map (fun c => (1689649153-1+2*2^9*c.k,94242515144265+c.lower,94242891765878+c.upper)) = pointBounds12861 := by
 decide +kernel
def cuts12862 : List PrefixCut := [⟨38,310158779,310159005⟩,
⟨90,726246552,726247082⟩,
⟨128,1032057742,1032058495⟩]
theorem checked12862 : checkPrefixCuts (2^48) 1689780225 9 Manual.Count131072.C012862.packed 128 cuts12862 = true := by
 decide +kernel
def pointBounds12862 : List (Nat × Nat × Nat) := [(1689819136,94243847945592,94244224568177),(1689872384,94244264033365,94244640656254)]
theorem point_links_checked12862 : (cuts12862.take 2).map (fun c => (1689780225-1+2*2^9*c.k,94243537786813+c.lower,94243914409172+c.upper)) = pointBounds12862 := by
 decide +kernel
def cuts12863 : List PrefixCut := [⟨14,114760667,114760753⟩,
⟨66,531488429,531488816⟩,
⟨118,943872826,943873516⟩,
⟨128,1021817996,1021818742⟩]
theorem checked12863 : checkPrefixCuts (2^48) 1689911297 9 Manual.Count131072.C012863.packed 128 cuts12863 = true := by
 decide +kernel
def pointBounds12863 : List (Nat × Nat × Nat) := [(1689925632,94244684605222,94245061228420),(1689978880,94245101332984,94245477956483),(1690032128,94245513717381,94245890341183)]
theorem point_links_checked12863 : (cuts12863.take 3).map (fun c => (1689911297-1+2*2^9*c.k,94244569844555+c.lower,94244946467667+c.upper)) = pointBounds12863 := by
 decide +kernel
def cuts12864 : List PrefixCut := [⟨42,334426182,334426424⟩,
⟨94,748949485,748950029⟩,
⟨128,1023237235,1023237979⟩]
theorem checked12864 : checkPrefixCuts (2^48) 1690042369 9 Manual.Count131072.C012864.packed 128 cuts12864 = true := by
 decide +kernel
def pointBounds12864 : List (Nat × Nat × Nat) := [(1690085376,94245926088733,94246302712833),(1690138624,94246340612036,94246717236438)]
theorem point_links_checked12864 : (cuts12864.take 2).map (fun c => (1690042369-1+2*2^9*c.k,94245591662551+c.lower,94245968286409+c.upper)) = pointBounds12864 := by
 decide +kernel
def cuts12865 : List PrefixCut := [⟨18,148382862,148382967⟩,
⟨70,562047485,562047891⟩,
⟨122,977031348,977032056⟩,
⟨128,1025822730,1025823473⟩]
theorem checked12865 : checkPrefixCuts (2^48) 1690173441 9 Manual.Count131072.C012865.packed 128 cuts12865 = true := by
 decide +kernel
def pointBounds12865 : List (Nat × Nat × Nat) := [(1690191872,94246763282648,94247139907355),(1690245120,94247176947271,94247553572279),(1690298368,94247591931134,94247968556444)]
theorem point_links_checked12865 : (cuts12865.take 3).map (fun c => (1690173441-1+2*2^9*c.k,94246614899786+c.lower,94246991524388+c.upper)) = pointBounds12865 := by
 decide +kernel
def cuts12866 : List PrefixCut := [⟨46,376670135,376670410⟩,
⟨98,796123690,796124268⟩,
⟨128,1037565731,1037566483⟩]
theorem checked12866 : checkPrefixCuts (2^48) 1690304513 9 Manual.Count131072.C012866.packed 128 cuts12866 = true := by
 decide +kernel
def pointBounds12866 : List (Nat × Nat × Nat) := [(1690351616,94248017392651,94248394018271),(1690404864,94248436846206,94248813472129)]
theorem point_links_checked12866 : (cuts12866.take 2).map (fun c => (1690304513-1+2*2^9*c.k,94247640722516+c.lower,94248017347861+c.upper)) = pointBounds12866 := by
 decide +kernel
def cuts12867 : List PrefixCut := [⟨22,183326557,183326686⟩,
⟨74,595594143,595594573⟩,
⟨126,1020003048,1020003787⟩,
⟨128,1035487311,1035488062⟩]
theorem checked12867 : checkPrefixCuts (2^48) 1690435585 9 Manual.Count131072.C012867.packed 128 cuts12867 = true := by
 decide +kernel
def pointBounds12867 : List (Nat × Nat × Nat) := [(1690458112,94248861614804,94249238241030),(1690511360,94249273882390,94249650508917),(1690564608,94249698291295,94250074918131)]
theorem point_links_checked12867 : (cuts12867.take 3).map (fun c => (1690435585-1+2*2^9*c.k,94248678288247+c.lower,94249054914344+c.upper)) = pointBounds12867 := by
 decide +kernel
def cuts12868 : List PrefixCut := [⟨50,406580425,406580718⟩,
⟨102,821472826,821473427⟩,
⟨128,1028581122,1028581877⟩]
theorem checked12868 : checkPrefixCuts (2^48) 1690566657 9 Manual.Count131072.C012868.packed 128 cuts12868 = true := by
 decide +kernel
def pointBounds12868 : List (Nat × Nat × Nat) := [(1690617856,94250120355983,94250496983124),(1690671104,94250535248384,94250911875833)]
theorem point_links_checked12868 : (cuts12868.take 2).map (fun c => (1690566657-1+2*2^9*c.k,94249713775558+c.lower,94250090402406+c.upper)) = pointBounds12868 := by
 decide +kernel
def cuts12869 : List PrefixCut := [⟨26,205273728,205273878⟩,
⟨78,621305155,621305610⟩,
⟨128,1023839345,1023840095⟩]
theorem checked12869 : checkPrefixCuts (2^48) 1690697729 9 Manual.Count131072.C012869.packed 128 cuts12869 = true := by
 decide +kernel
def pointBounds12869 : List (Nat × Nat × Nat) := [(1690724352,94250947630408,94251324258161),(1690777600,94251363661835,94251740289893)]
theorem point_links_checked12869 : (cuts12869.take 2).map (fun c => (1690697729-1+2*2^9*c.k,94250742356680+c.lower,94251118984283+c.upper)) = pointBounds12869 := by
 decide +kernel
def cuts12870 : List PrefixCut := [⟨2,15315372,15315383⟩,
⟨54,435149435,435149750⟩,
⟨106,847313077,847313698⟩,
⟨128,1022761650,1022762397⟩]
theorem checked12870 : checkPrefixCuts (2^48) 1690828801 9 Manual.Count131072.C012870.packed 128 cuts12870 = true := by
 decide +kernel
def pointBounds12870 : List (Nat × Nat × Nat) := [(1690830848,94251781511397,94252158139761),(1690884096,94252201345460,94252577974128),(1690937344,94252613509102,94252990138076)]
theorem point_links_checked12870 : (cuts12870.take 3).map (fun c => (1690828801-1+2*2^9*c.k,94251766196025+c.lower,94252142824378+c.upper)) = pointBounds12870 := by
 decide +kernel
def cuts12871 : List PrefixCut := [⟨30,246689503,246689678⟩,
⟨82,672975650,672976136⟩,
⟨128,1034500839,1034501589⟩]
theorem checked12871 : checkPrefixCuts (2^48) 1690959873 9 Manual.Count131072.C012871.packed 128 cuts12871 = true := by
 decide +kernel
def pointBounds12871 : List (Nat × Nat × Nat) := [(1690990592,94253035647178,94253412276453),(1691043840,94253461933325,94253838562911)]
theorem point_links_checked12871 : (cuts12871.take 2).map (fun c => (1690959873-1+2*2^9*c.k,94252788957675+c.lower,94253165586775+c.upper)) = pointBounds12871 := by
 decide +kernel
def cuts12872 : List PrefixCut := [⟨6,48269175,48269210⟩,
⟨58,466039822,466040164⟩,
⟨110,884795903,884796550⟩,
⟨128,1025765274,1025766025⟩]
theorem checked12872 : checkPrefixCuts (2^48) 1691090945 9 Manual.Count131072.C012872.packed 128 cuts12872 = true := by
 decide +kernel
def pointBounds12872 : List (Nat × Nat × Nat) := [(1691097088,94253871727689,94254248357574),(1691150336,94254289498336,94254666128528),(1691203584,94254708254417,94255084884914)]
theorem point_links_checked12872 : (cuts12872.take 3).map (fun c => (1691090945-1+2*2^9*c.k,94253823458514+c.lower,94254200088364+c.upper)) = pointBounds12872 := by
 decide +kernel
def cuts12873 : List PrefixCut := [⟨34,267454792,267454994⟩,
⟨86,691510302,691510816⟩,
⟨128,1024853684,1024854446⟩]
theorem checked12873 : checkPrefixCuts (2^48) 1691222017 9 Manual.Count131072.C012873.packed 128 cuts12873 = true := by
 decide +kernel
def pointBounds12873 : List (Nat × Nat × Nat) := [(1691256832,94255116678580,94255493309383),(1691310080,94255540734090,94255917365205)]
theorem point_links_checked12873 : (cuts12873.take 2).map (fun c => (1691222017-1+2*2^9*c.k,94254849223788+c.lower,94255225854389+c.upper)) = pointBounds12873 := by
 decide +kernel
def cuts12874 : List PrefixCut := [⟨10,77884292,77884348⟩,
⟨62,486769062,486769420⟩,
⟨114,910618093,910618750⟩,
⟨128,1020114404,1020115142⟩]
theorem checked12874 : checkPrefixCuts (2^48) 1691353089 9 Manual.Count131072.C012874.packed 128 cuts12874 = true := by
 decide +kernel
def pointBounds12874 : List (Nat × Nat × Nat) := [(1691363328,94255951961764,94256328593183),(1691416576,94256360846534,94256737478255),(1691469824,94256784695565,94257161327585)]
theorem point_links_checked12874 : (cuts12874.take 3).map (fun c => (1691353089-1+2*2^9*c.k,94255874077472+c.lower,94256250708835+c.upper)) = pointBounds12874 := by
 decide +kernel
def cuts12875 : List PrefixCut := [⟨38,303190176,303190396⟩,
⟨90,721521286,721521814⟩,
⟨128,1027690064,1027690816⟩]
theorem checked12875 : checkPrefixCuts (2^48) 1691484161 9 Manual.Count131072.C012875.packed 128 cuts12875 = true := by
 decide +kernel
def pointBounds12875 : List (Nat × Nat × Nat) := [(1691523072,94257197382052,94257574014373),(1691576320,94257615713162,94257992345791)]
theorem point_links_checked12875 : (cuts12875.take 2).map (fun c => (1691484161-1+2*2^9*c.k,94256894191876+c.lower,94257270823977+c.upper)) = pointBounds12875 := by
 decide +kernel
def cuts12876 : List PrefixCut := [⟨14,113813107,113813190⟩,
⟨66,530287552,530287941⟩,
⟨118,945584172,945584864⟩,
⟨128,1026944852,1026945601⟩]
theorem checked12876 : checkPrefixCuts (2^48) 1691615233 9 Manual.Count131072.C012876.packed 128 cuts12876 = true := by
 decide +kernel
def pointBounds12876 : List (Nat × Nat × Nat) := [(1691629568,94258035695047,94258412327983),(1691682816,94258452169492,94258828802734),(1691736064,94258867466112,94259244099657)]
theorem point_links_checked12876 : (cuts12876.take 3).map (fun c => (1691615233-1+2*2^9*c.k,94257921881940+c.lower,94258298514793+c.upper)) = pointBounds12876 := by
 decide +kernel
def cuts12877 : List PrefixCut := [⟨42,332924661,332924903⟩,
⟨94,747862336,747862887⟩,
⟨128,1017548224,1017548971⟩]
theorem checked12877 : checkPrefixCuts (2^48) 1691746305 9 Manual.Count131072.C012877.packed 128 cuts12877 = true := by
 decide +kernel
def pointBounds12877 : List (Nat × Nat × Nat) := [(1691789312,94259281751453,94259658385297),(1691842560,94259696689128,94260073323281)]
theorem point_links_checked12877 : (cuts12877.take 2).map (fun c => (1691746305-1+2*2^9*c.k,94258948826792+c.lower,94259325460394+c.upper)) = pointBounds12877 := by
 decide +kernel
def cuts12878 : List PrefixCut := [⟨18,148067043,148067149⟩,
⟨70,566139592,566140011⟩,
⟨122,983533497,983534217⟩,
⟨128,1031111247,1031112002⟩]
theorem checked12878 : checkPrefixCuts (2^48) 1691877377 9 Manual.Count131072.C012878.packed 128 cuts12878 = true := by
 decide +kernel
def pointBounds12878 : List (Nat × Nat × Nat) := [(1691895808,94260114442059,94260491076514),(1691949056,94260532514608,94260909149376),(1692002304,94260949908513,94261326543582)]
theorem point_links_checked12878 : (cuts12878.take 3).map (fun c => (1691877377-1+2*2^9*c.k,94259966375016+c.lower,94260343009365+c.upper)) = pointBounds12878 := by
 decide +kernel
def cuts12879 : List PrefixCut := [⟨46,362649951,362650215⟩,
⟨98,779019490,779020060⟩,
⟨128,1018554998,1018555744⟩]
theorem checked12879 : checkPrefixCuts (2^48) 1692008449 9 Manual.Count131072.C012879.packed 128 cuts12879 = true := by
 decide +kernel
def pointBounds12879 : List (Nat × Nat × Nat) := [(1692055552,94261360136214,94261736771582),(1692108800,94261776505753,94262153141427)]
theorem point_links_checked12879 : (cuts12879.take 2).map (fun c => (1692008449-1+2*2^9*c.k,94260997486263+c.lower,94261374121367+c.upper)) = pointBounds12879 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000089
