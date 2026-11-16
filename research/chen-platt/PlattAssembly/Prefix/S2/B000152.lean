import PlattAssemblyKernel
import PlattCertificates.Count131072.C014864
import PlattCertificates.Count131072.C014865
import PlattCertificates.Count131072.C014866
import PlattCertificates.Count131072.C014867
import PlattCertificates.Count131072.C014868
import PlattCertificates.Count131072.C014869
import PlattCertificates.Count131072.C014870
import PlattCertificates.Count131072.C014871
import PlattCertificates.Count131072.C014872
import PlattCertificates.Count131072.C014873
import PlattCertificates.Count131072.C014874
import PlattCertificates.Count131072.C014875
import PlattCertificates.Count131072.C014876
import PlattCertificates.Count131072.C014877
import PlattCertificates.Count131072.C014878
import PlattCertificates.Count131072.C014879
import PlattCertificates.Count131072.C014880
import PlattCertificates.Count131072.C014881
import PlattCertificates.Count131072.C014882
import PlattCertificates.Count131072.C014883
import PlattCertificates.Count131072.C014884
import PlattCertificates.Count131072.C014885
import PlattCertificates.Count131072.C014886
import PlattCertificates.Count131072.C014887
import PlattCertificates.Count131072.C014888
import PlattCertificates.Count131072.C014889
import PlattCertificates.Count131072.C014890
import PlattCertificates.Count131072.C014891
import PlattCertificates.Count131072.C014892
import PlattCertificates.Count131072.C014893
import PlattCertificates.Count131072.C014894
import PlattCertificates.Count131072.C014895
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000152
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14864 : List PrefixCut := [⟨26,182680486,182680605⟩,
⟨86,590277914,590278304⟩,
⟨128,878053875,878054457⟩]
theorem checked14864 : checkPrefixCuts (2^48) 1952186369 9 Manual.Count131072.C014864.packed 128 cuts14864 = true := by
 decide +kernel
def pointBounds14864 : List (Nat × Nat × Nat) := [(1952212992,96149390922378,96149768876627),(1952274432,96149798519806,96150176474326)]
theorem point_links_checked14864 : (cuts14864.take 2).map (fun c => (1952186369-1+2*2^9*c.k,96149208241892+c.lower,96149586196022+c.upper)) = pointBounds14864 := by
 decide +kernel
def cuts14865 : List PrefixCut := [⟨18,124422222,124422307⟩,
⟨78,536174983,536175342⟩,
⟨128,885347358,885347951⟩]
theorem checked14865 : checkPrefixCuts (2^48) 1952317441 9 Manual.Count131072.C014865.packed 128 cuts14865 = true := by
 decide +kernel
def pointBounds14865 : List (Nat × Nat × Nat) := [(1952335872,96150210717989,96150588672786),(1952397312,96150622470750,96151000425821)]
theorem point_links_checked14865 : (cuts14865.take 2).map (fun c => (1952317441-1+2*2^9*c.k,96150086295767+c.lower,96150464250479+c.upper)) = pointBounds14865 := by
 decide +kernel
def cuts14866 : List PrefixCut := [⟨10,70640705,70640753⟩,
⟨70,480925920,480926246⟩,
⟨128,882116506,882117103⟩]
theorem checked14866 : checkPrefixCuts (2^48) 1952448513 9 Manual.Count131072.C014866.packed 128 cuts14866 = true := by
 decide +kernel
def pointBounds14866 : List (Nat × Nat × Nat) := [(1952458752,96151042283830,96151420239183),(1952520192,96151452569045,96151830524676)]
theorem point_links_checked14866 : (cuts14866.take 2).map (fun c => (1952448513-1+2*2^9*c.k,96150971643125+c.lower,96151349598430+c.upper)) = pointBounds14866 := by
 decide +kernel
def cuts14867 : List PrefixCut := [⟨2,13694755,13694765⟩,
⟨62,439378585,439378878⟩,
⟨122,858418138,858418708⟩,
⟨128,900797049,900797647⟩]
theorem checked14867 : checkPrefixCuts (2^48) 1952579585 9 Manual.Count131072.C014867.packed 128 cuts14867 = true := by
 decide +kernel
def pointBounds14867 : List (Nat × Nat × Nat) := [(1952581632,96151867454386,96152245410298),(1952643072,96152293138216,96152671094411),(1952704512,96152712177769,96153090134241)]
theorem point_links_checked14867 : (cuts14867.take 3).map (fun c => (1952579585-1+2*2^9*c.k,96151853759631+c.lower,96152231715533+c.upper)) = pointBounds14867 := by
 decide +kernel
def cuts14868 : List PrefixCut := [⟨54,366701500,366701745⟩,
⟨114,779949136,779949654⟩,
⟨128,878394415,878394998⟩]
theorem checked14868 : checkPrefixCuts (2^48) 1952710657 9 Manual.Count131072.C014868.packed 128 cuts14868 = true := by
 decide +kernel
def pointBounds14868 : List (Nat × Nat × Nat) := [(1952765952,96153121258180,96153499214925),(1952827392,96153534505816,96153912462834)]
theorem point_links_checked14868 : (cuts14868.take 2).map (fun c => (1952710657-1+2*2^9*c.k,96152754556680+c.lower,96153132513180+c.upper)) = pointBounds14868 := by
 decide +kernel
def cuts14869 : List PrefixCut := [⟨46,323004961,323005174⟩,
⟨106,740262120,740262615⟩,
⟨128,890586790,890587386⟩]
theorem checked14869 : checkPrefixCuts (2^48) 1952841729 9 Manual.Count131072.C014869.packed 128 cuts14869 = true := by
 decide +kernel
def pointBounds14869 : List (Nat × Nat × Nat) := [(1952888832,96153955956056,96154333913352),(1952950272,96154373213215,96154751170793)]
theorem point_links_checked14869 : (cuts14869.take 2).map (fun c => (1952841729-1+2*2^9*c.k,96153632951095+c.lower,96154010908178+c.upper)) = pointBounds14869 := by
 decide +kernel
def cuts14870 : List PrefixCut := [⟨38,262163287,262163464⟩,
⟨98,671611669,671612119⟩,
⟨128,882456040,882456632⟩]
theorem checked14870 : checkPrefixCuts (2^48) 1952972801 9 Manual.Count131072.C014870.packed 128 cuts14870 = true := by
 decide +kernel
def pointBounds14870 : List (Nat × Nat × Nat) := [(1953011712,96154785701172,96155163659028),(1953073152,96155195149554,96155573107683)]
theorem point_links_checked14870 : (cuts14870.take 2).map (fun c => (1952972801-1+2*2^9*c.k,96154523537885+c.lower,96154901495564+c.upper)) = pointBounds14870 := by
 decide +kernel
def cuts14871 : List PrefixCut := [⟨30,208823474,208823617⟩,
⟨90,620552019,620552436⟩,
⟨128,887008588,887009184⟩]
theorem checked14871 : checkPrefixCuts (2^48) 1953103873 9 Manual.Count131072.C014871.packed 128 cuts14871 = true := by
 decide +kernel
def pointBounds14871 : List (Nat × Nat × Nat) := [(1953134592,96155614817399,96155992775813),(1953196032,96156026545944,96156404504632)]
theorem point_links_checked14871 : (cuts14871.take 2).map (fun c => (1953103873-1+2*2^9*c.k,96155405993925+c.lower,96155783952196+c.upper)) = pointBounds14871 := by
 decide +kernel
def cuts14872 : List PrefixCut := [⟨22,145835483,145835583⟩,
⟨82,558402733,558403112⟩,
⟨128,869800870,869801453⟩]
theorem checked14872 : checkPrefixCuts (2^48) 1953234945 9 Manual.Count131072.C014872.packed 128 cuts14872 = true := by
 decide +kernel
def pointBounds14872 : List (Nat × Nat × Nat) := [(1953257472,96156438837996,96156816796963),(1953318912,96156851405246,96157229364492)]
theorem point_links_checked14872 : (cuts14872.take 2).map (fun c => (1953234945-1+2*2^9*c.k,96156293002513+c.lower,96156670961380+c.upper)) = pointBounds14872 := by
 decide +kernel
def cuts14873 : List PrefixCut := [⟨14,94671622,94671685⟩,
⟨74,515714463,515714809⟩,
⟨128,884872322,884872916⟩]
theorem checked14873 : checkPrefixCuts (2^48) 1953366017 9 Manual.Count131072.C014873.packed 128 cuts14873 = true := by
 decide +kernel
def pointBounds14873 : List (Nat × Nat × Nat) := [(1953380352,96157257475005,96157635434518),(1953441792,96157678517846,96158056477642)]
theorem point_links_checked14873 : (cuts14873.take 2).map (fun c => (1953366017-1+2*2^9*c.k,96157162803383+c.lower,96157540762833+c.upper)) = pointBounds14873 := by
 decide +kernel
def cuts14874 : List PrefixCut := [⟨6,41209017,41209044⟩,
⟨66,452427520,452427825⟩,
⟨126,865938368,865938946⟩,
⟨128,878617241,878617828⟩]
theorem checked14874 : checkPrefixCuts (2^48) 1953497089 9 Manual.Count131072.C014874.packed 128 cuts14874 = true := by
 decide +kernel
def pointBounds14874 : List (Nat × Nat × Nat) := [(1953503232,96158088884722,96158466844793),(1953564672,96158500103225,96158878063574),(1953626112,96158913614073,96159291574695)]
theorem point_links_checked14874 : (cuts14874.take 3).map (fun c => (1953497089-1+2*2^9*c.k,96158047675705+c.lower,96158425635749+c.upper)) = pointBounds14874 := by
 decide +kernel
def cuts14875 : List PrefixCut := [⟨58,399089999,399090272⟩,
⟨118,816608826,816609378⟩,
⟨128,884753335,884753932⟩]
theorem checked14875 : checkPrefixCuts (2^48) 1953628161 9 Manual.Count131072.C014875.packed 128 cuts14875 = true := by
 decide +kernel
def pointBounds14875 : List (Nat × Nat × Nat) := [(1953687552,96159325382945,96159703343849),(1953748992,96159742901772,96160120862955)]
theorem point_links_checked14875 : (cuts14875.take 2).map (fun c => (1953628161-1+2*2^9*c.k,96158926292946+c.lower,96159304253577+c.upper)) = pointBounds14875 := by
 decide +kernel
def cuts14876 : List PrefixCut := [⟨50,343886705,343886938⟩,
⟨110,753744016,753744520⟩,
⟨128,874753886,874754473⟩]
theorem checked14876 : checkPrefixCuts (2^48) 1953759233 9 Manual.Count131072.C014876.packed 128 cuts14876 = true := by
 decide +kernel
def pointBounds14876 : List (Nat × Nat × Nat) := [(1953810432,96160154932986,96160532894447),(1953871872,96160564790297,96160942752029)]
theorem point_links_checked14876 : (cuts14876.take 2).map (fun c => (1953759233-1+2*2^9*c.k,96159811046281+c.lower,96160189007509+c.upper)) = pointBounds14876 := by
 decide +kernel
def cuts14877 : List PrefixCut := [⟨42,291571594,291571792⟩,
⟨102,706156836,706157307⟩,
⟨128,891261101,891261694⟩]
theorem checked14877 : checkPrefixCuts (2^48) 1953890305 9 Manual.Count131072.C014877.packed 128 cuts14877 = true := by
 decide +kernel
def pointBounds14877 : List (Nat × Nat × Nat) := [(1953933312,96160977371761,96161355333774),(1953994752,96161391957003,96161769919289)]
theorem point_links_checked14877 : (cuts14877.take 2).map (fun c => (1953890305-1+2*2^9*c.k,96160685800167+c.lower,96161063761982+c.upper)) = pointBounds14877 := by
 decide +kernel
def cuts14878 : List PrefixCut := [⟨34,233069233,233069388⟩,
⟨94,645323740,645324176⟩,
⟨128,879101706,879102299⟩]
theorem checked14878 : checkPrefixCuts (2^48) 1954021377 9 Manual.Count131072.C014878.packed 128 cuts14878 = true := by
 decide +kernel
def pointBounds14878 : List (Nat × Nat × Nat) := [(1954056192,96161810130501,96162188093064),(1954117632,96162222385008,96162600347852)]
theorem point_links_checked14878 : (cuts14878.take 2).map (fun c => (1954021377-1+2*2^9*c.k,96161577061268+c.lower,96161955023676+c.upper)) = pointBounds14878 := by
 decide +kernel
def cuts14879 : List PrefixCut := [⟨26,180192023,180192144⟩,
⟨86,590548163,590548557⟩,
⟨128,883075731,883076322⟩]
theorem checked14879 : checkPrefixCuts (2^48) 1954152449 9 Manual.Count131072.C014879.packed 128 cuts14879 = true := by
 decide +kernel
def pointBounds14879 : List (Nat × Nat × Nat) := [(1954179072,96162636354997,96163014318119),(1954240512,96163046711137,96163424674532)]
theorem point_links_checked14879 : (cuts14879.take 2).map (fun c => (1954152449-1+2*2^9*c.k,96162456162974+c.lower,96162834125975+c.upper)) = pointBounds14879 := by
 decide +kernel
def cuts14880 : List PrefixCut := [⟨18,120120219,120120300⟩,
⟨78,540244378,540244736⟩,
⟨128,881864419,881865004⟩]
theorem checked14880 : checkPrefixCuts (2^48) 1954283521 9 Manual.Count131072.C014880.packed 128 cuts14880 = true := by
 decide +kernel
def pointBounds14880 : List (Nat × Nat × Nat) := [(1954301952,96163459358924,96163837322597),(1954363392,96163879483083,96164257447033)]
theorem point_links_checked14880 : (cuts14880.take 2).map (fun c => (1954283521-1+2*2^9*c.k,96163339238705+c.lower,96163717202297+c.upper)) = pointBounds14880 := by
 decide +kernel
def cuts14881 : List PrefixCut := [⟨10,66537083,66537127⟩,
⟨70,488507041,488507364⟩,
⟨128,884829655,884830239⟩]
theorem checked14881 : checkPrefixCuts (2^48) 1954414593 9 Manual.Count131072.C014881.packed 128 cuts14881 = true := by
 decide +kernel
def pointBounds14881 : List (Nat × Nat × Nat) := [(1954424832,96164287640207,96164665604428),(1954486272,96164709610165,96165087574665)]
theorem point_links_checked14881 : (cuts14881.take 2).map (fun c => (1954414593-1+2*2^9*c.k,96164221103124+c.lower,96164599067301+c.upper)) = pointBounds14881 := by
 decide +kernel
def cuts14882 : List PrefixCut := [⟨2,13824990,13824999⟩,
⟨62,426695876,426696162⟩,
⟨122,830481505,830482066⟩,
⟨128,870801774,870802363⟩]
theorem checked14882 : checkPrefixCuts (2^48) 1954545665 9 Manual.Count131072.C014882.packed 128 cuts14882 = true := by
 decide +kernel
def pointBounds14882 : List (Nat × Nat × Nat) := [(1954547712,96165119757769,96165497722539),(1954609152,96165532628655,96165910593702),(1954670592,96165936414284,96166314379606)]
theorem point_links_checked14882 : (cuts14882.take 3).map (fun c => (1954545665-1+2*2^9*c.k,96165105932779+c.lower,96165483897540+c.upper)) = pointBounds14882 := by
 decide +kernel
def cuts14883 : List PrefixCut := [⟨54,366908655,366908895⟩,
⟨114,785500432,785500953⟩,
⟨128,878662996,878663580⟩]
theorem checked14883 : checkPrefixCuts (2^48) 1954676737 9 Manual.Count131072.C014883.packed 128 cuts14883 = true := by
 decide +kernel
def pointBounds14883 : List (Nat × Nat × Nat) := [(1954732032,96166343643208,96166721608798),(1954793472,96166762234985,96167140200856)]
theorem point_links_checked14883 : (cuts14883.take 2).map (fun c => (1954676737-1+2*2^9*c.k,96165976734553+c.lower,96166354699903+c.upper)) = pointBounds14883 := by
 decide +kernel
def cuts14884 : List PrefixCut := [⟨46,314040727,314040937⟩,
⟨106,740237214,740237704⟩,
⟨128,888682915,888683503⟩]
theorem checked14884 : checkPrefixCuts (2^48) 1954807809 9 Manual.Count131072.C014884.packed 128 cuts14884 = true := by
 decide +kernel
def pointBounds14884 : List (Nat × Nat × Nat) := [(1954854912,96167169438276,96167547404420),(1954916352,96167595634763,96167973601187)]
theorem point_links_checked14884 : (cuts14884.take 2).map (fun c => (1954807809-1+2*2^9*c.k,96166855397549+c.lower,96167233363483+c.upper)) = pointBounds14884 := by
 decide +kernel
def cuts14885 : List PrefixCut := [⟨38,261323658,261323832⟩,
⟨98,677127266,677127718⟩,
⟨128,877969451,877970037⟩]
theorem checked14885 : checkPrefixCuts (2^48) 1954938881 9 Manual.Count131072.C014885.packed 128 cuts14885 = true := by
 decide +kernel
def pointBounds14885 : List (Nat × Nat × Nat) := [(1954977792,96168005404122,96168383370818),(1955039232,96168421207730,96168799174704)]
theorem point_links_checked14885 : (cuts14885.take 2).map (fun c => (1954938881-1+2*2^9*c.k,96167744080464+c.lower,96168122046986+c.upper)) = pointBounds14885 := by
 decide +kernel
def cuts14886 : List PrefixCut := [⟨30,210773030,210773170⟩,
⟨90,617048571,617048987⟩,
⟨128,878342429,878343016⟩]
theorem checked14886 : checkPrefixCuts (2^48) 1955069953 9 Manual.Count131072.C014886.packed 128 cuts14886 = true := by
 decide +kernel
def pointBounds14886 : List (Nat × Nat × Nat) := [(1955100672,96168832822945,96169210790193),(1955162112,96169239098486,96169617066010)]
theorem point_links_checked14886 : (cuts14886.take 2).map (fun c => (1955069953-1+2*2^9*c.k,96168622049915+c.lower,96169000017023+c.upper)) = pointBounds14886 := by
 decide +kernel
def cuts14887 : List PrefixCut := [⟨22,150583508,150583611⟩,
⟨82,563023792,563024170⟩,
⟨128,886200975,886201568⟩]
theorem checked14887 : checkPrefixCuts (2^48) 1955201025 9 Manual.Count131072.C014887.packed 128 cuts14887 = true := by
 decide +kernel
def pointBounds14887 : List (Nat × Nat × Nat) := [(1955223552,96169650975852,96170028943650),(1955284992,96170063416136,96170441384209)]
theorem point_links_checked14887 : (cuts14887.take 2).map (fun c => (1955201025-1+2*2^9*c.k,96169500392344+c.lower,96169878360039+c.upper)) = pointBounds14887 := by
 decide +kernel
def cuts14888 : List PrefixCut := [⟨14,95008274,95008340⟩,
⟨74,511597143,511597488⟩,
⟨128,885709880,885710472⟩]
theorem checked14888 : checkPrefixCuts (2^48) 1955332097 9 Manual.Count131072.C014888.packed 128 cuts14888 = true := by
 decide +kernel
def pointBounds14888 : List (Nat × Nat × Nat) := [(1955346432,96170481601593,96170859569947),(1955407872,96170898190462,96171276159095)]
theorem point_links_checked14888 : (cuts14888.take 2).map (fun c => (1955332097-1+2*2^9*c.k,96170386593319+c.lower,96170764561607+c.upper)) = pointBounds14888 := by
 decide +kernel
def cuts14889 : List PrefixCut := [⟨6,45773745,45773775⟩,
⟨66,452260633,452260933⟩,
⟨126,864923977,864924552⟩,
⟨128,879029436,879030019⟩]
theorem checked14889 : checkPrefixCuts (2^48) 1955463169 9 Manual.Count131072.C014889.packed 128 cuts14889 = true := by
 decide +kernel
def pointBounds14889 : List (Nat × Nat × Nat) := [(1955469312,96171318076944,96171696045854),(1955530752,96171724563832,96172102533012),(1955592192,96172137227176,96172515196631)]
theorem point_links_checked14889 : (cuts14889.take 3).map (fun c => (1955463169-1+2*2^9*c.k,96171272303199+c.lower,96171650272079+c.upper)) = pointBounds14889 := by
 decide +kernel
def cuts14890 : List PrefixCut := [⟨58,400272029,400272301⟩,
⟨118,811614034,811614582⟩,
⟨128,878538648,878539242⟩]
theorem checked14890 : checkPrefixCuts (2^48) 1955594241 9 Manual.Count131072.C014890.packed 128 cuts14890 = true := by
 decide +kernel
def pointBounds14890 : List (Nat × Nat × Nat) := [(1955653632,96172551604664,96172929574399),(1955715072,96172962946669,96173340916680)]
theorem point_links_checked14890 : (cuts14890.take 2).map (fun c => (1955594241-1+2*2^9*c.k,96172151332635+c.lower,96172529302098+c.upper)) = pointBounds14890 := by
 decide +kernel
def cuts14891 : List PrefixCut := [⟨50,346995103,346995333⟩,
⟨110,759606582,759607094⟩,
⟨128,889561413,889562013⟩]
theorem checked14891 : checkPrefixCuts (2^48) 1955725313 9 Manual.Count131072.C014891.packed 128 cuts14891 = true := by
 decide +kernel
def pointBounds14891 : List (Nat × Nat × Nat) := [(1955776512,96173376866386,96173754836673),(1955837952,96173789477865,96174167448434)]
theorem point_links_checked14891 : (cuts14891.take 2).map (fun c => (1955725313-1+2*2^9*c.k,96173029871283+c.lower,96173407841340+c.upper)) = pointBounds14891 := by
 decide +kernel
def cuts14892 : List PrefixCut := [⟨42,282068106,282068297⟩,
⟨102,691919483,691919955⟩,
⟨128,873527883,873528476⟩]
theorem checked14892 : checkPrefixCuts (2^48) 1955856385 9 Manual.Count131072.C014892.packed 128 cuts14892 = true := by
 decide +kernel
def pointBounds14892 : List (Nat × Nat × Nat) := [(1955899392,96174201500802,96174579471650),(1955960832,96174611352179,96174989323308)]
theorem point_links_checked14892 : (cuts14892.take 2).map (fun c => (1955856385-1+2*2^9*c.k,96173919432696+c.lower,96174297403353+c.upper)) = pointBounds14892 := by
 decide +kernel
def cuts14893 : List PrefixCut := [⟨34,234705721,234705877⟩,
⟨94,648848153,648848589⟩,
⟨128,882391151,882391743⟩]
theorem checked14893 : checkPrefixCuts (2^48) 1955987457 9 Manual.Count131072.C014893.packed 128 cuts14893 = true := by
 decide +kernel
def pointBounds14893 : List (Nat × Nat × Nat) := [(1956022272,96175027666300,96175405637706),(1956083712,96175441808732,96175819780418)]
theorem point_links_checked14893 : (cuts14893.take 2).map (fun c => (1955987457-1+2*2^9*c.k,96174792960579+c.lower,96175170931829+c.upper)) = pointBounds14893 := by
 decide +kernel
def cuts14894 : List PrefixCut := [⟨26,184471610,184471731⟩,
⟨86,591969169,591969560⟩,
⟨128,887080437,887081019⟩]
theorem checked14894 : checkPrefixCuts (2^48) 1956118529 9 Manual.Count131072.C014894.packed 128 cuts14894 = true := by
 decide +kernel
def pointBounds14894 : List (Nat × Nat × Nat) := [(1956145152,96175859823340,96176237795303),(1956206592,96176267320899,96176645293132)]
theorem point_links_checked14894 : (cuts14894.take 2).map (fun c => (1956118529-1+2*2^9*c.k,96175675351730+c.lower,96176053323572+c.upper)) = pointBounds14894 := by
 decide +kernel
def cuts14895 : List PrefixCut := [⟨18,123596599,123596683⟩,
⟨78,539701479,539701844⟩,
⟨128,888891451,888892047⟩]
theorem checked14895 : checkPrefixCuts (2^48) 1956249601 9 Manual.Count131072.C014895.packed 128 cuts14895 = true := by
 decide +kernel
def pointBounds14895 : List (Nat × Nat × Nat) := [(1956268032,96176686028766,96177064001274),(1956329472,96177102133646,96177480106435)]
theorem point_links_checked14895 : (cuts14895.take 2).map (fun c => (1956249601-1+2*2^9*c.k,96176562432167+c.lower,96176940404591+c.upper)) = pointBounds14895 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000152
