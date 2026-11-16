import PlattAssemblyKernel
import PlattCertificates.Count131072.C017872
import PlattCertificates.Count131072.C017873
import PlattCertificates.Count131072.C017874
import PlattCertificates.Count131072.C017875
import PlattCertificates.Count131072.C017876
import PlattCertificates.Count131072.C017877
import PlattCertificates.Count131072.C017878
import PlattCertificates.Count131072.C017879
import PlattCertificates.Count131072.C017880
import PlattCertificates.Count131072.C017881
import PlattCertificates.Count131072.C017882
import PlattCertificates.Count131072.C017883
import PlattCertificates.Count131072.C017884
import PlattCertificates.Count131072.C017885
import PlattCertificates.Count131072.C017886
import PlattCertificates.Count131072.C017887
import PlattCertificates.Count131072.C017888
import PlattCertificates.Count131072.C017889
import PlattCertificates.Count131072.C017890
import PlattCertificates.Count131072.C017891
import PlattCertificates.Count131072.C017892
import PlattCertificates.Count131072.C017893
import PlattCertificates.Count131072.C017894
import PlattCertificates.Count131072.C017895
import PlattCertificates.Count131072.C017896
import PlattCertificates.Count131072.C017897
import PlattCertificates.Count131072.C017898
import PlattCertificates.Count131072.C017899
import PlattCertificates.Count131072.C017900
import PlattCertificates.Count131072.C017901
import PlattCertificates.Count131072.C017902
import PlattCertificates.Count131072.C017903
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000246
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17872 : List PrefixCut := [⟨20,115638741,115638810⟩,
⟨92,529962496,529962823⟩,
⟨128,734720471,734720925⟩]
theorem checked17872 : checkPrefixCuts (2^48) 2346450945 9 Manual.Count131072.C017872.packed 128 cuts17872 = true := by
 decide +kernel
def pointBounds17872 : List (Nat × Nat × Nat) := [(2346471424,98559448119992,98559827613761),(2346545152,98559862443747,98560241937774)]
theorem point_links_checked17872 : (cuts17872.take 2).map (fun c => (2346450945-1+2*2^9*c.k,98559332481251+c.lower,98559711974951+c.upper)) = pointBounds17872 := by
 decide +kernel
def cuts17873 : List PrefixCut := [⟨36,205354549,205354674⟩,
⟨108,618332968,618333350⟩,
⟨128,735279173,735279624⟩]
theorem checked17873 : checkPrefixCuts (2^48) 2346582017 9 Manual.Count131072.C017873.packed 128 cuts17873 = true := by
 decide +kernel
def pointBounds17873 : List (Nat × Nat × Nat) := [(2346618880,98560272556271,98560652050550),(2346692608,98560685534690,98561065029226)]
theorem point_links_checked17873 : (cuts17873.take 2).map (fun c => (2346582017-1+2*2^9*c.k,98560067201722+c.lower,98560446695876+c.upper)) = pointBounds17873 := by
 decide +kernel
def cuts17874 : List PrefixCut := [⟨52,298777877,298778060⟩,
⟨124,709211488,709211927⟩,
⟨128,732599343,732599796⟩]
theorem checked17874 : checkPrefixCuts (2^48) 2346713089 9 Manual.Count131072.C017874.packed 128 cuts17874 = true := by
 decide +kernel
def pointBounds17874 : List (Nat × Nat × Nat) := [(2346766336,98561101258772,98561480753560),(2346840064,98561511692383,98561891187427)]
theorem point_links_checked17874 : (cuts17874.take 2).map (fun c => (2346713089-1+2*2^9*c.k,98560802480895+c.lower,98561181975500+c.upper)) = pointBounds17874 := by
 decide +kernel
def cuts17875 : List PrefixCut := [⟨68,386913100,386913334⟩,
⟨128,718886227,718886663⟩]
theorem checked17875 : checkPrefixCuts (2^48) 2346844161 9 Manual.Count131072.C017875.packed 128 cuts17875 = true := by
 decide +kernel
def pointBounds17875 : List (Nat × Nat × Nat) := [(2346913792,98561921993338,98562301488630)]
theorem point_links_checked17875 : (cuts17875.take 1).map (fun c => (2346844161-1+2*2^9*c.k,98561535080238+c.lower,98561914575296+c.upper)) = pointBounds17875 := by
 decide +kernel
def cuts17876 : List PrefixCut := [⟨12,68480371,68480412⟩,
⟨84,477915995,477916286⟩,
⟨128,728320115,728320561⟩]
theorem checked17876 : checkPrefixCuts (2^48) 2346975233 9 Manual.Count131072.C017876.packed 128 cuts17876 = true := by
 decide +kernel
def pointBounds17876 : List (Nat × Nat × Nat) := [(2346987520,98562322446836,98562701942371),(2347061248,98562731882460,98563111378245)]
theorem point_links_checked17876 : (cuts17876.take 2).map (fun c => (2346975233-1+2*2^9*c.k,98562253966465+c.lower,98562633461959+c.upper)) = pointBounds17876 := by
 decide +kernel
def cuts17877 : List PrefixCut := [⟨28,161536935,161537034⟩,
⟨100,572505730,572506082⟩,
⟨128,727919801,727920249⟩]
theorem checked17877 : checkPrefixCuts (2^48) 2347106305 9 Manual.Count131072.C017877.packed 128 cuts17877 = true := by
 decide +kernel
def pointBounds17877 : List (Nat × Nat × Nat) := [(2347134976,98563143823515,98563523319554),(2347208704,98563554792310,98563934288602)]
theorem point_links_checked17877 : (cuts17877.take 2).map (fun c => (2347106305-1+2*2^9*c.k,98562982286580+c.lower,98563361782520+c.upper)) = pointBounds17877 := by
 decide +kernel
def cuts17878 : List PrefixCut := [⟨44,256021483,256021641⟩,
⟨116,661688276,661688678⟩,
⟨128,730877003,730877448⟩]
theorem checked17878 : checkPrefixCuts (2^48) 2347237377 9 Manual.Count131072.C017878.packed 128 cuts17878 = true := by
 decide +kernel
def pointBounds17878 : List (Nat × Nat × Nat) := [(2347282432,98563966227864,98564345724410),(2347356160,98564371894657,98564751391447)]
theorem point_links_checked17878 : (cuts17878.take 2).map (fun c => (2347237377-1+2*2^9*c.k,98563710206381+c.lower,98564089702769+c.upper)) = pointBounds17878 := by
 decide +kernel
def cuts17879 : List PrefixCut := [⟨60,340182612,340182823⟩,
⟨128,724840756,724841207⟩]
theorem checked17879 : checkPrefixCuts (2^48) 2347368449 9 Manual.Count131072.C017879.packed 128 cuts17879 = true := by
 decide +kernel
def pointBounds17879 : List (Nat × Nat × Nat) := [(2347429888,98564781265996,98565160763040)]
theorem point_links_checked17879 : (cuts17879.take 1).map (fun c => (2347368449-1+2*2^9*c.k,98564441083384+c.lower,98564820580217+c.upper)) = pointBounds17879 := by
 decide +kernel
def cuts17880 : List PrefixCut := [⟨4,22901668,22901682⟩,
⟨76,437642787,437643063⟩,
⟨128,736190793,736191247⟩]
theorem checked17880 : checkPrefixCuts (2^48) 2347499521 9 Manual.Count131072.C017880.packed 128 cuts17880 = true := by
 decide +kernel
def pointBounds17880 : List (Nat × Nat × Nat) := [(2347503616,98565188825808,98565568323106),(2347577344,98565603566927,98565983064487)]
theorem point_links_checked17880 : (cuts17880.take 2).map (fun c => (2347499521-1+2*2^9*c.k,98565165924140+c.lower,98565545421424+c.upper)) = pointBounds17880 := by
 decide +kernel
def cuts17881 : List PrefixCut := [⟨20,113662273,113662343⟩,
⟨92,521423465,521423785⟩,
⟨128,727757062,727757511⟩]
theorem checked17881 : checkPrefixCuts (2^48) 2347630593 9 Manual.Count131072.C017881.packed 128 cuts17881 = true := by
 decide +kernel
def pointBounds17881 : List (Nat × Nat × Nat) := [(2347651072,98566015777206,98566395275014),(2347724800,98566423538398,98566803036456)]
theorem point_links_checked17881 : (cuts17881.take 2).map (fun c => (2347630593-1+2*2^9*c.k,98565902114933+c.lower,98566281612671+c.upper)) = pointBounds17881 := by
 decide +kernel
def cuts17882 : List PrefixCut := [⟨36,202853564,202853687⟩,
⟨108,603755682,603756052⟩,
⟨128,721362446,721362888⟩]
theorem checked17882 : checkPrefixCuts (2^48) 2347761665 9 Manual.Count131072.C017882.packed 128 cuts17882 = true := by
 decide +kernel
def pointBounds17882 : List (Nat × Nat × Nat) := [(2347798528,98566832725559,98567212223869),(2347872256,98567233627677,98567613126234)]
theorem point_links_checked17882 : (cuts17882.take 2).map (fun c => (2347761665-1+2*2^9*c.k,98566629871995+c.lower,98567009370182+c.upper)) = pointBounds17882 := by
 decide +kernel
def cuts17883 : List PrefixCut := [⟨52,294911435,294911615⟩,
⟨124,700703410,700703841⟩,
⟨128,723839761,723840206⟩]
theorem checked17883 : checkPrefixCuts (2^48) 2347892737 9 Manual.Count131072.C017883.packed 128 cuts17883 = true := by
 decide +kernel
def pointBounds17883 : List (Nat × Nat × Nat) := [(2347945984,98567646145876,98568025644685),(2348019712,98568051937851,98568431436911)]
theorem point_links_checked17883 : (cuts17883.take 2).map (fun c => (2347892737-1+2*2^9*c.k,98567351234441+c.lower,98567730733070+c.upper)) = pointBounds17883 := by
 decide +kernel
def cuts17884 : List PrefixCut := [⟨68,394270861,394271100⟩,
⟨128,734588116,734588564⟩]
theorem checked17884 : checkPrefixCuts (2^48) 2348023809 9 Manual.Count131072.C017884.packed 128 cuts17884 = true := by
 decide +kernel
def pointBounds17884 : List (Nat × Nat × Nat) := [(2348093440,98568469345063,98568848844376)]
theorem point_links_checked17884 : (cuts17884.take 1).map (fun c => (2348023809-1+2*2^9*c.k,98568075074202+c.lower,98568454573276+c.upper)) = pointBounds17884 := by
 decide +kernel
def cuts17885 : List PrefixCut := [⟨12,66887655,66887696⟩,
⟨84,470843485,470843778⟩,
⟨128,721721208,721721651⟩]
theorem checked17885 : checkPrefixCuts (2^48) 2348154881 9 Manual.Count131072.C017885.packed 128 cuts17885 = true := by
 decide +kernel
def pointBounds17885 : List (Nat × Nat × Nat) := [(2348167168,98568876549973,98569256049536),(2348240896,98569280505803,98569660005618)]
theorem point_links_checked17885 : (cuts17885.take 2).map (fun c => (2348154881-1+2*2^9*c.k,98568809662318+c.lower,98569189161840+c.upper)) = pointBounds17885 := by
 decide +kernel
def cuts17886 : List PrefixCut := [⟨28,160856471,160856572⟩,
⟨100,569341534,569341886⟩,
⟨128,732348436,732348888⟩]
theorem checked17886 : checkPrefixCuts (2^48) 2348285953 9 Manual.Count131072.C017886.packed 128 cuts17886 = true := by
 decide +kernel
def pointBounds17886 : List (Nat × Nat × Nat) := [(2348314624,98569692239997,98570071740063),(2348388352,98570100725060,98570480225377)]
theorem point_links_checked17886 : (cuts17886.take 2).map (fun c => (2348285953-1+2*2^9*c.k,98569531383526+c.lower,98569910883491+c.upper)) = pointBounds17886 := by
 decide +kernel
def cuts17887 : List PrefixCut := [⟨44,251697905,251698058⟩,
⟨116,652366833,652367232⟩,
⟨128,722479616,722480058⟩]
theorem checked17887 : checkPrefixCuts (2^48) 2348417025 9 Manual.Count131072.C017887.packed 128 cuts17887 = true := by
 decide +kernel
def pointBounds17887 : List (Nat × Nat × Nat) := [(2348462080,98570515429867,98570894930437),(2348535808,98570916098795,98571295599611)]
theorem point_links_checked17887 : (cuts17887.take 2).map (fun c => (2348417025-1+2*2^9*c.k,98570263731962+c.lower,98570643232379+c.upper)) = pointBounds17887 := by
 decide +kernel
def cuts17888 : List PrefixCut := [⟨60,336655941,336656150⟩,
⟨128,723637638,723638086⟩]
theorem checked17888 : checkPrefixCuts (2^48) 2348548097 9 Manual.Count131072.C017888.packed 128 cuts17888 = true := by
 decide +kernel
def pointBounds17888 : List (Nat × Nat × Nat) := [(2348609536,98571322867519,98571702368587)]
theorem point_links_checked17888 : (cuts17888.take 1).map (fun c => (2348548097-1+2*2^9*c.k,98570986211578+c.lower,98571365712437+c.upper)) = pointBounds17888 := by
 decide +kernel
def cuts17889 : List PrefixCut := [⟨4,22171103,22171117⟩,
⟨76,432389607,432389878⟩,
⟨128,728271045,728271500⟩]
theorem checked17889 : checkPrefixCuts (2^48) 2348679169 9 Manual.Count131072.C017889.packed 128 cuts17889 = true := by
 decide +kernel
def pointBounds17889 : List (Nat × Nat × Nat) := [(2348683264,98571732020319,98572111521640),(2348756992,98572142238823,98572521740401)]
theorem point_links_checked17889 : (cuts17889.take 2).map (fun c => (2348679169-1+2*2^9*c.k,98571709849216+c.lower,98572089350523+c.upper)) = pointBounds17889 := by
 decide +kernel
def cuts17890 : List PrefixCut := [⟨20,115402745,115402815⟩,
⟨92,527872380,527872694⟩,
⟨128,730866904,730867340⟩]
theorem checked17890 : checkPrefixCuts (2^48) 2348810241 9 Manual.Count131072.C017890.packed 128 cuts17890 = true := by
 decide +kernel
def pointBounds17890 : List (Nat × Nat × Nat) := [(2348830720,98572553523006,98572933024838),(2348904448,98572965992641,98573345494717)]
theorem point_links_checked17890 : (cuts17890.take 2).map (fun c => (2348810241-1+2*2^9*c.k,98572438120261+c.lower,98572817622023+c.upper)) = pointBounds17890 := by
 decide +kernel
def cuts17891 : List PrefixCut := [⟨36,207305192,207305321⟩,
⟨108,610881699,610882072⟩,
⟨128,727350989,727351434⟩]
theorem checked17891 : checkPrefixCuts (2^48) 2348941313 9 Manual.Count131072.C017891.packed 128 cuts17891 = true := by
 decide +kernel
def pointBounds17891 : List (Nat × Nat × Nat) := [(2348978176,98573376292357,98573755794684),(2349051904,98573779868864,98574159371435)]
theorem point_links_checked17891 : (cuts17891.take 2).map (fun c => (2348941313-1+2*2^9*c.k,98573168987165+c.lower,98573548489363+c.upper)) = pointBounds17891 := by
 decide +kernel
def cuts17892 : List PrefixCut := [⟨52,298118354,298118533⟩,
⟨124,699153360,699153788⟩,
⟨128,722517726,722518168⟩]
theorem checked17892 : checkPrefixCuts (2^48) 2349072385 9 Manual.Count131072.C017892.packed 128 cuts17892 = true := by
 decide +kernel
def pointBounds17892 : List (Nat × Nat × Nat) := [(2349125632,98574194456508,98574573959330),(2349199360,98574595491514,98574974994585)]
theorem point_links_checked17892 : (cuts17892.take 2).map (fun c => (2349072385-1+2*2^9*c.k,98573896338154+c.lower,98574275840797+c.upper)) = pointBounds17892 := by
 decide +kernel
def cuts17893 : List PrefixCut := [⟨68,386284830,386285067⟩,
⟨128,722717042,722717481⟩]
theorem checked17893 : checkPrefixCuts (2^48) 2349203457 9 Manual.Count131072.C017893.packed 128 cuts17893 = true := by
 decide +kernel
def pointBounds17893 : List (Nat × Nat × Nat) := [(2349273088,98575005140710,98575384644032)]
theorem point_links_checked17893 : (cuts17893.take 1).map (fun c => (2349203457-1+2*2^9*c.k,98574618855880+c.lower,98574998358965+c.upper)) = pointBounds17893 := by
 decide +kernel
def cuts17894 : List PrefixCut := [⟨12,70687998,70688041⟩,
⟨84,485822604,485822909⟩,
⟨128,732500991,732501443⟩]
theorem checked17894 : checkPrefixCuts (2^48) 2349334529 9 Manual.Count131072.C017894.packed 128 cuts17894 = true := by
 decide +kernel
def pointBounds17894 : List (Nat × Nat × Nat) := [(2349346816,98575412260920,98575791764487),(2349420544,98575827395526,98576206899355)]
theorem point_links_checked17894 : (cuts17894.take 2).map (fun c => (2349334529-1+2*2^9*c.k,98575341572922+c.lower,98575721076446+c.upper)) = pointBounds17894 := by
 decide +kernel
def cuts17895 : List PrefixCut := [⟨28,163051963,163052059⟩,
⟨100,576123920,576124270⟩,
⟨128,730183947,730184393⟩]
theorem checked17895 : checkPrefixCuts (2^48) 2349465601 9 Manual.Count131072.C017895.packed 128 cuts17895 = true := by
 decide +kernel
def pointBounds17895 : List (Nat × Nat × Nat) := [(2349494272,98576237125876,98576616629948),(2349568000,98576650197833,98577029702159)]
theorem point_links_checked17895 : (cuts17895.take 2).map (fun c => (2349465601-1+2*2^9*c.k,98576074073913+c.lower,98576453577889+c.upper)) = pointBounds17895 := by
 decide +kernel
def cuts17896 : List PrefixCut := [⟨44,254087216,254087374⟩,
⟨116,666055094,666055502⟩,
⟨128,733617076,733617526⟩]
theorem checked17896 : checkPrefixCuts (2^48) 2349596673 9 Manual.Count131072.C017896.packed 128 cuts17896 = true := by
 decide +kernel
def pointBounds17896 : List (Nat × Nat × Nat) := [(2349641728,98577058345076,98577437849656),(2349715456,98577470312954,98577849817784)]
theorem point_links_checked17896 : (cuts17896.take 2).map (fun c => (2349596673-1+2*2^9*c.k,98576804257860+c.lower,98577183762282+c.upper)) = pointBounds17896 := by
 decide +kernel
def cuts17897 : List PrefixCut := [⟨60,335887972,335888180⟩,
⟨128,720279738,720280177⟩]
theorem checked17897 : checkPrefixCuts (2^48) 2349727745 9 Manual.Count131072.C017897.packed 128 cuts17897 = true := by
 decide +kernel
def pointBounds17897 : List (Nat × Nat × Nat) := [(2349789184,98577873762908,98578253267988)]
theorem point_links_checked17897 : (cuts17897.take 1).map (fun c => (2349727745-1+2*2^9*c.k,98577537874936+c.lower,98577917379808+c.upper)) = pointBounds17897 := by
 decide +kernel
def cuts17898 : List PrefixCut := [⟨4,21800624,21800637⟩,
⟨76,434568214,434568474⟩,
⟨128,726108890,726109328⟩]
theorem checked17898 : checkPrefixCuts (2^48) 2349858817 9 Manual.Count131072.C017898.packed 128 cuts17898 = true := by
 decide +kernel
def pointBounds17898 : List (Nat × Nat × Nat) := [(2349862912,98578279955298,98578659460622),(2349936640,98578692722888,98579072228459)]
theorem point_links_checked17898 : (cuts17898.take 2).map (fun c => (2349858817-1+2*2^9*c.k,98578258154674+c.lower,98578637659985+c.upper)) = pointBounds17898 := by
 decide +kernel
def cuts17899 : List PrefixCut := [⟨20,115704146,115704218⟩,
⟨92,527727218,527727542⟩,
⟨128,732775697,732776144⟩]
theorem checked17899 : checkPrefixCuts (2^48) 2349989889 9 Manual.Count131072.C017899.packed 128 cuts17899 = true := by
 decide +kernel
def pointBounds17899 : List (Nat × Nat × Nat) := [(2350010368,98579099967710,98579479473531),(2350084096,98579511990782,98579891496855)]
theorem point_links_checked17899 : (cuts17899.take 2).map (fun c => (2349989889-1+2*2^9*c.k,98578984263564+c.lower,98579363769313+c.upper)) = pointBounds17899 := by
 decide +kernel
def cuts17900 : List PrefixCut := [⟨36,203608078,203608207⟩,
⟨108,609736773,609737148⟩,
⟨128,723872090,723872537⟩]
theorem checked17900 : checkPrefixCuts (2^48) 2350120961 9 Manual.Count131072.C017900.packed 128 cuts17900 = true := by
 decide +kernel
def pointBounds17900 : List (Nat × Nat × Nat) := [(2350157824,98579920647339,98580300153664),(2350231552,98580326776034,98580706282605)]
theorem point_links_checked17900 : (cuts17900.take 2).map (fun c => (2350120961-1+2*2^9*c.k,98579717039261+c.lower,98580096545457+c.upper)) = pointBounds17900 := by
 decide +kernel
def cuts17901 : List PrefixCut := [⟨52,299046591,299046776⟩,
⟨124,711496954,711497392⟩,
⟨128,735568137,735568590⟩]
theorem checked17901 : checkPrefixCuts (2^48) 2350252033 9 Manual.Count131072.C017901.packed 128 cuts17901 = true := by
 decide +kernel
def pointBounds17901 : List (Nat × Nat × Nat) := [(2350305280,98580739957942,98581119464770),(2350379008,98581152408305,98581531915386)]
theorem point_links_checked17901 : (cuts17901.take 2).map (fun c => (2350252033-1+2*2^9*c.k,98580440911351+c.lower,98580820417994+c.upper)) = pointBounds17901 := by
 decide +kernel
def cuts17902 : List PrefixCut := [⟨68,385492103,385492343⟩,
⟨128,732293663,732294119⟩]
theorem checked17902 : checkPrefixCuts (2^48) 2350383105 9 Manual.Count131072.C017902.packed 128 cuts17902 = true := by
 decide +kernel
def pointBounds17902 : List (Nat × Nat × Nat) := [(2350452736,98581561971591,98581941478927)]
theorem point_links_checked17902 : (cuts17902.take 1).map (fun c => (2350383105-1+2*2^9*c.k,98581176479488+c.lower,98581555986584+c.upper)) = pointBounds17902 := by
 decide +kernel
def cuts17903 : List PrefixCut := [⟨12,66940268,66940309⟩,
⟨84,478034577,478034869⟩,
⟨128,725666885,725667329⟩]
theorem checked17903 : checkPrefixCuts (2^48) 2350514177 9 Manual.Count131072.C017903.packed 128 cuts17903 = true := by
 decide +kernel
def pointBounds17903 : List (Nat × Nat × Nat) := [(2350526464,98581975713419,98582355221012),(2350600192,98582386807728,98582766315572)]
theorem point_links_checked17903 : (cuts17903.take 2).map (fun c => (2350514177-1+2*2^9*c.k,98581908773151+c.lower,98582288280703+c.upper)) = pointBounds17903 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000246
