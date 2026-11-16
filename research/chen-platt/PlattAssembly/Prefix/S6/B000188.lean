import PlattAssemblyKernel
import PlattCertificates.Count131072.C056016
import PlattCertificates.Count131072.C056017
import PlattCertificates.Count131072.C056018
import PlattCertificates.Count131072.C056019
import PlattCertificates.Count131072.C056020
import PlattCertificates.Count131072.C056021
import PlattCertificates.Count131072.C056022
import PlattCertificates.Count131072.C056023
import PlattCertificates.Count131072.C056024
import PlattCertificates.Count131072.C056025
import PlattCertificates.Count131072.C056026
import PlattCertificates.Count131072.C056027
import PlattCertificates.Count131072.C056028
import PlattCertificates.Count131072.C056029
import PlattCertificates.Count131072.C056030
import PlattCertificates.Count131072.C056031
import PlattCertificates.Count131072.C056032
import PlattCertificates.Count131072.C056033
import PlattCertificates.Count131072.C056034
import PlattCertificates.Count131072.C056035
import PlattCertificates.Count131072.C056036
import PlattCertificates.Count131072.C056037
import PlattCertificates.Count131072.C056038
import PlattCertificates.Count131072.C056039
import PlattCertificates.Count131072.C056040
import PlattCertificates.Count131072.C056041
import PlattCertificates.Count131072.C056042
import PlattCertificates.Count131072.C056043
import PlattCertificates.Count131072.C056044
import PlattCertificates.Count131072.C056045
import PlattCertificates.Count131072.C056046
import PlattCertificates.Count131072.C056047
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000188
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts56016 : List PrefixCut := [⟨64,221045565,221045690⟩]
theorem checked56016 : checkPrefixCuts (2^48) 7346061313 10 Manual.Count131072.C056016.packed 64 cuts56016 = true := by
 decide +kernel
def cuts56017 : List PrefixCut := [⟨3,10958301,10958307⟩,
⟨64,223148975,223149104⟩]
theorem checked56017 : checkPrefixCuts (2^48) 7346192385 10 Manual.Count131072.C056017.packed 64 cuts56017 = true := by
 decide +kernel
def pointBounds56017 : List (Nat × Nat × Nat) := [(7346198528,113067511959225,113067899882734)]
theorem point_links_checked56017 : (cuts56017.take 1).map (fun c => (7346192385-1+2*2^10*c.k,113067501000924+c.lower,113067888924427+c.upper)) = pointBounds56017 := by
 decide +kernel
def cuts56018 : List PrefixCut := [⟨52,177512432,177512533⟩,
⟨64,219581697,219581822⟩]
theorem checked56018 : checkPrefixCuts (2^48) 7346323457 10 Manual.Count131072.C056018.packed 64 cuts56018 = true := by
 decide +kernel
def pointBounds56018 : List (Nat × Nat × Nat) := [(7346429952,113067901662331,113068289586064)]
theorem point_links_checked56018 : (cuts56018.take 1).map (fun c => (7346323457-1+2*2^10*c.k,113067724149899+c.lower,113068112073531+c.upper)) = pointBounds56018 := by
 decide +kernel
def cuts56019 : List PrefixCut := [⟨64,220650584,220650713⟩]
theorem checked56019 : checkPrefixCuts (2^48) 7346454529 10 Manual.Count131072.C056019.packed 64 cuts56019 = true := by
 decide +kernel
def cuts56020 : List PrefixCut := [⟨37,126779390,126779462⟩,
⟨64,219267368,219267495⟩]
theorem checked56020 : checkPrefixCuts (2^48) 7346585601 10 Manual.Count131072.C056020.packed 64 cuts56020 = true := by
 decide +kernel
def pointBounds56020 : List (Nat × Nat × Nat) := [(7346661376,113068291161570,113068679085528)]
theorem point_links_checked56020 : (cuts56020.take 1).map (fun c => (7346585601-1+2*2^10*c.k,113068164382180+c.lower,113068552306066+c.upper)) = pointBounds56020 := by
 decide +kernel
def cuts56021 : List PrefixCut := [⟨64,222941462,222941585⟩]
theorem checked56021 : checkPrefixCuts (2^48) 7346716673 10 Manual.Count131072.C056021.packed 64 cuts56021 = true := by
 decide +kernel
def cuts56022 : List PrefixCut := [⟨22,76164684,76164727⟩,
⟨64,222975801,222975926⟩]
theorem checked56022 : checkPrefixCuts (2^48) 7346847745 10 Manual.Count131072.C056022.packed 64 cuts56022 = true := by
 decide +kernel
def pointBounds56022 : List (Nat × Nat × Nat) := [(7346892800,113068682755694,113069070679873)]
theorem point_links_checked56022 : (cuts56022.take 1).map (fun c => (7346847745-1+2*2^10*c.k,113068606591010+c.lower,113068994515146+c.upper)) = pointBounds56022 := by
 decide +kernel
def cuts56023 : List PrefixCut := [⟨64,220251738,220251863⟩]
theorem checked56023 : checkPrefixCuts (2^48) 7346978817 10 Manual.Count131072.C056023.packed 64 cuts56023 = true := by
 decide +kernel
def cuts56024 : List PrefixCut := [⟨7,24863795,24863809⟩,
⟨64,219979624,219979751⟩]
theorem checked56024 : checkPrefixCuts (2^48) 7347109889 10 Manual.Count131072.C056024.packed 64 cuts56024 = true := by
 decide +kernel
def pointBounds56024 : List (Nat × Nat × Nat) := [(7347124224,113069074682344,113069462606744)]
theorem point_links_checked56024 : (cuts56024.take 1).map (fun c => (7347109889-1+2*2^10*c.k,113069049818549+c.lower,113069437742935+c.upper)) = pointBounds56024 := by
 decide +kernel
def cuts56025 : List PrefixCut := [⟨56,187565711,187565820⟩,
⟨64,215301893,215302019⟩]
theorem checked56025 : checkPrefixCuts (2^48) 7347240961 10 Manual.Count131072.C056025.packed 64 cuts56025 = true := by
 decide +kernel
def pointBounds56025 : List (Nat × Nat × Nat) := [(7347355648,113069457363884,113069845288506)]
theorem point_links_checked56025 : (cuts56025.take 1).map (fun c => (7347240961-1+2*2^10*c.k,113069269798173+c.lower,113069657722686+c.upper)) = pointBounds56025 := by
 decide +kernel
def cuts56026 : List PrefixCut := [⟨64,220125031,220125155⟩]
theorem checked56026 : checkPrefixCuts (2^48) 7347372033 10 Manual.Count131072.C056026.packed 64 cuts56026 = true := by
 decide +kernel
def cuts56027 : List PrefixCut := [⟨41,141014326,141014409⟩,
⟨64,221002173,221002301⟩]
theorem checked56027 : checkPrefixCuts (2^48) 7347503105 10 Manual.Count131072.C056027.packed 64 cuts56027 = true := by
 decide +kernel
def pointBounds56027 : List (Nat × Nat × Nat) := [(7347587072,113069846239423,113070234164269)]
theorem point_links_checked56027 : (cuts56027.take 1).map (fun c => (7347503105-1+2*2^10*c.k,113069705225097+c.lower,113070093149860+c.upper)) = pointBounds56027 := by
 decide +kernel
def cuts56028 : List PrefixCut := [⟨64,217205754,217205878⟩]
theorem checked56028 : checkPrefixCuts (2^48) 7347634177 10 Manual.Count131072.C056028.packed 64 cuts56028 = true := by
 decide +kernel
def cuts56029 : List PrefixCut := [⟨26,90099036,90099086⟩,
⟨64,223292720,223292844⟩]
theorem checked56029 : checkPrefixCuts (2^48) 7347765249 10 Manual.Count131072.C056029.packed 64 cuts56029 = true := by
 decide +kernel
def pointBounds56029 : List (Nat × Nat × Nat) := [(7347818496,113070233532060,113070621457125)]
theorem point_links_checked56029 : (cuts56029.take 1).map (fun c => (7347765249-1+2*2^10*c.k,113070143433024+c.lower,113070531358039+c.upper)) = pointBounds56029 := by
 decide +kernel
def cuts56030 : List PrefixCut := [⟨64,219956077,219956201⟩]
theorem checked56030 : checkPrefixCuts (2^48) 7347896321 10 Manual.Count131072.C056030.packed 64 cuts56030 = true := by
 decide +kernel
def cuts56031 : List PrefixCut := [⟨11,37501699,37501719⟩,
⟨64,224740371,224740499⟩]
theorem checked56031 : checkPrefixCuts (2^48) 7348027393 10 Manual.Count131072.C056031.packed 64 cuts56031 = true := by
 decide +kernel
def pointBounds56031 : List (Nat × Nat × Nat) := [(7348049920,113070624183520,113071012108803)]
theorem point_links_checked56031 : (cuts56031.take 1).map (fun c => (7348027393-1+2*2^10*c.k,113070586681821+c.lower,113070974607084+c.upper)) = pointBounds56031 := by
 decide +kernel
def cuts56032 : List PrefixCut := [⟨60,210601885,210602004⟩,
⟨64,224736371,224736498⟩]
theorem checked56032 : checkPrefixCuts (2^48) 7348158465 10 Manual.Count131072.C056032.packed 64 cuts56032 = true := by
 decide +kernel
def pointBounds56032 : List (Nat × Nat × Nat) := [(7348281344,113071022024077,113071409949587)]
theorem point_links_checked56032 : (cuts56032.take 1).map (fun c => (7348158465-1+2*2^10*c.k,113070811422192+c.lower,113071199347583+c.upper)) = pointBounds56032 := by
 decide +kernel
def cuts56033 : List PrefixCut := [⟨64,217914167,217914291⟩]
theorem checked56033 : checkPrefixCuts (2^48) 7348289537 10 Manual.Count131072.C056033.packed 64 cuts56033 = true := by
 decide +kernel
def cuts56034 : List PrefixCut := [⟨45,155054172,155054258⟩,
⟨64,220323426,220323548⟩]
theorem checked56034 : checkPrefixCuts (2^48) 7348420609 10 Manual.Count131072.C056034.packed 64 cuts56034 = true := by
 decide +kernel
def pointBounds56034 : List (Nat × Nat × Nat) := [(7348512768,113071409126902,113071797052630)]
theorem point_links_checked56034 : (cuts56034.take 1).map (fun c => (7348420609-1+2*2^10*c.k,113071254072730+c.lower,113071641998372+c.upper)) = pointBounds56034 := by
 decide +kernel
def cuts56035 : List PrefixCut := [⟨64,219744941,219745066⟩]
theorem checked56035 : checkPrefixCuts (2^48) 7348551681 10 Manual.Count131072.C056035.packed 64 cuts56035 = true := by
 decide +kernel
def cuts56036 : List PrefixCut := [⟨30,103302135,103302192⟩,
⟨64,220545372,220545494⟩]
theorem checked56036 : checkPrefixCuts (2^48) 7348682753 10 Manual.Count131072.C056036.packed 64 cuts56036 = true := by
 decide +kernel
def pointBounds56036 : List (Nat × Nat × Nat) := [(7348744192,113071797443232,113072185369178)]
theorem point_links_checked56036 : (cuts56036.take 1).map (fun c => (7348682753-1+2*2^10*c.k,113071694141097+c.lower,113072082066986+c.upper)) = pointBounds56036 := by
 decide +kernel
def cuts56037 : List PrefixCut := [⟨64,225903695,225903822⟩]
theorem checked56037 : checkPrefixCuts (2^48) 7348813825 10 Manual.Count131072.C056037.packed 64 cuts56037 = true := by
 decide +kernel
def cuts56038 : List PrefixCut := [⟨15,50519444,50519472⟩,
⟨64,219082055,219082182⟩]
theorem checked56038 : checkPrefixCuts (2^48) 7348944897 10 Manual.Count131072.C056038.packed 64 cuts56038 = true := by
 decide +kernel
def pointBounds56038 : List (Nat × Nat × Nat) := [(7348975616,113072191109608,113072579035774)]
theorem point_links_checked56038 : (cuts56038.take 1).map (fun c => (7348944897-1+2*2^10*c.k,113072140590164+c.lower,113072528516302+c.upper)) = pointBounds56038 := by
 decide +kernel
def cuts56039 : List PrefixCut := [⟨64,220495299,220495426⟩]
theorem checked56039 : checkPrefixCuts (2^48) 7349075969 10 Manual.Count131072.C056039.packed 64 cuts56039 = true := by
 decide +kernel
def pointBounds56039 : List (Nat × Nat × Nat) := [(7349207040,113072580167518,113072968093910)]
theorem point_links_checked56039 : (cuts56039.take 1).map (fun c => (7349075969-1+2*2^10*c.k,113072359672219+c.lower,113072747598484+c.upper)) = pointBounds56039 := by
 decide +kernel
def cuts56040 : List PrefixCut := [⟨64,220950939,220951064⟩]
theorem checked56040 : checkPrefixCuts (2^48) 7349207041 10 Manual.Count131072.C056040.packed 64 cuts56040 = true := by
 decide +kernel
def cuts56041 : List PrefixCut := [⟨49,169779878,169779975⟩,
⟨64,221827876,221828003⟩]
theorem checked56041 : checkPrefixCuts (2^48) 7349338113 10 Manual.Count131072.C056041.packed 64 cuts56041 = true := by
 decide +kernel
def pointBounds56041 : List (Nat × Nat × Nat) := [(7349438464,113072970898335,113073358824949)]
theorem point_links_checked56041 : (cuts56041.take 1).map (fun c => (7349338113-1+2*2^10*c.k,113072801118457+c.lower,113073189044974+c.upper)) = pointBounds56041 := by
 decide +kernel
def cuts56042 : List PrefixCut := [⟨64,223202673,223202794⟩]
theorem checked56042 : checkPrefixCuts (2^48) 7349469185 10 Manual.Count131072.C056042.packed 64 cuts56042 = true := by
 decide +kernel
def cuts56043 : List PrefixCut := [⟨34,119106165,119106234⟩,
⟨64,220096580,220096708⟩]
theorem checked56043 : checkPrefixCuts (2^48) 7349600257 10 Manual.Count131072.C056043.packed 64 cuts56043 = true := by
 decide +kernel
def pointBounds56043 : List (Nat × Nat × Nat) := [(7349669888,113073365255171,113073753182005)]
theorem point_links_checked56043 : (cuts56043.take 1).map (fun c => (7349600257-1+2*2^10*c.k,113073246149006+c.lower,113073634075771+c.upper)) = pointBounds56043 := by
 decide +kernel
def cuts56044 : List PrefixCut := [⟨64,220169234,220169361⟩]
theorem checked56044 : checkPrefixCuts (2^48) 7349731329 10 Manual.Count131072.C056044.packed 64 cuts56044 = true := by
 decide +kernel
def cuts56045 : List PrefixCut := [⟨19,65678532,65678569⟩,
⟨64,221046126,221046251⟩]
theorem checked56045 : checkPrefixCuts (2^48) 7349862401 10 Manual.Count131072.C056045.packed 64 cuts56045 = true := by
 decide +kernel
def pointBounds56045 : List (Nat × Nat × Nat) := [(7349901312,113073752093352,113074140020409)]
theorem point_links_checked56045 : (cuts56045.take 1).map (fun c => (7349862401-1+2*2^10*c.k,113073686414820+c.lower,113074074341840+c.upper)) = pointBounds56045 := by
 decide +kernel
def cuts56046 : List PrefixCut := [⟨64,222420827,222420950⟩]
theorem checked56046 : checkPrefixCuts (2^48) 7349993473 10 Manual.Count131072.C056046.packed 64 cuts56046 = true := by
 decide +kernel
def cuts56047 : List PrefixCut := [⟨4,13747990,13747998⟩,
⟨64,221153130,221153256⟩]
theorem checked56047 : checkPrefixCuts (2^48) 7350124545 10 Manual.Count131072.C056047.packed 64 cuts56047 = true := by
 decide +kernel
def pointBounds56047 : List (Nat × Nat × Nat) := [(7350132736,113074143629763,113074531557039)]
theorem point_links_checked56047 : (cuts56047.take 1).map (fun c => (7350124545-1+2*2^10*c.k,113074129881773+c.lower,113074517809041+c.upper)) = pointBounds56047 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000188
