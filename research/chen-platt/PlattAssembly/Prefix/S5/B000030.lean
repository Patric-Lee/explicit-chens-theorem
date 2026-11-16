import PlattAssemblyKernel
import PlattCertificates.Count131072.C040960
import PlattCertificates.Count131072.C040961
import PlattCertificates.Count131072.C040962
import PlattCertificates.Count131072.C040963
import PlattCertificates.Count131072.C040964
import PlattCertificates.Count131072.C040965
import PlattCertificates.Count131072.C040966
import PlattCertificates.Count131072.C040967
import PlattCertificates.Count131072.C040968
import PlattCertificates.Count131072.C040969
import PlattCertificates.Count131072.C040970
import PlattCertificates.Count131072.C040971
import PlattCertificates.Count131072.C040972
import PlattCertificates.Count131072.C040973
import PlattCertificates.Count131072.C040974
import PlattCertificates.Count131072.C040975
import PlattCertificates.Count131072.C040976
import PlattCertificates.Count131072.C040977
import PlattCertificates.Count131072.C040978
import PlattCertificates.Count131072.C040979
import PlattCertificates.Count131072.C040980
import PlattCertificates.Count131072.C040981
import PlattCertificates.Count131072.C040982
import PlattCertificates.Count131072.C040983
import PlattCertificates.Count131072.C040984
import PlattCertificates.Count131072.C040985
import PlattCertificates.Count131072.C040986
import PlattCertificates.Count131072.C040987
import PlattCertificates.Count131072.C040988
import PlattCertificates.Count131072.C040989
import PlattCertificates.Count131072.C040990
import PlattCertificates.Count131072.C040991
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000030
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40960 : List PrefixCut := [⟨43,205630695,205630818⟩,
⟨64,307056467,307056649⟩]
theorem checked40960 : checkPrefixCuts (2^48) 5372641281 10 Manual.Count131072.C040960.packed 64 cuts40960 = true := by
 decide +kernel
def pointBounds40960 : List (Nat × Nat × Nat) := [(5372729344,109164319683145,109164705365307)]
theorem point_links_checked40960 : (cuts40960.take 1).map (fun c => (5372641281-1+2*2^10*c.k,109164114052450+c.lower,109164499734489+c.upper)) = pointBounds40960 := by
 decide +kernel
def cuts40961 : List PrefixCut := [⟨61,292380402,292380575⟩,
⟨64,306420356,306420537⟩]
theorem checked40961 : checkPrefixCuts (2^48) 5372772353 10 Manual.Count131072.C040961.packed 64 cuts40961 = true := by
 decide +kernel
def pointBounds40961 : List (Nat × Nat × Nat) := [(5372897280,109164713489319,109165099171713)]
theorem point_links_checked40961 : (cuts40961.take 1).map (fun c => (5372772353-1+2*2^10*c.k,109164421108917+c.lower,109164806791138+c.upper)) = pointBounds40961 := by
 decide +kernel
def cuts40962 : List PrefixCut := [⟨64,307617722,307617904⟩]
theorem checked40962 : checkPrefixCuts (2^48) 5372903425 10 Manual.Count131072.C040962.packed 64 cuts40962 = true := by
 decide +kernel
def cuts40963 : List PrefixCut := [⟨15,70197814,70197856⟩,
⟨64,305252836,305253016⟩]
theorem checked40963 : checkPrefixCuts (2^48) 5373034497 10 Manual.Count131072.C040963.packed 64 cuts40963 = true := by
 decide +kernel
def pointBounds40963 : List (Nat × Nat × Nat) := [(5373065216,109165105344809,109165491027435)]
theorem point_links_checked40963 : (cuts40963.take 1).map (fun c => (5373034497-1+2*2^10*c.k,109165035146995+c.lower,109165420829579+c.upper)) = pointBounds40963 := by
 decide +kernel
def cuts40964 : List PrefixCut := [⟨33,157312074,157312167⟩,
⟨64,306816960,306817141⟩]
theorem checked40964 : checkPrefixCuts (2^48) 5373165569 10 Manual.Count131072.C040964.packed 64 cuts40964 = true := by
 decide +kernel
def pointBounds40964 : List (Nat × Nat × Nat) := [(5373233152,109165497711905,109165883394762)]
theorem point_links_checked40964 : (cuts40964.take 1).map (fun c => (5373165569-1+2*2^10*c.k,109165340399831+c.lower,109165726082595+c.upper)) = pointBounds40964 := by
 decide +kernel
def cuts40965 : List PrefixCut := [⟨51,243269033,243269180⟩,
⟨64,304661764,304661947⟩]
theorem checked40965 : checkPrefixCuts (2^48) 5373296641 10 Manual.Count131072.C040965.packed 64 cuts40965 = true := by
 decide +kernel
def pointBounds40965 : List (Nat × Nat × Nat) := [(5373401088,109165890485824,109166276168916)]
theorem point_links_checked40965 : (cuts40965.take 1).map (fun c => (5373296641-1+2*2^10*c.k,109165647216791+c.lower,109166032899736+c.upper)) = pointBounds40965 := by
 decide +kernel
def cuts40966 : List PrefixCut := [⟨64,307378239,307378418⟩]
theorem checked40966 : checkPrefixCuts (2^48) 5373427713 10 Manual.Count131072.C040966.packed 64 cuts40966 = true := by
 decide +kernel
def cuts40967 : List PrefixCut := [⟨5,23519256,23519270⟩,
⟨64,309361131,309361313⟩]
theorem checked40967 : checkPrefixCuts (2^48) 5373558785 10 Manual.Count131072.C040967.packed 64 cuts40967 = true := by
 decide +kernel
def pointBounds40967 : List (Nat × Nat × Nat) := [(5373569024,109166282776050,109166668459371)]
theorem point_links_checked40967 : (cuts40967.take 1).map (fun c => (5373558785-1+2*2^10*c.k,109166259256794+c.lower,109166644940101+c.upper)) = pointBounds40967 := by
 decide +kernel
def cuts40968 : List PrefixCut := [⟨23,112040736,112040799⟩,
⟨64,308306044,308306226⟩]
theorem checked40968 : checkPrefixCuts (2^48) 5373689857 10 Manual.Count131072.C040968.packed 64 cuts40968 = true := by
 decide +kernel
def pointBounds40968 : List (Nat × Nat × Nat) := [(5373736960,109166680658661,109167066342213)]
theorem point_links_checked40968 : (cuts40968.take 1).map (fun c => (5373689857-1+2*2^10*c.k,109166568617925+c.lower,109166954301414+c.upper)) = pointBounds40968 := by
 decide +kernel
def cuts40969 : List PrefixCut := [⟨41,196628895,196629015⟩,
⟨64,307984238,307984423⟩]
theorem checked40969 : checkPrefixCuts (2^48) 5373820929 10 Manual.Count131072.C040969.packed 64 cuts40969 = true := by
 decide +kernel
def pointBounds40969 : List (Nat × Nat × Nat) := [(5373904896,109167073552864,109167459236655)]
theorem point_links_checked40969 : (cuts40969.take 1).map (fun c => (5373820929-1+2*2^10*c.k,109166876923969+c.lower,109167262607640+c.upper)) = pointBounds40969 := by
 decide +kernel
def cuts40970 : List PrefixCut := [⟨59,282102752,282102921⟩,
⟨64,305043618,305043800⟩]
theorem checked40970 : checkPrefixCuts (2^48) 5373952001 10 Manual.Count131072.C040970.packed 64 cuts40970 = true := by
 decide +kernel
def pointBounds40970 : List (Nat × Nat × Nat) := [(5374072832,109167467010959,109167852694984)]
theorem point_links_checked40970 : (cuts40970.take 1).map (fun c => (5373952001-1+2*2^10*c.k,109167184908207+c.lower,109167570592063+c.upper)) = pointBounds40970 := by
 decide +kernel
def cuts40971 : List PrefixCut := [⟨64,304564804,304564984⟩]
theorem checked40971 : checkPrefixCuts (2^48) 5374083073 10 Manual.Count131072.C040971.packed 64 cuts40971 = true := by
 decide +kernel
def cuts40972 : List PrefixCut := [⟨14,65730552,65730591⟩,
⟨64,306076245,306076426⟩]
theorem checked40972 : checkPrefixCuts (2^48) 5374214145 10 Manual.Count131072.C040972.packed 64 cuts40972 = true := by
 decide +kernel
def pointBounds40972 : List (Nat × Nat × Nat) := [(5374242816,109167860247181,109168245931438)]
theorem point_links_checked40972 : (cuts40972.take 1).map (fun c => (5374214145-1+2*2^10*c.k,109167794516629+c.lower,109168180200847+c.upper)) = pointBounds40972 := by
 decide +kernel
def cuts40973 : List PrefixCut := [⟨33,158220266,158220355⟩,
⟨64,304811831,304812007⟩]
theorem checked40973 : checkPrefixCuts (2^48) 5374345217 10 Manual.Count131072.C040973.packed 64 cuts40973 = true := by
 decide +kernel
def pointBounds40973 : List (Nat × Nat × Nat) := [(5374412800,109168258813140,109168644497628)]
theorem point_links_checked40973 : (cuts40973.take 1).map (fun c => (5374345217-1+2*2^10*c.k,109168100592874+c.lower,109168486277273+c.upper)) = pointBounds40973 := by
 decide +kernel
def cuts40974 : List PrefixCut := [⟨52,249081265,249081414⟩,
⟨64,305118626,305118809⟩]
theorem checked40974 : checkPrefixCuts (2^48) 5374476289 10 Manual.Count131072.C040974.packed 64 cuts40974 = true := by
 decide +kernel
def pointBounds40974 : List (Nat × Nat × Nat) := [(5374582784,109168654485970,109169040170694)]
theorem point_links_checked40974 : (cuts40974.take 1).map (fun c => (5374476289-1+2*2^10*c.k,109168405404705+c.lower,109168791089280+c.upper)) = pointBounds40974 := by
 decide +kernel
def cuts40975 : List PrefixCut := [⟨64,307153630,307153814⟩]
theorem checked40975 : checkPrefixCuts (2^48) 5374607361 10 Manual.Count131072.C040975.packed 64 cuts40975 = true := by
 decide +kernel
def cuts40976 : List PrefixCut := [⟨7,35035463,35035483⟩,
⟨64,305941657,305941834⟩]
theorem checked40976 : checkPrefixCuts (2^48) 5374738433 10 Manual.Count131072.C040976.packed 64 cuts40976 = true := by
 decide +kernel
def pointBounds40976 : List (Nat × Nat × Nat) := [(5374752768,109169052712424,109169438397386)]
theorem point_links_checked40976 : (cuts40976.take 1).map (fun c => (5374738433-1+2*2^10*c.k,109169017676961+c.lower,109169403361903+c.upper)) = pointBounds40976 := by
 decide +kernel
def cuts40977 : List PrefixCut := [⟨26,124375038,124375112⟩,
⟨64,303525255,303525434⟩]
theorem checked40977 : checkPrefixCuts (2^48) 5374869505 10 Manual.Count131072.C040977.packed 64 cuts40977 = true := by
 decide +kernel
def pointBounds40977 : List (Nat × Nat × Nat) := [(5374922752,109169447993656,109169833678849)]
theorem point_links_checked40977 : (cuts40977.take 1).map (fun c => (5374869505-1+2*2^10*c.k,109169323618618+c.lower,109169709303737+c.upper)) = pointBounds40977 := by
 decide +kernel
def cuts40978 : List PrefixCut := [⟨45,218684452,218684581⟩,
⟨64,307026448,307026629⟩]
theorem checked40978 : checkPrefixCuts (2^48) 5375000577 10 Manual.Count131072.C040978.packed 64 cuts40978 = true := by
 decide +kernel
def pointBounds40978 : List (Nat × Nat × Nat) := [(5375092736,109169845828325,109170231513752)]
theorem point_links_checked40978 : (cuts40978.take 1).map (fun c => (5375000577-1+2*2^10*c.k,109169627143873+c.lower,109170012829171+c.upper)) = pointBounds40978 := by
 decide +kernel
def cuts40979 : List PrefixCut := [⟨64,303615172,303615351⟩]
theorem checked40979 : checkPrefixCuts (2^48) 5375131649 10 Manual.Count131072.C040979.packed 64 cuts40979 = true := by
 decide +kernel
def pointBounds40979 : List (Nat × Nat × Nat) := [(5375262720,109170237785493,109170623471151)]
theorem point_links_checked40979 : (cuts40979.take 1).map (fun c => (5375131649-1+2*2^10*c.k,109169934170321+c.lower,109170319855800+c.upper)) = pointBounds40979 := by
 decide +kernel
def cuts40980 : List PrefixCut := [⟨64,308425272,308425454⟩]
theorem checked40980 : checkPrefixCuts (2^48) 5375262721 10 Manual.Count131072.C040980.packed 64 cuts40980 = true := by
 decide +kernel
def cuts40981 : List PrefixCut := [⟨19,91897759,91897814⟩,
⟨64,309307933,309308113⟩]
theorem checked40981 : checkPrefixCuts (2^48) 5375393793 10 Manual.Count131072.C040981.packed 64 cuts40981 = true := by
 decide +kernel
def pointBounds40981 : List (Nat × Nat × Nat) := [(5375432704,109170638108524,109171023794419)]
theorem point_links_checked40981 : (cuts40981.take 1).map (fun c => (5375393793-1+2*2^10*c.k,109170546210765+c.lower,109170931896605+c.upper)) = pointBounds40981 := by
 decide +kernel
def cuts40982 : List PrefixCut := [⟨38,179601419,179601527⟩,
⟨64,300503644,300503824⟩]
theorem checked40982 : checkPrefixCuts (2^48) 5375524865 10 Manual.Count131072.C040982.packed 64 cuts40982 = true := by
 decide +kernel
def pointBounds40982 : List (Nat × Nat × Nat) := [(5375602688,109171035120117,109171420806245)]
theorem point_links_checked40982 : (cuts40982.take 1).map (fun c => (5375524865-1+2*2^10*c.k,109170855518698+c.lower,109171241204718+c.upper)) = pointBounds40982 := by
 decide +kernel
def cuts40983 : List PrefixCut := [⟨57,273269255,273269415⟩,
⟨64,307041341,307041521⟩]
theorem checked40983 : checkPrefixCuts (2^48) 5375655937 10 Manual.Count131072.C040983.packed 64 cuts40983 = true := by
 decide +kernel
def pointBounds40983 : List (Nat × Nat × Nat) := [(5375772672,109171429291597,109171814977957)]
theorem point_links_checked40983 : (cuts40983.take 1).map (fun c => (5375655937-1+2*2^10*c.k,109171156022342+c.lower,109171541708542+c.upper)) = pointBounds40983 := by
 decide +kernel
def cuts40984 : List PrefixCut := [⟨64,308447531,308447715⟩]
theorem checked40984 : checkPrefixCuts (2^48) 5375787009 10 Manual.Count131072.C040984.packed 64 cuts40984 = true := by
 decide +kernel
def cuts40985 : List PrefixCut := [⟨12,57541835,57541868⟩,
⟨64,306241007,306241188⟩]
theorem checked40985 : checkPrefixCuts (2^48) 5375918081 10 Manual.Count131072.C040985.packed 64 cuts40985 = true := by
 decide +kernel
def pointBounds40985 : List (Nat × Nat × Nat) := [(5375942656,109171829053049,109172214739646)]
theorem point_links_checked40985 : (cuts40985.take 1).map (fun c => (5375918081-1+2*2^10*c.k,109171771511214+c.lower,109172157197778+c.upper)) = pointBounds40985 := by
 decide +kernel
def cuts40986 : List PrefixCut := [⟨31,144400307,144400395⟩,
⟨64,302673273,302673455⟩]
theorem checked40986 : checkPrefixCuts (2^48) 5376049153 10 Manual.Count131072.C040986.packed 64 cuts40986 = true := by
 decide +kernel
def pointBounds40986 : List (Nat × Nat × Nat) := [(5376112640,109172222152528,109172607839361)]
theorem point_links_checked40986 : (cuts40986.take 1).map (fun c => (5376049153-1+2*2^10*c.k,109172077752221+c.lower,109172463438966+c.upper)) = pointBounds40986 := by
 decide +kernel
def cuts40987 : List PrefixCut := [⟨50,238374245,238374384⟩,
⟨64,306435468,306435647⟩]
theorem checked40987 : checkPrefixCuts (2^48) 5376180225 10 Manual.Count131072.C040987.packed 64 cuts40987 = true := by
 decide +kernel
def pointBounds40987 : List (Nat × Nat × Nat) := [(5376282624,109172618799739,109173004486805)]
theorem point_links_checked40987 : (cuts40987.take 1).map (fun c => (5376180225-1+2*2^10*c.k,109172380425494+c.lower,109172766112421+c.upper)) = pointBounds40987 := by
 decide +kernel
def cuts40988 : List PrefixCut := [⟨64,307160977,307161155⟩]
theorem checked40988 : checkPrefixCuts (2^48) 5376311297 10 Manual.Count131072.C040988.packed 64 cuts40988 = true := by
 decide +kernel
def cuts40989 : List PrefixCut := [⟨5,23454289,23454302⟩,
⟨64,308567015,308567200⟩]
theorem checked40989 : checkPrefixCuts (2^48) 5376442369 10 Manual.Count131072.C040989.packed 64 cuts40989 = true := by
 decide +kernel
def pointBounds40989 : List (Nat × Nat × Nat) := [(5376452608,109173017476228,109173403163525)]
theorem point_links_checked40989 : (cuts40989.take 1).map (fun c => (5376442369-1+2*2^10*c.k,109172994021939+c.lower,109173379709223+c.upper)) = pointBounds40989 := by
 decide +kernel
def cuts40990 : List PrefixCut := [⟨24,115174094,115174162⟩,
⟨64,305837234,305837411⟩]
theorem checked40990 : checkPrefixCuts (2^48) 5376573441 10 Manual.Count131072.C040990.packed 64 cuts40990 = true := by
 decide +kernel
def pointBounds40990 : List (Nat × Nat × Nat) := [(5376622592,109173417763048,109173803450585)]
theorem point_links_checked40990 : (cuts40990.take 1).map (fun c => (5376573441-1+2*2^10*c.k,109173302588954+c.lower,109173688276423+c.upper)) = pointBounds40990 := by
 decide +kernel
def cuts40991 : List PrefixCut := [⟨43,207098153,207098275⟩,
⟨64,306824433,306824614⟩]
theorem checked40991 : checkPrefixCuts (2^48) 5376704513 10 Manual.Count131072.C040991.packed 64 cuts40991 = true := by
 decide +kernel
def pointBounds40991 : List (Nat × Nat × Nat) := [(5376792576,109173815524341,109174201212109)]
theorem point_links_checked40991 : (cuts40991.take 1).map (fun c => (5376704513-1+2*2^10*c.k,109173608426188+c.lower,109173994113834+c.upper)) = pointBounds40991 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000030
