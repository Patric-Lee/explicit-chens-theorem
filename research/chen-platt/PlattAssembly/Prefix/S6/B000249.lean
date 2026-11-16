import PlattAssemblyKernel
import PlattCertificates.Count131072.C057968
import PlattCertificates.Count131072.C057969
import PlattCertificates.Count131072.C057970
import PlattCertificates.Count131072.C057971
import PlattCertificates.Count131072.C057972
import PlattCertificates.Count131072.C057973
import PlattCertificates.Count131072.C057974
import PlattCertificates.Count131072.C057975
import PlattCertificates.Count131072.C057976
import PlattCertificates.Count131072.C057977
import PlattCertificates.Count131072.C057978
import PlattCertificates.Count131072.C057979
import PlattCertificates.Count131072.C057980
import PlattCertificates.Count131072.C057981
import PlattCertificates.Count131072.C057982
import PlattCertificates.Count131072.C057983
import PlattCertificates.Count131072.C057984
import PlattCertificates.Count131072.C057985
import PlattCertificates.Count131072.C057986
import PlattCertificates.Count131072.C057987
import PlattCertificates.Count131072.C057988
import PlattCertificates.Count131072.C057989
import PlattCertificates.Count131072.C057990
import PlattCertificates.Count131072.C057991
import PlattCertificates.Count131072.C057992
import PlattCertificates.Count131072.C057993
import PlattCertificates.Count131072.C057994
import PlattCertificates.Count131072.C057995
import PlattCertificates.Count131072.C057996
import PlattCertificates.Count131072.C057997
import PlattCertificates.Count131072.C057998
import PlattCertificates.Count131072.C057999
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000249
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts57968 : List PrefixCut := [⟨64,210088517,210088634⟩]
theorem checked57968 : checkPrefixCuts (2^48) 7601913857 10 Manual.Count131072.C057968.packed 64 cuts57968 = true := by
 decide +kernel
def cuts57969 : List PrefixCut := [⟨20,66535915,66535952⟩,
⟨64,212417527,212417644⟩]
theorem checked57969 : checkPrefixCuts (2^48) 7602044929 10 Manual.Count131072.C057969.packed 64 cuts57969 = true := by
 decide +kernel
def pointBounds57969 : List (Nat × Nat × Nat) := [(7602085888,113491365162258,113491753326770)]
theorem point_links_checked57969 : (cuts57969.take 1).map (fun c => (7602044929-1+2*2^10*c.k,113491298626343+c.lower,113491686790818+c.upper)) = pointBounds57969 := by
 decide +kernel
def cuts57970 : List PrefixCut := [⟨64,209896138,209896259⟩]
theorem checked57970 : checkPrefixCuts (2^48) 7602176001 10 Manual.Count131072.C057970.packed 64 cuts57970 = true := by
 decide +kernel
def cuts57971 : List PrefixCut := [⟨8,26546846,26546862⟩,
⟨64,211965884,211966004⟩]
theorem checked57971 : checkPrefixCuts (2^48) 7602307073 10 Manual.Count131072.C057971.packed 64 cuts57971 = true := by
 decide +kernel
def pointBounds57971 : List (Nat × Nat × Nat) := [(7602323456,113491747486854,113492135651583)]
theorem point_links_checked57971 : (cuts57971.take 1).map (fun c => (7602307073-1+2*2^10*c.k,113491720940008+c.lower,113492109104721+c.upper)) = pointBounds57971 := by
 decide +kernel
def cuts57972 : List PrefixCut := [⟨61,202632288,202632404⟩,
⟨64,212591655,212591777⟩]
theorem checked57972 : checkPrefixCuts (2^48) 7602438145 10 Manual.Count131072.C057972.packed 64 cuts57972 = true := by
 decide +kernel
def pointBounds57972 : List (Nat × Nat × Nat) := [(7602563072,113492135538180,113492523703129)]
theorem point_links_checked57972 : (cuts57972.take 1).map (fun c => (7602438145-1+2*2^10*c.k,113491932905892+c.lower,113492321070725+c.upper)) = pointBounds57972 := by
 decide +kernel
def cuts57973 : List PrefixCut := [⟨64,211329204,211329322⟩]
theorem checked57973 : checkPrefixCuts (2^48) 7602569217 10 Manual.Count131072.C057973.packed 64 cuts57973 = true := by
 decide +kernel
def cuts57974 : List PrefixCut := [⟨50,165417723,165417817⟩,
⟨64,213769040,213769161⟩]
theorem checked57974 : checkPrefixCuts (2^48) 7602700289 10 Manual.Count131072.C057974.packed 64 cuts57974 = true := by
 decide +kernel
def pointBounds57974 : List (Nat × Nat × Nat) := [(7602802688,113492522244474,113492910409641)]
theorem point_links_checked57974 : (cuts57974.take 1).map (fun c => (7602700289-1+2*2^10*c.k,113492356826751+c.lower,113492744991824+c.upper)) = pointBounds57974 := by
 decide +kernel
def cuts57975 : List PrefixCut := [⟨64,215209221,215209344⟩]
theorem checked57975 : checkPrefixCuts (2^48) 7602831361 10 Manual.Count131072.C057975.packed 64 cuts57975 = true := by
 decide +kernel
def cuts57976 : List PrefixCut := [⟨39,130463929,130464001⟩,
⟨64,215279559,215279677⟩]
theorem checked57976 : checkPrefixCuts (2^48) 7602962433 10 Manual.Count131072.C057976.packed 64 cuts57976 = true := by
 decide +kernel
def pointBounds57976 : List (Nat × Nat × Nat) := [(7603042304,113492916268941,113493304434330)]
theorem point_links_checked57976 : (cuts57976.take 1).map (fun c => (7602962433-1+2*2^10*c.k,113492785805012+c.lower,113493173970329+c.upper)) = pointBounds57976 := by
 decide +kernel
def cuts57977 : List PrefixCut := [⟨64,212351205,212351329⟩]
theorem checked57977 : checkPrefixCuts (2^48) 7603093505 10 Manual.Count131072.C057977.packed 64 cuts57977 = true := by
 decide +kernel
def cuts57978 : List PrefixCut := [⟨28,92809954,92810008⟩,
⟨64,212458608,212458730⟩]
theorem checked57978 : checkPrefixCuts (2^48) 7603224577 10 Manual.Count131072.C057978.packed 64 cuts57978 = true := by
 decide +kernel
def pointBounds57978 : List (Nat × Nat × Nat) := [(7603281920,113493306245730,113493694411343)]
theorem point_links_checked57978 : (cuts57978.take 1).map (fun c => (7603224577-1+2*2^10*c.k,113493213435776+c.lower,113493601601335+c.upper)) = pointBounds57978 := by
 decide +kernel
def cuts57979 : List PrefixCut := [⟨64,212825132,212825256⟩]
theorem checked57979 : checkPrefixCuts (2^48) 7603355649 10 Manual.Count131072.C057979.packed 64 cuts57979 = true := by
 decide +kernel
def cuts57980 : List PrefixCut := [⟨17,56194995,56195029⟩,
⟨64,210008040,210008159⟩]
theorem checked57980 : checkPrefixCuts (2^48) 7603486721 10 Manual.Count131072.C057980.packed 64 cuts57980 = true := by
 decide +kernel
def pointBounds57980 : List (Nat × Nat × Nat) := [(7603521536,113493694914511,113494083080350)]
theorem point_links_checked57980 : (cuts57980.take 1).map (fun c => (7603486721-1+2*2^10*c.k,113493638719516+c.lower,113494026885321+c.upper)) = pointBounds57980 := by
 decide +kernel
def cuts57981 : List PrefixCut := [⟨64,214261504,214261631⟩]
theorem checked57981 : checkPrefixCuts (2^48) 7603617793 10 Manual.Count131072.C057981.packed 64 cuts57981 = true := by
 decide +kernel
def cuts57982 : List PrefixCut := [⟨6,19397369,19397380⟩,
⟨64,212925173,212925294⟩]
theorem checked57982 : checkPrefixCuts (2^48) 7603748865 10 Manual.Count131072.C057982.packed 64 cuts57982 = true := by
 decide +kernel
def pointBounds57982 : List (Nat × Nat × Nat) := [(7603761152,113494082386429,113494470552491)]
theorem point_links_checked57982 : (cuts57982.take 1).map (fun c => (7603748865-1+2*2^10*c.k,113494062989060+c.lower,113494451155111+c.upper)) = pointBounds57982 := by
 decide +kernel
def cuts57983 : List PrefixCut := [⟨59,199891676,199891790⟩,
⟨64,216512156,216512280⟩]
theorem checked57983 : checkPrefixCuts (2^48) 7603879937 10 Manual.Count131072.C057983.packed 64 cuts57983 = true := by
 decide +kernel
def pointBounds57983 : List (Nat × Nat × Nat) := [(7604000768,113494475805909,113494863972195)]
theorem point_links_checked57983 : (cuts57983.take 1).map (fun c => (7603879937-1+2*2^10*c.k,113494275914233+c.lower,113494664080405+c.upper)) = pointBounds57983 := by
 decide +kernel
def cuts57984 : List PrefixCut := [⟨64,215583023,215583143⟩]
theorem checked57984 : checkPrefixCuts (2^48) 7604011009 10 Manual.Count131072.C057984.packed 64 cuts57984 = true := by
 decide +kernel
def cuts57985 : List PrefixCut := [⟨48,161092564,161092656⟩,
⟨64,214098672,214098792⟩]
theorem checked57985 : checkPrefixCuts (2^48) 7604142081 10 Manual.Count131072.C057985.packed 64 cuts57985 = true := by
 decide +kernel
def pointBounds57985 : List (Nat × Nat × Nat) := [(7604240384,113494869101976,113495257268484)]
theorem point_links_checked57985 : (cuts57985.take 1).map (fun c => (7604142081-1+2*2^10*c.k,113494708009412+c.lower,113495096175828+c.upper)) = pointBounds57985 := by
 decide +kernel
def cuts57986 : List PrefixCut := [⟨64,213835896,213836020⟩]
theorem checked57986 : checkPrefixCuts (2^48) 7604273153 10 Manual.Count131072.C057986.packed 64 cuts57986 = true := by
 decide +kernel
def cuts57987 : List PrefixCut := [⟨37,123702576,123702646⟩,
⟨64,213721151,213721270⟩]
theorem checked57987 : checkPrefixCuts (2^48) 7604404225 10 Manual.Count131072.C057987.packed 64 cuts57987 = true := by
 decide +kernel
def pointBounds57987 : List (Nat × Nat × Nat) := [(7604480000,113495259646556,113495647813286)]
theorem point_links_checked57987 : (cuts57987.take 1).map (fun c => (7604404225-1+2*2^10*c.k,113495135943980+c.lower,113495524110640+c.upper)) = pointBounds57987 := by
 decide +kernel
def cuts57988 : List PrefixCut := [⟨64,211829795,211829911⟩]
theorem checked57988 : checkPrefixCuts (2^48) 7604535297 10 Manual.Count131072.C057988.packed 64 cuts57988 = true := by
 decide +kernel
def cuts57989 : List PrefixCut := [⟨26,84945561,84945609⟩,
⟨64,209716369,209716489⟩]
theorem checked57989 : checkPrefixCuts (2^48) 7604666369 10 Manual.Count131072.C057989.packed 64 cuts57989 = true := by
 decide +kernel
def pointBounds57989 : List (Nat × Nat × Nat) := [(7604719616,113495646440487,113496034607430)]
theorem point_links_checked57989 : (cuts57989.take 1).map (fun c => (7604666369-1+2*2^10*c.k,113495561494926+c.lower,113495949661821+c.upper)) = pointBounds57989 := by
 decide +kernel
def cuts57990 : List PrefixCut := [⟨64,213377002,213377118⟩]
theorem checked57990 : checkPrefixCuts (2^48) 7604797441 10 Manual.Count131072.C057990.packed 64 cuts57990 = true := by
 decide +kernel
def cuts57991 : List PrefixCut := [⟨15,49115050,49115077⟩,
⟨64,211263645,211263765⟩]
theorem checked57991 : checkPrefixCuts (2^48) 7604928513 10 Manual.Count131072.C057991.packed 64 cuts57991 = true := by
 decide +kernel
def pointBounds57991 : List (Nat × Nat × Nat) := [(7604959232,113496033703347,113496421870505)]
theorem point_links_checked57991 : (cuts57991.take 1).map (fun c => (7604928513-1+2*2^10*c.k,113495984588297+c.lower,113496372755428+c.upper)) = pointBounds57991 := by
 decide +kernel
def cuts57992 : List PrefixCut := [⟨64,214479965,214480087⟩]
theorem checked57992 : checkPrefixCuts (2^48) 7605059585 10 Manual.Count131072.C057992.packed 64 cuts57992 = true := by
 decide +kernel
def cuts57993 : List PrefixCut := [⟨4,12731740,12731748⟩,
⟨64,215253499,215253627⟩]
theorem checked57993 : checkPrefixCuts (2^48) 7605190657 10 Manual.Count131072.C057993.packed 64 cuts57993 = true := by
 decide +kernel
def pointBounds57993 : List (Nat × Nat × Nat) := [(7605198848,113496423063647,113496811231028)]
theorem point_links_checked57993 : (cuts57993.take 1).map (fun c => (7605190657-1+2*2^10*c.k,113496410331907+c.lower,113496798499280+c.upper)) = pointBounds57993 := by
 decide +kernel
def cuts57994 : List PrefixCut := [⟨57,191859676,191859788⟩,
⟨64,215656883,215657008⟩]
theorem checked57994 : checkPrefixCuts (2^48) 7605321729 10 Manual.Count131072.C057994.packed 64 cuts57994 = true := by
 decide +kernel
def pointBounds57994 : List (Nat × Nat × Nat) := [(7605438464,113496817445082,113497205612695)]
theorem point_links_checked57994 : (cuts57994.take 1).map (fun c => (7605321729-1+2*2^10*c.k,113496625585406+c.lower,113497013752907+c.upper)) = pointBounds57994 := by
 decide +kernel
def cuts57995 : List PrefixCut := [⟨64,210323848,210323970⟩]
theorem checked57995 : checkPrefixCuts (2^48) 7605452801 10 Manual.Count131072.C057995.packed 64 cuts57995 = true := by
 decide +kernel
def cuts57996 : List PrefixCut := [⟨46,150958687,150958774⟩,
⟨64,210135169,210135287⟩]
theorem checked57996 : checkPrefixCuts (2^48) 7605583873 10 Manual.Count131072.C057996.packed 64 cuts57996 = true := by
 decide +kernel
def pointBounds57996 : List (Nat × Nat × Nat) := [(7605678080,113497202524824,113497590692659)]
theorem point_links_checked57996 : (cuts57996.take 1).map (fun c => (7605583873-1+2*2^10*c.k,113497051566137+c.lower,113497439733885+c.upper)) = pointBounds57996 := by
 decide +kernel
def cuts57997 : List PrefixCut := [⟨64,213721324,213721447⟩]
theorem checked57997 : checkPrefixCuts (2^48) 7605714945 10 Manual.Count131072.C057997.packed 64 cuts57997 = true := by
 decide +kernel
def cuts57998 : List PrefixCut := [⟨35,116906784,116906849⟩,
⟨64,214013705,214013826⟩]
theorem checked57998 : checkPrefixCuts (2^48) 7605846017 10 Manual.Count131072.C057998.packed 64 cuts57998 = true := by
 decide +kernel
def pointBounds57998 : List (Nat × Nat × Nat) := [(7605917696,113497592329414,113497980497468)]
theorem point_links_checked57998 : (cuts57998.take 1).map (fun c => (7605846017-1+2*2^10*c.k,113497475422630+c.lower,113497863590619+c.upper)) = pointBounds57998 := by
 decide +kernel
def cuts57999 : List PrefixCut := [⟨64,211530553,211530671⟩]
theorem checked57999 : checkPrefixCuts (2^48) 7605977089 10 Manual.Count131072.C057999.packed 64 cuts57999 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000249
