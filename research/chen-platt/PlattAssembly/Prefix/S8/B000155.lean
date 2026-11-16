import PlattAssemblyKernel
import PlattCertificates.Count131072.C074960
import PlattCertificates.Count131072.C074961
import PlattCertificates.Count131072.C074962
import PlattCertificates.Count131072.C074963
import PlattCertificates.Count131072.C074964
import PlattCertificates.Count131072.C074965
import PlattCertificates.Count131072.C074966
import PlattCertificates.Count131072.C074967
import PlattCertificates.Count131072.C074968
import PlattCertificates.Count131072.C074969
import PlattCertificates.Count131072.C074970
import PlattCertificates.Count131072.C074971
import PlattCertificates.Count131072.C074972
import PlattCertificates.Count131072.C074973
import PlattCertificates.Count131072.C074974
import PlattCertificates.Count131072.C074975
import PlattCertificates.Count131072.C074976
import PlattCertificates.Count131072.C074977
import PlattCertificates.Count131072.C074978
import PlattCertificates.Count131072.C074979
import PlattCertificates.Count131072.C074980
import PlattCertificates.Count131072.C074981
import PlattCertificates.Count131072.C074982
import PlattCertificates.Count131072.C074983
import PlattCertificates.Count131072.C074984
import PlattCertificates.Count131072.C074985
import PlattCertificates.Count131072.C074986
import PlattCertificates.Count131072.C074987
import PlattCertificates.Count131072.C074988
import PlattCertificates.Count131072.C074989
import PlattCertificates.Count131072.C074990
import PlattCertificates.Count131072.C074991
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000155
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74960 : List PrefixCut := [⟨64,162599381,162599479⟩]
theorem checked74960 : checkPrefixCuts (2^48) 9829089281 10 Manual.Count131072.C074960.packed 64 cuts74960 = true := by
 decide +kernel
def cuts74961 : List PrefixCut := [⟨7,18384647,18384659⟩,
⟨64,164945389,164945490⟩]
theorem checked74961 : checkPrefixCuts (2^48) 9829220353 10 Manual.Count131072.C074961.packed 64 cuts74961 = true := by
 decide +kernel
def pointBounds74961 : List (Nat × Nat × Nat) := [(9829234688,116652377421349,116652767424929)]
theorem point_links_checked74961 : (cuts74961.take 1).map (fun c => (9829220353-1+2*2^10*c.k,116652359036702+c.lower,116652749040270+c.upper)) = pointBounds74961 := by
 decide +kernel
def cuts74962 : List PrefixCut := [⟨64,161363685,161363788⟩]
theorem checked74962 : checkPrefixCuts (2^48) 9829351425 10 Manual.Count131072.C074962.packed 64 cuts74962 = true := by
 decide +kernel
def cuts74963 : List PrefixCut := [⟨29,73479185,73479229⟩,
⟨64,162077430,162077524⟩]
theorem checked74963 : checkPrefixCuts (2^48) 9829482497 10 Manual.Count131072.C074963.packed 64 cuts74963 = true := by
 decide +kernel
def pointBounds74963 : List (Nat × Nat × Nat) := [(9829541888,116652758824961,116653148828777)]
theorem point_links_checked74963 : (cuts74963.take 1).map (fun c => (9829482497-1+2*2^10*c.k,116652685345776+c.lower,116653075349548+c.upper)) = pointBounds74963 := by
 decide +kernel
def cuts74964 : List PrefixCut := [⟨64,162275714,162275814⟩]
theorem checked74964 : checkPrefixCuts (2^48) 9829613569 10 Manual.Count131072.C074964.packed 64 cuts74964 = true := by
 decide +kernel
def cuts74965 : List PrefixCut := [⟨51,132321703,132321779⟩,
⟨64,165623828,165623922⟩]
theorem checked74965 : checkPrefixCuts (2^48) 9829744641 10 Manual.Count131072.C074965.packed 64 cuts74965 = true := by
 decide +kernel
def pointBounds74965 : List (Nat × Nat × Nat) := [(9829849088,116653142020623,116653532024665)]
theorem point_links_checked74965 : (cuts74965.take 1).map (fun c => (9829744641-1+2*2^10*c.k,116653009698920+c.lower,116653399702886+c.upper)) = pointBounds74965 := by
 decide +kernel
def cuts74966 : List PrefixCut := [⟨64,160581960,160582056⟩]
theorem checked74966 : checkPrefixCuts (2^48) 9829875713 10 Manual.Count131072.C074966.packed 64 cuts74966 = true := by
 decide +kernel
def cuts74967 : List PrefixCut := [⟨64,163672294,163672393⟩]
theorem checked74967 : checkPrefixCuts (2^48) 9830006785 10 Manual.Count131072.C074967.packed 64 cuts74967 = true := by
 decide +kernel
def cuts74968 : List PrefixCut := [⟨9,23622921,23622935⟩,
⟨64,161436681,161436784⟩]
theorem checked74968 : checkPrefixCuts (2^48) 9830137857 10 Manual.Count131072.C074968.packed 64 cuts74968 = true := by
 decide +kernel
def pointBounds74968 : List (Nat × Nat × Nat) := [(9830156288,116653523199923,116653913204192)]
theorem point_links_checked74968 : (cuts74968.take 1).map (fun c => (9830137857-1+2*2^10*c.k,116653499577002+c.lower,116653889581257+c.upper)) = pointBounds74968 := by
 decide +kernel
def cuts74969 : List PrefixCut := [⟨64,160632806,160632905⟩]
theorem checked74969 : checkPrefixCuts (2^48) 9830268929 10 Manual.Count131072.C074969.packed 64 cuts74969 = true := by
 decide +kernel
def cuts74970 : List PrefixCut := [⟨31,79571146,79571196⟩,
⟨64,162692237,162692338⟩]
theorem checked74970 : checkPrefixCuts (2^48) 9830400001 10 Manual.Count131072.C074970.packed 64 cuts74970 = true := by
 decide +kernel
def pointBounds74970 : List (Nat × Nat × Nat) := [(9830463488,116653901217635,116654291222142)]
theorem point_links_checked74970 : (cuts74970.take 1).map (fun c => (9830400001-1+2*2^10*c.k,116653821646489+c.lower,116654211650946+c.upper)) = pointBounds74970 := by
 decide +kernel
def cuts74971 : List PrefixCut := [⟨64,161573395,161573484⟩]
theorem checked74971 : checkPrefixCuts (2^48) 9830531073 10 Manual.Count131072.C074971.packed 64 cuts74971 = true := by
 decide +kernel
def cuts74972 : List PrefixCut := [⟨54,138465240,138465326⟩,
⟨64,163919080,163919181⟩]
theorem checked74972 : checkPrefixCuts (2^48) 9830662145 10 Manual.Count131072.C074972.packed 64 cuts74972 = true := by
 decide +kernel
def pointBounds74972 : List (Nat × Nat × Nat) := [(9830772736,116654284377361,116654674382094)]
theorem point_links_checked74972 : (cuts74972.take 1).map (fun c => (9830662145-1+2*2^10*c.k,116654145912121+c.lower,116654535916768+c.upper)) = pointBounds74972 := by
 decide +kernel
def cuts74973 : List PrefixCut := [⟨64,164518161,164518258⟩]
theorem checked74973 : checkPrefixCuts (2^48) 9830793217 10 Manual.Count131072.C074973.packed 64 cuts74973 = true := by
 decide +kernel
def cuts74974 : List PrefixCut := [⟨64,162912599,162912696⟩]
theorem checked74974 : checkPrefixCuts (2^48) 9830924289 10 Manual.Count131072.C074974.packed 64 cuts74974 = true := by
 decide +kernel
def cuts74975 : List PrefixCut := [⟨13,32725416,32725434⟩,
⟨64,162309181,162309275⟩]
theorem checked74975 : checkPrefixCuts (2^48) 9831055361 10 Manual.Count131072.C074975.packed 64 cuts74975 = true := by
 decide +kernel
def pointBounds74975 : List (Nat × Nat × Nat) := [(9831081984,116654669987377,116655059992337)]
theorem point_links_checked74975 : (cuts74975.take 1).map (fun c => (9831055361-1+2*2^10*c.k,116654637261961+c.lower,116655027266903+c.upper)) = pointBounds74975 := by
 decide +kernel
def cuts74976 : List PrefixCut := [⟨64,162221125,162221230⟩]
theorem checked74976 : checkPrefixCuts (2^48) 9831186433 10 Manual.Count131072.C074976.packed 64 cuts74976 = true := by
 decide +kernel
def cuts74977 : List PrefixCut := [⟨36,92304173,92304231⟩,
⟨64,160415271,160415367⟩]
theorem checked74977 : checkPrefixCuts (2^48) 9831317505 10 Manual.Count131072.C074977.packed 64 cuts74977 = true := by
 decide +kernel
def pointBounds74977 : List (Nat × Nat × Nat) := [(9831391232,116655054096440,116655444101639)]
theorem point_links_checked74977 : (cuts74977.take 1).map (fun c => (9831317505-1+2*2^10*c.k,116654961792267+c.lower,116655351797408+c.upper)) = pointBounds74977 := by
 decide +kernel
def cuts74978 : List PrefixCut := [⟨64,164678972,164679068⟩]
theorem checked74978 : checkPrefixCuts (2^48) 9831448577 10 Manual.Count131072.C074978.packed 64 cuts74978 = true := by
 decide +kernel
def cuts74979 : List PrefixCut := [⟨59,148644335,148644425⟩,
⟨64,161183970,161184068⟩]
theorem checked74979 : checkPrefixCuts (2^48) 9831579649 10 Manual.Count131072.C074979.packed 64 cuts74979 = true := by
 decide +kernel
def pointBounds74979 : List (Nat × Nat × Nat) := [(9831700480,116655435530845,116655825536268)]
theorem point_links_checked74979 : (cuts74979.take 1).map (fun c => (9831579649-1+2*2^10*c.k,116655286886510+c.lower,116655676891843+c.upper)) = pointBounds74979 := by
 decide +kernel
def cuts74980 : List PrefixCut := [⟨64,165104019,165104120⟩]
theorem checked74980 : checkPrefixCuts (2^48) 9831710721 10 Manual.Count131072.C074980.packed 64 cuts74980 = true := by
 decide +kernel
def cuts74981 : List PrefixCut := [⟨64,163727630,163727732⟩]
theorem checked74981 : checkPrefixCuts (2^48) 9831841793 10 Manual.Count131072.C074981.packed 64 cuts74981 = true := by
 decide +kernel
def cuts74982 : List PrefixCut := [⟨18,46664408,46664436⟩,
⟨64,166874566,166874666⟩]
theorem checked74982 : checkPrefixCuts (2^48) 9831972865 10 Manual.Count131072.C074982.packed 64 cuts74982 = true := by
 decide +kernel
def pointBounds74982 : List (Nat × Nat × Nat) := [(9832009728,116655823566537,116656213572199)]
theorem point_links_checked74982 : (cuts74982.take 1).map (fun c => (9831972865-1+2*2^10*c.k,116655776902129+c.lower,116656166907763+c.upper)) = pointBounds74982 := by
 decide +kernel
def cuts74983 : List PrefixCut := [⟨64,162778557,162778652⟩]
theorem checked74983 : checkPrefixCuts (2^48) 9832103937 10 Manual.Count131072.C074983.packed 64 cuts74983 = true := by
 decide +kernel
def cuts74984 : List PrefixCut := [⟨41,103088137,103088195⟩,
⟨64,162547350,162547443⟩]
theorem checked74984 : checkPrefixCuts (2^48) 9832235009 10 Manual.Count131072.C074984.packed 64 cuts74984 = true := by
 decide +kernel
def pointBounds74984 : List (Nat × Nat × Nat) := [(9832318976,116656209643389,116656599649276)]
theorem point_links_checked74984 : (cuts74984.take 1).map (fun c => (9832235009-1+2*2^10*c.k,116656106555252+c.lower,116656496561081+c.upper)) = pointBounds74984 := by
 decide +kernel
def cuts74985 : List PrefixCut := [⟨64,162659689,162659791⟩]
theorem checked74985 : checkPrefixCuts (2^48) 9832366081 10 Manual.Count131072.C074985.packed 64 cuts74985 = true := by
 decide +kernel
def cuts74986 : List PrefixCut := [⟨64,160596400,160596502⟩]
theorem checked74986 : checkPrefixCuts (2^48) 9832497153 10 Manual.Count131072.C074986.packed 64 cuts74986 = true := by
 decide +kernel
def pointBounds74986 : List (Nat × Nat × Nat) := [(9832628224,116656592358691,116656982364817)]
theorem point_links_checked74986 : (cuts74986.take 1).map (fun c => (9832497153-1+2*2^10*c.k,116656431762291+c.lower,116656821768315+c.upper)) = pointBounds74986 := by
 decide +kernel
def cuts74987 : List PrefixCut := [⟨64,161825188,161825287⟩]
theorem checked74987 : checkPrefixCuts (2^48) 9832628225 10 Manual.Count131072.C074987.packed 64 cuts74987 = true := by
 decide +kernel
def cuts74988 : List PrefixCut := [⟨64,164542511,164542608⟩]
theorem checked74988 : checkPrefixCuts (2^48) 9832759297 10 Manual.Count131072.C074988.packed 64 cuts74988 = true := by
 decide +kernel
def cuts74989 : List PrefixCut := [⟨23,59198124,59198162⟩,
⟨64,161878144,161878245⟩]
theorem checked74989 : checkPrefixCuts (2^48) 9832890369 10 Manual.Count131072.C074989.packed 64 cuts74989 = true := by
 decide +kernel
def pointBounds74989 : List (Nat × Nat × Nat) := [(9832937472,116656977924514,116657367930874)]
theorem point_links_checked74989 : (cuts74989.take 1).map (fun c => (9832890369-1+2*2^10*c.k,116656918726390+c.lower,116657308732712+c.upper)) = pointBounds74989 := by
 decide +kernel
def cuts74990 : List PrefixCut := [⟨64,163164103,163164199⟩]
theorem checked74990 : checkPrefixCuts (2^48) 9833021441 10 Manual.Count131072.C074990.packed 64 cuts74990 = true := by
 decide +kernel
def cuts74991 : List PrefixCut := [⟨46,117505448,117505519⟩,
⟨64,163219198,163219293⟩]
theorem checked74991 : checkPrefixCuts (2^48) 9833152513 10 Manual.Count131072.C074991.packed 64 cuts74991 = true := by
 decide +kernel
def pointBounds74991 : List (Nat × Nat × Nat) := [(9833246720,116657361274085,116657751280675)]
theorem point_links_checked74991 : (cuts74991.take 1).map (fun c => (9833152513-1+2*2^10*c.k,116657243768637+c.lower,116657633775156+c.upper)) = pointBounds74991 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000155
