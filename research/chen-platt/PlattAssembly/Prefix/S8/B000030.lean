import PlattAssemblyKernel
import PlattCertificates.Count131072.C070960
import PlattCertificates.Count131072.C070961
import PlattCertificates.Count131072.C070962
import PlattCertificates.Count131072.C070963
import PlattCertificates.Count131072.C070964
import PlattCertificates.Count131072.C070965
import PlattCertificates.Count131072.C070966
import PlattCertificates.Count131072.C070967
import PlattCertificates.Count131072.C070968
import PlattCertificates.Count131072.C070969
import PlattCertificates.Count131072.C070970
import PlattCertificates.Count131072.C070971
import PlattCertificates.Count131072.C070972
import PlattCertificates.Count131072.C070973
import PlattCertificates.Count131072.C070974
import PlattCertificates.Count131072.C070975
import PlattCertificates.Count131072.C070976
import PlattCertificates.Count131072.C070977
import PlattCertificates.Count131072.C070978
import PlattCertificates.Count131072.C070979
import PlattCertificates.Count131072.C070980
import PlattCertificates.Count131072.C070981
import PlattCertificates.Count131072.C070982
import PlattCertificates.Count131072.C070983
import PlattCertificates.Count131072.C070984
import PlattCertificates.Count131072.C070985
import PlattCertificates.Count131072.C070986
import PlattCertificates.Count131072.C070987
import PlattCertificates.Count131072.C070988
import PlattCertificates.Count131072.C070989
import PlattCertificates.Count131072.C070990
import PlattCertificates.Count131072.C070991
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000030
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70960 : List PrefixCut := [⟨64,172971146,172971249⟩]
theorem checked70960 : checkPrefixCuts (2^48) 9304801281 10 Manual.Count131072.C070960.packed 64 cuts70960 = true := by
 decide +kernel
def cuts70961 : List PrefixCut := [⟨23,59925244,59925280⟩,
⟨64,170972203,170972306⟩]
theorem checked70961 : checkPrefixCuts (2^48) 9304932353 10 Manual.Count131072.C070961.packed 64 cuts70961 = true := by
 decide +kernel
def pointBounds70961 : List (Nat × Nat × Nat) := [(9304979456,115981011403039,115981401006811)]
theorem point_links_checked70961 : (cuts70961.take 1).map (fun c => (9304932353-1+2*2^10*c.k,115980951477795+c.lower,115981341081531+c.upper)) = pointBounds70961 := by
 decide +kernel
def cuts70962 : List PrefixCut := [⟨64,169275846,169275951⟩]
theorem checked70962 : checkPrefixCuts (2^48) 9305063425 10 Manual.Count131072.C070962.packed 64 cuts70962 = true := by
 decide +kernel
def cuts70963 : List PrefixCut := [⟨37,100124517,100124573⟩,
⟨64,170664918,170665016⟩]
theorem checked70963 : checkPrefixCuts (2^48) 9305194497 10 Manual.Count131072.C070963.packed 64 cuts70963 = true := by
 decide +kernel
def pointBounds70963 : List (Nat × Nat × Nat) := [(9305270272,115981391850361,115981781454361)]
theorem point_links_checked70963 : (cuts70963.take 1).map (fun c => (9305194497-1+2*2^10*c.k,115981291725844+c.lower,115981681329788+c.upper)) = pointBounds70963 := by
 decide +kernel
def cuts70964 : List PrefixCut := [⟨64,173687366,173687470⟩]
theorem checked70964 : checkPrefixCuts (2^48) 9305325569 10 Manual.Count131072.C070964.packed 64 cuts70964 = true := by
 decide +kernel
def cuts70965 : List PrefixCut := [⟨51,136207653,136207729⟩,
⟨64,172051519,172051616⟩]
theorem checked70965 : checkPrefixCuts (2^48) 9305456641 10 Manual.Count131072.C070965.packed 64 cuts70965 = true := by
 decide +kernel
def pointBounds70965 : List (Nat × Nat × Nat) := [(9305561088,115981772285781,115982161890003)]
theorem point_links_checked70965 : (cuts70965.take 1).map (fun c => (9305456641-1+2*2^10*c.k,115981636078128+c.lower,115982025682274+c.upper)) = pointBounds70965 := by
 decide +kernel
def cuts70966 : List PrefixCut := [⟨64,174680652,174680751⟩]
theorem checked70966 : checkPrefixCuts (2^48) 9305587713 10 Manual.Count131072.C070966.packed 64 cuts70966 = true := by
 decide +kernel
def cuts70967 : List PrefixCut := [⟨64,171925672,171925775⟩]
theorem checked70967 : checkPrefixCuts (2^48) 9305718785 10 Manual.Count131072.C070967.packed 64 cuts70967 = true := by
 decide +kernel
def cuts70968 : List PrefixCut := [⟨1,3085203,3085205⟩,
⟨64,173828810,173828913⟩]
theorem checked70968 : checkPrefixCuts (2^48) 9305849857 10 Manual.Count131072.C070968.packed 64 cuts70968 = true := by
 decide +kernel
def pointBounds70968 : List (Nat × Nat × Nat) := [(9305851904,115982157821174,115982547425621)]
theorem point_links_checked70968 : (cuts70968.take 1).map (fun c => (9305849857-1+2*2^10*c.k,115982154735971+c.lower,115982544340416+c.upper)) = pointBounds70968 := by
 decide +kernel
def cuts70969 : List PrefixCut := [⟨64,173947342,173947443⟩]
theorem checked70969 : checkPrefixCuts (2^48) 9305980929 10 Manual.Count131072.C070969.packed 64 cuts70969 = true := by
 decide +kernel
def cuts70970 : List PrefixCut := [⟨15,39350291,39350318⟩,
⟨64,171857922,171858023⟩]
theorem checked70970 : checkPrefixCuts (2^48) 9306112001 10 Manual.Count131072.C070970.packed 64 cuts70970 = true := by
 decide +kernel
def pointBounds70970 : List (Nat × Nat × Nat) := [(9306142720,115982541862414,115982931467090)]
theorem point_links_checked70970 : (cuts70970.take 1).map (fun c => (9306112001-1+2*2^10*c.k,115982502512123+c.lower,115982892116772+c.upper)) = pointBounds70970 := by
 decide +kernel
def cuts70971 : List PrefixCut := [⟨64,171432066,171432168⟩]
theorem checked70971 : checkPrefixCuts (2^48) 9306243073 10 Manual.Count131072.C070971.packed 64 cuts70971 = true := by
 decide +kernel
def cuts70972 : List PrefixCut := [⟨29,81299345,81299391⟩,
⟨64,177025010,177025116⟩]
theorem checked70972 : checkPrefixCuts (2^48) 9306374145 10 Manual.Count131072.C070972.packed 64 cuts70972 = true := by
 decide +kernel
def pointBounds70972 : List (Nat × Nat × Nat) := [(9306433536,115982927101456,115983316706354)]
theorem point_links_checked70972 : (cuts70972.take 1).map (fun c => (9306374145-1+2*2^10*c.k,115982845802111+c.lower,115983235406963+c.upper)) = pointBounds70972 := by
 decide +kernel
def cuts70973 : List PrefixCut := [⟨64,174239994,174240098⟩]
theorem checked70973 : checkPrefixCuts (2^48) 9306505217 10 Manual.Count131072.C070973.packed 64 cuts70973 = true := by
 decide +kernel
def cuts70974 : List PrefixCut := [⟨44,119919003,119919073⟩,
⟨64,174025835,174025941⟩]
theorem checked70974 : checkPrefixCuts (2^48) 9306636289 10 Manual.Count131072.C070974.packed 64 cuts70974 = true := by
 decide +kernel
def pointBounds70974 : List (Nat × Nat × Nat) := [(9306726400,115983316986118,115983706591250)]
theorem point_links_checked70974 : (cuts70974.take 1).map (fun c => (9306636289-1+2*2^10*c.k,115983197067115+c.lower,115983586672177+c.upper)) = pointBounds70974 := by
 decide +kernel
def cuts70975 : List PrefixCut := [⟨64,173720943,173721044⟩]
theorem checked70975 : checkPrefixCuts (2^48) 9306767361 10 Manual.Count131072.C070975.packed 64 cuts70975 = true := by
 decide +kernel
def cuts70976 : List PrefixCut := [⟨59,157356869,157356962⟩,
⟨64,170603422,170603525⟩]
theorem checked70976 : checkPrefixCuts (2^48) 9306898433 10 Manual.Count131072.C070976.packed 64 cuts70976 = true := by
 decide +kernel
def pointBounds70976 : List (Nat × Nat × Nat) := [(9307019264,115983702170762,115984091776124)]
theorem point_links_checked70976 : (cuts70976.take 1).map (fun c => (9306898433-1+2*2^10*c.k,115983544813893+c.lower,115983934419162+c.upper)) = pointBounds70976 := by
 decide +kernel
def cuts70977 : List PrefixCut := [⟨64,172385376,172385478⟩]
theorem checked70977 : checkPrefixCuts (2^48) 9307029505 10 Manual.Count131072.C070977.packed 64 cuts70977 = true := by
 decide +kernel
def cuts70978 : List PrefixCut := [⟨64,175255980,175256082⟩]
theorem checked70978 : checkPrefixCuts (2^48) 9307160577 10 Manual.Count131072.C070978.packed 64 cuts70978 = true := by
 decide +kernel
def cuts70979 : List PrefixCut := [⟨10,27429832,27429848⟩,
⟨64,174285750,174285849⟩]
theorem checked70979 : checkPrefixCuts (2^48) 9307291649 10 Manual.Count131072.C070979.packed 64 cuts70979 = true := by
 decide +kernel
def pointBounds70979 : List (Nat × Nat × Nat) := [(9307312128,115984090488503,115984480094095)]
theorem point_links_checked70979 : (cuts70979.take 1).map (fun c => (9307291649-1+2*2^10*c.k,115984063058671+c.lower,115984452664247+c.upper)) = pointBounds70979 := by
 decide +kernel
def cuts70980 : List PrefixCut := [⟨64,172075654,172075751⟩]
theorem checked70980 : checkPrefixCuts (2^48) 9307422721 10 Manual.Count131072.C070980.packed 64 cuts70980 = true := by
 decide +kernel
def cuts70981 : List PrefixCut := [⟨25,67559449,67559488⟩,
⟨64,171831312,171831413⟩]
theorem checked70981 : checkPrefixCuts (2^48) 9307553793 10 Manual.Count131072.C070981.packed 64 cuts70981 = true := by
 decide +kernel
def pointBounds70981 : List (Nat × Nat × Nat) := [(9307604992,115984476979524,115984866585335)]
theorem point_links_checked70981 : (cuts70981.take 1).map (fun c => (9307553793-1+2*2^10*c.k,115984409420075+c.lower,115984799025847+c.upper)) = pointBounds70981 := by
 decide +kernel
def cuts70982 : List PrefixCut := [⟨64,172826830,172826938⟩]
theorem checked70982 : checkPrefixCuts (2^48) 9307684865 10 Manual.Count131072.C070982.packed 64 cuts70982 = true := by
 decide +kernel
def cuts70983 : List PrefixCut := [⟨40,107626188,107626251⟩,
⟨64,171191415,171191519⟩]
theorem checked70983 : checkPrefixCuts (2^48) 9307815937 10 Manual.Count131072.C070983.packed 64 cuts70983 = true := by
 decide +kernel
def pointBounds70983 : List (Nat × Nat × Nat) := [(9307897856,115984861704405,115985251310449)]
theorem point_links_checked70983 : (cuts70983.take 1).map (fun c => (9307815937-1+2*2^10*c.k,115984754078217+c.lower,115985143684198+c.upper)) = pointBounds70983 := by
 decide +kernel
def cuts70984 : List PrefixCut := [⟨64,172186930,172187035⟩]
theorem checked70984 : checkPrefixCuts (2^48) 9307947009 10 Manual.Count131072.C070984.packed 64 cuts70984 = true := by
 decide +kernel
def cuts70985 : List PrefixCut := [⟨55,146450716,146450800⟩,
⟨64,171337787,171337885⟩]
theorem checked70985 : checkPrefixCuts (2^48) 9308078081 10 Manual.Count131072.C070985.packed 64 cuts70985 = true := by
 decide +kernel
def pointBounds70985 : List (Nat × Nat × Nat) := [(9308190720,115985243907278,115985633513552)]
theorem point_links_checked70985 : (cuts70985.take 1).map (fun c => (9308078081-1+2*2^10*c.k,115985097456562+c.lower,115985487062752+c.upper)) = pointBounds70985 := by
 decide +kernel
def cuts70986 : List PrefixCut := [⟨64,173542839,173542946⟩]
theorem checked70986 : checkPrefixCuts (2^48) 9308209153 10 Manual.Count131072.C070986.packed 64 cuts70986 = true := by
 decide +kernel
def cuts70987 : List PrefixCut := [⟨64,172058695,172058798⟩]
theorem checked70987 : checkPrefixCuts (2^48) 9308340225 10 Manual.Count131072.C070987.packed 64 cuts70987 = true := by
 decide +kernel
def cuts70988 : List PrefixCut := [⟨6,15300709,15300718⟩,
⟨64,171149115,171149211⟩]
theorem checked70988 : checkPrefixCuts (2^48) 9308471297 10 Manual.Count131072.C070988.packed 64 cuts70988 = true := by
 decide +kernel
def pointBounds70988 : List (Nat × Nat × Nat) := [(9308483584,115985629696592,115986019303099)]
theorem point_links_checked70988 : (cuts70988.take 1).map (fun c => (9308471297-1+2*2^10*c.k,115985614395883+c.lower,115986004002381+c.upper)) = pointBounds70988 := by
 decide +kernel
def cuts70989 : List PrefixCut := [⟨64,172174804,172174901⟩]
theorem checked70989 : checkPrefixCuts (2^48) 9308602369 10 Manual.Count131072.C070989.packed 64 cuts70989 = true := by
 decide +kernel
def cuts70990 : List PrefixCut := [⟨21,57874867,57874898⟩,
⟨64,173533080,173533176⟩]
theorem checked70990 : checkPrefixCuts (2^48) 9308733441 10 Manual.Count131072.C070990.packed 64 cuts70990 = true := by
 decide +kernel
def pointBounds70990 : List (Nat × Nat × Nat) := [(9308776448,115986015594669,115986405201391)]
theorem point_links_checked70990 : (cuts70990.take 1).map (fun c => (9308733441-1+2*2^10*c.k,115985957719802+c.lower,115986347326493+c.upper)) = pointBounds70990 := by
 decide +kernel
def cuts70991 : List PrefixCut := [⟨64,171776880,171776982⟩]
theorem checked70991 : checkPrefixCuts (2^48) 9308864513 10 Manual.Count131072.C070991.packed 64 cuts70991 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000030
