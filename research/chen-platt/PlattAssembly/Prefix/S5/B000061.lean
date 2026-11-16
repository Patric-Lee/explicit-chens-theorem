import PlattAssemblyKernel
import PlattCertificates.Count131072.C041952
import PlattCertificates.Count131072.C041953
import PlattCertificates.Count131072.C041954
import PlattCertificates.Count131072.C041955
import PlattCertificates.Count131072.C041956
import PlattCertificates.Count131072.C041957
import PlattCertificates.Count131072.C041958
import PlattCertificates.Count131072.C041959
import PlattCertificates.Count131072.C041960
import PlattCertificates.Count131072.C041961
import PlattCertificates.Count131072.C041962
import PlattCertificates.Count131072.C041963
import PlattCertificates.Count131072.C041964
import PlattCertificates.Count131072.C041965
import PlattCertificates.Count131072.C041966
import PlattCertificates.Count131072.C041967
import PlattCertificates.Count131072.C041968
import PlattCertificates.Count131072.C041969
import PlattCertificates.Count131072.C041970
import PlattCertificates.Count131072.C041971
import PlattCertificates.Count131072.C041972
import PlattCertificates.Count131072.C041973
import PlattCertificates.Count131072.C041974
import PlattCertificates.Count131072.C041975
import PlattCertificates.Count131072.C041976
import PlattCertificates.Count131072.C041977
import PlattCertificates.Count131072.C041978
import PlattCertificates.Count131072.C041979
import PlattCertificates.Count131072.C041980
import PlattCertificates.Count131072.C041981
import PlattCertificates.Count131072.C041982
import PlattCertificates.Count131072.C041983
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000061
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts41952 : List PrefixCut := [⟨64,298982612,298982790⟩]
theorem checked41952 : checkPrefixCuts (2^48) 5502664705 10 Manual.Count131072.C041952.packed 64 cuts41952 = true := by
 decide +kernel
def cuts41953 : List PrefixCut := [⟨13,59642214,59642250⟩,
⟨64,301072671,301072844⟩]
theorem checked41953 : checkPrefixCuts (2^48) 5502795777 10 Manual.Count131072.C041953.packed 64 cuts41953 = true := by
 decide +kernel
def pointBounds41953 : List (Nat × Nat × Nat) := [(5502822400,109464716151211,109465102010120)]
theorem point_links_checked41953 : (cuts41953.take 1).map (fun c => (5502795777-1+2*2^10*c.k,109464656508997+c.lower,109465042367870+c.upper)) = pointBounds41953 := by
 decide +kernel
def cuts41954 : List PrefixCut := [⟨33,151863525,151863615⟩,
⟨64,296462059,296462237⟩]
theorem checked41954 : checkPrefixCuts (2^48) 5502926849 10 Manual.Count131072.C041954.packed 64 cuts41954 = true := by
 decide +kernel
def pointBounds41954 : List (Nat × Nat × Nat) := [(5502994432,109465109445193,109465495304329)]
theorem point_links_checked41954 : (cuts41954.take 1).map (fun c => (5502926849-1+2*2^10*c.k,109464957581668+c.lower,109465343440714+c.upper)) = pointBounds41954 := by
 decide +kernel
def cuts41955 : List PrefixCut := [⟨53,247455517,247455663⟩,
⟨64,298040592,298040768⟩]
theorem checked41955 : checkPrefixCuts (2^48) 5503057921 10 Manual.Count131072.C041955.packed 64 cuts41955 = true := by
 decide +kernel
def pointBounds41955 : List (Nat × Nat × Nat) := [(5503166464,109465501499244,109465887358614)]
theorem point_links_checked41955 : (cuts41955.take 1).map (fun c => (5503057921-1+2*2^10*c.k,109465254043727+c.lower,109465639902951+c.upper)) = pointBounds41955 := by
 decide +kernel
def cuts41956 : List PrefixCut := [⟨64,297010592,297010769⟩]
theorem checked41956 : checkPrefixCuts (2^48) 5503188993 10 Manual.Count131072.C041956.packed 64 cuts41956 = true := by
 decide +kernel
def cuts41957 : List PrefixCut := [⟨9,42707154,42707177⟩,
⟨64,299100471,299100645⟩]
theorem checked41957 : checkPrefixCuts (2^48) 5503320065 10 Manual.Count131072.C041957.packed 64 cuts41957 = true := by
 decide +kernel
def pointBounds41957 : List (Nat × Nat × Nat) := [(5503338496,109465891802065,109466277661665)]
theorem point_links_checked41957 : (cuts41957.take 1).map (fun c => (5503320065-1+2*2^10*c.k,109465849094911+c.lower,109466234954488+c.upper)) = pointBounds41957 := by
 decide +kernel
def cuts41958 : List PrefixCut := [⟨29,134562189,134562267⟩,
⟨64,297303277,297303450⟩]
theorem checked41958 : checkPrefixCuts (2^48) 5503451137 10 Manual.Count131072.C041958.packed 64 cuts41958 = true := by
 decide +kernel
def pointBounds41958 : List (Nat × Nat × Nat) := [(5503510528,109466282757571,109466668617400)]
theorem point_links_checked41958 : (cuts41958.take 1).map (fun c => (5503451137-1+2*2^10*c.k,109466148195382+c.lower,109466534055133+c.upper)) = pointBounds41958 := by
 decide +kernel
def cuts41959 : List PrefixCut := [⟨49,228151045,228151182⟩,
⟨64,295966485,295966666⟩]
theorem checked41959 : checkPrefixCuts (2^48) 5503582209 10 Manual.Count131072.C041959.packed 64 cuts41959 = true := by
 decide +kernel
def pointBounds41959 : List (Nat × Nat × Nat) := [(5503682560,109466673649704,109467059509765)]
theorem point_links_checked41959 : (cuts41959.take 1).map (fun c => (5503582209-1+2*2^10*c.k,109466445498659+c.lower,109466831358583+c.upper)) = pointBounds41959 := by
 decide +kernel
def cuts41960 : List PrefixCut := [⟨64,300204207,300204384⟩]
theorem checked41960 : checkPrefixCuts (2^48) 5503713281 10 Manual.Count131072.C041960.packed 64 cuts41960 = true := by
 decide +kernel
def cuts41961 : List PrefixCut := [⟨5,23576212,23576226⟩,
⟨64,301987024,301987198⟩]
theorem checked41961 : checkPrefixCuts (2^48) 5503844353 10 Manual.Count131072.C041961.packed 64 cuts41961 = true := by
 decide +kernel
def pointBounds41961 : List (Nat × Nat × Nat) := [(5503854592,109467065245563,109467451105859)]
theorem point_links_checked41961 : (cuts41961.take 1).map (fun c => (5503844353-1+2*2^10*c.k,109467041669351+c.lower,109467427529633+c.upper)) = pointBounds41961 := by
 decide +kernel
def cuts41962 : List PrefixCut := [⟨25,118235804,118235876⟩,
⟨64,301059327,301059506⟩]
theorem checked41962 : checkPrefixCuts (2^48) 5503975425 10 Manual.Count131072.C041962.packed 64 cuts41962 = true := by
 decide +kernel
def pointBounds41962 : List (Nat × Nat × Nat) := [(5504026624,109467461892179,109467847752707)]
theorem point_links_checked41962 : (cuts41962.take 1).map (fun c => (5503975425-1+2*2^10*c.k,109467343656375+c.lower,109467729516831+c.upper)) = pointBounds41962 := by
 decide +kernel
def cuts41963 : List PrefixCut := [⟨45,208543369,208543496⟩,
⟨64,297216722,297216903⟩]
theorem checked41963 : checkPrefixCuts (2^48) 5504106497 10 Manual.Count131072.C041963.packed 64 cuts41963 = true := by
 decide +kernel
def pointBounds41963 : List (Nat × Nat × Nat) := [(5504198656,109467853259071,109468239119833)]
theorem point_links_checked41963 : (cuts41963.take 1).map (fun c => (5504106497-1+2*2^10*c.k,109467644715702+c.lower,109468030576337+c.upper)) = pointBounds41963 := by
 decide +kernel
def cuts41964 : List PrefixCut := [⟨64,296698289,296698459⟩]
theorem checked41964 : checkPrefixCuts (2^48) 5504237569 10 Manual.Count131072.C041964.packed 64 cuts41964 = true := by
 decide +kernel
def cuts41965 : List PrefixCut := [⟨1,4909116,4909119⟩,
⟨64,301037775,301037952⟩]
theorem checked41965 : checkPrefixCuts (2^48) 5504368641 10 Manual.Count131072.C041965.packed 64 cuts41965 = true := by
 decide +kernel
def pointBounds41965 : List (Nat × Nat × Nat) := [(5504370688,109468243539829,109468629400818)]
theorem point_links_checked41965 : (cuts41965.take 1).map (fun c => (5504368641-1+2*2^10*c.k,109468238630713+c.lower,109468624491699+c.upper)) = pointBounds41965 := by
 decide +kernel
def cuts41966 : List PrefixCut := [⟨21,96901235,96901292⟩,
⟨64,294689909,294690082⟩]
theorem checked41966 : checkPrefixCuts (2^48) 5504499713 10 Manual.Count131072.C041966.packed 64 cuts41966 = true := by
 decide +kernel
def pointBounds41966 : List (Nat × Nat × Nat) := [(5504542720,109468636569723,109469022430943)]
theorem point_links_checked41966 : (cuts41966.take 1).map (fun c => (5504499713-1+2*2^10*c.k,109468539668488+c.lower,109468925529651+c.upper)) = pointBounds41966 := by
 decide +kernel
def cuts41967 : List PrefixCut := [⟨41,191802914,191803023⟩,
⟨64,296728244,296728415⟩]
theorem checked41967 : checkPrefixCuts (2^48) 5504630785 10 Manual.Count131072.C041967.packed 64 cuts41967 = true := by
 decide +kernel
def pointBounds41967 : List (Nat × Nat × Nat) := [(5504714752,109469026161311,109469412022756)]
theorem point_links_checked41967 : (cuts41967.take 1).map (fun c => (5504630785-1+2*2^10*c.k,109468834358397+c.lower,109469220219733+c.upper)) = pointBounds41967 := by
 decide +kernel
def cuts41968 : List PrefixCut := [⟨61,285165408,285165578⟩,
⟨64,299431179,299431358⟩]
theorem checked41968 : checkPrefixCuts (2^48) 5504761857 10 Manual.Count131072.C041968.packed 64 cuts41968 = true := by
 decide +kernel
def pointBounds41968 : List (Nat × Nat × Nat) := [(5504886784,109469416252049,109469802113726)]
theorem point_links_checked41968 : (cuts41968.take 1).map (fun c => (5504761857-1+2*2^10*c.k,109469131086641+c.lower,109469516948148+c.upper)) = pointBounds41968 := by
 decide +kernel
def cuts41969 : List PrefixCut := [⟨64,293339454,293339625⟩]
theorem checked41969 : checkPrefixCuts (2^48) 5504892929 10 Manual.Count131072.C041969.packed 64 cuts41969 = true := by
 decide +kernel
def cuts41970 : List PrefixCut := [⟨17,79303226,79303274⟩,
⟨64,297934146,297934324⟩]
theorem checked41970 : checkPrefixCuts (2^48) 5505024001 10 Manual.Count131072.C041970.packed 64 cuts41970 = true := by
 decide +kernel
def pointBounds41970 : List (Nat × Nat × Nat) := [(5505058816,109469803160500,109470189022405)]
theorem point_links_checked41970 : (cuts41970.take 1).map (fun c => (5505024001-1+2*2^10*c.k,109469723857274+c.lower,109470109719131+c.upper)) = pointBounds41970 := by
 decide +kernel
def cuts41971 : List PrefixCut := [⟨38,180792037,180792144⟩,
⟨64,299869988,299870168⟩]
theorem checked41971 : checkPrefixCuts (2^48) 5505155073 10 Manual.Count131072.C041971.packed 64 cuts41971 = true := by
 decide +kernel
def pointBounds41971 : List (Nat × Nat × Nat) := [(5505232896,109470202583457,109470588445599)]
theorem point_links_checked41971 : (cuts41971.take 1).map (fun c => (5505155073-1+2*2^10*c.k,109470021791420+c.lower,109470407653455+c.upper)) = pointBounds41971 := by
 decide +kernel
def cuts41972 : List PrefixCut := [⟨59,275168496,275168655⟩,
⟨64,298277875,298278047⟩]
theorem checked41972 : checkPrefixCuts (2^48) 5505286145 10 Manual.Count131072.C041972.packed 64 cuts41972 = true := by
 decide +kernel
def pointBounds41972 : List (Nat × Nat × Nat) := [(5505406976,109470596829904,109470982692278)]
theorem point_links_checked41972 : (cuts41972.take 1).map (fun c => (5505286145-1+2*2^10*c.k,109470321661408+c.lower,109470707523623+c.upper)) = pointBounds41972 := by
 decide +kernel
def cuts41973 : List PrefixCut := [⟨64,297094862,297095033⟩]
theorem checked41973 : checkPrefixCuts (2^48) 5505417217 10 Manual.Count131072.C041973.packed 64 cuts41973 = true := by
 decide +kernel
def cuts41974 : List PrefixCut := [⟨16,76534912,76534957⟩,
⟨64,299797429,299797601⟩]
theorem checked41974 : checkPrefixCuts (2^48) 5505548289 10 Manual.Count131072.C041974.packed 64 cuts41974 = true := by
 decide +kernel
def pointBounds41974 : List (Nat × Nat × Nat) := [(5505581056,109470993569057,109471379431660)]
theorem point_links_checked41974 : (cuts41974.take 1).map (fun c => (5505548289-1+2*2^10*c.k,109470917034145+c.lower,109471302896703+c.upper)) = pointBounds41974 := by
 decide +kernel
def cuts41975 : List PrefixCut := [⟨37,173668586,173668687⟩,
⟨64,296671731,296671903⟩]
theorem checked41975 : checkPrefixCuts (2^48) 5505679361 10 Manual.Count131072.C041975.packed 64 cuts41975 = true := by
 decide +kernel
def pointBounds41975 : List (Nat × Nat × Nat) := [(5505755136,109471390500160,109471776362991)]
theorem point_links_checked41975 : (cuts41975.take 1).map (fun c => (5505679361-1+2*2^10*c.k,109471216831574+c.lower,109471602694304+c.upper)) = pointBounds41975 := by
 decide +kernel
def cuts41976 : List PrefixCut := [⟨58,273710894,273711054⟩,
⟨64,301828041,301828217⟩]
theorem checked41976 : checkPrefixCuts (2^48) 5505810433 10 Manual.Count131072.C041976.packed 64 cuts41976 = true := by
 decide +kernel
def pointBounds41976 : List (Nat × Nat × Nat) := [(5505929216,109471787214199,109472173077261)]
theorem point_links_checked41976 : (cuts41976.take 1).map (fun c => (5505810433-1+2*2^10*c.k,109471513503305+c.lower,109471899366207+c.upper)) = pointBounds41976 := by
 decide +kernel
def cuts41977 : List PrefixCut := [⟨64,297731125,297731301⟩]
theorem checked41977 : checkPrefixCuts (2^48) 5505941505 10 Manual.Count131072.C041977.packed 64 cuts41977 = true := by
 decide +kernel
def cuts41978 : List PrefixCut := [⟨15,70035317,70035358⟩,
⟨64,300177826,300177993⟩]
theorem checked41978 : checkPrefixCuts (2^48) 5506072577 10 Manual.Count131072.C041978.packed 64 cuts41978 = true := by
 decide +kernel
def pointBounds41978 : List (Nat × Nat × Nat) := [(5506103296,109472183097788,109472568961083)]
theorem point_links_checked41978 : (cuts41978.take 1).map (fun c => (5506072577-1+2*2^10*c.k,109472113062471+c.lower,109472498925725+c.upper)) = pointBounds41978 := by
 decide +kernel
def cuts41979 : List PrefixCut := [⟨36,166699876,166699969⟩,
⟨64,300835208,300835381⟩]
theorem checked41979 : checkPrefixCuts (2^48) 5506203649 10 Manual.Count131072.C041979.packed 64 cuts41979 = true := by
 decide +kernel
def pointBounds41979 : List (Nat × Nat × Nat) := [(5506277376,109472579940173,109472965803687)]
theorem point_links_checked41979 : (cuts41979.take 1).map (fun c => (5506203649-1+2*2^10*c.k,109472413240297+c.lower,109472799103718+c.upper)) = pointBounds41979 := by
 decide +kernel
def cuts41980 : List PrefixCut := [⟨57,267959695,267959851⟩,
⟨64,300930306,300930480⟩]
theorem checked41980 : checkPrefixCuts (2^48) 5506334721 10 Manual.Count131072.C041980.packed 64 cuts41980 = true := by
 decide +kernel
def pointBounds41980 : List (Nat × Nat × Nat) := [(5506451456,109472982035200,109473367898950)]
theorem point_links_checked41980 : (cuts41980.take 1).map (fun c => (5506334721-1+2*2^10*c.k,109472714075505+c.lower,109473099939099+c.upper)) = pointBounds41980 := by
 decide +kernel
def cuts41981 : List PrefixCut := [⟨64,293766833,293767013⟩]
theorem checked41981 : checkPrefixCuts (2^48) 5506465793 10 Manual.Count131072.C041981.packed 64 cuts41981 = true := by
 decide +kernel
def cuts41982 : List PrefixCut := [⟨14,65326002,65326042⟩,
⟨64,299791426,299791603⟩]
theorem checked41982 : checkPrefixCuts (2^48) 5506596865 10 Manual.Count131072.C041982.packed 64 cuts41982 = true := by
 decide +kernel
def pointBounds41982 : List (Nat × Nat × Nat) := [(5506625536,109473374098646,109473759962634)]
theorem point_links_checked41982 : (cuts41982.take 1).map (fun c => (5506596865-1+2*2^10*c.k,109473308772644+c.lower,109473694636592+c.upper)) = pointBounds41982 := by
 decide +kernel
def cuts41983 : List PrefixCut := [⟨35,163514948,163515049⟩,
⟨64,295439633,295439811⟩]
theorem checked41983 : checkPrefixCuts (2^48) 5506727937 10 Manual.Count131072.C041983.packed 64 cuts41983 = true := by
 decide +kernel
def pointBounds41983 : List (Nat × Nat × Nat) := [(5506799616,109473772079018,109474157943244)]
theorem point_links_checked41983 : (cuts41983.take 1).map (fun c => (5506727937-1+2*2^10*c.k,109473608564070+c.lower,109473994428195+c.upper)) = pointBounds41983 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000061
