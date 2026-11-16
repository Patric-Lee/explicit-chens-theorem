import PlattAssemblyKernel
import PlattCertificates.Count131072.C075920
import PlattCertificates.Count131072.C075921
import PlattCertificates.Count131072.C075922
import PlattCertificates.Count131072.C075923
import PlattCertificates.Count131072.C075924
import PlattCertificates.Count131072.C075925
import PlattCertificates.Count131072.C075926
import PlattCertificates.Count131072.C075927
import PlattCertificates.Count131072.C075928
import PlattCertificates.Count131072.C075929
import PlattCertificates.Count131072.C075930
import PlattCertificates.Count131072.C075931
import PlattCertificates.Count131072.C075932
import PlattCertificates.Count131072.C075933
import PlattCertificates.Count131072.C075934
import PlattCertificates.Count131072.C075935
import PlattCertificates.Count131072.C075936
import PlattCertificates.Count131072.C075937
import PlattCertificates.Count131072.C075938
import PlattCertificates.Count131072.C075939
import PlattCertificates.Count131072.C075940
import PlattCertificates.Count131072.C075941
import PlattCertificates.Count131072.C075942
import PlattCertificates.Count131072.C075943
import PlattCertificates.Count131072.C075944
import PlattCertificates.Count131072.C075945
import PlattCertificates.Count131072.C075946
import PlattCertificates.Count131072.C075947
import PlattCertificates.Count131072.C075948
import PlattCertificates.Count131072.C075949
import PlattCertificates.Count131072.C075950
import PlattCertificates.Count131072.C075951
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000185
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75920 : List PrefixCut := [⟨64,162523388,162523488⟩]
theorem checked75920 : checkPrefixCuts (2^48) 9954918401 10 Manual.Count131072.C075920.packed 64 cuts75920 = true := by
 decide +kernel
def cuts75921 : List PrefixCut := [⟨59,147083503,147083592⟩,
⟨64,160683407,160683503⟩]
theorem checked75921 : checkPrefixCuts (2^48) 9955049473 10 Manual.Count131072.C075921.packed 64 cuts75921 = true := by
 decide +kernel
def pointBounds75921 : List (Nat × Nat × Nat) := [(9955170304,116808080932231,116808471029465)]
theorem point_links_checked75921 : (cuts75921.take 1).map (fun c => (9955049473-1+2*2^10*c.k,116807933848728+c.lower,116808323945873+c.upper)) = pointBounds75921 := by
 decide +kernel
def cuts75922 : List PrefixCut := [⟨64,160144096,160144189⟩]
theorem checked75922 : checkPrefixCuts (2^48) 9955180545 10 Manual.Count131072.C075922.packed 64 cuts75922 = true := by
 decide +kernel
def cuts75923 : List PrefixCut := [⟨64,161188102,161188202⟩]
theorem checked75923 : checkPrefixCuts (2^48) 9955311617 10 Manual.Count131072.C075923.packed 64 cuts75923 = true := by
 decide +kernel
def cuts75924 : List PrefixCut := [⟨19,47697249,47697277⟩,
⟨64,161440443,161440538⟩]
theorem checked75924 : checkPrefixCuts (2^48) 9955442689 10 Manual.Count131072.C075924.packed 64 cuts75924 = true := by
 decide +kernel
def pointBounds75924 : List (Nat × Nat × Nat) := [(9955481600,116808463561582,116808853659044)]
theorem point_links_checked75924 : (cuts75924.take 1).map (fun c => (9955442689-1+2*2^10*c.k,116808415864333+c.lower,116808805961767+c.upper)) = pointBounds75924 := by
 decide +kernel
def cuts75925 : List PrefixCut := [⟨64,161692774,161692864⟩]
theorem checked75925 : checkPrefixCuts (2^48) 9955573761 10 Manual.Count131072.C075925.packed 64 cuts75925 = true := by
 decide +kernel
def cuts75926 : List PrefixCut := [⟨43,107605511,107605577⟩,
⟨64,161068644,161068745⟩]
theorem checked75926 : checkPrefixCuts (2^48) 9955704833 10 Manual.Count131072.C075926.packed 64 cuts75926 = true := by
 decide +kernel
def pointBounds75926 : List (Nat × Nat × Nat) := [(9955792896,116808846603061,116809236700746)]
theorem point_links_checked75926 : (cuts75926.take 1).map (fun c => (9955704833-1+2*2^10*c.k,116808738997550+c.lower,116809129095169+c.upper)) = pointBounds75926 := by
 decide +kernel
def cuts75927 : List PrefixCut := [⟨64,161320970,161321065⟩]
theorem checked75927 : checkPrefixCuts (2^48) 9955835905 10 Manual.Count131072.C075927.packed 64 cuts75927 = true := by
 decide +kernel
def cuts75928 : List PrefixCut := [⟨64,159876992,159877087⟩]
theorem checked75928 : checkPrefixCuts (2^48) 9955966977 10 Manual.Count131072.C075928.packed 64 cuts75928 = true := by
 decide +kernel
def cuts75929 : List PrefixCut := [⟨3,7378888,7378892⟩,
⟨64,159422545,159422642⟩]
theorem checked75929 : checkPrefixCuts (2^48) 9956098049 10 Manual.Count131072.C075929.packed 64 cuts75929 = true := by
 decide +kernel
def pointBounds75929 : List (Nat × Nat × Nat) := [(9956104192,116809228643044,116809618740958)]
theorem point_links_checked75929 : (cuts75929.take 1).map (fun c => (9956098049-1+2*2^10*c.k,116809221264156+c.lower,116809611362066+c.upper)) = pointBounds75929 := by
 decide +kernel
def cuts75930 : List PrefixCut := [⟨64,159618346,159618444⟩]
theorem checked75930 : checkPrefixCuts (2^48) 9956229121 10 Manual.Count131072.C075930.packed 64 cuts75930 = true := by
 decide +kernel
def cuts75931 : List PrefixCut := [⟨27,69828834,69828879⟩,
⟨64,161934442,161934544⟩]
theorem checked75931 : checkPrefixCuts (2^48) 9956360193 10 Manual.Count131072.C075931.packed 64 cuts75931 = true := by
 decide +kernel
def pointBounds75931 : List (Nat × Nat × Nat) := [(9956415488,116809610133881,116810000232031)]
theorem point_links_checked75931 : (cuts75931.take 1).map (fun c => (9956360193-1+2*2^10*c.k,116809540305047+c.lower,116809930403152+c.upper)) = pointBounds75931 := by
 decide +kernel
def cuts75932 : List PrefixCut := [⟨64,162667326,162667422⟩]
theorem checked75932 : checkPrefixCuts (2^48) 9956491265 10 Manual.Count131072.C075932.packed 64 cuts75932 = true := by
 decide +kernel
def cuts75933 : List PrefixCut := [⟨51,126451578,126451650⟩,
⟨64,159866463,159866553⟩]
theorem checked75933 : checkPrefixCuts (2^48) 9956622337 10 Manual.Count131072.C075933.packed 64 cuts75933 = true := by
 decide +kernel
def pointBounds75933 : List (Nat × Nat × Nat) := [(9956726784,116809991358393,116810381456768)]
theorem point_links_checked75933 : (cuts75933.take 1).map (fun c => (9956622337-1+2*2^10*c.k,116809864906815+c.lower,116810255005118+c.upper)) = pointBounds75933 := by
 decide +kernel
def cuts75934 : List PrefixCut := [⟨64,163652475,163652570⟩]
theorem checked75934 : checkPrefixCuts (2^48) 9956753409 10 Manual.Count131072.C075934.packed 64 cuts75934 = true := by
 decide +kernel
def cuts75935 : List PrefixCut := [⟨64,156243806,156243901⟩]
theorem checked75935 : checkPrefixCuts (2^48) 9956884481 10 Manual.Count131072.C075935.packed 64 cuts75935 = true := by
 decide +kernel
def cuts75936 : List PrefixCut := [⟨11,28721274,28721288⟩,
⟨64,164072212,164072301⟩]
theorem checked75936 : checkPrefixCuts (2^48) 9957015553 10 Manual.Count131072.C075936.packed 64 cuts75936 = true := by
 decide +kernel
def pointBounds75936 : List (Nat × Nat × Nat) := [(9957038080,116810373390833,116810763489430)]
theorem point_links_checked75936 : (cuts75936.take 1).map (fun c => (9957015553-1+2*2^10*c.k,116810344669559+c.lower,116810734768142+c.upper)) = pointBounds75936 := by
 decide +kernel
def cuts75937 : List PrefixCut := [⟨64,159547094,159547191⟩]
theorem checked75937 : checkPrefixCuts (2^48) 9957146625 10 Manual.Count131072.C075937.packed 64 cuts75937 = true := by
 decide +kernel
def cuts75938 : List PrefixCut := [⟨35,88055308,88055355⟩,
⟨64,161354155,161354242⟩]
theorem checked75938 : checkPrefixCuts (2^48) 9957277697 10 Manual.Count131072.C075938.packed 64 cuts75938 = true := by
 decide +kernel
def pointBounds75938 : List (Nat × Nat × Nat) := [(9957349376,116810756344173,116811146442989)]
theorem point_links_checked75938 : (cuts75938.take 1).map (fun c => (9957277697-1+2*2^10*c.k,116810668288865+c.lower,116811058387634+c.upper)) = pointBounds75938 := by
 decide +kernel
def cuts75939 : List PrefixCut := [⟨64,163726519,163726613⟩]
theorem checked75939 : checkPrefixCuts (2^48) 9957408769 10 Manual.Count131072.C075939.packed 64 cuts75939 = true := by
 decide +kernel
def cuts75940 : List PrefixCut := [⟨59,148742759,148742844⟩,
⟨64,161745651,161745744⟩]
theorem checked75940 : checkPrefixCuts (2^48) 9957539841 10 Manual.Count131072.C075940.packed 64 cuts75940 = true := by
 decide +kernel
def pointBounds75940 : List (Nat × Nat × Nat) := [(9957660672,116811142112298,116811532211333)]
theorem point_links_checked75940 : (cuts75940.take 1).map (fun c => (9957539841-1+2*2^10*c.k,116810993369539+c.lower,116811383468489+c.upper)) = pointBounds75940 := by
 decide +kernel
def cuts75941 : List PrefixCut := [⟨64,161800045,161800139⟩]
theorem checked75941 : checkPrefixCuts (2^48) 9957670913 10 Manual.Count131072.C075941.packed 64 cuts75941 = true := by
 decide +kernel
def cuts75942 : List PrefixCut := [⟨64,159480063,159480165⟩]
theorem checked75942 : checkPrefixCuts (2^48) 9957801985 10 Manual.Count131072.C075942.packed 64 cuts75942 = true := by
 decide +kernel
def cuts75943 : List PrefixCut := [⟨19,47119989,47120019⟩,
⟨64,159591022,159591114⟩]
theorem checked75943 : checkPrefixCuts (2^48) 9957933057 10 Manual.Count131072.C075943.packed 64 cuts75943 = true := by
 decide +kernel
def pointBounds75943 : List (Nat × Nat × Nat) := [(9957971968,116811523515287,116811913614556)]
theorem point_links_checked75943 : (cuts75943.take 1).map (fun c => (9957933057-1+2*2^10*c.k,116811476395298+c.lower,116811866494537+c.upper)) = pointBounds75943 := by
 decide +kernel
def cuts75944 : List PrefixCut := [⟨64,161539267,161539363⟩]
theorem checked75944 : checkPrefixCuts (2^48) 9958064129 10 Manual.Count131072.C075944.packed 64 cuts75944 = true := by
 decide +kernel
def cuts75945 : List PrefixCut := [⟨43,106815436,106815500⟩,
⟨64,159219380,159219473⟩]
theorem checked75945 : checkPrefixCuts (2^48) 9958195201 10 Manual.Count131072.C075945.packed 64 cuts75945 = true := by
 decide +kernel
def pointBounds75945 : List (Nat × Nat × Nat) := [(9958283264,116811904341023,116812294440514)]
theorem point_links_checked75945 : (cuts75945.take 1).map (fun c => (9958195201-1+2*2^10*c.k,116811797525587+c.lower,116812187625014+c.upper)) = pointBounds75945 := by
 decide +kernel
def cuts75946 : List PrefixCut := [⟨64,162043789,162043893⟩]
theorem checked75946 : checkPrefixCuts (2^48) 9958326273 10 Manual.Count131072.C075946.packed 64 cuts75946 = true := by
 decide +kernel
def cuts75947 : List PrefixCut := [⟨64,160826270,160826365⟩]
theorem checked75947 : checkPrefixCuts (2^48) 9958457345 10 Manual.Count131072.C075947.packed 64 cuts75947 = true := by
 decide +kernel
def cuts75948 : List PrefixCut := [⟨3,7801010,7801015⟩,
⟨64,162322165,162322258⟩]
theorem checked75948 : checkPrefixCuts (2^48) 9958588417 10 Manual.Count131072.C075948.packed 64 cuts75948 = true := by
 decide +kernel
def pointBounds75948 : List (Nat × Nat × Nat) := [(9958594560,116812287416036,116812677515760)]
theorem point_links_checked75948 : (cuts75948.take 1).map (fun c => (9958588417-1+2*2^10*c.k,116812279615026+c.lower,116812669714745+c.upper)) = pointBounds75948 := by
 decide +kernel
def cuts75949 : List PrefixCut := [⟨64,159917591,159917687⟩]
theorem checked75949 : checkPrefixCuts (2^48) 9958719489 10 Manual.Count131072.C075949.packed 64 cuts75949 = true := by
 decide +kernel
def cuts75950 : List PrefixCut := [⟨27,68285131,68285172⟩,
⟨64,159519799,159519894⟩]
theorem checked75950 : checkPrefixCuts (2^48) 9958850561 10 Manual.Count131072.C075950.packed 64 cuts75950 = true := by
 decide +kernel
def pointBounds75950 : List (Nat × Nat × Nat) := [(9958905856,116812670139913,116813060239862)]
theorem point_links_checked75950 : (cuts75950.take 1).map (fun c => (9958850561-1+2*2^10*c.k,116812601854782+c.lower,116812991954690+c.upper)) = pointBounds75950 := by
 decide +kernel
def cuts75951 : List PrefixCut := [⟨64,161807009,161807103⟩]
theorem checked75951 : checkPrefixCuts (2^48) 9958981633 10 Manual.Count131072.C075951.packed 64 cuts75951 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000185
